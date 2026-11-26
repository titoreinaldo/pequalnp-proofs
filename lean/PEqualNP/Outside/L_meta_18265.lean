import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18265
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Ref := Bool ⊕ Nat

def evalRef (w : List Bool) : Ref → Bool
  | .inl b => b
  | .inr j => w.getD j false

def isFalseRef : Ref → Bool
  | .inl b => !b
  | .inr _ => false

def isTrueRef : Ref → Bool
  | .inl b => b
  | .inr _ => false

def liveRef : Ref → Option Nat
  | .inl _ => none
  | .inr i => some i

def shrink (op : GateOp) (xs : List Ref) : Gate :=
  if op.eval [false,true] then
    if xs.any isTrueRef then ⟨.and, []⟩ else ⟨.or,xs.filterMap liveRef⟩
  else
    if xs.any isFalseRef then ⟨.or, []⟩ else ⟨.and,xs.filterMap liveRef⟩

lemma wireAll (w : List Bool) (xs : List Ref) :
    (xs.map (evalRef w)).all id =
       (!xs.any isFalseRef && ((xs.filterMap liveRef).map fun j => w.getD j false).all id) := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with b|j
    · cases b <;> simp [evalRef,isFalseRef,liveRef,ih]
    · simp [evalRef,isFalseRef,liveRef,ih,Bool.and_comm,Bool.and_left_comm]

lemma wireAny (w : List Bool) (xs : List Ref) :
    (xs.map (evalRef w)).any id =
       (xs.any isTrueRef || ((xs.filterMap liveRef).map fun j => w.getD j false).any id) := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with b|j
    · cases b <;> simp [evalRef,isTrueRef,liveRef,ih]
    · simp [evalRef,isTrueRef,liveRef,ih,Bool.or_comm,Bool.or_left_comm]

lemma shrink_eval (w : List Bool) (o : GateOp) (xs : List Ref)
    (ho : o = .and ∨ o = .or) :
    (shrink o xs).op.eval ((shrink o xs).inputs.map fun j => w.getD j false) =
       o.eval (xs.map (evalRef w)) := by
  rcases ho with rfl|rfl
  · rw [show GateOp.and.eval _ = (xs.map (evalRef w)).all id by rfl, wireAll]
    cases hh : xs.any isFalseRef <;> simp [shrink,GateOp.eval,hh]
  · rw [show GateOp.or.eval _ = (xs.map (evalRef w)).any id by rfl, wireAny]
    cases hh : xs.any isTrueRef <;> simp [shrink,GateOp.eval,hh]

lemma shrink_mono (o : GateOp) (xs : List Ref) (h : xs.length ≤ 2) :
    (shrink o xs).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
      (shrink o xs).inputs.length ≤ 2 := by
  have h' : (xs.filterMap liveRef).length ≤ 2 := (List.length_filterMap_le liveRef xs).trans h
  unfold shrink
  split <;> split <;> simp [h']

structure Bank where
  gates : List Gate
  names : List Ref

def refAt (s : Bank) (i : Nat) : Ref := s.names.getD i (.inl false)

def init (n : Nat) : Bank := ⟨[], (List.range n).map Sum.inr⟩

def addGate (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) : Bank :=
  match kill with
  | some (.inl b) => ⟨s.gates,s.names ++ [.inl b]⟩
  | some (.inr j) => ⟨s.gates,s.names ++ [refAt s j]⟩
  | none => ⟨s.gates ++ [shrink g.op (g.inputs.map (refAt s))],
       s.names ++ [.inr (n + s.gates.length)]⟩

@[simp] lemma addGateNamesSize (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) :
    (addGate n s g kill).names.length = s.names.length + 1 := by
  cases kill with
  | none => simp [addGate]
  | some k => cases k <;> simp [addGate]

lemma addGateSize (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) :
    (addGate n s g kill).gates.length = s.gates.length + if kill.isSome then 0 else 1 := by
  cases kill with
  | none => simp [addGate]
  | some k => cases k <;> simp [addGate]

def loop (n : Nat) (kill : Nat → Option Ref) (j : Nat) (s : Bank) : List Gate → Bank
  | [] => s
  | g::gs => loop n kill (j+1) (addGate n s g (kill j)) gs


def consistent (s : Bank) (old new : List Bool) : Prop :=
  old.length = s.names.length ∧
    (∀ i, evalRef new (refAt s i) = old.getD i false) ∧
    (∀ i ∈ s.names, ∀ j, i = .inr j → j < new.length)

def appendValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

lemma preserveRef (s : Bank) (old new : List Bool) (h : consistent s old new) (i : Nat) (b : Bool) :
    evalRef (new ++ [b]) (refAt s i) = evalRef new (refAt s i) := by
  generalize hr : refAt s i = q
  cases q with
  | inl b' => rfl
  | inr j =>
    have hj : j < new.length := by
      apply h.2.2 (.inr j) _ j rfl
      by_cases hi : i < s.names.length
      · have he : s.names[i] = Sum.inr j := by
          unfold refAt at hr
          rw [List.getD_eq_getElem _ _ hi] at hr
          exact hr
        rw [← he]; exact List.getElem_mem hi
      · have hn : s.names.length ≤ i := by omega
        unfold refAt at hr
        rw [List.getD_eq_default _ _ hn] at hr
        contradiction
    exact List.getD_append _ _ _ _ hj

lemma add_end {α : Type} (s : List α) (x d : α) (i : Nat) :
    (s ++ [x]).getD i d = if i = s.length then x else s.getD i d := by
  by_cases hi : i < s.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
  · by_cases he : i = s.length
    · subst i; simp
    · have h1 : s.length ≤ i := by omega
      have h2 : (s ++ [x]).length ≤ i := by simp; omega
      rw [ite_eq_right he, List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

lemma newGateEval (s : Bank) (old new : List Bool) (g : Gate) (h : consistent s old new)
    (ho : g.op = .and ∨ g.op = .or) :
    appendValue new (shrink g.op (g.inputs.map (refAt s))) = appendValue old g := by
  unfold appendValue
  rw [shrink_eval _ _ _ ho, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h.2.1 i

lemma validCurrent {s : Bank} {w : List Bool}
    (h : ∀ r ∈ s.names, ∀ j, r = .inr j → j < w.length) (i j : Nat)
    (hr : refAt s i = .inr j) : j < w.length := by
  apply h (.inr j) _ j rfl
  by_cases hi : i < s.names.length
  · have hh : s.names[i] = Sum.inr j := by
      unfold refAt at hr
      rw [List.getD_eq_getElem _ _ hi] at hr
      exact hr
    rw [← hh]; exact List.getElem_mem hi
  · have hn : s.names.length ≤ i := by omega
    unfold refAt at hr
    rw [List.getD_eq_default _ _ hn] at hr
    contradiction


def addLiveValues (n : Nat) (s : Bank) (g : Gate) (kill : Option Ref) (new : List Bool) :=
  if kill.isSome then new else new ++ [appendValue new (shrink g.op (g.inputs.map (refAt s)))]

lemma consKeep (n : Nat) (s : Bank) (old new : List Bool) (g : Gate)
    (h : consistent s old new) (hnew : new.length = n + s.gates.length)
    (ho : g.op = .and ∨ g.op = .or) :
    consistent (addGate n s g none) (old ++ [appendValue old g]) (addLiveValues n s g none new) := by
  let b := appendValue new (shrink g.op (g.inputs.map (refAt s)))
  have eqb : b = appendValue old g := newGateEval s old new g h ho
  change (old ++ [appendValue old g]).length = (s.names ++ [Sum.inr (n + s.gates.length)]).length ∧
    (∀ i, evalRef (new ++ [b]) ((s.names ++ [Sum.inr (n + s.gates.length)]).getD i (.inl false)) =
      (old ++ [appendValue old g]).getD i false) ∧ _
  refine ⟨by simp [h.1], ?_, ?_⟩
  · intro i
    rw [add_end,add_end,h.1]
    by_cases hi : i = s.names.length
    · simp only [hi,ite_eq_left rfl,evalRef,← hnew]
      simp [eqb]
    · simp only [ite_eq_right hi]
      exact (preserveRef s old new h i b).trans (h.2.1 i)
  · intro q hq j hj
    simp only [addGate,List.mem_append,List.mem_singleton] at hq
    rcases hq with hq|rfl
    · have hv := h.2.2 q hq j hj
      simp [addLiveValues]; omega
    · simp only [Sum.inr.injEq] at hj
      simp [addLiveValues]; omega

def resolve (s : Bank) : Ref → Ref
  | .inl b => .inl b
  | .inr i => refAt s i

lemma consKill (n : Nat) (s : Bank) (old new : List Bool) (g : Gate) (mark : Ref)
    (h : consistent s old new)
    (hm : evalRef new (resolve s mark) = appendValue old g) :
    consistent (addGate n s g (some mark)) (old ++ [appendValue old g])
      (addLiveValues n s g (some mark) new) := by
  let q : Ref := resolve s mark
  have eS : addGate n s g (some mark) = ⟨s.gates, s.names ++ [q]⟩ := by
    cases mark <;> rfl
  rw [eS]
  change (old ++ [_]).length = (s.names ++ [q]).length ∧
    (∀ i, evalRef new ((s.names ++ [q]).getD i (.inl false)) = (old ++ [appendValue old g]).getD i false) ∧ _
  refine ⟨by simp [h.1], ?_, ?_⟩
  · intro i
    rw [add_end,add_end,h.1]
    by_cases hi : i = s.names.length
    · rw [ite_eq_left hi, ite_eq_left hi]
      simpa only [q] using hm
    · rw [ite_eq_right hi, ite_eq_right hi]
      exact h.2.1 i
  · intro r hr j hj
    simp only [List.mem_append,List.mem_singleton] at hr
    rcases hr with h0|rfl
    · exact h.2.2 r h0 j hj
    · cases mark with
      | inl x => contradiction
      | inr i => exact validCurrent h.2.2 i j hj


def run (gs : List Gate) (v : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [appendValue w g]) v

lemma run_pres (gs : List Gate) (v : List Bool) (j : Nat) (hj : j < v.length) :
    (run gs v).getD j false = v.getD j false := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (v ++ [appendValue v g])).getD j false = _
    rw [ih _ (by simp;omega), List.getD_append _ _ _ _ hj]

lemma runLen (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [appendValue w g])).length = _
    rw [ih]; simp; omega

lemma runHead (g : Gate) (gs : List Gate) (w : List Bool) :
    (run (g::gs) w).getD w.length false = appendValue w g := by
  change (run gs (w ++ [appendValue w g])).getD w.length false = _
  rw [run_pres _ _ _ (by simp)]
  simp

def Good (kill : Nat → Option Ref) (j : Nat) (gs : List Gate) (old : List Bool) : Prop :=
  ∀ i, i < gs.length →
    let f := run gs old
    match kill (j+i) with
    | none => True
    | some (.inl b) => f.getD (old.length+i) false = b
    | some (.inr w) => w < old.length+i ∧ f.getD (old.length+i) false = f.getD w false

lemma good_tail {kill : Nat → Option Ref} {j : Nat} {g : Gate} {gs : List Gate} {old : List Bool}
    (h : Good kill j (g::gs) old) :
    Good kill (j+1) gs (old ++ [appendValue old g]) := by
  intro i hi
  have he := h (i+1) (by simpa using hi)
  simp only [List.length_append,List.length_singleton] at *
  have hj : j + (i+1) = j+1+i := by omega
  rw [hj] at he
  have hlen : old.length+(i+1) = old.length+1+i := by omega
  rw [hlen] at he
  exact he

lemma good_head {kill : Nat → Option Ref} {j : Nat} {g : Gate} {gs : List Gate} {old : List Bool}
    (h : Good kill j (g::gs) old) (r : Ref) (hr : kill j = some r) :
    (match r with | .inl b => b | .inr w => old.getD w false) = appendValue old g := by
  have hh := h 0 (by simp)
  simp only [Nat.add_zero, hr] at hh
  cases r with
  | inl b =>
    change (run (g::gs) old).getD old.length false = b at hh
    rw [runHead] at hh
    exact hh.symm
  | inr w =>
    change w < old.length ∧
      (run (g::gs) old).getD old.length false = (run (g::gs) old).getD w false at hh
    rw [runHead,run_pres _ _ _ hh.1] at hh
    exact hh.2.symm


lemma loopConsistent (n : Nat) (kill : Nat → Option Ref) (j : Nat)
    (s : Bank) (gs : List Gate) (old new : List Bool)
    (hmono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hgood : Good kill j gs old) (hc : consistent s old new)
    (hn : new = run s.gates (new.take n)) (hi : n ≤ new.length)
    (hlen : new.length = n + s.gates.length) :
    consistent (loop n kill j s gs) (run gs old)
      (run (loop n kill j s gs).gates (new.take n)) := by
  induction gs generalizing j s old new with
  | nil =>
    change consistent s old (run s.gates (new.take n))
    rw [← hn]
    exact hc
  | cons g gs ih =>
    let N := addGate n s g (kill j)
    let v := addLiveValues n s g (kill j) new
    have hv : v = run N.gates (new.take n) := by
      cases hk : kill j with
      | none =>
        change addLiveValues n s g (kill j) new = run (addGate n s g (kill j)).gates _
        simp only [hk,addLiveValues,Option.isSome_none, Bool.false_eq_true, ite_eq_right,
          addGate,run,List.foldl_append,List.foldl_cons,List.foldl_nil]
        exact congrArg (fun w => w ++ [appendValue w (shrink g.op (g.inputs.map (refAt s)))]) hn
      | some m =>
        cases m <;> simpa [v,N,hk,addLiveValues,addGate] using hn
    have ht : v.take n = new.take n := by
      change (addLiveValues n s g (kill j) new).take n = _
      cases hk : kill j <;> simp [addLiveValues,hk,List.take_append,hi]
    have hvl : v.length = n + N.gates.length := by
      rw [hv,runLen,List.length_take,Nat.min_eq_left hi]
    have hcn : consistent N (old ++ [appendValue old g]) v := by
      change consistent (addGate n s g (kill j)) _ (addLiveValues n s g (kill j) new)
      cases hk : kill j with
      | none => simpa [hk] using consKeep n s old new g hc hlen (hmono g List.mem_cons_self)
      | some m =>
        have hm := good_head hgood m hk
        have he : evalRef new (resolve s m) =
            appendValue old g := by
          cases m with
          | inl b => exact hm
          | inr i => exact (hc.2.1 i).trans hm
        simpa [hk] using consKill n s old new g m hc he
    have H := ih (j+1) N (old ++ [appendValue old g]) v
      (fun g hg => hmono g (List.mem_cons_of_mem _ hg)) (good_tail hgood) hcn
      (by rw [ht]; exact hv) (by omega) hvl
    rw [ht] at H
    exact H


def killedCount (kill : Nat → Option Ref) (j g : Nat) : Nat :=
  ((List.range' j g).filter (fun i => (kill i).isSome)).length

theorem loopSize (n : Nat) (kill : Nat → Option Ref) (j : Nat)
    (s : Bank) (gs : List Gate) :
    (loop n kill j s gs).gates.length + killedCount kill j gs.length =
       s.gates.length + gs.length := by
  induction gs generalizing j s with
  | nil => simp [loop,killedCount]
  | cons g gs ih =>
    have he := ih (j+1) (addGate n s g (kill j))
    simp only [addGateSize] at he
    simp only [loop,List.length_cons,killedCount,List.range'_succ,List.filter_cons]
    unfold killedCount at he
    cases hk : kill j <;> simp [hk] at * <;> omega

theorem loopMono (n : Nat) (kill : Nat → Option Ref) (j : Nat)
    (s : Bank) (gs : List Gate)
    (hs : Monotone2 ⟨s.gates,0⟩) (hg : Monotone2 ⟨gs,0⟩) :
    Monotone2 ⟨(loop n kill j s gs).gates,0⟩ := by
  induction gs generalizing j s with
  | nil => exact hs
  | cons g gs ih =>
    simp only [loop]
    apply ih
    · intro a ha
      change a ∈ (addGate n s g (kill j)).gates at ha
      have hlen := (hg g List.mem_cons_self).2
      cases hk : kill j with
      | none =>
        simp only [hk,addGate,List.mem_append,List.mem_singleton] at ha
        rcases ha with ha|rfl
        · exact hs a ha
        · exact shrink_mono _ _ (by simpa using hlen)
      | some r =>
        cases r <;> exact hs a (by simpa [hk,addGate] using ha)
    · intro a ha
      exact hg a (List.mem_cons_of_mem _ ha)


lemma refAt_init (n i : Nat) :
    refAt (init n) i = if i < n then .inr i else .inl false := by
  simp only [refAt,init,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range]
  by_cases h : i < n <;> simp [h]

lemma init_consistent (v : List Bool) : consistent (init v.length) v v := by
  refine ⟨by simp [init], ?_, ?_⟩
  · intro i
    rw [refAt_init]
    by_cases h : i < v.length
    · simp [h,evalRef]
    · simp only [ite_eq_right h,evalRef]
      symm; exact List.getD_eq_default _ _ (by omega)
  · intro r hr i hi
    subst r
    change Sum.inr i ∈ (List.range v.length).map Sum.inr at hr
    simpa using hr

lemma names_extend (n : Nat) (s : Bank) (g : Gate) (k : Option Ref) :
    ∃ r, (addGate n s g k).names = s.names ++ [r] := by
  cases k with
  | none => exact ⟨_, rfl⟩
  | some r => cases r <;> exact ⟨_,rfl⟩

lemma loopNamesLen (n : Nat) (k : Nat → Option Ref) (j : Nat) (s : Bank) (gs : List Gate) :
    (loop n k j s gs).names.length = s.names.length + gs.length := by
  induction gs generalizing j s with
  | nil => simp [loop]
  | cons g gs ih =>
    simp only [loop,ih,addGateNamesSize,List.length_cons]
    omega

lemma loopRef_pres (n : Nat) (k : Nat → Option Ref) (j : Nat) (s : Bank) (gs : List Gate)
    (i : Nat) (hi : i < s.names.length) :
    refAt (loop n k j s gs) i = refAt s i := by
  induction gs generalizing j s with
  | nil => rfl
  | cons g gs ih =>
    simp only [loop]
    rw [ih _ _ (by simp;omega)]
    obtain ⟨r,hr⟩ := names_extend n s g (k j)
    unfold refAt
    rw [hr,List.getD_append _ _ _ _ hi]

lemma loopRef_live (n : Nat) (k : Nat → Option Ref) (j : Nat) (s : Bank) (gs : List Gate)
    (i : Nat) (hi : i < gs.length) (hk : k (j+i) = none) :
    ∃ w, refAt (loop n k j s gs) (s.names.length+i) = .inr w := by
  induction gs generalizing j s i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero =>
      simp only [Nat.add_zero] at hk ⊢
      simp only [loop]
      rw [loopRef_pres _ _ _ _ _ _ (by simp)]
      refine ⟨n+s.gates.length, ?_⟩
      simp [refAt,addGate,hk]
    | succ i =>
      simp only [loop]
      have he : j + (i+1) = j+1+i := by omega
      rw [he] at hk
      obtain ⟨r,hr⟩ := ih (j+1) (addGate n s g (k j)) i (by simpa using hi) hk
      refine ⟨r,?_⟩
      rw [addGateNamesSize] at hr
      rwa [show s.names.length + (i+1) = s.names.length + 1 + i by omega]

end PEqualNP.Outside.L_meta_18265


open PEqualNP.Outside.L_meta_18265 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_18265 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (ZL : Finset (Fin n)) (ZR : Finset (Fin m))
  (K : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.Represents.Represents A C →
  (∀ j ∈ K, j < C.gates.length ∧ n + m + j ≠ C.output ∧
    ((∃ b : Bool, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false = b) ∨
     (∃ w < n + m + j, ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR →
        (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + j) false =
          (C.wires (PEqualNP.Represents.oneEach u v)).getD w false))) →
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size + K.card ≤ C.size ∧
    ∀ (u : Fin n) (v : Fin m), u ∉ ZL → v ∉ ZR → C'.eval (PEqualNP.Represents.oneEach u v) = A u v := by
  intro n m A C ZL ZR K hmono hrep hb
  classical
  let N := n+m
  let holds (j : Nat) (r : Ref) : Prop :=
    match r with
    | .inl b => ∀ u v, u ∉ ZL → v ∉ ZR →
        (C.wires (oneEach u v)).getD (N+j) false = b
    | .inr w => w < N+j ∧ ∀ u v, u ∉ ZL → v ∉ ZR →
        (C.wires (oneEach u v)).getD (N+j) false =
          (C.wires (oneEach u v)).getD w false
  have someR (j : Nat) (hj : j ∈ K) : ∃ r, holds j r := by
    rcases (hb j hj).2.2 with ⟨b,hb⟩|⟨w,hw,he⟩
    · exact ⟨.inl b, hb⟩
    · exact ⟨.inr w, hw, he⟩
  let kill (j : Nat) : Option Ref := if hj : j ∈ K then some (Classical.choose (someR j hj)) else none
  let S : Bank := loop N kill 0 (init N) C.gates
  let o := match refAt S C.output with | .inr r => r | .inl _ => N + S.gates.length
  let D : Circuit := ⟨S.gates,o⟩
  have monoD : Monotone2 D := loopMono N kill 0 (init N) C.gates (by simp [Monotone2,init]) hmono
  have killsEq : killedCount kill 0 C.gates.length = K.card := by
    unfold killedCount
    let L := (List.range' 0 C.gates.length).filter (fun j => (kill j).isSome)
    have nd : L.Nodup := by
      unfold L
      apply List.Nodup.filter
      exact List.nodup_range' _
    have hK : L.toFinset = K := by
      ext j
      simp only [L,List.mem_toFinset,List.mem_filter]
      by_cases hj : j ∈ K
      · have hj' := (hb j hj).1
        simp [kill,hj,List.mem_range',hj']
      · simp [kill,hj]
    rw [← hK,List.toFinset_card_of_nodup nd]
  have sizeD : D.size + K.card ≤ C.size := by
    change S.gates.length + K.card ≤ C.gates.length
    rw [← killsEq]
    apply le_of_eq
    simpa only [init,List.length_nil,Nat.zero_add,S] using loopSize N kill 0 (init N) C.gates
  have namesLen : S.names.length = N+C.gates.length := by
    simp [S,loopNamesLen,init]
  have outputRef : refAt S C.output ≠ .inl true := by
    by_cases h0 : C.output < N
    · have h0' : C.output < (init N).names.length := by simpa [init] using h0
      change refAt (loop N kill 0 (init N) C.gates) C.output ≠ _
      rw [loopRef_pres _ _ _ _ _ _ h0',refAt_init,ite_eq_left h0]
      simp
    · by_cases h1 : C.output < N + C.gates.length
      · have hi : C.output-N < C.gates.length := by omega
        have he : N + (C.output-N) = C.output := by omega
        have hj : C.output-N ∉ K := by
          intro hk
          exact (hb _ hk).2.1 he
        have hk : kill (0+(C.output-N)) = none := by simp [kill,hj]
        obtain ⟨w,hw⟩ := loopRef_live N kill 0 (init N) C.gates (C.output-N) hi hk
        have hh : (init N).names.length = N := by simp [init]
        rw [hh,he] at hw
        change refAt (loop N kill 0 (init N) C.gates) C.output ≠ _
        rw [hw]; simp
      · unfold refAt
        rw [List.getD_eq_default _ _ (by omega)]
        decide
  refine ⟨D,monoD,sizeD,?_⟩
  intro u v hu hv
  let raw := oneEach u v
  have hn : raw.length = N := by simp [raw,oneEach,N]
  have good : Good kill 0 C.gates raw := by
    intro i hi
    by_cases hj : i ∈ K
    · have hr := Classical.choose_spec (someR i hj)
      cases hh : Classical.choose (someR i hj) with
      | inl b =>
        simp only [hh,holds] at hr
        simp only [Nat.zero_add,kill,dite_eq_left hj,hh,hn]
        exact hr u v hu hv
      | inr w =>
        simp only [hh,holds] at hr
        simp only [Nat.zero_add,kill,dite_eq_left hj,hh,hn]
        exact ⟨hr.1,hr.2 u v hu hv⟩
    · simp [kill,hj]
  have base : consistent (init N) raw raw := by simpa only [hn] using init_consistent raw
  have hm : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
    intro g hg; simpa using (hmono g hg).1
  have hdone := loopConsistent N kill 0 (init N) C.gates raw raw hm good base
    (by simp [init,run,hn]) (by omega) (by simp [init,hn])
  have hDone : consistent S (C.wires raw) (run S.gates raw) := by
    change consistent (loop N kill 0 (init N) C.gates) (run C.gates raw) (run (loop N kill 0 (init N) C.gates).gates raw)
    rwa [List.take_of_length_le (by omega : raw.length ≤ N)] at hdone
  have he := hDone.2.1 C.output
  have hs : D.eval raw = evalRef (run S.gates raw) (refAt S C.output) := by
    cases hR : refAt S C.output with
    | inr w => simp [D,o,hR,evalRef,Circuit.eval,Circuit.wires,run,appendValue]
    | inl b =>
      cases b
      · change (run S.gates raw).getD o false = false
        have hol : o = N + S.gates.length := by simp [o,hR]
        rw [hol, List.getD_eq_default]
        simp [runLen,hn]
      · exact False.elim (outputRef hR)
  exact hs.trans (he.trans (hrep u v))
