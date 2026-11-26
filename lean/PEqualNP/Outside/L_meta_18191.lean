import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18191
open PEqualNP.CircuitLowerBounds
-- The scalar-recursion correctness replay is adapted from the public L-meta-17241.
-- The generic lemmas for the append-only fold are adapted from the public project proof of L-meta-5809.
private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private def startList (n : Nat) (S : List Nat) (v : Nat) : List (Option Nat) :=
  (List.range n).map fun i => if i = v then some 1 else if i ∈ S then some 0 else none

private def step (R : List (Option Nat)) (g : Gate) : Option Nat :=
  let ins := g.inputs.map fun i => R.getD i none
  match g.op with
  | .or => ins.foldl (fun acc o => match acc, o with
      | none, o => o
      | some a, none => some a
      | some a, some b => some (min a b)) none
  | .and => ins.foldl (fun acc o => match acc, o with
      | some a, some b => some (a+b)
      | _, _ => none) (some 0)
  | _ => none

private lemma startLen (n : Nat) (S : List Nat) (v : Nat) :
    (startList n S v).length = n := by simp [startList]

private lemma startGet (n : Nat) (S : List Nat) (v : Nat) (k : Fin n) :
    (startList n S v).getD k none =
      if k.val = v then some 1 else if k.val ∈ S then some 0 else none := by
  rw [List.getD_eq_getElem?_getD]
  simp [startList, k.isLt]

private lemma stepAnd (R : List (Option Nat)) (g : Gate) (a b : Nat)
    (hi : g.inputs = [a,b]) (ho : g.op = .and) :
    step R g = (R.getD a none).bind fun x => (R.getD b none).map (fun y => x+y) := by
  simp only [step, hi, ho, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  cases R.getD a none <;> cases R.getD b none <;> simp

private lemma stepOr (R : List (Option Nat)) (g : Gate) (a b : Nat)
    (hi : g.inputs = [a,b]) (ho : g.op = .or) :
    step R g = ((R.getD a none).map fun x => min x ((R.getD b none).getD x)).orElse
      (fun _ => R.getD b none) := by
  simp only [step, hi, ho, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  cases R.getD a none <;> cases R.getD b none <;> simp

theorem scalar_eq : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List ℕ) (x4 : ℕ),   have x5 : ℕ → Option ℕ := fun (x5 : ℕ) => (PEqualNP.ReadK.scalarMults x2 x1 x3 x4).getD x5 Option.none;   (∀ (x6 : Fin x1), x5 ↑x6 = if ↑x6 = x4 then Option.some (1 : ℕ) else if ↑x6 ∈ x3 then Option.some (0 : ℕ) else Option.none) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x2.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → x8 < x1 + x6 → x9 < x1 + x6 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 (x1 + x6) = (x5 x8).bind fun (x15 : ℕ) => Option.map (fun (x16 : ℕ) => x15 + x16) (x5 x9)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 (x1 + x6) = (Option.map (fun (x15 : ℕ) => Min.min x15 ((x5 x9).getD x15)) (x5 x8)).orElse fun (x15 : Unit) => x5 x9) := by

  intro n C S v
  dsimp only
  let R := startList n S v
  have lR : R.length = n := startLen n S v
  let F (w : List (Option Nat)) (g : Gate) := w ++ [step w g]
  change (∀ k : Fin n, (C.gates.foldl F R).getD k none = _) ∧ _
  constructor
  · intro k
    have hk : k.val < R.length := by rw [lR]; exact k.isLt
    rw [foldl_append_getD_lt step C.gates R none k.val hk]
    exact startGet n S v k
  · intro j g a b hget hi ha hb
    have hj : j < C.gates.length := by
      have E : C.gates[j]?.isSome = true := by rw [hget]; rfl
      simpa using E
    let pre := (C.gates.take j).foldl F R
    have ag : pre.getD a none = (C.gates.foldl F R).getD a none :=
      foldl_append_take_getD step C.gates R none j a (Nat.le_of_lt hj) (by omega)
    have bg : pre.getD b none = (C.gates.foldl F R).getD b none :=
      foldl_append_take_getD step C.gates R none j b (Nat.le_of_lt hj) (by omega)
    have evalJ : (C.gates.foldl F R).getD (n+j) none = step pre g := by
      rw [← lR, foldl_append_getD_gate step C.gates R none j hj g]
      have W : C.gates.getD j g = g := by rw [List.getD_eq_getElem?_getD, hget]; rfl
      rw [W]
    change ((_ → (C.gates.foldl F R).getD (n+j) none = _) ∧
      (_ → (C.gates.foldl F R).getD (n+j) none = _))
    constructor
    · intro hop
      rw [evalJ, stepAnd pre g a b hi hop, ag, bg]
      rfl
    · intro hop
      rw [evalJ, stepOr pre g a b hi hop, ag, bg]
      rfl


end PEqualNP.Outside.L_meta_18191

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_18191 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) → (∀ x3 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] x3).getD x1.output Option.none).getD (2 : ℕ)) → ∀ (x4 : Bool), ∃ (x5 : ℕ → ℕ), x5 (if x4 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x5 (if x4 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x6 < (25 : ℕ), x6 ≠ (0 : ℕ) → x6 ≠ (7 : ℕ) → x5 x6 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x5 x1.output ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((25 : ℕ) + x6) ≤ x5 x8 + x5 x9) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((25 : ℕ) + x6) ≤ Min.min (x5 x8) (x5 x9)) := by
  intro C hgate hout b
  let v : Nat := if b = true then 7 else 0
  let m (i : Nat) := (PEqualNP.ReadK.scalarMults C 25 [0,7] v).getD i none
  let cap (o : Option Nat) := min 2 (o.getD 2)
  have hm : (∀ i : Fin 25, m i = if i.val = v then some 1 else if i.val ∈ [0,7] then some 0 else none) ∧ _ :=
    PEqualNP.Outside.L_meta_18191.scalar_eq 25 C [0,7] v
  have init (i : Nat) (hi : i < 25) :
      m i = if i = v then some 1 else if i ∈ [0,7] then some 0 else none := hm.1 ⟨i,hi⟩
  refine ⟨fun i => cap (m i), ?_, ?_, ?_, ?_, ?_⟩
  · cases b <;> simp [cap, v, init, show 0 < 25 by decide, show 7 < 25 by decide]
  · cases b <;> simp [cap, v, init, show 0 < 25 by decide, show 7 < 25 by decide]
  · intro i hi h0 h7
    change cap (m i) = 2
    rw [init i hi]
    cases b <;> simp [cap, v, h0, h7]
  · have hv : v ∈ ([0,7] : List Nat) := by cases b <;> decide
    have hh : 2 ≤ (m C.output).getD 2 := hout v hv
    exact Nat.le_min.mpr ⟨le_refl _, hh⟩
  · intro j g a c hj hi
    obtain ⟨_, a', c', hh, _, ha', hc'⟩ := hgate j g hj
    have hij : a = a' ∧ c = c' := by simpa [hi] using hh
    obtain ⟨rfl,rfl⟩ := hij
    obtain ⟨ha, ho⟩ := hm.2 j g a c hj hi ha' hc'
    constructor
    · intro hop
      change cap (m (25+j)) ≤ cap (m a) + cap (m c)
      rw [show m (25+j) = (m a).bind (fun q => (m c).map (fun t => q+t)) from ha hop]
      unfold cap
      cases m a <;> cases m c <;> simp [Nat.min_def] <;> split_ifs <;> omega
    · intro hop
      change cap (m (25+j)) ≤ min (cap (m a)) (cap (m c))
      rw [show m (25+j) = ((m a).map (fun q => min q ((m c).getD q))).orElse (fun _ => m c) from ho hop]
      unfold cap
      cases m a <;> cases m c <;> simp [Nat.min_def] <;> split_ifs <;> omega
