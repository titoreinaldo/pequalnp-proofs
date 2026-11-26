import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17896

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability helpers follow L_meta_7895, L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

-- Erasing an unread gate gives a smaller circuit, as in L_meta_7696.
def shiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w - 1

def unshiftW (n k w : ℕ) : ℕ :=
  if w < n + k then w else w + 1

def unshiftG (k j : ℕ) : ℕ :=
  if j < k then j else j + 1

def shiftGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftW n k)⟩

def delDead (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx k).map (shiftGate n k), shiftW n k C.output⟩

lemma unshiftW_shiftW (n k w : ℕ) (hne : w ≠ n + k) :
    unshiftW n k (shiftW n k w) = w := by
  unfold unshiftW shiftW
  split_ifs <;> omega


lemma delDead_size (n k : ℕ) (C : Circuit) (hk : k < C.size) :
    (delDead n k C).size + 1 = C.size := by
  unfold Circuit.size at hk ⊢
  unfold delDead
  simp only [List.length_map, List.length_eraseIdx_of_lt hk]
  omega

lemma delDead_length (n k : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (delDead n k C).gates.length = C.gates.length - 1 := by
  simp [delDead, List.length_eraseIdx_of_lt hk]

lemma delDead_gateAt (n k : ℕ) (C : Circuit) (hk : k < C.gates.length)
    (j : ℕ) (hj : j < (delDead n k C).gates.length) :
    gateAt (delDead n k C) j = shiftGate n k (gateAt C (unshiftG k j)) := by
  have hj_lt : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj_e : j < (C.gates.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt hk]; exact hj_lt
  rw [gateAt_eq hj]
  simp only [delDead, List.getElem_map, unshiftG]
  split_ifs with hjk
  · rw [List.getElem_eraseIdx_of_lt hj_e hjk, gateAt_eq (C := C) (j := j) (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hj_e (by omega), gateAt_eq (C := C) (j := j + 1) (by omega)]


lemma delDead_readsBack (n k : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hk : k < C.gates.length) (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ReadsBack n (delDead n k C) := by
  intro j hj w' hw'
  rw [delDead_gateAt n k C hk j hj] at hw'
  simp only [shiftGate, List.mem_map] at hw'
  obtain ⟨w, hw, rfl⟩ := hw'
  have hj_len : j < C.gates.length - 1 := by
    rw [← delDead_length n k C hk]; exact hj
  have hj0_lt : unshiftG k j < C.gates.length := by
    unfold unshiftG; split_ifs <;> omega
  have hw_lt : w < n + unshiftG k j := hRB (unshiftG k j) hj0_lt w hw
  have hw_ne : w ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hw)
  unfold shiftW
  unfold unshiftG at hw_lt
  split_ifs at hw_lt ⊢ <;> omega


def evalStep {α : Type} (d0 : α) (evalG : GateOp → List α → α) (acc : List α) (g : Gate) :
    List α :=
  acc ++ [evalG g.op (g.inputs.map fun i => acc.getD i d0)]

lemma foldl_evalStep_length {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) :
    (gs.foldl (evalStep d0 evalG) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, evalStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_evalStep_prefix {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (gs : List Gate) (acc : List α) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl (evalStep d0 evalG) acc).getD w d0 = acc.getD w d0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (evalStep d0 evalG acc g).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (evalStep d0 evalG acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_left hw]

lemma foldl_evalStep_gate {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG (gateAt C j).op
        ((gateAt C j).inputs.map fun u => (C.gates.foldl (evalStep d0 evalG) init).getD u d0) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (evalStep d0 evalG) init with hacc
  have hacc_len : acc.length = n + j := by
    rw [hacc, foldl_evalStep_length, hinit, List.length_take]
    omega
  have hpref : ∀ u < n + j,
      (C.gates.foldl (evalStep d0 evalG) init).getD u d0 = acc.getD u d0 := by
    intro u hu
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_evalStep_prefix d0 evalG (C.gates.drop j) acc u (by omega)
  have hval : (C.gates.foldl (evalStep d0 evalG) init).getD (n + j) d0 =
      evalG C.gates[j].op (C.gates[j].inputs.map fun u => acc.getD u d0) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + j < (evalStep d0 evalG acc C.gates[j]).length := by
      simp only [evalStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_evalStep_prefix d0 evalG (C.gates.drop (j + 1)) (evalStep d0 evalG acc C.gates[j])
      (n + j) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [evalStep, List.getElem?_append_right (by omega : acc.length ≤ n + j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq hj]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq hj] at hu
  exact (hpref u (hRB j hj u hu)).symm

lemma delDead_evalStep_eq {α : Type} (d0 : α) (evalG : GateOp → List α → α)
    (n k : ℕ) (C : Circuit) (init : List α) (hinit : init.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    ∀ w : ℕ,
      ((delDead n k C).gates.foldl (evalStep d0 evalG) init).getD w d0 =
        (C.gates.foldl (evalStep d0 evalG) init).getD (unshiftW n k w) d0 := by
  have hRB' : ReadsBack n (delDead n k C) := delDead_readsBack n k C hRB hk hno
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw_oob : n + (delDead n k C).gates.length ≤ w
    · have hlen' : ((delDead n k C).gates.foldl (evalStep d0 evalG) init).length =
          n + (delDead n k C).gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hlen : (C.gates.foldl (evalStep d0 evalG) init).length = n + C.gates.length := by
        rw [foldl_evalStep_length, hinit]
      have hdl := delDead_length n k C hk
      have huw : n + C.gates.length ≤ unshiftW n k w := by
        unfold unshiftW; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · push Not at hw_oob
      by_cases hwn : w < n
      · have huw : unshiftW n k w = w := by unfold unshiftW; split_ifs <;> omega
        rw [huw]
        rw [foldl_evalStep_prefix d0 evalG (delDead n k C).gates init w (by omega)]
        rw [foldl_evalStep_prefix d0 evalG C.gates init w (by omega)]
      · set j := w - n with hj_def
        have hw_eq : w = n + j := by omega
        have hj_lt : j < (delDead n k C).gates.length := by omega
        have hdl := delDead_length n k C hk
        have hj0_lt : unshiftG k j < C.gates.length := by
          unfold unshiftG; split_ifs <;> omega
        have huw : unshiftW n k (n + j) = n + unshiftG k j := by
          unfold unshiftW unshiftG; split_ifs <;> omega
        rw [hw_eq, huw]
        rw [foldl_evalStep_gate d0 evalG n (delDead n k C) init hinit hRB' j hj_lt]
        rw [foldl_evalStep_gate d0 evalG n C init hinit hRB (unshiftG k j) hj0_lt]
        rw [delDead_gateAt n k C hk j hj_lt]
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : shiftW n k u < n + j := by
          have hmem : shiftW n k u ∈ (gateAt (delDead n k C) j).inputs := by
            rw [delDead_gateAt n k C hk j hj_lt]
            simp only [shiftGate, List.mem_map]
            exact ⟨u, hu, rfl⟩
          exact hRB' j hj_lt (shiftW n k u) hmem
        have hu_ne : u ≠ n + k := fun heq => hno (unshiftG k j) hj0_lt (heq ▸ hu)
        simp only [Function.comp_apply]
        rw [ih (shiftW n k u) (by omega), unshiftW_shiftW n k u hu_ne]

lemma delDead_wires_eq (n k : ℕ) (C : Circuit) (l : List Bool) (hl : l.length = n)
    (hRB : ReadsBack n C) (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) (w : ℕ) :
    ((delDead n k C).wires l).getD w false = (C.wires l).getD (unshiftW n k w) false :=
  delDead_evalStep_eq false GateOp.eval n k C l hl hRB hk hno w

private lemma delDead_ao2 {n k : ℕ} {C : Circuit} (h : IsAO2 n C)
    (hk : k < C.gates.length)
    (hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs) :
    IsAO2 n (delDead n k C) := by
  have mapped : ∀ g ∈ (delDead n k C).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    have hm := List.mem_of_mem_eraseIdx hg'
    exact ⟨h.1 g' hm, by simp [shiftGate, h.2.2 g' hm]⟩
  exact ⟨fun g hg => (mapped g hg).1, delDead_readsBack n k C h.2.1 hk hno,
    fun g hg => (mapped g hg).2⟩

private def IsSmallest (n : ℕ) (C : Circuit) : Prop :=
  ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size

private lemma reader {n k : ℕ} {C : Circuit} (h : IsAO2 n C) (hmin : IsSmallest n C)
    (hk : k < C.gates.length) (hout : C.output ≠ n + k) :
    ∃ j < C.gates.length, n + k ∈ (gateAt C j).inputs := by
  by_contra hnot
  have hno : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs :=
    fun j hj hj' => hnot ⟨j, hj, hj'⟩
  have heq : circuitFun n (delDead n k C) = circuitFun n C := by
    funext x
    unfold circuitFun Circuit.eval
    rw [delDead_wires_eq n k C _ List.length_ofFn h.2.1 hk hno]
    change (C.wires (List.ofFn x)).getD (unshiftW n k (shiftW n k C.output)) false = _
    rw [unshiftW_shiftW n k C.output hout]
  have hle := hmin _ (delDead_ao2 h hk hno) heq
  have hsize := delDead_size n k C hk
  omega

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
theorem junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
theorem andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
theorem andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
theorem operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
theorem operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hr, hjv⟩

lemma readData {j k : ℕ} (h : k ∈ readers n C j) :
    k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  simpa only [readers, Finset.mem_filter, Finset.mem_range] using h

lemma readLt (hAO : IsAO2 n C) {j k : ℕ} (h : k ∈ readers n C j) : j < k := by
  have hlt := hAO.2.1 k (readData h).1 _ (readData h).2
  omega

lemma junkNotBelow {j : ℕ} (hj : j ∈ junk G C) : ¬ BelowF G C j := by
  obtain ⟨_, _, x, hx, hf⟩ := junkData hj
  intro h
  exact Bool.false_ne_true (hf.symm.trans (h x hx))

lemma leastRead (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (hd : ¬ BelowF G C j) : (readers n C j).Nonempty := by
  have hout : C.output ≠ n + j := by
    intro heq
    apply hd
    intro x hx
    have h : val C (List.ofFn x) C.output = graphFun G ∅ x := congrFun hL.2.1 x
    rw [heq] at h
    exact h.symm.trans hx
  obtain ⟨k, hk, hin⟩ := reader hL.1
    (fun D hD heq => hL.2.2 D hD (heq.trans hL.2.1)) hj hout
  exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hin⟩⟩

lemma emptySide {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (h : side (n := n) C a b = ∅) : a ∈ centreless G C := by
  apply Finset.mem_filter.mpr
  refine ⟨ha, ?_⟩
  fin_cases b
  · exact Or.inl h
  · exact Or.inr h

-- A reader of a dirty gate with no input in its OR closure consumes one of the two budgets.
lemma classifyReader (hAO : IsAO2 n C) (hE : centreless G C = ∅) {j k : ℕ}
    (hd : ¬ BelowF G C j) (hz : orIn n C (n + j) = ∅) (hr : k ∈ readers n C j) :
    k ∈ junk G C ∨ k ∈ orN G C \ lam G C := by
  obtain ⟨hk, hin⟩ := readData hr
  obtain ⟨b, hb⟩ := inputsAsOpnd hAO hk hin
  have hs : side (n := n) C k b = ∅ := by
    change orIn n C (opnd C k b) = ∅
    rwa [← hb]
  rcases hAO.1 _ (gateAt_mem hk) with hand | hor
  · left
    have hnb : ¬ BelowF G C k := by
      intro hbelow
      have ht : k ∈ tops G C := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hk (And.intro hand hbelow)
      have hcen := emptySide ht hs
      rw [hE] at hcen
      exact Finset.notMem_empty _ hcen
    have hw : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
      by_contra hnone
      apply hnb
      intro x hx
      by_contra hf
      exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hand, hk, hw⟩
  · right
    have hnb : ¬ BelowF G C k := by
      intro hbelow
      apply hd
      intro x hx
      exact hbelow x ((val_or (n := n) (by simp) hk hor).mpr
        ⟨_, hin, hAO.2.1 k hk _ hin, hx⟩)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
        And.intro hk (And.intro hor hnb)
    · intro hlam
      obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hlam
      have hn : (orIn n C (opnd C k b)).Nonempty := by
        fin_cases b
        · exact h0
        · exact h1
      rw [← hb, hz] at hn
      exact Finset.not_nonempty_empty hn

private theorem nonemptyBudget (hL : IsLeastAO G C) (hT : TopForm G C)
    (h : (Ustar G C).Nonempty) :
    (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty := by
  classical
  by_cases hE : centreless G C = ∅
  · right
    obtain ⟨e,he⟩ := h
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨a,ha,b,j,hj,path,_⟩ := residualTrace hL hT he
      rcases lastOrBefore (orReaches_reach j _ path).1 with eq | ⟨m,hm,hop,hin,_,_⟩
      · have hv : side (n := n) C a b = ∅ := by
          change orIn n C (opnd C a b) = ∅
          rw [eq]
          exact andRawEmpty (junkData hj).2.1
        have e := emptySide ha hv
        rw [hE] at e
        exact (Finset.notMem_empty _ e).elim
      · have hr : m ∈ readers n C j :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hin⟩
        rcases classifyReader hL.1 hE (junkNotBelow hj) (andRawEmpty (junkData hj).2.1) hr with hJ | hM
        · have ha := (junkData hJ).2.1
          rw [hop] at ha
          cases ha
        · exact ⟨m,hM⟩
  · exact Or.inl (Finset.nonempty_iff_ne_empty.mpr hE)

end PEqualNP.Outside.L_meta_17896

/-- An uncovered edge forces a centreless top or a non-lambda OR gate. -/
theorem PEqualNP.Outside.L_meta_17896 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (PEqualNP.TopForm.Ustar x1 x3).Nonempty → (PEqualNP.TopForm.centreless x1 x3).Nonempty ∨ (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).Nonempty := by
  intro G _ C hL hT h
  exact PEqualNP.Outside.L_meta_17896.nonemptyBudget hL hT h
