import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18193
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- Monotonicity of append-only Boolean circuit evaluation follows L-meta-1042.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

def mergeWire (n j : ℕ) : ℕ := if j < n then j else j - n

def mergeGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (mergeWire n)⟩

def mergeC (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mergeGate n), mergeWire n C.output⟩

theorem merge_size (n : Nat) (C : Circuit) : (mergeC n C).size = C.size := by
  simp [mergeC, Circuit.size]

theorem merge_mono (n : Nat) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (mergeC n C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa only [mergeGate, List.length_map] using h a ha

theorem merge_base (v : List Bool) (j : Nat) :
    (v ++ v).getD j false = v.getD (mergeWire v.length j) false := by
  unfold mergeWire
  by_cases h : j < v.length
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · simp only [if_neg h, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]

theorem merge_append (n : Nat) (v w : List Bool) (b : Bool)
    (h : v.length = n + w.length) (hw : n ≤ w.length)
    (hr : ∀ j, v.getD j false = w.getD (mergeWire n j) false) :
    ∀ j, (v ++ [b]).getD j false = (w ++ [b]).getD (mergeWire n j) false := by
  intro j
  by_cases hj : j < v.length
  · have he : mergeWire n j < w.length := by unfold mergeWire; split <;> omega
    rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ he]
    exact hr j
  · have he : mergeWire n j - w.length = j - v.length := by
      unfold mergeWire
      split <;> omega
    have hn : w.length ≤ mergeWire n j := by
      unfold mergeWire
      split <;> omega
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right hn, he]

theorem merge_fold (n : Nat) (gs : List Gate) (v w : List Bool)
    (h : v.length = n + w.length) (hw : n ≤ w.length)
    (hr : ∀ j, v.getD j false = w.getD (mergeWire n j) false) :
    ∀ j, (wiresFrom gs v).getD j false =
      (wiresFrom (gs.map (mergeGate n)) w).getD (mergeWire n j) false := by
  induction gs generalizing v w with
  | nil => exact hr
  | cons g gs ih =>
    have hh : (g.inputs.map fun k => v.getD k false) =
        ((g.inputs.map (mergeWire n)).map fun k => w.getD k false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun j _ => hr j)
    simp only [wiresFrom, List.foldl_cons, List.map_cons, mergeGate, ← hh]
    exact ih _ _ (by simp [h]; omega) (by simp; omega) (merge_append n v w _ h hw hr)

theorem merged_eval (C : Circuit) (v : List Bool) :
    (mergeC v.length C).eval v = C.eval (v ++ v) := by
  symm
  exact merge_fold v.length C.gates (v ++ v) v (by simp [Nat.two_mul]) (le_refl _) (merge_base v) C.output

def one {n : Nat} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

lemma readFn {n : Nat} (f : Fin n → Bool) (j : Nat) :
    (List.ofFn f).getD j false = if h : j < n then f ⟨j,h⟩ else false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

lemma app_read_mono {n : Nat} (f g h k : Fin n → Bool)
    (hf : ∀ i, f i = true → h i = true) (hg : ∀ i, g i = true → k i = true) :
    ∀ j, (List.ofFn f ++ List.ofFn g).getD j false = true →
      (List.ofFn h ++ List.ofFn k).getD j false = true := by
  intro j hj
  by_cases hjn : j < n
  · have Hf : j < (List.ofFn f).length := by simp [hjn]
    have Hh : j < (List.ofFn h).length := by simp [hjn]
    rw [List.getD_append _ _ _ _ Hf, readFn, dite_eq_left hjn] at hj
    rw [List.getD_append _ _ _ _ Hh, readFn, dite_eq_left hjn]
    exact hf _ hj
  · have Hf : (List.ofFn f).length ≤ j := by simp; omega
    have Hh : (List.ofFn h).length ≤ j := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right Hf, List.length_ofFn,
      ← List.getD_eq_getElem?_getD, readFn] at hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right Hh, List.length_ofFn,
      ← List.getD_eq_getElem?_getD, readFn]
    by_cases hh : j - n < n
    · rw [dite_eq_left hh] at hj ⊢
      exact hg _ hj
    · rw [dite_eq_right hh] at hj
      contradiction

end PEqualNP.Outside.L_meta_18193

open PEqualNP.Outside.L_meta_18193 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_18193 :
    ∀ n s : ℕ, RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  intro n s H
  by_cases hn : n = 0
  · subst n
    refine ⟨⟨[],0⟩, by simp [Monotone2], by simp [Circuit.size], ?_⟩
    intro x; rfl
  obtain ⟨C,hmon,hs,hrep⟩ := H
  refine ⟨mergeC n C, merge_mono n C hmon, by simpa [merge_size] using hs, ?_⟩
  intro x
  have hd := merged_eval C (List.ofFn x)
  rw [List.length_ofFn] at hd
  rw [hd, List.count_ofFn]
  let S : Finset (Fin n) := Finset.univ.filter fun i => x i = true
  change C.eval (List.ofFn x ++ List.ofFn x) = decide (2 ≤ S.card)
  have memS (i : Fin n) : i ∈ S ↔ x i = true := by simp [S]
  have mon (f g h k : Fin n → Bool) (hf : ∀ i, f i = true → h i = true)
      (hg : ∀ i, g i = true → k i = true) :
      C.eval (List.ofFn f ++ List.ofFn g) = true →
      C.eval (List.ofFn h ++ List.ofFn k) = true :=
    wiresFrom_mono C.gates (fun g hg => by simpa using (hmon g hg).1) _ _
      (by simp) (app_read_mono f g h k hf hg) C.output
  by_cases hc : 2 ≤ S.card
  · have hnt : S.Nontrivial := Finset.one_lt_card_iff_nontrivial.mp hc
    obtain ⟨a,ha,b,hb,hab⟩ := hnt
    have he : C.eval (List.ofFn (one a) ++ List.ofFn (one b)) = true := by
      change C.eval (oneEach a b) = true
      simpa [hab] using hrep a b
    have hm (i j : Fin n) (hj : j ∈ S) : one j i = true → x i = true := by
      simp only [one, decide_eq_true_eq]; rintro rfl; exact (memS _).1 hj
    exact (mon _ _ _ _ (fun i => hm i a ha) (fun i => hm i b hb) he).trans
      (by simp [hc])
  · have hu : ∃ a : Fin n, ∀ j, x j = true → j = a := by
      by_cases ht : S.Nonempty
      · obtain ⟨a,ha⟩ := ht
        refine ⟨a, fun j hj => ?_⟩
        by_contra hja
        exact hc (Finset.Nontrivial.two_le_card ⟨j,(memS _).2 hj,a,ha,hja⟩)
      · refine ⟨⟨0, Nat.pos_of_ne_zero hn⟩, fun j hj => False.elim ?_⟩
        exact ht ⟨j,(memS _).2 hj⟩
    obtain ⟨a,ha⟩ := hu
    have hp (j : Fin n) (hj : x j = true) : one a j = true := by
      simp [one, ha j hj]
    have he : C.eval (List.ofFn (one a) ++ List.ofFn (one a)) = false := by
      change C.eval (oneEach a a) = false
      simpa using hrep a a
    cases hC : C.eval (List.ofFn x ++ List.ofFn x)
    · simp [hc]
    · have ht := mon _ _ _ _ hp hp hC
      rw [he] at ht
      contradiction
