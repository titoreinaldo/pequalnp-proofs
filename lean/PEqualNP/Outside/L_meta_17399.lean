import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17399

private abbrev F := Fin 13

private def I (x y : F) : Prop :=
  x = y ∨ x = y+1 ∨ x = y+3 ∨ x = y+9

instance (x y : F) : Decidable (I x y) := by unfold I; infer_instance

private def avoid (R : F → F → Prop) [DecidableRel R] (A : Finset F) : Finset F :=
  Finset.univ.filter (fun y => ∀ x ∈ A, ¬R x y)

private def arc (R : F → F → Prop) [DecidableRel R] (A : Finset F) : Prop :=
  ∀ y : F, (A.filter fun x => R x y).card ≤ 2

private lemma avoid_mem (R : F → F → Prop) [DecidableRel R] (A : Finset F) (y : F) :
    y ∈ avoid R A ↔ ∀ x ∈ A, ¬R x y := by simp [avoid]

private lemma noBigL (R : F → F → Prop) [DecidableRel R] (A : Finset F) (ha : arc R A)
    (h : 3 ≤ A.card) : ¬∃ y, ∀ x ∈ A, R x y := by
  rintro ⟨y, hy⟩
  have e : A.filter (fun x => R x y) = A := Finset.filter_true_of_mem hy
  have q := ha y
  rw [e] at q
  omega

private def good (R : F → F → Prop) [DecidableRel R] (A : Finset F) : Prop :=
  3 ≤ (avoid R A).card ∧ ¬∃ x : F, ∀ y ∈ avoid R A, R x y

instance (R : F → F → Prop) [DecidableRel R] (A : Finset F) : Decidable (arc R A) := by
  unfold arc; infer_instance

instance (R : F → F → Prop) [DecidableRel R] (A : Finset F) : Decidable (good R A) := by
  unfold good; infer_instance

open PEqualNP.MetaComplexity
private lemma tableIndex_succ {n : Nat} (x : Fin (n+1) → Bool) :
    tableIndex x = 2 * tableIndex (fun j : Fin n => x j.succ) + (if x 0 then 1 else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.val_zero, Nat.pow_zero, Fin.val_succ, Nat.pow_succ]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : x i.succ = true <;> simp [h, Nat.mul_comm]

private lemma tableIndex_bit {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (tableIndex x).testBit i.val = x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let b : Nat := if x 0 then 1 else 0
    have hb : b < 2^1 := by cases h : x 0 <;> simp [b,h]
    rw [tableIndex_succ]
    change (2^1 * tableIndex (fun j : Fin n => x j.succ) + b).testBit i.val = x i
    rw [Nat.testBit_two_pow_mul_add _ hb]
    cases i using Fin.cases with
    | zero => cases h : x 0 <;> simp [b, h]
    | succ j => simpa [Fin.val_succ] using ih (fun a : Fin n => x a.succ) j


private def unPack (q : Nat) : Finset F :=
  Finset.univ.filter (fun i : F => q.testBit i.val)

private lemma unPack_mem (q : Nat) (i : F) : i ∈ unPack q ↔ q.testBit i.val = true := by
  simp [unPack]

private lemma unpack_surj (S : Finset F) : ∃ q : Fin 8192, unPack q.val = S := by
  let f : F → Bool := fun j => decide (j ∈ S)
  let q : Fin 8192 := Fin.ofNat 8192 (PEqualNP.MetaComplexity.tableIndex f)
  refine ⟨q, ?_⟩
  ext i
  rw [unPack_mem]
  change ((PEqualNP.MetaComplexity.tableIndex f) % (2^13)).testBit i.val = true ↔ i ∈ S
  rw [Nat.testBit_mod_two_pow, tableIndex_bit]
  simp [i.isLt, f]

private def pa (h : Fin 32) (l : Fin 256) : Nat := h.val * 256 + l.val

private lemma pa_surj (i : Fin 8192) : ∃ h : Fin 32, ∃ l : Fin 256, pa h l = i.val := by
  refine ⟨⟨i.val / 256, ?_⟩, ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩, ?_⟩
  · omega
  · simp [pa]; omega

private def testBoth (q : Nat) : Prop :=
  (arc I (unPack q) → good I (unPack q)) ∧
  (arc (fun x y => I y x) (unPack q) → good (fun x y => I y x) (unPack q))

instance (q : Nat) : Decidable (testBoth q) := by unfold testBoth; infer_instance
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk0 : ∀ l : Fin 256, testBoth (pa 0 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk1 : ∀ l : Fin 256, testBoth (pa 1 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk2 : ∀ l : Fin 256, testBoth (pa 2 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk3 : ∀ l : Fin 256, testBoth (pa 3 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk4 : ∀ l : Fin 256, testBoth (pa 4 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk5 : ∀ l : Fin 256, testBoth (pa 5 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk6 : ∀ l : Fin 256, testBoth (pa 6 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk7 : ∀ l : Fin 256, testBoth (pa 7 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk8 : ∀ l : Fin 256, testBoth (pa 8 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk9 : ∀ l : Fin 256, testBoth (pa 9 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk10 : ∀ l : Fin 256, testBoth (pa 10 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk11 : ∀ l : Fin 256, testBoth (pa 11 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk12 : ∀ l : Fin 256, testBoth (pa 12 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk13 : ∀ l : Fin 256, testBoth (pa 13 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk14 : ∀ l : Fin 256, testBoth (pa 14 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk15 : ∀ l : Fin 256, testBoth (pa 15 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk16 : ∀ l : Fin 256, testBoth (pa 16 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk17 : ∀ l : Fin 256, testBoth (pa 17 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk18 : ∀ l : Fin 256, testBoth (pa 18 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk19 : ∀ l : Fin 256, testBoth (pa 19 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk20 : ∀ l : Fin 256, testBoth (pa 20 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk21 : ∀ l : Fin 256, testBoth (pa 21 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk22 : ∀ l : Fin 256, testBoth (pa 22 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk23 : ∀ l : Fin 256, testBoth (pa 23 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk24 : ∀ l : Fin 256, testBoth (pa 24 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk25 : ∀ l : Fin 256, testBoth (pa 25 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk26 : ∀ l : Fin 256, testBoth (pa 26 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk27 : ∀ l : Fin 256, testBoth (pa 27 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk28 : ∀ l : Fin 256, testBoth (pa 28 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk29 : ∀ l : Fin 256, testBoth (pa 29 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk30 : ∀ l : Fin 256, testBoth (pa 30 l) := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
private lemma chk31 : ∀ l : Fin 256, testBoth (pa 31 l) := by decide +kernel
private lemma both (a : Finset F) :
    (arc I a → good I a) ∧ (arc (fun x y => I y x) a → good (fun x y => I y x) a) := by
  obtain ⟨q,rfl⟩ := unpack_surj a
  obtain ⟨h,l,he⟩ := pa_surj q
  change testBoth q.val
  rw [← he]
  fin_cases h
  · exact chk0 l
  · exact chk1 l
  · exact chk2 l
  · exact chk3 l
  · exact chk4 l
  · exact chk5 l
  · exact chk6 l
  · exact chk7 l
  · exact chk8 l
  · exact chk9 l
  · exact chk10 l
  · exact chk11 l
  · exact chk12 l
  · exact chk13 l
  · exact chk14 l
  · exact chk15 l
  · exact chk16 l
  · exact chk17 l
  · exact chk18 l
  · exact chk19 l
  · exact chk20 l
  · exact chk21 l
  · exact chk22 l
  · exact chk23 l
  · exact chk24 l
  · exact chk25 l
  · exact chk26 l
  · exact chk27 l
  · exact chk28 l
  · exact chk29 l
  · exact chk30 l
  · exact chk31 l

private lemma goodI (a : Finset F) : arc I a → good I a := (both a).1
private lemma goodIt (a : Finset F) : arc (fun x y => I y x) a → good (fun x y => I y x) a := (both a).2

private lemma padPair (S B : Finset F) (ss : B ⊆ S) (hS : 3 ≤ S.card)
    (hB : B.card < 3) : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ B ⊆ ({a,b}:Finset F) := by
  obtain ⟨a, ha, b, hb, ne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  rcases (show B.card = 0 ∨ B.card = 1 ∨ B.card = 2 by omega) with z | z | z
  · have e := Finset.card_eq_zero.mp z
    exact ⟨a,ha,b,hb,ne,by simp [e]⟩
  · obtain ⟨c,rfl⟩ := Finset.card_eq_one.mp z
    have hcs : c ∈ S := ss (by simp)
    by_cases h : c=a
    · subst c
      exact ⟨a,ha,b,hb,ne,by simp⟩
    · exact ⟨c,hcs,a,ha,h,by simp⟩
  · obtain ⟨c,d,h,rfl⟩ := Finset.card_eq_two.mp z
    exact ⟨c,ss (by simp),d,ss (by simp),h,by rfl⟩

private lemma grow (R : F → F → Prop) [DecidableRel R]
    (cross : ∀ a b : F, a≠b → ∃! p, R p a ∧ R p b)
    (S B : Finset F) (ss : B ⊆ S) (sz : 3 ≤ S.card) (st : ¬∃ p, ∀ y ∈ S, R p y)
    (ab : arc (fun a b => R b a) B) :
    ∃ T : Finset F, B ⊆ T ∧ T ⊆ S ∧ 3 ≤ T.card ∧ arc (fun a b => R b a) T := by
  by_cases hB : 3 ≤ B.card
  · exact ⟨B, by rfl, ss, hB, ab⟩
  obtain ⟨a,ha,b,hb,hab,sub⟩ := padPair S B ss sz (by omega)
  obtain ⟨p, hp, hu⟩ := cross a b hab
  have hbad : ¬∀ y ∈ S, R p y := fun h => st ⟨p,h⟩
  push Not at hbad
  obtain ⟨c,hc,hn⟩ := hbad
  have hca : c≠a := fun e => hn (e.symm ▸ hp.1)
  have hcb : c≠b := fun e => hn (e.symm ▸ hp.2)
  let U : Finset F := {a,b,c}
  have hU : U.card = 3 := by simp [U, hab, Ne.symm hca, Ne.symm hcb]
  refine ⟨U, ?_, ?_, by omega, ?_⟩
  · intro x hx
    have := sub hx
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  · intro x hx
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro q
    change (U.filter fun y => R q y).card ≤ 2
    have hh : ¬(R q a ∧ R q b ∧ R q c) := by
      rintro ⟨fa,fb,fc⟩
      have e := hu q ⟨fa,fb⟩
      exact hn (e ▸ fc)
    have hss : (U.filter fun y => R q y).card ≤ U.card := Finset.card_filter_le _ _
    by_contra H
    have ee : (U.filter fun y => R q y) = U :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    apply hh
    have r : ∀ y ∈ U, R q y := by
      intro y h
      have h' : y ∈ U.filter fun y => R q y := ee.symm ▸ h
      exact (Finset.mem_filter.mp h').2
    exact ⟨r a (by simp [U]), r b (by simp [U]), r c (by simp [U])⟩

private lemma fromCrossCard (R : F → F → Prop) [DecidableRel R] {a b : F}
    (h : (Finset.univ.filter (fun p : F => R p a ∧ R p b)).card = 1) : ∃! p, R p a ∧ R p b := by
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp h
  have same (q : F) : R q a ∧ R q b ↔ q = p := by
    have e : q ∈ Finset.univ.filter (fun p : F => R p a ∧ R p b) ↔ q = p := by rw [hp]; simp
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using e
  exact ⟨p,(same p).2 rfl, fun q hq => (same q).1 hq⟩

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private lemma crossCardI : ∀ a b : F, a ≠ b →
    (Finset.univ.filter (fun p : F => I p a ∧ I p b)).card = 1 := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private lemma crossCardIt : ∀ a b : F, a ≠ b →
    (Finset.univ.filter (fun p : F => I a p ∧ I b p)).card = 1 := by decide +kernel

private lemma crossI (a b : F) (ne : a ≠ b) : ∃! p, I p a ∧ I p b :=
  fromCrossCard I (crossCardI a b ne)

private lemma crossIt (a b : F) (ne : a ≠ b) : ∃! p, I a p ∧ I b p :=
  fromCrossCard (fun x y => I y x) (crossCardIt a b ne)

private lemma main (A B : Finset F) (dis : ∀ x ∈ A, ∀ y ∈ B, ¬I x y)
    (aA : arc I A) (aB : arc (fun x y => I y x) B) :
    ∃ X : Finset F, A ⊆ X ∧ B ⊆ avoid I X ∧
    (∀ p ∉ X, ∃ l ∈ avoid I X, I p l) ∧
    (¬∃ l, ∀ p ∈ X, I p l) ∧ ¬∃ p, ∀ l ∈ avoid I X, I p l := by
  have sA : A ⊆ avoid (fun x y => I y x) B := fun p hp =>
    (avoid_mem _ _ _).2 (dis p hp)
  obtain ⟨A',hAA,eA,cA,arA⟩ := grow (fun x y => I y x) crossIt _ A sA (goodIt _ aB).1 (goodIt _ aB).2 aA
  have sB : B ⊆ avoid I A' := by
    intro l hl
    exact (avoid_mem _ _ _).2 fun p hp => (avoid_mem _ _ _).1 (eA hp) l hl
  obtain ⟨B',hBB,eB,cB,arB⟩ := grow I crossI _ B sB (goodI _ arA).1 (goodI _ arA).2 aB
  let S := avoid I A'
  let X := avoid (fun x y => I y x) S
  have eAX : A' ⊆ X := by
    intro p hp
    exact (avoid_mem _ _ _).2 fun l hl => (avoid_mem _ _ _).1 hl p hp
  have eSX : S = avoid I X := by
    apply Finset.Subset.antisymm
    · intro l hl
      exact (avoid_mem _ _ _).2 fun p hp => (avoid_mem _ _ _).1 hp l hl
    · intro l hl
      exact (avoid_mem _ _ _).2 fun p hp => (avoid_mem _ _ _).1 hl p (eAX hp)
  refine ⟨X, hAA.trans eAX, ?_, ?_, ?_, ?_⟩
  · rw [← eSX]
    exact hBB.trans eB
  · rw [← eSX]
    intro p hp
    have h : ¬∀ l ∈ S, ¬ I p l := fun z => hp ((avoid_mem _ _ _).2 z)
    push Not at h
    exact h
  · rintro ⟨l,hl⟩
    exact noBigL I _ arA cA ⟨l,fun p hp => hl p (eAX hp)⟩
  · rw [← eSX]
    rintro ⟨p,hp⟩
    exact noBigL (fun x y => I y x) _ arB cB ⟨p,fun l hl => hp l (eB hl)⟩
end PEqualNP.Outside.L_meta_17399

open PEqualNP.Outside.L_meta_17399 in
theorem PEqualNP.Outside.L_meta_17399 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, ¬x1 x5 x7) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x7 x6}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x1 x7 x8}.card ≤ (2 : ℕ)) → ∃ (x8 : Finset (Fin (13 : ℕ))), x3 ⊆ x8 ∧ x4 ⊆ x2 x8 ∧ (∀ x9 ∉ x8, ∃ x11 ∈ x2 x8, x1 x9 x11) ∧ (¬∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x1 x10 x9) ∧ ¬∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x2 x8, x1 x9 x10 := main
