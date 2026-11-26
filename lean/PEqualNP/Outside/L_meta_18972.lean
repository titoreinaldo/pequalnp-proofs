import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_18972
open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

def C : Circuit := ⟨[⟨.and, [1,5]⟩,
  ⟨.and, [2,6]⟩,
  ⟨.and, [3,7]⟩,
  ⟨.and, [4,8]⟩,
  ⟨.not, [15]⟩,
  ⟨.not, [16]⟩,
  ⟨.and, [19,20]⟩,
  ⟨.not, [21]⟩,
  ⟨.or, [22,17]⟩,
  ⟨.or, [23,18]⟩,
  ⟨.and, [0,24]⟩,
  ⟨.and, [2,9]⟩,
  ⟨.and, [3,10]⟩,
  ⟨.and, [4,11]⟩,
  ⟨.or, [26,27]⟩,
  ⟨.or, [29,28]⟩,
  ⟨.and, [1,30]⟩,
  ⟨.and, [2,3]⟩,
  ⟨.and, [6,7]⟩,
  ⟨.and, [9,10]⟩,
  ⟨.and, [13,14]⟩,
  ⟨.or, [32,33]⟩,
  ⟨.or, [36,34]⟩,
  ⟨.or, [37,35]⟩,
  ⟨.and, [12,38]⟩,
  ⟨.and, [2,4]⟩,
  ⟨.and, [6,8]⟩,
  ⟨.and, [9,11]⟩,
  ⟨.or, [40,41]⟩,
  ⟨.or, [43,42]⟩,
  ⟨.and, [13,44]⟩,
  ⟨.and, [3,4]⟩,
  ⟨.and, [7,8]⟩,
  ⟨.and, [10,11]⟩,
  ⟨.or, [46,47]⟩,
  ⟨.or, [49,48]⟩,
  ⟨.and, [14,50]⟩,
  ⟨.and, [6,9]⟩,
  ⟨.and, [7,10]⟩,
  ⟨.and, [8,11]⟩,
  ⟨.or, [52,53]⟩,
  ⟨.or, [55,54]⟩,
  ⟨.and, [5,56]⟩,
  ⟨.or, [25,31]⟩,
  ⟨.or, [58,39]⟩,
  ⟨.or, [59,45]⟩,
  ⟨.or, [60,51]⟩,
  ⟨.or, [61,57]⟩],62⟩
def run (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

def push (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (push x g) := rfl

theorem push_len (w : List Bool) (g : Gate) : (push w g).length = w.length + 1 := by
  simp [push]

theorem run_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih (push w g) (by rw [push_len]; omega)]
    exact List.getD_append _ _ _ _ hi


theorem evalAt (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g)
    (hf : ∀ i ∈ g.inputs, i < w.length+j) :
    (run gs w).getD (w.length+j) false =
      g.op.eval (g.inputs.map (fun i => (run gs w).getD i false)) := by
  induction gs generalizing w j with
  | nil => simp at hg
  | cons a gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hg
      subst a
      simp only [Nat.add_zero] at hf ⊢
      have he :
          g.inputs.map (fun i => (run (g::gs) w).getD i false) =
            g.inputs.map (fun i => w.getD i false) :=
        List.map_congr_left (fun i h => run_prefix _ _ _ (hf i h))
      rw [he,run_cons,run_prefix _ _ _ (by rw [push_len]; omega)]
      simp [push, List.getD_append_right]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hg
      rw [run_cons]
      have hlen : (push w a).length+j=w.length+(j+1) := by rw [push_len]; omega
      simpa only [hlen] using ih (push w a) j hg (fun i hi => by rw [hlen]; exact hf i hi)

def W (x : Fin 15 → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

theorem inp (x : Fin 15 → Bool) (i : Fin 15) : W x i.val = x i := by
  change (run C.gates (List.ofFn x)).getD i.val false = _
  rw [run_prefix _ _ _ (by simp),List.getD_eq_getElem]
  · rw [List.getElem_ofFn]
  · simp

theorem localGate (x : Fin 15 → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hf : ∀ i ∈ g.inputs, i < 15+j) :
    W x (15+j) = g.op.eval (g.inputs.map (W x)) := by
  have p := evalAt C.gates (List.ofFn x) j g hg
  have q : ∀ i ∈ g.inputs, i < (List.ofFn x).length + j := by
    simpa only [List.length_ofFn] using hf
  specialize p q
  rw [List.length_ofFn] at p
  exact p

set_option maxRecDepth 20000 in
theorem rbSmall :
    ∀ j : Fin 48, ∀ i ∈ (gateAt C j.val).inputs, i < 15 + j.val := by
  intro j
  fin_cases j <;> simp [gateAt,C]

set_option maxRecDepth 18000 in
theorem noDead :
    ∀ j : Fin 48, C.output = 15 + j.val ∨
      ∃ i : Fin 48, j.val < i.val ∧ 15 + j.val ∈ (C.gates.getD i.val ⟨.and,[]⟩).inputs := by
  intro j
  fin_cases j
  · exact Or.inr ⟨(4:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(5:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(8:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(9:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(6:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(6:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(7:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(8:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(9:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(10:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(43:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(14:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(14:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(15:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(15:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(16:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(43:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(21:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(21:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(22:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(23:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(22:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(23:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(24:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(44:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(28:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(28:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(29:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(29:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(30:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(45:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(34:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(34:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(35:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(35:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(36:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(46:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(40:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(40:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(41:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(41:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(42:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(47:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(44:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(45:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(46:Fin 48), by decide, by decide⟩
  · exact Or.inr ⟨(47:Fin 48), by decide, by decide⟩
  · left; decide

theorem dem (a b : Bool) : (!(!a && !b)) = (a || b) := by cases a <;> cases b <;> rfl

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem meaning (x : Fin 15 → Bool) : W x 62 = ((x 0 && x 1 && x 5) || (x 0 && x 2 && x 6) || (x 0 && x 3 && x 7) || (x 0 && x 4 && x 8) || (x 1 && x 2 && x 9) || (x 1 && x 3 && x 10) || (x 1 && x 4 && x 11) || (x 2 && x 3 && x 12) || (x 2 && x 4 && x 13) || (x 3 && x 4 && x 14) || (x 5 && x 6 && x 9) || (x 5 && x 7 && x 10) || (x 5 && x 8 && x 11) || (x 6 && x 7 && x 12) || (x 6 && x 8 && x 13) || (x 7 && x 8 && x 14) || (x 9 && x 10 && x 12) || (x 9 && x 11 && x 13) || (x 10 && x 11 && x 14) || (x 12 && x 13 && x 14)) := by
  have e0 : W x 0 = x 0 := inp x (0 : Fin 15)
  have e1 : W x 1 = x 1 := inp x (1 : Fin 15)
  have e2 : W x 2 = x 2 := inp x (2 : Fin 15)
  have e3 : W x 3 = x 3 := inp x (3 : Fin 15)
  have e4 : W x 4 = x 4 := inp x (4 : Fin 15)
  have e5 : W x 5 = x 5 := inp x (5 : Fin 15)
  have e6 : W x 6 = x 6 := inp x (6 : Fin 15)
  have e7 : W x 7 = x 7 := inp x (7 : Fin 15)
  have e8 : W x 8 = x 8 := inp x (8 : Fin 15)
  have e9 : W x 9 = x 9 := inp x (9 : Fin 15)
  have e10 : W x 10 = x 10 := inp x (10 : Fin 15)
  have e11 : W x 11 = x 11 := inp x (11 : Fin 15)
  have e12 : W x 12 = x 12 := inp x (12 : Fin 15)
  have e13 : W x 13 = x 13 := inp x (13 : Fin 15)
  have e14 : W x 14 = x 14 := inp x (14 : Fin 15)
  have g0 : W x 15 = (W x 1 && W x 5) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 0 (⟨.and, [1,5]⟩ : Gate) (by rfl) (by simp)
  have g1 : W x 16 = (W x 2 && W x 6) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 1 (⟨.and, [2,6]⟩ : Gate) (by rfl) (by simp)
  have g2 : W x 17 = (W x 3 && W x 7) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 2 (⟨.and, [3,7]⟩ : Gate) (by rfl) (by simp)
  have g3 : W x 18 = (W x 4 && W x 8) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 3 (⟨.and, [4,8]⟩ : Gate) (by rfl) (by simp)
  have g4 : W x 19 = (!(W x 15)) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 4 (⟨.not, [15]⟩ : Gate) (by rfl) (by simp)
  have g5 : W x 20 = (!(W x 16)) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 5 (⟨.not, [16]⟩ : Gate) (by rfl) (by simp)
  have g6 : W x 21 = (W x 19 && W x 20) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 6 (⟨.and, [19,20]⟩ : Gate) (by rfl) (by simp)
  have g7 : W x 22 = (!(W x 21)) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 7 (⟨.not, [21]⟩ : Gate) (by rfl) (by simp)
  have g8 : W x 23 = (W x 22 || W x 17) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 8 (⟨.or, [22,17]⟩ : Gate) (by rfl) (by simp)
  have g9 : W x 24 = (W x 23 || W x 18) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 9 (⟨.or, [23,18]⟩ : Gate) (by rfl) (by simp)
  have g10 : W x 25 = (W x 0 && W x 24) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 10 (⟨.and, [0,24]⟩ : Gate) (by rfl) (by simp)
  have g11 : W x 26 = (W x 2 && W x 9) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 11 (⟨.and, [2,9]⟩ : Gate) (by rfl) (by simp)
  have g12 : W x 27 = (W x 3 && W x 10) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 12 (⟨.and, [3,10]⟩ : Gate) (by rfl) (by simp)
  have g13 : W x 28 = (W x 4 && W x 11) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 13 (⟨.and, [4,11]⟩ : Gate) (by rfl) (by simp)
  have g14 : W x 29 = (W x 26 || W x 27) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 14 (⟨.or, [26,27]⟩ : Gate) (by rfl) (by simp)
  have g15 : W x 30 = (W x 29 || W x 28) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 15 (⟨.or, [29,28]⟩ : Gate) (by rfl) (by simp)
  have g16 : W x 31 = (W x 1 && W x 30) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 16 (⟨.and, [1,30]⟩ : Gate) (by rfl) (by simp)
  have g17 : W x 32 = (W x 2 && W x 3) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 17 (⟨.and, [2,3]⟩ : Gate) (by rfl) (by simp)
  have g18 : W x 33 = (W x 6 && W x 7) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 18 (⟨.and, [6,7]⟩ : Gate) (by rfl) (by simp)
  have g19 : W x 34 = (W x 9 && W x 10) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 19 (⟨.and, [9,10]⟩ : Gate) (by rfl) (by simp)
  have g20 : W x 35 = (W x 13 && W x 14) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 20 (⟨.and, [13,14]⟩ : Gate) (by rfl) (by simp)
  have g21 : W x 36 = (W x 32 || W x 33) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 21 (⟨.or, [32,33]⟩ : Gate) (by rfl) (by simp)
  have g22 : W x 37 = (W x 36 || W x 34) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 22 (⟨.or, [36,34]⟩ : Gate) (by rfl) (by simp)
  have g23 : W x 38 = (W x 37 || W x 35) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 23 (⟨.or, [37,35]⟩ : Gate) (by rfl) (by simp)
  have g24 : W x 39 = (W x 12 && W x 38) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 24 (⟨.and, [12,38]⟩ : Gate) (by rfl) (by simp)
  have g25 : W x 40 = (W x 2 && W x 4) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 25 (⟨.and, [2,4]⟩ : Gate) (by rfl) (by simp)
  have g26 : W x 41 = (W x 6 && W x 8) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 26 (⟨.and, [6,8]⟩ : Gate) (by rfl) (by simp)
  have g27 : W x 42 = (W x 9 && W x 11) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 27 (⟨.and, [9,11]⟩ : Gate) (by rfl) (by simp)
  have g28 : W x 43 = (W x 40 || W x 41) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 28 (⟨.or, [40,41]⟩ : Gate) (by rfl) (by simp)
  have g29 : W x 44 = (W x 43 || W x 42) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 29 (⟨.or, [43,42]⟩ : Gate) (by rfl) (by simp)
  have g30 : W x 45 = (W x 13 && W x 44) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 30 (⟨.and, [13,44]⟩ : Gate) (by rfl) (by simp)
  have g31 : W x 46 = (W x 3 && W x 4) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 31 (⟨.and, [3,4]⟩ : Gate) (by rfl) (by simp)
  have g32 : W x 47 = (W x 7 && W x 8) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 32 (⟨.and, [7,8]⟩ : Gate) (by rfl) (by simp)
  have g33 : W x 48 = (W x 10 && W x 11) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 33 (⟨.and, [10,11]⟩ : Gate) (by rfl) (by simp)
  have g34 : W x 49 = (W x 46 || W x 47) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 34 (⟨.or, [46,47]⟩ : Gate) (by rfl) (by simp)
  have g35 : W x 50 = (W x 49 || W x 48) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 35 (⟨.or, [49,48]⟩ : Gate) (by rfl) (by simp)
  have g36 : W x 51 = (W x 14 && W x 50) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 36 (⟨.and, [14,50]⟩ : Gate) (by rfl) (by simp)
  have g37 : W x 52 = (W x 6 && W x 9) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 37 (⟨.and, [6,9]⟩ : Gate) (by rfl) (by simp)
  have g38 : W x 53 = (W x 7 && W x 10) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 38 (⟨.and, [7,10]⟩ : Gate) (by rfl) (by simp)
  have g39 : W x 54 = (W x 8 && W x 11) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 39 (⟨.and, [8,11]⟩ : Gate) (by rfl) (by simp)
  have g40 : W x 55 = (W x 52 || W x 53) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 40 (⟨.or, [52,53]⟩ : Gate) (by rfl) (by simp)
  have g41 : W x 56 = (W x 55 || W x 54) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 41 (⟨.or, [55,54]⟩ : Gate) (by rfl) (by simp)
  have g42 : W x 57 = (W x 5 && W x 56) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 42 (⟨.and, [5,56]⟩ : Gate) (by rfl) (by simp)
  have g43 : W x 58 = (W x 25 || W x 31) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 43 (⟨.or, [25,31]⟩ : Gate) (by rfl) (by simp)
  have g44 : W x 59 = (W x 58 || W x 39) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 44 (⟨.or, [58,39]⟩ : Gate) (by rfl) (by simp)
  have g45 : W x 60 = (W x 59 || W x 45) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 45 (⟨.or, [59,45]⟩ : Gate) (by rfl) (by simp)
  have g46 : W x 61 = (W x 60 || W x 51) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 46 (⟨.or, [60,51]⟩ : Gate) (by rfl) (by simp)
  have g47 : W x 62 = (W x 61 || W x 57) := by
    simpa only [GateOp.eval,List.map_cons,List.map_nil,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] using
      localGate x 47 (⟨.or, [61,57]⟩ : Gate) (by rfl) (by simp)
  rw [g47, g46, g45, g44, g43, g42, g41, g40, g39, g38, g37, g36, g35, g34, g33, g32, g31, g30, g29, g28, g27, g26, g25, g24, g23, g22, g21, g20, g19, g18, g17, g16, g15, g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1, g0, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14]
  rw [dem (x 1 && x 5) (x 2 && x 6)]
  simp only [Bool.and_or_distrib_left,Bool.and_or_distrib_right]
  ac_rfl

end PEqualNP.Outside.L_meta_18972

open PEqualNP.Outside.L_meta_18972
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_18972 :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 15 C ∧ C.size ≤ 48 ∧ (∀ x : Fin 15 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1 && x 5) || (x 0 && x 2 && x 6) || (x 0 && x 3 && x 7) || (x 0 && x 4 && x 8) || (x 1 && x 2 && x 9) || (x 1 && x 3 && x 10) || (x 1 && x 4 && x 11) || (x 2 && x 3 && x 12) || (x 2 && x 4 && x 13) || (x 3 && x 4 && x 14) || (x 5 && x 6 && x 9) || (x 5 && x 7 && x 10) || (x 5 && x 8 && x 11) || (x 6 && x 7 && x 12) || (x 6 && x 8 && x 13) || (x 7 && x 8 && x 14) || (x 9 && x 10 && x 12) || (x 9 && x 11 && x 13) || (x 10 && x 11 && x 14) || (x 12 && x 13 && x 14))) ∧ (∀ j < C.size, C.output = 15 + j ∨ ∃ i < C.size, j < i ∧ 15 + j ∈ (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) ∧ (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → 15 ≤ g.inputs.headD 0 → (C.gates.getD (g.inputs.headD 0 - 15) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ 15 ≤ g.inputs.headD 0) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  refine ⟨C,?_,?_,by decide,?_,?_,?_,?_⟩
  · simp [C,PEqualNP.MetaComplexity.FanInTwo]
  · intro j hj
    exact rbSmall ⟨j,hj⟩
  · exact meaning
  · intro j hj
    rcases noDead ⟨j,hj⟩ with hp | ⟨i,h1,h2⟩
    · exact Or.inl hp
    · exact Or.inr ⟨i.val,i.isLt,h1,h2⟩
  · simp [C]
  · exact ⟨⟨.not,[15]⟩,by simp [C], rfl,by decide⟩
