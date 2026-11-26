import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_18925
namespace Excl18924
open CircuitLowerBounds

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

theorem run_at (gs : List Gate) (w : List Bool) (j a b : ℕ)
    (hg : gs[j]? = some ⟨.or, [a,b]⟩)
    (ha : a < w.length + j) (hb : b < w.length + j) :
    (run gs w).getD (w.length + j) false =
      ((run gs w).getD a false || (run gs w).getD b false) := by
  induction gs generalizing w j with
  | nil => simp at hg
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst g
      simp only [Nat.add_zero] at ha hb ⊢
      rw [run_prefix _ _ _ ha, run_prefix _ _ _ hb, run_cons]
      rw [run_prefix _ _ _ (by rw [push_len]; omega)]
      unfold push
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
      simp [GateOp.eval]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hg
      rw [run_cons]
      have hlen : (push w g).length + j = w.length + (j+1) := by rw [push_len]; omega
      simpa only [hlen] using ih (push w g) j hg (by omega) (by omega)

def mkp (n j : ℕ) : Gate :=
  ⟨.or, [if j = 0 then 0 else n + j - 1, j + 1]⟩
def mks (n k j : ℕ) : Gate :=
  ⟨.or, [if j = 0 then n-1 else n + k + j - 1, n - (j+2)]⟩
def mkm (n k i : ℕ) : Gate :=
  ⟨.or, [if i = 0 then 0 else n + i - 1,
    if i+1 = k then n-1 else n+k+(k-i-2)]⟩
def G (n k : ℕ) : List Gate :=
  List.ofFn (fun j : Fin k => mkp n j.val) ++
  List.ofFn (fun j : Fin k => mks n k j.val) ++
  List.ofFn (fun j : Fin k => mkm n k j.val)
def W (n k : ℕ) (x : Fin n → Bool) (a : ℕ) : Bool :=
  (run (G n k) (List.ofFn x)).getD a false

theorem W_input (n k : ℕ) (x : Fin n → Bool) (a : Fin n) :
    W n k x a.val = x a := by
  unfold W
  rw [run_prefix _ _ _ (by simpa using a.isLt), List.getD_eq_getElem]
  simp
  simpa using a.isLt

theorem Gp (n k j : ℕ) (h : j < k) : (G n k)[j]? = some (mkp n j) := by
  unfold G
  simp [List.getElem?_append, h]
theorem Gs (n k j : ℕ) (h : j < k) : (G n k)[k+j]? = some (mks n k j) := by
  unfold G
  simp [List.getElem?_append, h, show ¬k + j < k by omega]
theorem Gm (n k j : ℕ) (h : j < k) : (G n k)[k+k+j]? = some (mkm n k j) := by
  unfold G
  simp [List.getElem?_append, h, show ¬k+k+j < k by omega,
    show ¬k+k+j-k < k by omega, show k+k+j-k-k = j by omega]
theorem atp {n k j : ℕ} (x : Fin n → Bool) (hj : j<k) (hk : k+2=n) :
    W n k x (n+j) = (W n k x (if j=0 then 0 else n+j-1) || W n k x (j+1)) := by
  unfold W
  have q := run_at (G n k) (List.ofFn x) j _ _ (Gp n k j hj)
  simpa using q (by simp only [List.length_ofFn]; split <;> omega)
    (by simp only [List.length_ofFn]; omega)
theorem ats {n k j : ℕ} (x : Fin n → Bool) (hj : j<k) (hk : k+2=n) :
    W n k x (n+k+j) =
      (W n k x (if j=0 then n-1 else n+k+j-1) || W n k x (n-(j+2))) := by
  unfold W
  have q := run_at (G n k) (List.ofFn x) (k+j) _ _ (Gs n k j hj)
  simpa only [List.length_ofFn, Nat.add_assoc] using
    q (by simp only [List.length_ofFn]; split <;> omega) (by simp only [List.length_ofFn]; omega)
theorem atm {n k j : ℕ} (x : Fin n → Bool) (hj : j<k) (hk : k+2=n) :
    W n k x (n+k+k+j) =
      (W n k x (if j=0 then 0 else n+j-1) ||
       W n k x (if j+1=k then n-1 else n+k+(k-j-2))) := by
  unfold W
  have q := run_at (G n k) (List.ofFn x) (k+k+j) _ _ (Gm n k j hj)
  simpa only [List.length_ofFn, Nat.add_assoc] using
    q (by simp only [List.length_ofFn]; split <;> omega)
      (by simp only [List.length_ofFn]; split <;> omega)

theorem pre {n k : ℕ} (hk : k+2=n) (x : Fin n → Bool) (j : ℕ) (hj : j<k) :
    W n k x (n+j) = true ↔ ∃ a : Fin n, a.val ≤ j+1 ∧ x a = true := by
  induction j with
  | zero =>
    rw [atp x hj hk]
    simp only [if_true, Bool.or_eq_true]
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    rw [show W n k x 0 = x a from W_input n k x a, show W n k x (0+1) = x b from W_input n k x b]
    constructor
    · rintro (h|h)
      · exact ⟨a, by simp [a], h⟩
      · exact ⟨b, by simp [b], h⟩
    · rintro ⟨i, hi, hx⟩
      by_cases h0 : i.val = 0
      · left; rwa [show a = i from Fin.ext h0.symm]
      · right; rwa [show b = i from Fin.ext (by dsimp [b]; omega)]
  | succ j ih =>
    rw [atp x hj hk]
    simp only [Nat.succ_ne_zero, if_false, Bool.or_eq_true]
    rw [show n+(j+1)-1=n+j by omega, ih (by omega)]
    let a : Fin n := ⟨j+1+1, by omega⟩
    rw [show W n k x (j+1+1) = x a from W_input n k x a]
    constructor
    · rintro (⟨i, hi, hx⟩|hx)
      · exact ⟨i, by omega, hx⟩
      · exact ⟨a, le_rfl, hx⟩
    · rintro ⟨i, hi, hx⟩
      by_cases h : i.val ≤ j+1
      · exact Or.inl ⟨i, h, hx⟩
      · right; rwa [show a = i from Fin.ext (by dsimp [a]; omega)]

theorem suf {n k : ℕ} (hk : k+2=n) (x : Fin n → Bool) (j : ℕ) (hj : j<k) :
    W n k x (n+k+j) = true ↔ ∃ a : Fin n, n-(j+2) ≤ a.val ∧ x a = true := by
  induction j with
  | zero =>
    rw [ats x hj hk]
    simp only [if_true, Bool.or_eq_true]
    let a : Fin n := ⟨n-1, by omega⟩
    let b : Fin n := ⟨n-2, by omega⟩
    rw [show W n k x (n-1) = x a from W_input n k x a, show W n k x (n-(0+2)) = x b from W_input n k x b]
    constructor
    · rintro (h|h)
      · exact ⟨a, by dsimp [a]; omega, h⟩
      · exact ⟨b, le_rfl, h⟩
    · rintro ⟨i, hi, hx⟩
      by_cases h : i.val = n-1
      · left; rwa [show a = i from Fin.ext h.symm]
      · right; rwa [show b = i from Fin.ext (by have := i.isLt; dsimp [b]; omega)]
  | succ j ih =>
    rw [ats x hj hk]
    simp only [Nat.succ_ne_zero, if_false, Bool.or_eq_true]
    rw [show n+k+(j+1)-1=n+k+j by omega, ih (by omega)]
    let a : Fin n := ⟨n-(j+1+2), by omega⟩
    rw [show W n k x (n-(j+1+2)) = x a from W_input n k x a]
    constructor
    · rintro (⟨i, hi, hx⟩|hx)
      · exact ⟨i, by omega, hx⟩
      · exact ⟨a, le_rfl, hx⟩
    · rintro ⟨i, hi, hx⟩
      by_cases h : n-(j+2) ≤ i.val
      · exact Or.inl ⟨i, h, hx⟩
      · right; rwa [show a = i from Fin.ext (by dsimp [a]; omega)]

theorem mp {n k : ℕ} (hk : k+2=n) (x : Fin n → Bool) (j : ℕ) (hj : j<k) :
    W n k x (if j=0 then 0 else n+j-1) = true ↔ ∃ a : Fin n, a.val ≤ j ∧ x a = true := by
  cases j with
  | zero =>
    rw [if_pos rfl]
    let a : Fin n := ⟨0, by omega⟩
    rw [show W n k x 0 = x a from W_input n k x a]
    constructor
    · intro h; exact ⟨a, le_rfl, h⟩
    · rintro ⟨i, h, hx⟩
      rwa [show a = i from Fin.ext (by dsimp [a]; omega)]
  | succ j =>
    rw [if_neg (Nat.succ_ne_zero _), show n+(j+1)-1 = n+j by omega, pre hk x j (by omega)]

theorem ms {n k : ℕ} (hk : k+2=n) (x : Fin n → Bool) (j : ℕ) (hj : j<k) :
    W n k x (if j+1=k then n-1 else n+k+(k-j-2)) = true ↔
      ∃ a : Fin n, j+2 ≤ a.val ∧ x a = true := by
  by_cases h : j+1=k
  · rw [if_pos h]
    let a : Fin n := ⟨n-1, by omega⟩
    rw [show W n k x (n-1) = x a from W_input n k x a]
    constructor
    · intro hx; exact ⟨a, by dsimp [a]; omega, hx⟩
    · rintro ⟨i, hi, hx⟩
      have := i.isLt
      rwa [show a = i from Fin.ext (by dsimp [a]; omega)]
  · rw [if_neg h, suf hk x (k-j-2) (by omega)]
    have he : n - (k - j - 2 + 2) = j+2 := by omega
    rw [he]

theorem basic (n k : ℕ) (hk : k+2=n) (hp : 0<k) :
    ∃ C : Circuit, MetaComplexity.Monotone2 C ∧ C.size ≤ 3*n-6 ∧
      ∃ w : Fin n → ℕ, ∀ x i,
        (C.wires (List.ofFn x)).getD (w i) false = decide (∃ j : Fin n, j ≠ i ∧ x j = true) := by
  refine ⟨⟨G n k,0⟩, ?_, ?_, fun i => if i.val=0 then n+k+(k-1)
      else if i.val=n-1 then n+(k-1) else n+k+k+(i.val-1), ?_⟩
  · intro g hg
    simp only [G, List.mem_append, List.mem_ofFn] at hg
    rcases hg with ((⟨_,rfl⟩|⟨_,rfl⟩)|⟨_,rfl⟩) <;> simp [mkp,mks,mkm]
  · simp [Circuit.size, G]
    omega
  · intro x i
    change W n k x _ = _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hil := i.isLt
    by_cases h0 : i.val = 0
    · rw [if_pos h0, suf hk x (k-1) (by omega)]
      constructor
      · rintro ⟨a, ha, hx⟩
        exact ⟨a, fun h => by rw [h,h0] at ha; omega, hx⟩
      · rintro ⟨a, ha, hx⟩
        exact ⟨a, by have hne : a.val ≠ i.val := fun h => ha (Fin.ext h); omega, hx⟩
    · rw [if_neg h0]
      by_cases he : i.val = n-1
      · rw [if_pos he, pre hk x (k-1) (by omega)]
        constructor
        · rintro ⟨a, ha, hx⟩
          exact ⟨a, fun h => by rw [h,he] at ha; omega, hx⟩
        · rintro ⟨a, ha, hx⟩
          have hne : a.val ≠ i.val := fun h => ha (Fin.ext h)
          exact ⟨a, by have := a.isLt; omega, hx⟩
      · have hm : i.val-1 < k := by omega
        rw [if_neg he, atm x hm hk, Bool.or_eq_true, mp hk x _ hm, ms hk x _ hm]
        constructor
        · rintro (⟨a, ha, hx⟩|⟨a, ha, hx⟩) <;>
            exact ⟨a, fun h => by rw [h] at ha; omega, hx⟩
        · rintro ⟨a, ha, hx⟩
          have hn : a.val ≠ i.val := fun h => ha (Fin.ext h)
          by_cases h : a.val < i.val
          · exact Or.inl ⟨a, by omega, hx⟩
          · exact Or.inr ⟨a, by omega, hx⟩
end Excl18924

open PEqualNP.CircuitLowerBounds
private theorem allButOne :
∀ (n : ℕ), ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 3 * n - 6 ∧
  ∃ w : Fin n → ℕ, ∀ (x : Fin n → Bool) (i : Fin n),
    (C.wires (List.ofFn x)).getD (w i) false = decide (∃ j : Fin n, j ≠ i ∧ x j = true) := by
  intro n
  obtain (_|_|_|n) := n
  · refine ⟨⟨[],0⟩, ?_, by decide, fun i => Fin.elim0 i, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · intro _ i; exact Fin.elim0 i
  · refine ⟨⟨[],0⟩, ?_, by decide, fun _ => 1, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · intro x i; fin_cases i
      simp [Circuit.wires, List.ofFn_succ]
  · refine ⟨⟨[],0⟩, ?_, by decide, fun i => 1-i.val, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · intro x i; fin_cases i <;> simp [Circuit.wires, List.ofFn_succ, Fin.exists_fin_succ]
  · exact Excl18924.basic _ (n+1) (by omega) (by omega)

namespace Comp18925
open CircuitLowerBounds MetaComplexity Represents Excl18924

inductive Ref where
  | zero | one | wire (i : ℕ)
  deriving DecidableEq

def Ref.read (w : List Bool) : Ref → Bool
  | .zero => false
  | .one => true
  | .wire i => w.getD i false

def Ref.index : Ref → Option ℕ
  | .wire i => some i
  | _ => none

def andGate (l : List Ref) : Gate :=
  if .zero ∈ l then ⟨.or, []⟩ else ⟨.and, l.filterMap Ref.index⟩

def orGate (l : List Ref) : Gate :=
  if .one ∈ l then ⟨.and, []⟩ else ⟨.or, l.filterMap Ref.index⟩

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

theorem andValue (w : List Bool) (l : List Ref) :
    gateValue w (andGate l) = (l.map (Ref.read w)).all id := by
  by_cases hz : Ref.zero ∈ l
  · rw [andGate, if_pos hz]
    have h : (l.map (Ref.read w)).all id = false := by
      rw [Bool.eq_false_iff]
      intro ht
      have q := List.all_eq_true.mp ht false (List.mem_map.mpr ⟨Ref.zero,hz,rfl⟩)
      contradiction
    rw [h]; rfl
  · rw [andGate, if_neg hz]
    change ((l.filterMap Ref.index).map (fun i => w.getD i false)).all id = _
    induction l with
    | nil => rfl
    | cons t l ih =>
      have hl : Ref.zero ∉ l := fun h => hz (List.mem_cons_of_mem _ h)
      cases t with
      | zero => exfalso; exact hz (by simp)
      | one => simpa [Ref.index, Ref.read] using ih hl
      | wire i => simpa [Ref.index, Ref.read] using congrArg (fun v => w.getD i false && v) (ih hl)

theorem orValue (w : List Bool) (l : List Ref) :
    gateValue w (orGate l) = (l.map (Ref.read w)).any id := by
  by_cases hz : Ref.one ∈ l
  · rw [orGate, if_pos hz]
    have h : (l.map (Ref.read w)).any id = true :=
      List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨Ref.one,hz,rfl⟩, rfl⟩
    rw [h]; rfl
  · rw [orGate, if_neg hz]
    change ((l.filterMap Ref.index).map (fun i => w.getD i false)).any id = _
    induction l with
    | nil => rfl
    | cons t l ih =>
      have hl : Ref.one ∉ l := fun h => hz (List.mem_cons_of_mem _ h)
      cases t with
      | zero => simpa [Ref.index, Ref.read] using ih hl
      | one => exfalso; exact hz (by simp)
      | wire i => simpa [Ref.index, Ref.read] using congrArg (fun v => w.getD i false || v) (ih hl)

def OK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem andOK (l : List Ref) (h : l.length ≤ 2) : OK (andGate l) := by
  unfold andGate
  split <;> simp [OK]
  exact (List.length_filterMap_le _ _).trans h

theorem orOK (l : List Ref) (h : l.length ≤ 2) : OK (orGate l) := by
  unfold orGate
  split <;> simp [OK]
  exact (List.length_filterMap_le _ _).trans h

def Ref.live (k : ℕ) : Ref → Prop
  | .wire i => i < k
  | _ => True

theorem stable (x y : List Bool) (r : Ref) (h : r.live x.length) :
    r.read (x ++ y) = r.read x := by
  cases r
  · rfl
  · rfl
  · exact List.getD_append _ _ _ _ h

def positive (i k : ℕ) (f : ℕ → Ref × Ref) : Ref :=
  if i < k then (f i).1 else .zero
def negative (i k : ℕ) (f : ℕ → Ref × Ref) : Ref :=
  if i < k then (f i).2 else .one

theorem rdpos (u v : List Bool) (f : ℕ → Ref × Ref)
    (h : ∀ i < u.length, ((f i).1).read v = u.getD i false) (i : ℕ) :
    (positive i u.length f).read v = u.getD i false := by
  by_cases hi : i < u.length
  · simpa [positive, hi] using h i hi
  · simp [positive, hi, Ref.read, List.getD_eq_default _ _ (by omega : u.length ≤ i)]

theorem rdneg (u v : List Bool) (f : ℕ → Ref × Ref)
    (h : ∀ i < u.length, ((f i).2).read v = !(u.getD i false)) (i : ℕ) :
    (negative i u.length f).read v = !(u.getD i false) := by
  by_cases hi : i < u.length
  · simpa [negative, hi] using h i hi
  · simp [negative, hi, Ref.read, List.getD_eq_default _ _ (by omega : u.length ≤ i)]

def gates (u : ℕ) (f : ℕ → Ref × Ref) (g : Gate) : Gate × Gate :=
  let p := g.inputs.map fun i => positive i u f
  let q := g.inputs.map fun i => negative i u f
  match g.op with
  | .and => (andGate p, orGate q)
  | .or => (orGate p, andGate q)
  | .not => (orGate [q.headD .one], orGate [p.headD .zero])
  | _ => (orGate [], andGate [])

def oldOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem gates_ok (m : ℕ) (f : ℕ → Ref × Ref) (g : Gate) (h : oldOK g) :
    OK (gates m f g).1 ∧ OK (gates m f g).2 := by
  have hp : (g.inputs.map (fun i => positive i m f)).length ≤ 2 := by simpa using h.2
  have hn : (g.inputs.map (fun i => negative i m f)).length ≤ 2 := by simpa using h.2
  cases hg : g.op <;> simp only [gates, hg]
  · exact ⟨andOK _ hp, orOK _ hn⟩
  · exact ⟨orOK _ hp, andOK _ hn⟩
  · exact ⟨orOK _ (by simp), orOK _ (by simp)⟩
  · have hp := h.1; simp [hg] at hp
  · have hp := h.1; simp [hg] at hp

theorem demorgan1 (b : List Bool) :
    (b.map Bool.not).any id = !(b.all id) := by
  induction b with
  | nil => rfl
  | cons x _ ih => cases x <;> simp [ih]

theorem demorgan2 (b : List Bool) :
    (b.map Bool.not).all id = !(b.any id) := by
  induction b with
  | nil => rfl
  | cons x _ ih => cases x <;> simp [ih]

def Rel (u v : List Bool) (f : ℕ → Ref × Ref) : Prop :=
  ∀ i < u.length,
    ((f i).1).live v.length ∧ ((f i).2).live v.length ∧
    ((f i).1).read v = u.getD i false ∧ ((f i).2).read v = !(u.getD i false)

theorem oneStep (u v : List Bool) (f : ℕ → Ref × Ref) (h : Rel u v f)
    (g : Gate) (hg : oldOK g) :
    gateValue v (gates u.length f g).1 = gateValue u g ∧
    gateValue v (gates u.length f g).2 = !(gateValue u g) := by
  have hp := rdpos u v f (fun i hi => (h i hi).2.2.1)
  have hn := rdneg u v f (fun i hi => (h i hi).2.2.2)
  have qp (l : List ℕ) :
      (l.map (fun i => positive i u.length f)).map (Ref.read v) = l.map (fun i => u.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hp i)
  have qn (l : List ℕ) :
      (l.map (fun i => negative i u.length f)).map (Ref.read v) = (l.map (fun i => u.getD i false)).map Bool.not := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun i _ => hn i)
  cases hop : g.op
  · simp only [gates, hop, gateValue, GateOp.eval]
    change gateValue v (andGate _) = _ ∧ gateValue v (orGate _) = _
    rw [andValue, orValue, qp, qn, demorgan1]
    exact ⟨rfl,rfl⟩
  · simp only [gates, hop, gateValue, GateOp.eval]
    change gateValue v (orGate _) = _ ∧ gateValue v (andGate _) = _
    rw [orValue, andValue, qp, qn, demorgan2]
    exact ⟨rfl,rfl⟩
  · simp only [gates, hop, gateValue, GateOp.eval]
    change gateValue v (orGate [_]) = _ ∧ gateValue v (orGate [_]) = _
    rw [orValue, orValue]
    cases hi : g.inputs with
    | nil => exact ⟨rfl,rfl⟩
    | cons i is => simp only [List.map_cons, List.map_nil, List.headD_cons, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.not_not, hp, hn, and_self]
  · have p := hg.1; simp [hop] at p
  · have p := hg.1; simp [hop] at p

def newer (u v i : ℕ) (f : ℕ → Ref × Ref) : Ref × Ref :=
  if i = u then (.wire v,.wire (v+1)) else f i

def compile : List Gate → ℕ → ℕ → (ℕ → Ref × Ref) → List Gate × (ℕ → Ref × Ref)
  | [], _, _, f => ([], f)
  | g :: gs, u, v, f =>
    let r := compile gs (u+1) (v+2) (fun i => newer u v i f)
    ((gates u f g).1 :: (gates u f g).2 :: r.1, r.2)

theorem compile_len (gs : List Gate) (u v : ℕ) (f : ℕ → Ref × Ref) :
    (compile gs u v f).1.length = 2*gs.length := by
  induction gs generalizing u v f with
  | nil => rfl
  | cons g gs ih => simp [compile,ih]; omega

theorem compile_ok (gs : List Gate) (u v : ℕ) (f : ℕ → Ref × Ref)
    (hg : ∀ g ∈ gs, oldOK g) : ∀ g ∈ (compile gs u v f).1, OK g := by
  induction gs generalizing u v f with
  | nil => simp [compile]
  | cons g gs ih =>
    intro z hz
    simp only [compile,List.mem_cons] at hz
    rcases hz with rfl|rfl|hz
    · exact (gates_ok _ _ _ (hg _ (by simp))).1
    · exact (gates_ok _ _ _ (hg _ (by simp))).2
    · exact ih _ _ _ (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) _ hz

theorem rdStable (u v : List Bool) (m : ℕ) (f : ℕ → Ref × Ref)
    (h : ∀ i < m, ((f i).1).live u.length ∧ ((f i).2).live u.length)
    (i : ℕ) :
    (positive i m f).read (u++v) = (positive i m f).read u ∧
    (negative i m f).read (u++v) = (negative i m f).read u := by
  by_cases hi : i < m
  · exact ⟨by simpa [positive,hi] using stable u v (f i).1 (h i hi).1,
      by simpa [negative,hi] using stable u v (f i).2 (h i hi).2⟩
  · simp [positive,negative,hi,Ref.read]

theorem indexLive (r : Ref) (i k : ℕ) (h : r.live k) (hi : r.index = some i) : i < k := by
  cases r <;> simp_all [Ref.live,Ref.index]

theorem andEarly (l : List Ref) (k : ℕ) (h : ∀ r ∈ l, r.live k) :
    ∀ i ∈ (andGate l).inputs, i < k := by
  intro i hi
  unfold andGate at hi
  split at hi
  · simp at hi
  · obtain ⟨r,hr,hi⟩ := List.mem_filterMap.mp hi
    exact indexLive r i k (h r hr) hi

theorem orEarly (l : List Ref) (k : ℕ) (h : ∀ r ∈ l, r.live k) :
    ∀ i ∈ (orGate l).inputs, i < k := by
  intro i hi
  unfold orGate at hi
  split at hi
  · simp at hi
  · obtain ⟨r,hr,hi⟩ := List.mem_filterMap.mp hi
    exact indexLive r i k (h r hr) hi

theorem gateEarly (u v : List Bool) (f : ℕ → Ref × Ref) (r : Rel u v f) (g : Gate) :
    ∀ i ∈ (gates u.length f g).2.inputs, i < v.length := by
  have hp (i : ℕ) : (positive i u.length f).live v.length := by
    by_cases hi : i<u.length
    · simpa [positive,hi] using (r i hi).1
    · simp [positive,hi,Ref.live]
  have hn (i : ℕ) : (negative i u.length f).live v.length := by
    by_cases hi : i<u.length
    · simpa [negative,hi] using (r i hi).2.1
    · simp [negative,hi,Ref.live]
  cases h : g.op <;> simp only [gates,h]
  · apply orEarly
    intro r hr; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr; exact hn i
  · apply andEarly
    intro r hr; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr; exact hn i
  · apply orEarly; intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    cases hi : g.inputs with
    | nil => trivial
    | cons i is => exact hp i
  · apply andEarly; simp
  · apply andEarly; simp

theorem value_stable (v t : List Bool) (g : Gate)
    (h : ∀ i ∈ g.inputs, i < v.length) :
    gateValue (v++t) g = gateValue v g := by
  unfold gateValue
  congr 1
  exact List.map_congr_left (fun i hi => List.getD_append _ _ _ _ (h i hi))

theorem relStep (u v : List Bool) (f : ℕ → Ref × Ref) (r : Rel u v f)
    (g : Gate) (hg : oldOK g) :
    Rel (push u g) (push (push v (gates u.length f g).1) (gates u.length f g).2)
      (fun i => newer u.length v.length i f) := by
  let a := gateValue u g
  have ⟨ha,hb⟩ := oneStep u v f r g hg
  have hp : push v (gates u.length f g).1 = v++[a] := by
    change v ++ [gateValue v _] = _
    rw [ha]
  have hq : push (push v (gates u.length f g).1) (gates u.length f g).2 = v++[a,!a] := by
    rw [hp]
    change (v++[a]) ++ [gateValue (v++[a]) _] = _
    rw [value_stable v [a] _ (gateEarly u v f r g),hb]
    simp [a]
  have ho : push u g = u ++ [a] := rfl
  intro i hi
  rw [ho] at hi
  rw [hq,ho]
  by_cases h : i<u.length
  · have hr := r i h
    have hne : i ≠ u.length := by omega
    simp only [newer,if_neg hne]
    have hlen : v.length ≤ (v++[a,!a]).length := by simp
    refine ⟨?_,?_,?_,?_⟩
    · generalize (f i).1 = lhs at *
      cases lhs <;> simp_all [Ref.live] <;> omega
    · generalize (f i).2 = lhs at *
      cases lhs <;> simp_all [Ref.live] <;> omega
    · rw [stable _ _ _ hr.1, List.getD_append _ _ _ _ h]; exact hr.2.2.1
    · rw [stable _ _ _ hr.2.1,List.getD_append _ _ _ _ h]; exact hr.2.2.2
  · have he : i=u.length := by simp at hi; omega
    subst i
    simp only [newer,if_pos rfl,if_true]
    simp only [Ref.live,Ref.read,List.length_append,List.length_cons,List.length_nil]
    have hw : v.length ≤ v.length+1 := by omega
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),List.getD_append_right _ _ _ _ hw,
      List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp

theorem compile_rel (gs : List Gate) (u v : List Bool) (f : ℕ → Ref × Ref)
    (r : Rel u v f) (hg : ∀ g ∈ gs, oldOK g) :
    Rel (run gs u) (run (compile gs u.length v.length f).1 v)
      (compile gs u.length v.length f).2 := by
  induction gs generalizing u v f with
  | nil => exact r
  | cons g gs ih =>
    have ha := relStep u v f r g (hg g (by simp))
    have hvl : (push (push v (gates u.length f g).1) (gates u.length f g).2).length = v.length+2 := by
      rw [push_len,push_len]
    simpa only [compile,run_cons,push_len,hvl] using ih (push u g)
      (push (push v (gates u.length f g).1) (gates u.length f g).2)
      _ ha (fun g h => hg g (List.mem_cons_of_mem _ h))


def embedGate (u : ℕ) (f : ℕ → Ref) (g : Gate) : Gate :=
  let p := g.inputs.map (fun i => if i<u then f i else Ref.zero)
  match g.op with
  | .and => andGate p
  | _ => orGate p

def embed : List Gate → ℕ → ℕ → (ℕ → Ref) → List Gate × (ℕ → Ref)
  | [],_,_,f => ([],f)
  | g :: gs,u,v,f =>
    let t := embed gs (u+1) (v+1) (fun i => if i=u then Ref.wire v else f i)
    (embedGate u f g :: t.1,t.2)

theorem lenRun (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons,ih,push_len,List.length_cons]; omega

theorem run_append (gs gt : List Gate) (x : List Bool) :
    run (gs++gt) x = run gt (run gs x) := by
  simp [run,Circuit.wires,List.foldl_append]

theorem embedLen (gs : List Gate) (u v : ℕ) (f : ℕ → Ref) :
    (embed gs u v f).1.length = gs.length := by
  induction gs generalizing u v f with
  | nil => rfl
  | cons g gs ih => simp [embed,ih]

theorem embedOK (gs : List Gate) (u v : ℕ) (f : ℕ → Ref)
    (h : ∀ g ∈ gs, OK g) : ∀ g ∈ (embed gs u v f).1, OK g := by
  induction gs generalizing u v f with
  | nil => simp [embed]
  | cons g gs ih =>
    intro k hk
    simp only [embed, List.mem_cons] at hk
    rcases hk with rfl|hk
    · have hg := h g (by simp)
      unfold embedGate
      cases g.op <;> first | apply andOK | apply orOK
      all_goals simpa using hg.2
    · exact ih _ _ _ (fun g hm => h g (List.mem_cons_of_mem _ hm)) _ hk

def Rel1 (u v : List Bool) (f : ℕ → Ref) : Prop :=
  ∀ i < u.length, (f i).live v.length ∧ (f i).read v = u.getD i false

theorem embValue (u v : List Bool) (f : ℕ → Ref) (r : Rel1 u v f) (g : Gate) (hg : OK g) :
    gateValue v (embedGate u.length f g) = gateValue u g := by
  have hh (i : ℕ) :
      (if i<u.length then f i else Ref.zero).read v = u.getD i false := by
    by_cases hi : i < u.length
    · simpa [hi] using (r i hi).2
    · simp [hi,Ref.read,List.getD_eq_default _ _ (by omega : u.length ≤ i)]
  have q :
      (g.inputs.map (fun i => if i<u.length then f i else Ref.zero)).map (Ref.read v) =
       g.inputs.map (fun i => u.getD i false) := by
    rw [List.map_map]; exact List.map_congr_left (fun i _ => hh i)
  rcases (show g.op = .and ∨ g.op = .or by simpa using hg.1) with he|he
  · simp only [embedGate,he]
    rw [andValue,q]
    simp [gateValue,he,GateOp.eval]
  · simp only [embedGate,he]
    rw [orValue,q]
    simp [gateValue,he,GateOp.eval]

theorem lMono (a b : ℕ) (h : a ≤ b) (r : Ref) (p : r.live a) : r.live b := by
  cases r <;> simp_all [Ref.live] <;> omega

theorem embStep (u v : List Bool) (f : ℕ → Ref) (r : Rel1 u v f)
    (g : Gate) (hg : OK g) :
    Rel1 (push u g) (push v (embedGate u.length f g))
      (fun i => if i=u.length then Ref.wire v.length else f i) := by
  have hv := embValue u v f r g hg
  have h1 : push u g = u ++ [gateValue u g] := rfl
  have h2 : push v (embedGate u.length f g) = v ++ [gateValue u g] := by
    change v++[gateValue v (embedGate u.length f g)] = _
    rw [hv]
  intro i hi
  rw [h1] at hi
  rw [h1,h2]
  by_cases h : i<u.length
  · have he : i ≠ u.length := by omega
    simp only [if_neg he]
    exact ⟨lMono _ _ (by simp) _ (r i h).1,
      by rw [stable _ _ _ (r i h).1,List.getD_append _ _ _ _ h]; exact (r i h).2⟩
  · have he : i=u.length := by simp at hi; omega
    subst i
    simp [Ref.live,Ref.read,List.getD_append_right]

theorem embedRel (gs : List Gate) (u v : List Bool) (f : ℕ → Ref)
    (r : Rel1 u v f) (h : ∀ g ∈ gs, OK g) :
    Rel1 (run gs u) (run (embed gs u.length v.length f).1 v)
      (embed gs u.length v.length f).2 := by
  induction gs generalizing u v f with
  | nil => exact r
  | cons g gs ih =>
    have q := ih (push u g) (push v (embedGate u.length f g)) _
      (embStep u v f r g (h g (by simp))) (fun g hm => h g (List.mem_cons_of_mem _ hm))
    simpa only [embed,run_cons,push_len] using q

theorem rel1Read (u v : List Bool) (f : ℕ → Ref) (r : Rel1 u v f) (i : ℕ) :
    let k := if i < u.length then f i else Ref.zero
    k.live v.length ∧ k.read v = u.getD i false := by
  dsimp
  by_cases h : i<u.length
  · simpa [h] using r i h
  · simp [h,Ref.live,Ref.read,List.getD_eq_default _ _ (by omega : u.length ≤ i)]


def pick (k i : ℕ) (f : ℕ → Ref) : Ref :=
  if i<k then f i else .zero

def WiresPos (k : ℕ) (f : ℕ → Ref × Ref) : Prop :=
  ∀ i < k, ∃ j, (f i).1 = .wire j

theorem compile_real (gs : List Gate) (u v : ℕ) (f : ℕ → Ref × Ref)
    (h : WiresPos u f) : WiresPos (u+gs.length) (compile gs u v f).2 := by
  induction gs generalizing u v f with
  | nil => simpa [compile] using h
  | cons g gs ih =>
    have hn : WiresPos (u+1) (fun i => newer u v i f) := by
      intro i hi
      by_cases he : i=u
      · exact ⟨v,by simp [newer,he]⟩
      · exact (by simpa [newer,he] using h i (by omega))
    have q := ih (u+1) (v+2) _ hn
    simpa only [compile,List.length_cons,show u+(gs.length+1) = u+1+gs.length by omega] using q

theorem oneOther {n : ℕ} (u i : Fin n) :
    decide (∃ j : Fin n, j ≠ i ∧ decide (j=u) = true) = !(decide (i=u)) := by
  by_cases hi : i=u
  · subst u; simp
  · have h' : u ≠ i := Ne.symm hi
    have hp : ∃ j : Fin n, j ≠ i ∧ decide (j=u) = true := ⟨u,h',by simp⟩
    simpa [hi,hp] using h'

theorem inputFn (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem]
  · simp
  · simpa using i.isLt

theorem main {n m s : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) (hC : FanInTwo C)
    (hsize : C.size ≤ s) (hA : Represents A C) :
    RepSizeAtMost A (2*s+((3*n-6)+(3*m-6))) := by
  obtain ⟨L,hL,hsL,l,hl⟩ := allButOne n
  obtain ⟨R,hR,hsR,r,hr⟩ := allButOne m
  let EL := embed L.gates n (n+m) Ref.wire
  let ER := embed R.gates m (n+m+L.size) (fun j => Ref.wire (n+j))
  let n0 := n+m+L.size+R.size
  let f : ℕ → Ref × Ref := fun i =>
    (.wire i, if h : i<n then
      pick (n+L.size) (l ⟨i,h⟩) EL.2
      else if h' : i-n<m then pick (m+R.size) (r ⟨i-n,h'⟩) ER.2 else .zero)
  let T := compile C.gates (n+m) n0 f
  let size := n0+2*C.size
  let out := if C.output < n+m+C.size then
    ((T.2 C.output).1).index.getD size
    else size
  refine ⟨⟨EL.1++ER.1++T.1,out⟩,?_,?_,?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (h|h)|h
    · exact embedOK _ _ _ _ hL _ h
    · exact embedOK _ _ _ _ hR _ h
    · exact compile_ok _ _ _ _ hC _ h
  · change (EL.1++ER.1++T.1).length ≤ _
    have eL : EL.1.length = L.size := embedLen _ _ _ _
    have eR : ER.1.length = R.size := embedLen _ _ _ _
    have eT : T.1.length = 2*C.size := compile_len _ _ _ _
    rw [List.length_append,List.length_append,eL,eR,eT]
    omega
  · intro u v
    let a : Fin n → Bool := fun i => decide (i=u)
    let b : Fin m → Bool := fun i => decide (i=v)
    let xx := List.ofFn a
    let yy := List.ofFn b
    let raw := xx++yy
    let vl := run EL.1 raw
    let vr := run ER.1 vl
    have lx : xx.length = n := List.length_ofFn
    have ly : yy.length = m := List.length_ofFn
    have lr : raw.length = n+m := by simp [raw,lx,ly]
    have lL : (run L.gates xx).length = n+L.size := by
      rw [lenRun,lx]; rfl
    have lR : (run R.gates yy).length = m+R.size := by
      rw [lenRun,ly]; rfl
    have l1 : vl.length = n+m+L.size := by
      change (run EL.1 raw).length = _
      rw [lenRun,lr,show EL.1.length = L.size from embedLen _ _ _ _]
    have l2 : vr.length = n0 := by
      change (run ER.1 vl).length = _
      rw [lenRun,l1,show ER.1.length=R.size from embedLen _ _ _ _]
    have rl : Rel1 xx raw Ref.wire := by
      intro i hi
      exact ⟨by change i < (xx++yy).length; simp <;> omega, List.getD_append _ _ _ _ hi⟩
    have rr : Rel1 yy vl (fun j => Ref.wire (n+j)) := by
      intro i hi
      have hlim : n+i<raw.length := by omega
      refine ⟨by rw [l1]; dsimp [Ref.live]; omega, ?_⟩
      change (run EL.1 raw).getD (n+i) false = yy.getD i false
      rw [run_prefix _ _ _ hlim]
      change (xx++yy).getD (n+i) false = _
      rw [List.getD_append_right _ _ _ _ (by omega : xx.length ≤ n+i),lx]
      simp
    have rlA : Rel1 (run L.gates xx) vl EL.2 := by
      have h := embedRel L.gates xx raw Ref.wire rl hL
      simpa only [lx,lr,EL,vl] using h
    have rrA : Rel1 (run R.gates yy) vr ER.2 := by
      have h := embedRel R.gates yy vl (fun j => Ref.wire (n+j)) rr hR
      simpa only [ly,l1,ER,vr] using h
    have negLeft (i : Fin n) :
        let z := pick (n+L.size) (l i) EL.2
        z.live vl.length ∧ z.read vl = !(a i) := by
      have p := rel1Read _ _ _ rlA (l i)
      have q := hl a i
      change (run L.gates xx).getD (l i) false = _ at q
      rw [oneOther] at q
      simpa only [lL,pick,q,a] using p
    have negRight (i : Fin m) :
        let z := pick (m+R.size) (r i) ER.2
        z.live vr.length ∧ z.read vr = !(b i) := by
      have p := rel1Read _ _ _ rrA (r i)
      have q := hr b i
      change (run R.gates yy).getD (r i) false = _ at q
      rw [oneOther] at q
      simpa only [lR,pick,q,b] using p
    have stableRun (z : Ref) (hz : z.live vl.length) :
        z.live vr.length ∧ z.read vr = z.read vl := by
      refine ⟨lMono _ _ (by rw [l1,l2]; dsimp [n0]; omega) _ hz, ?_⟩
      cases z
      · rfl
      · rfl
      · exact run_prefix _ _ _ hz
    have initial : Rel raw vr f := by
      intro i hi
      have il : i < n+m := by rwa [lr] at hi
      have iv : i < vl.length := by omega
      refine ⟨by dsimp [f,Ref.live]; rw [l2]; dsimp [n0]; omega, ?_, ?_, ?_⟩
      · by_cases h : i<n
        · simpa [f,h] using (stableRun _ (negLeft ⟨i,h⟩).1).1
        · have h' : i-n<m := by omega
          simpa [f,h,h'] using (negRight ⟨i-n,h'⟩).1
      · change (run ER.1 vl).getD i false = _
        rw [run_prefix _ _ _ iv]
        exact run_prefix _ _ _ hi
      · by_cases h : i<n
        · have q := negLeft ⟨i,h⟩
          have e : raw.getD i false = a ⟨i,h⟩ := by
            change (xx++yy).getD i false = _
            rw [List.getD_append _ _ _ _ (by omega : i < xx.length)]
            exact inputFn n a ⟨i,h⟩
          simp only [f,dif_pos h,e]
          rw [(stableRun _ q.1).2,q.2]
        · have h' : i-n<m := by omega
          have e : raw.getD i false = b ⟨i-n,h'⟩ := by
            change (xx++yy).getD i false = _
            rw [List.getD_append_right _ _ _ _ (by omega : xx.length ≤ i),lx]
            exact inputFn m b ⟨i-n,h'⟩
          simpa only [f,dif_neg h,dif_pos h',e] using (negRight ⟨i-n,h'⟩).2
    have same : Rel (run C.gates raw) (run T.1 vr) T.2 := by
      have q := compile_rel C.gates raw vr f initial hC
      simpa only [lr,l2,T] using q
    have oldlen : (run C.gates raw).length = n+m+C.size := by
      rw [lenRun,lr]; rfl
    have newlen : (run T.1 vr).length = size := by
      rw [lenRun,l2,show T.1.length = 2*C.size from compile_len _ _ _ _]
    have q := hA u v
    change (run C.gates raw).getD C.output false = A u v at q
    change (run (EL.1++ER.1++T.1) raw).getD out false = A u v
    rw [run_append,run_append]
    change (run T.1 vr).getD out false = A u v
    by_cases h : C.output < n+m+C.size
    · have hp : WiresPos (n+m) f := fun i _ => ⟨i,rfl⟩
      obtain ⟨j,hj⟩ := compile_real C.gates (n+m) n0 f hp C.output h
      have qq := (same C.output (by rwa [oldlen])).2.2.1
      rw [hj] at qq
      change ((T.2 C.output).1) = .wire j at hj
      have hout : out = j := by
        dsimp only [out]
        rw [if_pos h,hj]
        rfl
      rw [hout]
      exact qq.trans q
    · rw [show out=size by simp [out,h],List.getD_eq_default _ _ (by rw [newlen])]
      rw [List.getD_eq_default _ _ (by rw [oldlen]; omega)] at q
      exact q

end Comp18925
end PEqualNP.Outside.L_meta_18925

theorem PEqualNP.Outside.L_meta_18925 :
∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C →
  PEqualNP.Represents.RepSizeAtMost A (2 * s + ((3 * n - 6) + (3 * m - 6)))
  := @PEqualNP.Outside.L_meta_18925.Comp18925.main
