import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25582

namespace PEqualNP.Outside.L_meta_25628
open PEqualNP.Outside.L_meta_25582_aux
open scoped BigOperators
open Finset



def picked (N : ℕ) (mate : ℕ→ℕ) (bad : ℕ→Bool) : List ℕ :=
  (List.range N).filter (fun w=>bad w && (decide (w < mate w) || !(bad (mate w))))

theorem mem_picked {N : ℕ} {mate : ℕ→ℕ} {bad : ℕ→Bool} {w : ℕ} :
    w∈picked N mate bad ↔ w<N ∧ bad w=true ∧ (w < mate w ∨ bad (mate w)=false) := by
  simp [picked,List.mem_filter,Bool.and_eq_true,Bool.or_eq_true]

theorem picked_or_mate {N : ℕ} {mate : ℕ→ℕ} {bad : ℕ→Bool} {w : ℕ}
    (wb : w<N) (mb : mate w<N) (inv : mate (mate w)=w) (ne : w≠mate w)
    (badPair : bad w=true ∨ bad (mate w)=true) :
    w∈picked N mate bad ∨ mate w∈picked N mate bad := by
  by_cases hw : bad w=true
  · by_cases hm : bad (mate w)=true
    · rcases lt_or_gt_of_ne ne with lt|lt
      · exact Or.inl (mem_picked.mpr ⟨wb,hw,Or.inl lt⟩)
      · exact Or.inr (mem_picked.mpr ⟨mb,hm,Or.inl (inv.symm ▸ lt)⟩)
    · exact Or.inl (mem_picked.mpr ⟨wb,hw,Or.inr (Bool.eq_false_of_ne_true hm)⟩)
  · exact Or.inr (mem_picked.mpr ⟨mb,badPair.resolve_left hw,
      Or.inr (inv.symm ▸ Bool.eq_false_of_ne_true hw)⟩)

theorem picked_never_both {N : ℕ} {mate : ℕ→ℕ} {bad : ℕ→Bool} {w : ℕ}
    (inv : mate (mate w)=w) (h : w∈picked N mate bad) : mate w∉picked N mate bad := by
  intro h'
  obtain ⟨_,bw,w⟩ := mem_picked.mp h
  obtain ⟨_,bm,m⟩ := mem_picked.mp h'
  rw [inv] at m
  rcases w with h|h <;> rcases m with i|i
  · omega
  · simp [bw] at i
  · simp [bm] at h
  · simp [bm] at h

theorem cleanExistsIff {N : ℕ} {mate : ℕ→ℕ} {bad : ℕ→Bool}
    (mb : ∀ w<N,mate w<N) (inv : ∀ w<N,mate (mate w)=w) (ne : ∀ w<N,w≠mate w)
    (bucket : ℕ→ℕ) (stable : ∀ w<N,bucket (mate w)=bucket w)
    (c B : ℕ) (total : ((List.range N).filter
      (fun w=>decide (w < mate w) && decide (bucket w=c))).length=B) :
    (∃ w<N,bucket w=c ∧ bad w=false ∧ bad (mate w)=false) ↔
      ((picked N mate bad).filter (fun w=>decide (bucket w=c))).length < B := by
  classical
  let P := ((picked N mate bad).toFinset).filter (fun w=>bucket w=c)
  let T := (Finset.range N).filter (fun w=>w < mate w ∧ bucket w=c)
  let f (w : ℕ) := min w (mate w)
  have pc (w : ℕ) : w∈P ↔ w∈picked N mate bad ∧ bucket w=c := by simp [P]
  have tc (w : ℕ) : w∈T ↔ w<N ∧ w < mate w ∧ bucket w=c := by simp [T]
  have eqP : P.card=((picked N mate bad).filter (fun w=>decide (bucket w=c))).length := by
    have no : (picked N mate bad).Nodup := (List.nodup_range).filter _
    have eq : P=((picked N mate bad).filter (fun w=>decide (bucket w=c))).toFinset := by
      ext w
      simp [pc,List.mem_filter]
    rw [eq,List.toFinset_card_of_nodup (no.filter _)]
  have eqT : T.card=B := by
    let L := (List.range N).filter (fun w=>decide (w < mate w) && decide (bucket w=c))
    have eq : T=L.toFinset := by ext w; simp [tc,L,List.mem_filter,Bool.and_eq_true]
    rw [eq,List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    exact total
  have fEq {w : ℕ} (wb : w<N) : f (mate w)=f w := by simp [f,inv w wb,min_comm]
  have ft : P.image f⊆T := by
    intro z zz
    obtain ⟨w,wp,rfl⟩ := Finset.mem_image.mp zz
    obtain ⟨wP,wc⟩ := (pc w).1 wp
    have wb := (mem_picked.mp wP).1
    rcases lt_or_gt_of_ne (ne w wb) with lt|lt
    · rw [show f w=w from min_eq_left lt.le]
      exact (tc w).2 ⟨wb,lt,wc⟩
    · rw [show f w=mate w from min_eq_right lt.le]
      exact (tc _).2 ⟨mb w wb,(by rw [inv w wb]; exact lt),(stable w wb).trans wc⟩
  have fi : Set.InjOn f ↑P := by
    intro a aa b bb ab
    have ap := ((pc a).1 aa).1
    have bp := ((pc b).1 bb).1
    have ai := (mem_picked.mp ap).1
    have bi := (mem_picked.mp bp).1
    have ors : f a=a ∨ f a=mate a := by
      by_cases c : a ≤ mate a
      · exact Or.inl (min_eq_left c)
      · exact Or.inr (min_eq_right (by omega))
    have brs : f b=b ∨ f b=mate b := by
      by_cases c : b ≤ mate b
      · exact Or.inl (min_eq_left c)
      · exact Or.inr (min_eq_right (by omega))
    rcases ors with p|p <;> rcases brs with q|q
    · exact p.symm.trans (ab.trans q)
    · exact (picked_never_both (inv b bi) bp ((p.symm.trans (ab.trans q)) ▸ ap)).elim
    · exact (picked_never_both (inv a ai) ap ((p.symm.trans (ab.trans q)).symm ▸ bp)).elim
    · have same := congrArg mate (p.symm.trans (ab.trans q))
      rwa [inv a ai,inv b bi] at same
  have ci : (P.image f).card=P.card := Finset.card_image_of_injOn fi
  constructor
  · rintro ⟨w,wb,wc,wa,wm⟩
    have zw : f w∈T := by
      rcases lt_or_gt_of_ne (ne w wb) with h|h
      · rw [show f w=w from min_eq_left h.le]
        exact (tc w).2 ⟨wb,h,wc⟩
      · rw [show f w=mate w from min_eq_right h.le]
        exact (tc _).2 ⟨mb w wb,(by rw [inv w wb]; exact h),(stable w wb).trans wc⟩
    have nope : f w∉P.image f := by
      intro yes
      obtain ⟨u,up,eq⟩ := Finset.mem_image.mp yes
      have up' := ((pc u).1 up).1
      have ub := (mem_picked.mp up').1
      have bt := (mem_picked.mp up').2.1
      have a : f u=u ∨ f u=mate u := by
        by_cases h : u ≤ mate u
        · exact Or.inl (min_eq_left h)
        · exact Or.inr (min_eq_right (by omega))
      have b : f w=w ∨ f w=mate w := by
        by_cases h : w ≤ mate w
        · exact Or.inl (min_eq_left h)
        · exact Or.inr (min_eq_right (by omega))
      rcases a with a|a <;> rcases b with b|b
      · have e := a.symm.trans (eq.trans b)
        simp [e,wa] at bt
      · have e := a.symm.trans (eq.trans b)
        simp [e,wm] at bt
      · have e := congrArg mate (a.symm.trans (eq.trans b))
        rw [inv u ub] at e
        simp [e,wm] at bt
      · have e := congrArg mate (a.symm.trans (eq.trans b))
        rw [inv u ub,inv w wb] at e
        simp [e,wa] at bt
    have strict : P.image f ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨ft,fun eq=>nope (eq.symm ▸ zw)⟩
    have count := Finset.card_lt_card strict
    rwa [ci,eqP,eqT] at count
  · intro less
    have sc : (P.image f).card<T.card := by rwa [ci,eqP,eqT]
    have proper : P.image f ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨ft,fun h=>by rw [h] at sc; omega⟩
    obtain ⟨w,wt,notw⟩ := Finset.exists_of_ssubset proper
    obtain ⟨wb,wl,wc⟩ := (tc w).mp wt
    have good : bad w=false ∧ bad (mate w)=false := by
      by_contra no
      have exception : bad w=true ∨ bad (mate w)=true := by
        by_contra nope
        push Not at nope
        exact no ⟨Bool.eq_false_of_ne_true nope.1,Bool.eq_false_of_ne_true nope.2⟩
      have pp := picked_or_mate wb (mb w wb) (inv w wb) (ne w wb) exception
      apply notw
      have fw : f w=w := min_eq_left wl.le
      rcases pp with l|r
      · exact Finset.mem_image.mpr ⟨w,(pc w).2 ⟨l,wc⟩,fw⟩
      · exact Finset.mem_image.mpr ⟨mate w,(pc _).2 ⟨r,(stable w wb).trans wc⟩,(fEq wb).trans fw⟩
    exact ⟨w,wb,wc,good.1,good.2⟩



theorem sameHalfToggle (x y : ℕ) (h : x/2=y/2) : y=x ∨ y=x^^^1 := by
  by_cases ye : y=x
  · exact Or.inl ye
  · right
    by_cases e : x%2=0
    · rw [Nat.xor_one_of_even (Nat.even_iff.mpr e)]
      omega
    · have odd : Odd x := Nat.odd_iff.mpr (by omega)
      rw [Nat.xor_one_of_odd odd]
      omega

theorem edgesExact {N : ℕ} {mate : ℕ→ℕ} {bad : ℕ→Bool}
    (mb : ∀ w<N,mate w<N) (inv : ∀ w<N,mate (mate w)=w) (ne : ∀ w<N,w≠mate w)
    (physical clipped : ℕ→ℕ) (agreement : ∀ w<N,bad w=false → physical w=clipped w)
    (toggle : ∀ w<N,clipped (mate w)=clipped w^^^1)
    (y z fiber : ℕ)
    (total : ((List.range N).filter (fun w=>decide (w < mate w) &&
      decide (clipped w/2=y/2))).length=fiber) :
    (∃ w<N,physical w=y ∧ physical (mate w)=z) ↔
      (∃ p∈picked N mate bad,(physical p=y ∧ physical (mate p)=z) ∨
        (physical p=z ∧ physical (mate p)=y)) ∨
      (z=y^^^1 ∧ ((picked N mate bad).filter (fun w=>decide (clipped w/2=y/2))).length<fiber) := by
  classical
  let bucket (w : ℕ) := clipped w/2
  have stable (w : ℕ) (wb : w<N) : bucket (mate w)=bucket w := by
    simp [bucket,toggle w wb,Nat.xor_div_two]
  have pair := cleanExistsIff (bad:=bad) mb inv ne bucket stable (y/2) fiber total
  constructor
  · rintro ⟨w,wb,wy,mz⟩
    by_cases exception : bad w=true ∨ bad (mate w)=true
    · left
      rcases picked_or_mate wb (mb w wb) (inv w wb) (ne w wb) exception with l|r
      · exact ⟨w,l,Or.inl ⟨wy,mz⟩⟩
      · exact ⟨mate w,r,Or.inr ⟨mz,by rwa [inv w wb]⟩⟩
    · push Not at exception
      have ag := agreement w wb (Bool.eq_false_of_ne_true exception.1)
      have ag' := agreement (mate w) (mb w wb) (Bool.eq_false_of_ne_true exception.2)
      right
      refine ⟨?_,pair.mp ⟨w,wb,(congrArg (·/2) (ag.symm.trans wy)),
        Bool.eq_false_of_ne_true exception.1,Bool.eq_false_of_ne_true exception.2⟩⟩
      rw [←mz,ag',toggle w wb,←ag,wy]
  · rintro (⟨p,pp,coords⟩|⟨zt,less⟩)
    · have pb := (mem_picked.mp pp).1
      rcases coords with h|h
      · exact ⟨p,pb,h⟩
      · exact ⟨mate p,mb p pb,h.2,by rw [inv p pb]; exact h.1⟩
    · obtain ⟨w,wb,half,g1,g2⟩ := pair.mpr less
      rcases sameHalfToggle _ _ half with x|x
      · exact ⟨w,wb,(agreement w wb g1).trans x.symm,by
          rw [agreement (mate w) (mb w wb) g2,toggle w wb,zt,x]⟩
      · refine ⟨mate w,mb w wb,?_,?_⟩
        · rw [agreement (mate w) (mb w wb) g2,toggle w wb,←x]
        · rw [inv w wb,agreement w wb g1,zt,x,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem coloringFromEdges {N q : ℕ} (q0 : 0<q)
    (mate out : ℕ→ℕ) (sel : List ℕ) (bound : ∀ w<N,out w<2^q)
    (mateBound : ∀ w<N,mate w<N) (selBound : ∀ p∈sel,p<N)
    (edges : ∀ y z : Fin (2^q),
      (∃ w<N,out w=y.val ∧ out (mate w)=z.val) ↔
      (∃ p∈sel,(out p=y.val ∧ out (mate p)=z.val) ∨
        (out p=z.val ∧ out (mate p)=y.val)) ∨ z.val=y.val^^^1)
    (f : ℕ→Bool) :
    (∀ w<N,f (out w)≠f (out (mate w))) ↔
      (∀ p : Fin (2^(q-1)),f (2*p.val)≠f (2*p.val+1)) ∧
      ∀ p∈sel,f (out p)≠f (out (mate p)) := by
  have power : 2^q=2*2^(q-1) := by
    have e : q=q-1+1 := by omega
    nth_rewrite 1 [e]
    rw [Nat.pow_succ,Nat.mul_comm]
  constructor
  · intro all
    refine ⟨?_,fun p h=>all p (selBound p h)⟩
    intro p
    have pl := p.isLt
    let y : Fin (2^q) := ⟨2*p.val,by rw [power]; omega⟩
    let z : Fin (2^q) := ⟨2*p.val+1,by rw [power]; omega⟩
    have zx : z.val=y.val^^^1 := by
      change 2*p.val+1=(2*p.val)^^^1
      rw [Nat.xor_one_of_even ⟨p.val,by omega⟩]
    obtain ⟨w,wb,wy,wz⟩ := (edges y z).2 (Or.inr zx)
    have h := all w wb
    rw [wy,wz] at h
    exact h
  · rintro ⟨matching,explicit⟩ w wb
    let y : Fin (2^q) := ⟨out w,bound w wb⟩
    let z : Fin (2^q) := ⟨out (mate w),bound (mate w) (mateBound w wb)⟩
    have e := (edges y z).1 ⟨w,wb,rfl,rfl⟩
    change f y.val≠f z.val
    rcases e with ⟨p,pp,h|h⟩|e
    · have a := explicit p pp
      rwa [h.1,h.2] at a
    · have a := explicit p pp
      rw [h.1,h.2] at a
      exact Ne.symm a
    · have yl := y.isLt
      have yl' : y.val<2*2^(q-1) := yl.trans_eq power
      have pl : y.val/2<2^(q-1) := by omega
      have h := matching ⟨y.val/2,pl⟩
      by_cases even : y.val%2=0
      · have yy : y.val=2*(y.val/2) := by omega
        rw [Nat.xor_one_of_even (Nat.even_iff.mpr even),yy] at e
        rwa [yy,e]
      · have yy : y.val=2*(y.val/2)+1 := by omega
        rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))] at e
        have zz : z.val=2*(y.val/2) := by omega
        rw [yy,zz]
        exact Ne.symm h



theorem listRangeCount (N : ℕ) (p : ℕ→Bool) :
    ((List.range N).filter p).length =
    ((Finset.univ : Finset (Fin N)).filter (fun i=>p i.val=true)).card := by
  classical
  rw [←List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  symm
  apply Finset.card_bij (fun i _=>i.val)
  · intro i ii
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ii
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr i.isLt,ii⟩)
  · intro i hi j hj e
    exact Fin.ext e
  · intro j jj
    have h : j<N ∧ p j=true := by simpa using jj
    exact ⟨⟨j,h.1⟩,by simp [h.2],rfl⟩

theorem canonicalHalfFiber {N : ℕ} {mate : ℕ→ℕ}
    (mb : ∀ w<N,mate w<N) (inv : ∀ w<N,mate (mate w)=w) (ne : ∀ w<N,w≠mate w)
    (clip : ℕ→ℕ) (toggle : ∀ w<N,clip (mate w)=clip w^^^1)
    (c : ℕ) :
    ((List.range N).filter (fun w=>decide (w < mate w) && decide (clip w/2=c))).length =
      ((List.range N).filter (fun w=>decide (clip w=2*c))).length := by
  classical
  let L := (List.range N).filter (fun w=>decide (w < mate w) && decide (clip w/2=c))
  let E := (List.range N).filter (fun w=>decide (clip w=2*c))
  have ll (w) : w∈L.toFinset ↔ w<N ∧ w < mate w ∧ clip w/2=c := by
    simp [L,Bool.and_eq_true,and_assoc]
  have ee (w) : w∈E.toFinset ↔ w<N ∧ clip w=2*c := by simp [E]
  let f (w : ℕ) := if clip w=2*c then w else mate w
  let g (w : ℕ) := min w (mate w)
  have y : (2*c)/2=c := by omega
  have x1 : (2*c)^^^1=2*c+1 := Nat.xor_one_of_even ⟨c,by omega⟩
  have notx : (2*c)^^^1≠2*c := by rw [x1]; omega
  have fm (w) (ww : w∈L.toFinset) : f w∈E.toFinset := by
    obtain ⟨wb,_,half⟩ := (ll w).1 ww
    by_cases h : clip w=2*c
    · simpa [f,h] using (ee w).2 ⟨wb,h⟩
    · have q := (sameHalfToggle (clip w) (2*c) (half.trans y.symm)).resolve_left (Ne.symm h)
      have h' := (toggle w wb).trans q.symm
      simpa [f,h] using (ee (mate w)).2 ⟨mb w wb,h'⟩
  have gm (w) (ww : w∈E.toFinset) : g w∈L.toFinset := by
    obtain ⟨wb,clipw⟩ := (ee w).1 ww
    rcases lt_or_gt_of_ne (ne w wb) with h|h
    · have e : g w=w := min_eq_left h.le
      rw [e]
      exact (ll w).2 ⟨wb,h,by rw [clipw,y]⟩
    · have e : g w=mate w := min_eq_right h.le
      rw [e]
      exact (ll _).2 ⟨mb w wb,by rw [inv w wb]; exact h,by rw [toggle w wb,clipw,x1]; omega⟩
  have left (w) (ww : w∈L.toFinset) : g (f w)=w := by
    obtain ⟨wb,lt,_⟩ := (ll w).1 ww
    by_cases h : clip w=2*c
    · simp [f,h,g,min_eq_left lt.le]
    · simp [f,h,g,inv w wb,min_eq_right lt.le]
  have right (w) (ww : w∈E.toFinset) : f (g w)=w := by
    obtain ⟨wb,clipw⟩ := (ee w).1 ww
    rcases lt_or_gt_of_ne (ne w wb) with h|h
    · simp [g,min_eq_left h.le,f,clipw]
    · have nz : clip (mate w)≠2*c := by rw [toggle w wb,clipw]; exact notx
      simp [g,min_eq_right h.le,f,nz,inv w wb]
  change L.length=E.length
  rw [←List.toFinset_card_of_nodup (List.nodup_range.filter _ : L.Nodup),
    ←List.toFinset_card_of_nodup (List.nodup_range.filter _ : E.Nodup)]
  exact Finset.card_bij' (fun w _=>f w) (fun w _=>g w) fm gm left right



def pack (k u w : ℕ) : ℕ := rotF k 1 w ^^^ u

def pubRow (k u : ℕ) (cs : ℕ→ℕ) (t : ℕ) (z : ℤ) : Bool :=
  xor (pz k u (z+3-2*(t:ℤ))) (pz k (cs t) z)

def clip (k w : ℕ) (cut : ℤ) (z : ℤ) : Bool :=
  if z<cut then pz k w z else false

theorem pz_st_eq_stZ {k u w : ℕ} {cs : ℕ→ℕ}
    (hk : 0<k) (hu : u<2^k) (hw : w<2^k) (hc : ∀ t,cs t<2^k) :
    ∀ t z,pz k (st k u cs w t) z = stZ (pubRow k u cs) (pz k (pack k u w)) t z := by
  intro t
  induction t with
  | zero => intro z; rfl
  | succ t ih =>
    intro z
    have pre : pz k (preF k (st k u cs w t)) z =
        befZ (stZ (pubRow k u cs) (pz k (pack k u w)) t) z := by
      rw [pz_preF hk (st_lt hu hc w t),befZ_eq]
      simp only [ih]
    let p : ℤ := z+1-2*(t:ℤ)
    let raw := pz k w (z-((2*t:ℕ):ℤ))
    let row := pz k u p
    let con := pz k (cs (t+1)) z
    have inj : pz k (pack k u w) p=xor raw row := by
      unfold pack
      rw [pz_xor,pz_rot1 hk w hw]
      have e : p + -1 = z-((2*t:ℕ):ℤ) := by dsimp [p]; push_cast; ring
      rw [e]
    have pubEq : pubRow k u cs (t+1) z=xor row con := by
      unfold pubRow
      have e : z+3-2*((t+1:ℕ):ℤ)=p := by dsimp [p]; push_cast; ring
      rw [e]
    rw [pz_st_succ hk hw,stZ_succ,pre,pubEq]
    change xor (befZ _ z) (xor raw con)=xor (xor (befZ _ z) (pz k (pack k u w) p)) (xor row con)
    rw [inj]
    generalize befZ (stZ (pubRow k u cs) (pz k (pack k u w)) t) z = a
    cases a <;> cases raw <;> cases row <;> cases con <;> rfl

theorem clipStateAgreement {k n r w : ℕ} (pub : ℕ→ℤ→Bool) (cut : ℤ)
    (cb : ℕ→Bool) (tr : ∀ j<n,grd k pub cut (cntC cb) j w=cb j)
    (nr : n+4≤r) (z : ℤ) (hz : z+3*(r:ℤ)<cut+(cntC cb n:ℤ))
    (inj : z+3-2*(r:ℤ)<cut) :
    stZ pub (pz k w) r z = stZ pub (clip k w cut) r z := by
  have hr : r-1+1=r := by omega
  have frontier := front_val cut n cb r
  rw [show min n (r-4)=n by omega] at frontier
  have pre := (front82 k n pub cut cb w tr (clip k w cut)
    (fun z hz=>by simp [clip,hz]) (r-1)).2
  rw [hr] at pre
  have pb := pre z (by rw [frontier]; omega)
  have s : (r-1:ℕ)+1=r := by omega
  nth_rw 1 [←s]
  nth_rw 2 [←s]
  rw [stZ_succ,stZ_succ]
  rw [pb]
  have zr : z+1-2*((r-1:ℕ):ℤ)<cut := by
    have q : (((r-1:ℕ):ℤ))=(r:ℤ)-1 := by omega
    rw [q]; omega
  simp [clip,zr]

theorem clip_flip_agrees {k w : ℕ} (hk : 0<k) (cut p z : ℤ)
    (zp : p<z) (pc : cut≤p+k) :
    clip k (flipK k p w) cut z=clip k w cut z := by
  by_cases h : z<cut
  · simp only [clip,if_pos h]
    apply pz_flipK_off hk
    · omega
    · omega
  · simp [clip,h]

theorem clipFlipTri {k r w : ℕ} (hk : 0<k) (hr : 4≤r)
    (pub : ℕ→ℤ→Bool) (cut z p : ℤ)
    (eq : p=z+loZ r) (low : p<cut) (hi : cut≤p+k) :
    stZ pub (clip k (flipK k p w) cut) r z =
      !(stZ pub (clip k w cut) r z) := by
  obtain ⟨s,rfl⟩ : ∃ s,r=s+1 := ⟨r-1,by omega⟩
  have lead := zlead pub (clip k (flipK k p w) cut) (clip k w cut) s (by omega) z
    (fun x l _=>clip_flip_agrees hk cut p x (by omega) hi)
  rw [←eq] at lead
  simp only [clip,if_pos low,pz_flipK_on hk] at lead
  cases a : stZ pub (clip k (flipK k p w) cut) (s+1) z <;>
    cases b : stZ pub (clip k w cut) (s+1) z <;>
    cases c : pz k w p <;> simp_all

theorem clipFlipHigher {k r w : ℕ} (hk : 0<k)
    (pub : ℕ→ℤ→Bool) (cut z p : ℤ)
    (up : p<z+loZ r) (hi : cut≤p+k) :
    stZ pub (clip k (flipK k p w) cut) r z =
      stZ pub (clip k w cut) r z := by
  apply zdep
  intro x xl _
  exact clip_flip_agrees hk cut p x (by omega) hi



theorem extPz {k a b : ℕ} (aK : a<2^k) (bK : b<2^k)
    (eq : ∀ z,pz k a z=pz k b z) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases jl : j<k
  · simpa [pz_lt _ _ _ jl] using eq (j:ℤ)
  · rw [big_false aK (by omega),big_false bK (by omega)]

def unpack (k u w : ℕ) : ℕ := rotF k (k-1) (w^^^u)

theorem pack_lt {k u : ℕ} (hu : u<2^k) (w : ℕ) : pack k u w<2^k :=
  Nat.xor_lt_two_pow (rotF_lt _ _ _) hu

theorem pack_unpack {k u : ℕ} (hk : 0<k) (hu : u<2^k) {w : ℕ} (hw : w<2^k) :
    pack k u (unpack k u w)=w := by
  apply extPz (pack_lt hu _) hw
  intro z
  unfold pack unpack
  rw [pz_xor,pz_rot1 hk _ (rotF_lt _ _ _),pz_rotkm1 hk _ (Nat.xor_lt_two_pow hw hu)]
  rw [show z + -1 + 1 = z by ring,pz_xor]
  cases pz k w z <;> cases pz k u z <;> rfl

theorem unpack_pack {k u : ℕ} (hk : 0<k) (hu : u<2^k) {w : ℕ} (hw : w<2^k) :
    unpack k u (pack k u w)=w := by
  apply extPz (rotF_lt _ _ _) hw
  intro z
  simp only [pack,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  rw [pz_rotkm1 hk _ (rotF_lt _ _ _),pz_rot1 hk w hw]
  rw [show z+1+ -1=z by ring]

def packEquiv {k u : ℕ} (hk : 0<k) (hu : u<2^k) : Fin (2^k) ≃ Fin (2^k) where
  toFun w := ⟨pack k u w.val,pack_lt hu _⟩
  invFun w := ⟨unpack k u w.val,rotF_lt _ _ _⟩
  left_inv w := Fin.ext (unpack_pack hk hu w.isLt)
  right_inv w := Fin.ext (pack_unpack hk hu w.isLt)

theorem pack_flip {k u : ℕ} (hk : 0<k) (hu : u<2^k) {w : ℕ} (hw : w<2^k) (p : ℤ) :
    pack k u (flipK k (p-1) w)=flipK k p (pack k u w) := by
  apply extPz (pack_lt hu _) (flipK_lt hk _ (pack_lt hu _))
  intro z
  unfold pack
  rw [pz_xor,pz_rot1 hk _ (flipK_lt hk _ hw),pz_flipK hk,pz_flipK hk,pz_xor,pz_rot1 hk w hw]
  rw [show z+ -1-(p-1)=z-p by ring]
  cases pz k w (z+ -1) <;> cases pz k 1 (z-p) <;> cases pz k u z <;> rfl

def bitWord (q : ℕ) (g : ℕ→Bool) : ℕ :=
  (List.range q).foldl (fun acc i=>acc ||| ((g i).toNat <<< i)) 0

theorem bitWord_lt (q : ℕ) (g : ℕ→Bool) : bitWord q g<2^q := by
  apply (lt_pow_iff_bits _ _).2
  intro i il
  unfold bitWord
  rw [testBit_foldl_or]
  simp [show ¬ i<q by omega]

theorem bitWord_eq {q y : ℕ} {g : ℕ→Bool} (hy : y<2^q)
    (h : ∀ j<q,g j=y.testBit j) : bitWord q g=y := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold bitWord
  rw [testBit_foldl_or]
  by_cases il : i<q
  · simp [il,h i il]
  · rw [big_false hy (by omega)]
    simp [il]

def clippedWord (k r q : ℕ) (pub : ℕ→ℤ→Bool) (i cut : ℤ) (w : ℕ) : ℕ :=
  bitWord q (fun j=>stZ pub (clip k w cut) r (i+(j:ℤ)))

theorem clipTriCount (k r q : ℕ) (k0 : 0<k) (r4 : 4≤r) (qk : q≤k)
    (pub : ℕ→ℤ→Bool) (i : ℤ) (y : Fin (2^q)) :
    let cut := i+loZ r+k
    ((Finset.univ : Finset (Fin (2^k))).filter
      (fun w=>clippedWord k r q pub i cut w.val=y.val)).card=2^(k-q) := by
  classical
  intro cut
  let C (j : ℕ) (w : Fin (2^k)) := stZ pub (clip k w.val cut) r (i+((q-1-j:ℕ):ℤ))
  let σ (j : ℕ) := y.val.testBit (q-1-j)
  let p (j : ℕ) : ℤ := i+((q-1-j:ℕ):ℤ)+loZ r
  let F (j : ℕ) (w : Fin (2^k)) : Fin (2^k) := ⟨flipK k (p j) w.val,flipK_lt k0 _ w.isLt⟩
  have invol (j : ℕ) (_ : j<q) (w : Fin (2^k)) : F j (F j w)=w := Fin.ext (flipK_flipK _ _ _)
  have keep (j : ℕ) (jq : j<q) (h : ℕ) (hj : h<j) (w : Fin (2^k)) : C h (F j w)=C h w := by
    apply clipFlipHigher k0
    · dsimp [p]
      have : q-1-j<q-1-h := by omega
      omega
    · dsimp [cut,p]
      omega
  have flip (j : ℕ) (jq : j<q) (w : Fin (2^k)) : C j (F j w)= !C j w := by
    apply clipFlipTri k0 r4
    · rfl
    · dsimp [cut,p]
      have : q-1-j<k := by omega
      omega
    · dsimp [cut,p]
      omega
  have hh := halving q C σ F invol keep flip q le_rfl
  simp only [Fintype.card_fin] at hh
  have eq : ((Finset.univ : Finset (Fin (2^k))).filter (fun w=>∀ j<q,C j w=σ j)) =
      (Finset.univ.filter (fun w : Fin (2^k)=>clippedWord k r q pub i cut w.val=y.val)) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro all
      apply bitWord_eq y.isLt
      intro j jl
      have h := all (q-1-j) (by omega)
      have e : q-1-(q-1-j)=j := by omega
      simpa [C,σ,e] using h
    · intro he j jl
      have H := congrArg (fun a : ℕ=>a.testBit (q-1-j)) he
      unfold clippedWord bitWord at H
      rw [testBit_foldl_or] at H
      simpa [C,σ,show q-1-j<q by omega] using H
  rw [eq] at hh
  have power : 2^k=2^(k-q)*2^q := by rw [←Nat.pow_add]; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0<2^q) (hh.trans power)

theorem clipMateWord (k r q w : ℕ) (k0 : 0<k) (r4 : 4≤r) (q0 : 0<q)
    (pub : ℕ→ℤ→Bool) (i : ℤ) :
    let cut := i+loZ r+k
    clippedWord k r q pub i cut (flipK k (i+loZ r) w)=clippedWord k r q pub i cut w^^^1 := by
  intro cut
  apply Nat.eq_of_testBit_eq
  intro j
  unfold clippedWord bitWord
  rw [Nat.testBit_xor,testBit_foldl_or,testBit_foldl_or,Nat.testBit_two_pow (n:=0) (m:=j)]
  by_cases j0 : j=0
  · subst j
    simp only [q0,decide_true,Bool.true_and,Nat.cast_zero,add_zero]
    have flip := clipFlipTri (w:=w) k0 r4 pub cut i (i+loZ r) rfl (by dsimp [cut]; omega) (by rfl)
    rw [flip]
    cases stZ pub (clip k w cut) r i <;> rfl
  · have he := clipFlipHigher (w:=w) (r:=r) k0 pub cut (i+(j:ℤ)) (i+loZ r) (by omega) (by rfl)
    rw [he]
    simp [Ne.symm j0]



def walk (g : ℕ→ℕ→Bool) (j : ℕ) : ℕ :=
  (List.range j).foldl (fun x i=>x+(g i x).toNat) 0

def traceBit (g : ℕ→ℕ→Bool) (j : ℕ) : Bool := g j (walk g j)

theorem walk_eq_cnt (g : ℕ→ℕ→Bool) : ∀ j,walk g j=cntC (traceBit g) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have step : walk g (j+1)=walk g j+(traceBit g j).toNat := by
      unfold walk traceBit
      rw [fold_succ]
      rfl
    rw [step,cntC,ih]
    cases traceBit g j <;> rfl

def subsetBits {n : ℕ} (S : Finset (Fin n)) (j : ℕ) : Bool :=
  if h : j<n then decide (⟨j,h⟩∈S) else false

theorem count_subsetBits {n : ℕ} (S : Finset (Fin n)) :
    cntC (subsetBits S) n=S.card := by
  classical
  let L := (List.range n).filter (subsetBits S)
  have nodup : L.Nodup := List.nodup_range.filter _
  have eq : L.toFinset=S.image Fin.val := by
    ext j
    simp only [List.mem_toFinset,L,List.mem_filter,List.mem_range,Finset.mem_image]
    by_cases t : j<n
    · simp only [t,true_and]
      rw [subsetBits,dif_pos t,decide_eq_true_eq]
      constructor
      · intro s
        exact ⟨⟨j,t⟩,s,rfl⟩
      · rintro ⟨i,ii,e⟩
        exact (show i=(⟨j,t⟩:Fin n) from Fin.ext e) ▸ ii
    · simp only [t,false_and]
      constructor
      · exact False.elim
      · rintro ⟨i,_,rfl⟩
        exact t i.isLt
  have c := List.toFinset_card_of_nodup nodup
  rw [eq,Finset.card_image_of_injective _ Fin.val_injective] at c
  rw [←cntC_list]
  exact c.symm

theorem cnt_eq_of_prefix {n : ℕ} {a b : ℕ→Bool}
    (h : ∀ j<n,a j=b j) : cntC a n=cntC b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntC,cntC,ih (fun j hj=>h j (by omega)),h n (by omega)]

theorem traceFiberCount (k n : ℕ) (hk : 5*n+15≤k) (pub : ℕ→ℤ→Bool)
    (cut : ℤ) (cb : ℕ→Bool) :
    ((Finset.univ : Finset (Fin (2^k))).filter
      (fun w=>∀ j<n,grd k pub cut (cntC cb) j w.val=cb j)).card=2^(k-n) := by
  classical
  have k0 : 0<k := by omega
  let F (j : ℕ) (x : Fin (2^k)) : Fin (2^k) :=
    ⟨flipK k (ldZ cut (cntC cb) j) x.val,flipK_lt k0 _ x.isLt⟩
  let C (j : ℕ) (x : Fin (2^k)) := grd k pub cut (cntC cb) j x.val
  have i (j : ℕ) (jlt : j<n) (w : Fin (2^k)) : F j (F j w)=w :=
    Fin.ext (flipK_flipK _ _ _)
  have keep (j : ℕ) (jlt : j<n) (u : ℕ) (uLt : u<j) (x : Fin (2^k)) :
      C u (F j x)=C u x := grd_keep k0 pub cut (cntC cb) (cntC_mono cb) uLt (by omega) _
  have flip (j : ℕ) (jlt : j<n) (x : Fin (2^k)) : C j (F j x)= !C j x :=
    grd_toggle k0 pub cut (cntC cb) (by omega) _
  have h := halving n C cb F i keep flip n le_rfl
  simp only [Fintype.card_fin] at h
  have pow : 2^k=2^(k-n)*2^n := by rw [←Nat.pow_add]; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (h.trans pow)

def clippedGuard (k : ℕ) (pub : ℕ→ℤ→Bool) (cut : ℤ) (w j u : ℕ) : Bool :=
  grd k pub cut (fun _=>u) j w

set_option maxHeartbeats 10000000 in
theorem adaptiveTraceLowCount (k n B : ℕ) (hk : 5*n+15≤k) (pub : ℕ→ℤ→Bool) (cut : ℤ) :
    ((Finset.univ : Finset (Fin (2^k))).filter
      (fun w=>walk (clippedGuard k pub cut w.val) n<B)).card ≤
      2^(k-n)*(∑ m∈Finset.range B,Nat.choose n m) := by
  classical
  let U := (Finset.univ : Finset (Fin n))
  let Codes := (Finset.range B).biUnion (fun m=>U.powersetCard m)
  let F (S : Finset (Fin n)) := (Finset.univ : Finset (Fin (2^k))).filter
    (fun w=>∀ j<n,grd k pub cut (cntC (subsetBits S)) j w.val=subsetBits S j)
  let L := (Finset.univ : Finset (Fin (2^k))).filter
    (fun w=>walk (clippedGuard k pub cut w.val) n<B)
  have cv : L⊆Codes.biUnion F := by
    intro w ww
    let G := clippedGuard k pub cut w.val
    let S := U.filter (fun i : Fin n=>traceBit G i.val=true)
    have p (j : ℕ) (jl : j<n) : traceBit G j=subsetBits S j := by
      simp [subsetBits,jl,S,U]
    have cnt := cnt_eq_of_prefix p
    have sz : S.card<B := by
      rw [←count_subsetBits,←cnt,←walk_eq_cnt]
      exact (Finset.mem_filter.mp ww).2
    have sc : S∈Codes :=
      Finset.mem_biUnion.mpr ⟨S.card,Finset.mem_range.mpr sz,
        Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _,rfl⟩⟩
    refine Finset.mem_biUnion.mpr ⟨S,sc,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    intro j jl
    have d := cnt_eq_of_prefix (n:=j) (fun i il=>p i (by omega : i<n))
    have d' := walk_eq_cnt G j
    have px := p j jl
    unfold traceBit at px
    rw [d',d] at px
    exact px
  have count := (Finset.card_le_card cv).trans (Finset.card_biUnion_le (s:=Codes) (t:=F))
  have fcard (S : Finset (Fin n)) : (F S).card=2^(k-n) := traceFiberCount k n hk pub cut (subsetBits S)
  have bound : Codes.card≤∑ m∈Finset.range B,Nat.choose n m := by
    calc
      Codes.card ≤ ∑ m∈Finset.range B,(U.powersetCard m).card := Finset.card_biUnion_le
      _ = _ := by simp [Finset.card_powersetCard,U]
  have c : (∑ S∈Codes,(F S).card)=Codes.card*2^(k-n) := by simp [fcard]
  change L.card≤_
  rw [c] at count
  exact count.trans ((Nat.mul_le_mul_right _ bound).trans_eq (Nat.mul_comm _ _))



theorem rotOneMask (k s : ℕ) (hk : 0<k) :
    rotF k s 1 = 1 <<< (s%k) := by
  have ss : s%k<k := Nat.mod_lt _ hk
  have e : 1 >>> (k-s%k)=0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
    exact Nat.one_lt_two_pow (by omega)
  unfold rotF
  rw [e,Nat.or_zero,Nat.mod_eq_of_lt]
  rw [Nat.shiftLeft_eq,Nat.one_mul]
  exact Nat.pow_lt_pow_right (by decide) ss

theorem rawMateNat (k r i w : ℕ) (hk : 0<k) (hs : 2*r ≤ i+k+2) :
    w^^^(1<<<((i+k+2-2*r)%k))=flipK k ((i:ℤ)+2-2*(r:ℤ)) w := by
  let z := (i:ℤ)+2-2*(r:ℤ)
  have pp : ((i+k+2-2*r:ℕ):ℤ)=z+k := by rw [Nat.cast_sub hs]; push_cast; dsimp [z]; ring
  have modp : (i+k+2-2*r)%k=(z%(k:ℤ)).toNat := by
    calc
      (i+k+2-2*r)%k = ((((i+k+2-2*r)%k:ℕ):ℤ)).toNat := (Int.toNat_natCast _).symm
      _ = (((i+k+2-2*r:ℕ):ℤ)%(k:ℤ)).toNat := congrArg Int.toNat (Int.natCast_emod _ _)
      _ = (z%(k:ℤ)).toNat := by rw [pp,Int.add_emod_right]
  unfold flipK
  change w^^^(1<<<((i+k+2-2*r)%k))=w^^^rotF k ((z%(k:ℤ)).toNat) 1
  rw [rotOneMask _ _ hk,modp,Nat.mod_eq_of_lt (toNat_lt hk _)]

theorem wordPhysicalAgrees {k n r q w u : ℕ} (cs : ℕ→ℕ) (hh : ∀ t,cs t<2^k)
    (hk : 0<k) (hu : u<2^k) (hw : w<2^k) (hn : n+4≤r)
    (i : ℕ) (cut : ℤ) (cb : ℕ→Bool)
    (htr : ∀ j<n,grd k (pubRow k u cs) cut (cntC cb) j (pack k u w)=cb j)
    (front : (i:ℤ)+(q:ℤ)+3*(r:ℤ)≤cut+(cntC cb n:ℤ))
    (below : (i:ℤ)+(q:ℤ)+3-2*(r:ℤ)≤cut) :
    bitWord q (fun j=>(st k u cs w r).testBit ((i+j)%k))=
      clippedWord k r q (pubRow k u cs) (i:ℤ) cut (pack k u w) := by
  apply Nat.eq_of_testBit_eq
  intro j
  unfold clippedWord bitWord
  rw [testBit_foldl_or,testBit_foldl_or]
  by_cases jq : j<q
  · simp only [jq,decide_true,Bool.true_and]
    have p := pz_st_eq_stZ hk hu hw hh r ((i+j:ℕ):ℤ)
    rw [pz_nat] at p
    push_cast at p
    rw [p]
    exact clipStateAgreement (pubRow k u cs) cut cb htr hn ((i:ℤ)+(j:ℤ))
      (by omega) (by omega)
  · simp [jq]

theorem stZ_expandedFold (k u : ℕ) (cs : ℕ→ℕ) (start : ℤ→Bool) (r : ℕ) :
    (List.range r).foldl (fun (prev : ℤ→Bool) (t : ℕ) (z : ℤ) =>
      let p := z+1-2*(t:ℤ)
      xor (xor (xor (befZ prev z) (start p)) (pz k u p)) (pz k (cs (t+1)) z)) start =
      stZ (pubRow k u cs) start r := by
  unfold stZ
  congr 1
  funext prev t z
  simp only [pubRow]
  have p : z+3-2*((t+1:ℕ):ℤ)=z+1-2*(t:ℤ) := by push_cast; ring
  rw [p,Bool.xor_assoc]

theorem rawGuardPosition {k u w n cut : ℕ} (cs : ℕ→ℕ) (hh : ∀ t,cs t<2^k)
    (hk : 0<k) (hu : u<2^k) (hw : w<2^k)
    (bnd : 3*(n+4)≤cut+k) (j : ℕ) (jl : j<n) (ones : ℕ) :
    let now := 5+j
    let pos := cut+k-3*now+ones
    let layer := st k u cs w (now-1)
    xor (xor (layer.testBit (pos%k)) (layer.testBit ((pos+1)%k))) (layer.testBit ((pos+2)%k)) =
      clippedGuard k (pubRow k u cs) (cut:ℤ) (pack k u w) j ones := by
  intro now pos layer
  have ps : ((pos:ℕ):ℤ)=plZ (cut:ℤ) (fun _=>ones) j+(k:ℤ) := by
    dsimp [pos,now,plZ]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have tEq : now-1=4+j := by dsimp [now]; omega
  have gg (c : ℕ) : layer.testBit ((pos+c)%k)=
      stZ (pubRow k u cs) (pz k (pack k u w)) (4+j) (plZ (cut:ℤ) (fun _=>ones) j+(c:ℤ)) := by
    have pos' : ((pos+c:ℕ):ℤ) = plZ (cut:ℤ) (fun _=>ones) j+(c:ℤ)+(k:ℤ) := by push_cast; rw [ps]; ring
    have st := pz_st_eq_stZ hk hu hw hh (4+j) (plZ (cut:ℤ) (fun _=>ones) j+(c:ℤ))
    rw [←pz_add_k,←pos',pz_nat] at st
    simpa only [layer,tEq] using st
  unfold clippedGuard grd
  have z := gg 0
  simp only [Nat.add_zero,Nat.cast_zero,add_zero] at z
  rw [z,gg 1,gg 2]
  simp

theorem foldl_prefix_eq {α β : Type} (f g : α→β→α) :
    ∀ (L : List β), (∀ x i,i∈L → f x i=g x i) → ∀ x,L.foldl f x=L.foldl g x := by
  intro L
  induction L with
  | nil => intros; rfl
  | cons a L ih =>
    intro h x
    simp only [List.foldl_cons]
    rw [h _ _ (by simp)]
    exact ih (fun x i il=>h x i (by simp [il])) _

end PEqualNP.Outside.L_meta_25628

open PEqualNP.Outside.L_meta_25582_aux PEqualNP.Outside.L_meta_25628 in

set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_25628 :
∀ (k r e q n : Nat) (i : Fin k) (constants : Nat → Fin (2^k)),
  0 < q → k + e + 3 = 5*r → n+4 ≤ r → 5*n+15 ≤ k → e+q ≤ n →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2^k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell+1) % k)) && word.testBit ((cell+2) % k))).toNat <<< cell)) 0
  let state := fun (row raw rounds : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k-1) prev) ^^^ rot (2*tick) raw ^^^
        (constants (tick+1)).val) (rot 1 raw ^^^ row)
  let visibleOutput := fun (row raw : Nat) => (List.range q).foldl (fun out bitNo =>
    out ||| (((state row raw r).testBit ((i.val + bitNo) % k)).toNat <<< bitNo)) 0
  let mate := fun (word : Nat) => word ^^^ (1 <<< ((i.val + k + 2 - 2*r) % k))
  let budget := 2^(k-n) * (∑ m ∈ Finset.range (e+q), Nat.choose n m)
  let cutSite := i.val + k + 3 - 2*r
  let lowTrace := fun (input nameKey : Nat) =>
    let weight := (List.range n).foldl (fun (ones tickNo : Nat) =>
      let now := 5 + tickNo
      let pos := cutSite + k - 3*now + ones
      let layer := state input nameKey (now-1)
      ones + (xor (xor (layer.testBit (pos % k)) (layer.testBit ((pos+1) % k)))
                   (layer.testBit ((pos+2) % k))).toNat) 0
    decide (weight < e+q)
  let clipped := fun (fixedRow candidate : Nat) =>
    let residue := fun (place : Int) => (place % (k : Int)).toNat
    let period := rot 1 candidate ^^^ fixedRow
    let start := fun (site : Int) => if site < (cutSite : Int) then period.testBit (residue site) else false
    let mix := fun (tape : Int → Bool) (atSite : Int) =>
      xor (xor (tape (atSite-1)) (tape atSite)) (tape (atSite+1))
    let finalTape := (List.range r).foldl (fun (previous : Int → Bool) (tick : Nat) (z : Int) =>
      let p := z + 1 - 2*(tick : Int)
      let ordinary := xor (mix previous z) (!(mix previous (z+1)) && mix previous (z+2))
      xor (xor (xor ordinary (start p)) (fixedRow.testBit (residue p)))
        ((constants (tick+1)).val.testBit (residue z))) start
    (List.range q).foldl (fun (total j : Nat) => total ||| ((finalTape ((i.val : Int)+(j : Int))).toNat <<< j)) 0
  ∀ rowName : Fin (2^k),
    let wordOut := visibleOutput rowName.val
    let selected := (List.range (2^k)).filter (fun w =>
      lowTrace rowName.val w && (decide (w < mate w) || !(lowTrace rowName.val (mate w))))
    let touched := fun (c : Nat) =>
      (selected.filter (fun v => clipped rowName.val v / 2 == c)).length
    let follows := fun (lab : Nat → Bool) (x : Nat) => lab (wordOut x) ≠ lab (wordOut (mate x))
    selected.length ≤ budget ∧
    (∀ y z : Fin (2^q),
      (∃ base : Fin (2^k), wordOut base.val = y.val ∧ wordOut (mate base.val) = z.val) ↔
        (∃ p ∈ selected, (wordOut p = y.val ∧ wordOut (mate p) = z.val) ∨
          (wordOut p = z.val ∧ wordOut (mate p) = y.val)) ∨
        (z.val = (y.val ^^^ 1) ∧ touched (y.val / 2) < 2^(k-q))) ∧
    (budget < 2^(k-q) → ∀ coloring : Nat → Bool,
      (∀ rawKey : Fin (2^k), follows coloring rawKey.val) ↔
        (∀ pair : Fin (2^(q-1)), coloring (2*pair.val) ≠ coloring (2*pair.val+1)) ∧
        ∀ representative ∈ selected, follows coloring representative) := by
  intro k r e q n i constants q0 ledger nr kn en
  intro rot step state visibleOutput mate budget cutSite lowTrace clipped rowName wordOut selected touched follows
  classical
  let u := rowName.val
  let cs (t : ℕ) := (constants t).val
  let pub := pubRow k u cs
  let cut : ℤ := cutSite
  have k0 : 0<k := by omega
  have r4 : 4≤r := by omega
  have qr : q≤k := by omega
  have hk : ∀ t,cs t<2^k := fun t=>(constants t).isLt
  have ub : u<2^k := rowName.isLt
  have it := i.isLt
  have hpos : 2*r ≤ i.val+k+2 := by omega
  have lo : loZ r = -2*(r:ℤ)+3 := by simp [loZ,show ¬r≤3 by omega]
  have cutEq : cut = (i.val:ℤ)+loZ r+k := by
    dsimp [cut,cutSite]
    rw [Nat.cast_sub (by omega),lo]
    push_cast
    ring
  have cutLead : cut = (i.val:ℤ)+3*(r:ℤ)-(e:ℤ) := by
    rw [cutEq,lo]
    omega
  have beforeCut : (i.val:ℤ)+(q:ℤ)+3-2*(r:ℤ)≤cut := by rw [cutEq,lo]; omega
  have walkBound : 3*(n+4)≤cutSite+k := by dsimp [cutSite]; omega
  have mEq (w : ℕ) : mate w=flipK k ((i.val:ℤ)+2-2*(r:ℤ)) w := rawMateNat k r i.val w k0 hpos
  have mateBound (w : ℕ) (wb : w<2^k) : mate w<2^k := by
    rw [mEq]
    exact flipK_lt k0 _ wb
  have inv (w : ℕ) (_ : w<2^k) : mate (mate w)=w := by
    rw [mEq (mate w),mEq w,flipK_flipK]
  have nrMate (w : ℕ) (_ : w<2^k) : w≠mate w := by
    rw [mEq]
    intro h
    have z := congrArg (fun x : ℕ=>pz k x ((i.val:ℤ)+2-2*(r:ℤ))) h
    rw [pz_flipK_on k0] at z
    cases hbit : pz k w ((i.val:ℤ)+2-2*(r:ℤ)) <;> simp only [hbit,Bool.not_false,Bool.not_true,Bool.false_eq_true,Bool.true_eq_false] at z
  have stateEq : state = fun a b t=>st k a cs b t := rfl
  have wEq (w : ℕ) : wordOut w=bitWord q (fun j=>(st k u cs w r).testBit ((i.val+j)%k)) := rfl
  have wordBound (w : ℕ) (_ : w<2^k) : wordOut w<2^q := by rw [wEq]; exact bitWord_lt _ _
  have clipEq (w : ℕ) :
      clipped u w=clippedWord k r q pub (i.val:ℤ) cut (pack k u w) := by
    let start := clip k (pack k u w) cut
    let M (t : ℤ→Bool) (z : ℤ) := xor (xor (t (z-1)) (t z)) (t (z+1))
    have mixEq : M = mixZ := by
      funext t z
      exact congrArg (fun a=>xor a (t (z+1))) (Bool.xor_comm (t (z-1)) (t z))
    change bitWord q (fun j=>(List.range r).foldl (fun (prev : ℤ→Bool) (t : ℕ) (z : ℤ)=>
      let p := z+1-2*(t:ℤ)
      let ordinary := xor (M prev z) (!(M prev (z+1)) && M prev (z+2))
      xor (xor (xor ordinary (start p)) (pz k u p)) (pz k (cs (t+1)) z)) start ((i.val:ℤ)+(j:ℤ)))=_
    rw [mixEq]
    change bitWord q (fun j=>(List.range r).foldl (fun (prev : ℤ→Bool) (t : ℕ) (z : ℤ)=>
      let p := z+1-2*(t:ℤ)
      xor (xor (xor (befZ prev z) (start p)) (pz k u p)) (pz k (cs (t+1)) z)) start ((i.val:ℤ)+(j:ℤ)))=_
    rw [stZ_expandedFold] <;> rfl
  have badEq (w : ℕ) (wb : w<2^k) :
      lowTrace u w=decide (walk (clippedGuard k pub cut (pack k u w)) n<e+q) := by
    apply congrArg (fun v : ℕ=>decide (v<e+q))
    unfold walk
    apply foldl_prefix_eq
    intro ones j jl
    have h := rawGuardPosition (k:=k) (u:=u) (w:=w) (n:=n) (cut:=cutSite)
      cs hk k0 ub wb walkBound j (List.mem_range.mp jl) ones
    change ones + _ = ones + _
    rw [stateEq,h]
  have agree (w : ℕ) (wb : w<2^k) (no : lowTrace u w=false) : wordOut w=clipped u w := by
    rw [badEq w wb] at no
    let C := clippedGuard k pub cut (pack k u w)
    let cb := traceBit C
    have count : e+q≤cntC cb n := by
      have low := of_decide_eq_false no
      have h := walk_eq_cnt C n
      exact le_of_not_gt (h ▸ low)
    have tr (j : ℕ) (_ : j<n) :
        grd k pub cut (cntC cb) j (pack k u w)=cb j := by
      change C j (cntC cb j)=traceBit C j
      rw [←walk_eq_cnt C j]
      rfl
    rw [wEq,clipEq]
    exact wordPhysicalAgrees cs hk k0 ub wb nr i.val cut cb tr
      (by rw [cutLead]; omega) beforeCut
  have packM (w : ℕ) (wb : w<2^k) :
      pack k u (mate w)=flipK k ((i.val:ℤ)+loZ r) (pack k u w) := by
    rw [mEq,show (i.val:ℤ)+2-2*(r:ℤ)=(i.val:ℤ)+loZ r-1 by rw [lo]; ring]
    exact pack_flip k0 ub wb _
  have toggle (w : ℕ) (wb : w<2^k) : clipped u (mate w)=clipped u w^^^1 := by
    rw [clipEq (mate w),clipEq w,packM w wb,cutEq]
    exact clipMateWord k r q (pack k u w) k0 r4 q0 pub _
  let equiv := packEquiv k0 ub
  have lowCount : ((List.range (2^k)).filter (lowTrace u)).length≤budget := by
    rw [listRangeCount]
    have eq : ((Finset.univ : Finset (Fin (2^k))).filter
        (fun w=>lowTrace u w.val=true)).card =
        ((Finset.univ : Finset (Fin (2^k))).filter
         (fun w=>walk (clippedGuard k pub cut w.val) n<e+q)).card := by
      apply Finset.card_bijective equiv equiv.bijective
      intro w
      simp [badEq w.val w.isLt,equiv,packEquiv]
    rw [eq]
    exact adaptiveTraceLowCount k n (e+q) kn pub cut
  have sel : selected=picked (2^k) mate (lowTrace u) := rfl
  have selBound : selected.length≤budget := by
    rw [sel]
    apply le_trans _ lowCount
    unfold picked
    have h : ((List.range (2^k)).filter (fun w=>lowTrace u w &&
        (decide (w < mate w) || !(lowTrace u (mate w))))) =
      (((List.range (2^k)).filter (lowTrace u)).filter (fun w=>decide (w < mate w) ||
        !(lowTrace u (mate w)))) := by rw [List.filter_filter]; simp [Bool.and_comm]
    rw [h]
    exact List.filter_sublist.length_le
  have fiber (y : Fin (2^q)) :
      ((List.range (2^k)).filter (fun w=>decide (w < mate w) && decide (clipped u w/2=y.val/2))).length=2^(k-q) := by
    rw [canonicalHalfFiber mateBound inv nrMate (clipped u) toggle (y.val/2),listRangeCount]
    have yb : 2*(y.val/2)<2^q := by have := y.isLt; omega
    let y' : Fin (2^q) := ⟨2*(y.val/2),yb⟩
    have eq : ((Finset.univ : Finset (Fin (2^k))).filter (fun w=>decide (clipped u w.val=2*(y.val/2))=true)).card =
      ((Finset.univ : Finset (Fin (2^k))).filter
        (fun w=>clippedWord k r q pub (i.val:ℤ) cut w.val=y'.val)).card := by
      apply Finset.card_bijective equiv equiv.bijective
      intro w
      simp [clipEq,equiv,packEquiv,y']
    rw [eq,cutEq]
    exact clipTriCount k r q k0 r4 qr pub (i.val:ℤ) y'
  have edge (y z : Fin (2^q)) :
      (∃ w<2^k,wordOut w=y.val ∧ wordOut (mate w)=z.val) ↔
      (∃ p∈selected,(wordOut p=y.val ∧ wordOut (mate p)=z.val) ∨
        (wordOut p=z.val ∧ wordOut (mate p)=y.val)) ∨
      (z.val=y.val^^^1 ∧ touched (y.val/2)<2^(k-q)) := by
    rw [sel]
    exact edgesExact mateBound inv nrMate wordOut (clipped u) agree toggle y.val z.val _ (fiber y)
  refine ⟨selBound,?_,?_⟩
  · intro y z
    rw [←edge y z]
    exact ⟨fun ⟨w,wh⟩=>⟨w.val,w.isLt,wh⟩,fun ⟨w,wb,wh⟩=>⟨⟨w,wb⟩,wh⟩⟩
  · intro bnd coloring
    have eq : (∀ w : Fin (2^k),follows coloring w.val) ↔
        ∀ w<2^k,coloring (wordOut w)≠coloring (wordOut (mate w)) :=
      ⟨fun h w wb=>h ⟨w,wb⟩,fun h w=>h w.val w.isLt⟩
    rw [eq]
    apply coloringFromEdges q0 mate wordOut selected wordBound mateBound
    · intro p pp
      rw [sel] at pp
      exact (mem_picked.mp pp).1
    · intro y z
      rw [edge]
      have t : touched (y.val/2)<2^(k-q) := by
        have le : touched (y.val/2) ≤ selected.length := List.filter_sublist.length_le
        exact lt_of_le_of_lt (le.trans selBound) bnd
      simp [t]

