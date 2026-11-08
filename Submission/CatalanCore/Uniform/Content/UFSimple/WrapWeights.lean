module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapCredit
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapRelabel

@[expose] public section

/-! # Normalized weights of the original wrapped mixed source -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapWeights

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ}
  {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Normalize against the original common representative moment. -/
noncomputable def referenceC0 (p q o : ℕ) [Fact p.Prime] (Fr : Frame) (c : ι → ℕ)
    (Q : Matrix ι ι (LocRing p)[X]) (t0 : ℕ) : RatFunc (ZMod p) :=
  let d := dirOf Fr c Q t0 (loewRow p Fr c t0)
  rfH p (wT p q o ((t0:ℕ):ZMod p))*(rfH p (red p Fr.norm))⁻¹-
    fibMom c (Dmat c Q) (fun a => ellL p Fr (c a)-d) ((t0:ℕ):ZMod p)

/-- Normalized derived weight of the actual original wrapped matrix. -/
noncomputable def actualV (Fr : Frame) (q o : ℕ) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s)
    (hint : ∀ i j,(p:ℚ)^2*Fr.Mn (rowNode c (WrapActual.xs r (m:=s+l)) i)
      (colNode c (WrapActual.ys r (m:=s+l)) j)∈LocRing p) (t0 : ℕ) :
    ZMod p → RatFunc (ZMod p) :=
  let cr := fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a)
  let cc := fun a => WrapActual.colCoords c r s l hl hls (Sum.inl a)
  let Q := (WrapActual.reordered c r s l hl hls hint).toBlocks₁₁
  let Qo := (sLift c (WrapActual.xs r) (WrapActual.ys r) hint).toBlocks₁₁
  let d := dirOf Fr c Qo t0 (loewRow p Fr c t0)
  let C0 := referenceC0 p q o Fr c Qo t0
  WrapResponse.mixedV Fr cr cc Q d (fun u => rfH p (wT p q o u)*(rfH p (red p Fr.norm))⁻¹-C0)

/-- At every surplus colour, the actual normalized weight is the
original common-core weight. -/
theorem surplus_V_eq (c : ι → ℕ) (r s l t0 t : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hlo : r+2*l-1≤t) (hhi : t<r+p)
    (hint : ∀ i j,(p:ℚ)^2*Fr.Mn (rowNode c (WrapActual.xs r (m:=s+l)) i)
      (colNode c (WrapActual.ys r (m:=s+l)) j)∈LocRing p)
    (hDa : IsUnit (Dmat (fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a))
      (WrapActual.reordered c r s l hl hls hint).toBlocks₁₁).det)
    (hDo : IsUnit (Dmat c (sLift c (WrapActual.xs r) (WrapActual.ys r) hint).toBlocks₁₁).det) :
    actualV Fr q o c r s l hl hls hint t0 ((t:ℕ):ZMod p)=
      vS7 p q o Fr c (sLift c (WrapActual.xs r) (WrapActual.ys r) hint).toBlocks₁₁ t0 ((t:ℕ):ZMod p) := by
  dsimp only [actualV,referenceC0,vS7]
  unfold WrapResponse.mixedV vDer
  rw [WrapActual.surplus_mixedFibMom c r s l t hl hls hp hlo hhi hint _ hDa hDo]

/-- Every actual surplus node in the regular representative window has
zero normalized source weight. -/
theorem surplus_V_zero (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0) (htp : t0+delta<r+p)
    (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    actualV Fr q o (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy) t0 ((t0+delta:ℕ):ZMod p)=0 := by
  intro D
  let co := fun a:Fin r => (a:ℕ)
  let Qo := (sLift co (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
  have hDa := WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 co r s l hl hls hp hsize hc hx hy
  have hDo : IsUnit (Dmat co Qo).det :=
    isUnit_Dmat_det D co hc Qo (sLift_core_rel D hN co (WrapActual.xs r) (WrapActual.ys r) hc hx hy)
      (sLift_core_det co _ _ _)
  rw [surplus_V_eq co r s l t0 (t0+delta) hl hls hp (by omega) htp _ hDa hDo]
  exact vS7_zero T hN.le hsq hnorm hnorm0 hN hp2 ho hq0 co (WrapActual.xs r) (WrapActual.ys r)
    hc hx hy t0 (t0+delta) htN (WrapCell.fin_shiftData T hN.le hsq hnorm hnorm0 r t0 delta
      (by omega) htp hq hw)

/-- The actual normalized weight vanishes at this credited balanced class. -/
theorem balanced_top_V_zero {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (ht0p : t0<r+p) (t : Fin (2*l-1))
    (hq : t0/p=(r+(t:ℕ))/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) (r+(t:ℕ)) (t0-(r+(t:ℕ)))) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    actualV Fr q o (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy) t0 ((r+(t:ℕ):ℕ):ZMod p)=0 := by
  intro D
  let co := fun a:Fin r => (a:ℕ)
  have hm := WrapCredit.balanced_top_moment_credit T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp hsize
    hc hx hy t0 ht0 ht0p t hq hw
  dsimp only at hm
  erw [WrapBalanced.commonLift_eq_core D hN co (WrapActual.xs r) (WrapActual.ys r) hc hx hy] at hm
  have hle : r+(t:ℕ)≤t0 := by have := t.2; omega
  have heq : r+(t:ℕ)+(t0-(r+(t:ℕ)))=t0 := Nat.add_sub_of_le hle
  have ht0N : t0<N := by omega
  have hwstep := wT_window T hN.le hsq hnorm hnorm0 ho hq0 (r+(t:ℕ))
    (t0-(r+(t:ℕ))) (by rw [heq]; exact ht0N) hw
  rw [heq] at hwstep
  dsimp only [actualV,referenceC0]
  unfold WrapResponse.mixedV
  dsimp only
  rw [hm,hwstep.symm]
  ring

/-- The actual normalized weight vanishes at this credited balanced class. -/
theorem balanced_ordinary_V_zero {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (ht0p : t0<r+p) (t : Fin (2*l-1))
    (hq : (r+(t:ℕ)+p)/p=t0/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 (r+(t:ℕ)+p-t0)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    actualV Fr q o (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy) t0 ((r+(t:ℕ):ℕ):ZMod p)=0 := by
  intro D
  let co := fun a:Fin r => (a:ℕ)
  have hm := WrapCredit.balanced_moment_representative T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp hsize
    hc hx hy t0 ht0 ht0p t hq hw
  dsimp only at hm
  erw [WrapBalanced.commonLift_eq_core D hN co (WrapActual.xs r) (WrapActual.ys r) hc hx hy] at hm
  have heq : t0+(r+(t:ℕ)+p-t0)=r+(t:ℕ)+p := by omega
  have hhiN : r+(t:ℕ)+p<N := by have := t.2; omega
  have hwstep := wT_window T hN.le hsq hnorm hnorm0 ho hq0 t0
    (r+(t:ℕ)+p-t0) (by rw [heq]; exact hhiN) hw
  rw [heq] at hwstep
  have hcol : (((r+(t:ℕ)+p:ℕ):ZMod p))=((r+(t:ℕ):ℕ):ZMod p) := by
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
  rw [hcol] at hwstep
  dsimp only [actualV,referenceC0]
  unfold WrapResponse.mixedV
  dsimp only
  rw [hm,hwstep]
  ring

/-- Every residue in the regular virtual window has zero actual source
weight, including those beyond the original surplus interval. -/
theorem window_V_zero (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 tv : ℕ) (ht0 : r+2*l-1≤t0) (ht0p : t0<r+p) (htv : t0≤tv)
    (htvp : tv<r+(2*l-1)+p) (hdiv : tv/p=t0/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 (tv-t0)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    ∀ n, t0≤n → n≤tv → actualV Fr q o (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy) t0 ((n:ℕ):ZMod p)=0 := by
  intro D n hn0 hnv
  have heq : t0+(n-t0)=n := Nat.add_sub_of_le hn0
  have hnN : n<N := by omega
  have hqn : n/p=t0/p := div_eq_of_between hn0 hnv hdiv
  have hwn : NoSingWin D t0 (n-t0) := by
    intro k hk1 hk2
    apply hw k hk1
    omega
  by_cases hns : n<r+p
  · have hh := surplus_V_zero T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp hsize
      hc hx hy t0 (n-t0) ht0 (by rw [heq]; exact hns) (by rw [heq]; exact hqn)
      (by rw [heq]; exact hnN) hwn
    dsimp only at hh
    rwa [heq] at hh
  · let t : Fin (2*l-1) := ⟨n-(r+p),by omega⟩
    have he : r+(t:ℕ)+p=n := by dsimp [t]; omega
    have hw' : NoSingWin D t0 (r+(t:ℕ)+p-t0) := by rwa [he]
    have hh := balanced_ordinary_V_zero T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp hsize
      hc hx hy t0 ht0 ht0p t (by rw [he]; exact hqn) hw'
    dsimp only at hh
    have hc' : ((r+(t:ℕ):ℕ):ZMod p)=((n:ℕ):ZMod p) := by
      rw [← he]
      simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
    rwa [hc'] at hh

/-- Credited original common top extensions retain zero actual weight. -/
theorem common_top_V_zero (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 delta : ℕ) (ht0 : r+2*l-1≤t0) (ht0p : t0<r+p) (hd : delta≤t0)
    (hlt : t0-delta<r) (ha3 : r+(2*l-1)≤t0-delta+p) (hdiv : (t0-delta)/p=t0/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) (t0-delta) delta) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    actualV Fr q o (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy) t0 ((t0-delta:ℕ):ZMod p)=0 := by
  intro D
  let co := fun a:Fin r => (a:ℕ)
  let Qo := (sLift co (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
  have hDa := WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 co r s l hl hls hp hsize hc hx hy
  have hDo : IsUnit (Dmat co Qo).det :=
    isUnit_Dmat_det D co hc Qo (sLift_core_rel D hN co (WrapActual.xs r) (WrapActual.ys r) hc hx hy)
      (sLift_core_det co _ _ _)
  have hcplus : ((t0-delta+p:ℕ):ZMod p)=((t0-delta:ℕ):ZMod p) := by
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
  rw [← hcplus,surplus_V_eq co r s l t0 (t0-delta+p) hl hls hp (by omega) (by omega) _ hDa hDo,hcplus]
  have hh := WrapRelabel.fin_top_zero T hN hsq hnorm hnorm0 ho hq0 r hc t0 delta
    (by omega) (by omega) hd hlt (by omega) ht0p hdiv hw
  erw [WrapBalanced.commonLift_eq_core D hN co (WrapActual.xs r) (WrapActual.ys r) hc hx hy] at hh
  exact hh

/-- The entire credited residue window vanishes for the actual mixed
source, including both sorts of top extensions. -/
theorem credited_V_zero (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (w0 t0 tv : ℕ) (hmax : t0=max (r+2*l-1) w0) (ht0p : t0<r+p) (htv : t0≤tv)
    (htvp : tv<r+(2*l-1)+p) (hwin : tv<w0+p) (hdiv : tv/p=w0/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) w0 (tv-w0)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    ∀ n,w0≤n → n≤tv → actualV Fr q o (fun a:Fin r => (a:ℕ)) r s l hl hls
      (hint_of_poleData D hN hc hx hy) t0 ((n:ℕ):ZMod p)=0 := by
  intro D n hnw hnv
  have ht0 : r+2*l-1≤t0 := by omega
  have hwt : w0≤t0 := by omega
  have hdivT : t0/p=w0/p := div_eq_of_between hwt htv hdiv
  have hqn : n/p=t0/p := (div_eq_of_between hnw hnv hdiv).trans hdivT.symm
  by_cases hnt : t0≤n
  · have hw' : NoSingWin D t0 (tv-t0) := by
      intro k hk1 hk2
      apply hw k (by omega)
      omega
    exact window_V_zero T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp hsize hc hx hy
      t0 tv ht0 ht0p htv htvp (hdiv.trans hdivT.symm) hw' n hnt hnv
  · have ht0a : t0=r+2*l-1 := by omega
    have hwn : NoSingWin D n (t0-n) := by
      intro k hk1 hk2
      apply hw k (by omega)
      omega
    by_cases hnr : r≤n
    · let t : Fin (2*l-1) := ⟨n-r,by omega⟩
      have heq : r+(t:ℕ)=n := by dsimp [t]; omega
      have hh := balanced_top_V_zero T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp hsize hc hx hy
        t0 ht0 ht0p t (by rw [heq]; exact hqn.symm) (by rw [heq]; exact hwn)
      dsimp only at hh
      rwa [heq] at hh
    · have heq : t0-(t0-n)=n := by omega
      have hh := common_top_V_zero T hqp hN hsq hnorm hnorm0 ho hq0 r s l hl hls hp hsize hc hx hy
        t0 (t0-n) ht0 ht0p (by omega) (by rw [heq]; omega)
        (by rw [heq]; omega) (by rw [heq]; exact hqn) (by rw [heq]; exact hwn)
      dsimp only at hh
      rwa [heq] at hh

end CatalanCore.Uniform.Content.UFSimple.WrapWeights
