module

public import CatalanCore.Uniform.Content.UFSimple.WrapCell
public import CatalanCore.Uniform.Content.UFSimple.WrapCoupling

@[expose] public section

/-! # Actual wrapped joint-window displacement source -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapJBlock

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ}

/-- The original independently reordered matrix has a second-order
Cauchy numerator throughout every regular joint window. -/
theorem actual_hnum (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r, (a:ℕ)<N) (hx : ∀ i:Fin (s+l), WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l), WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (C0 : RatFunc (ZMod p))
    (Jr Jc : Finset (Fin (s+1-l)))
    (hJr : ∀ z∈Jr,
      let t := WrapActual.rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inr z)
      t0≤t ∧ t<r+p ∧ t/p=t0/p ∧
        NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 (t-t0))
    (hJc : ∀ z∈Jc,
      let t := WrapActual.colCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inr z)
      t0≤t ∧ t<r+p ∧ t/p=t0/p ∧
        NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 (t-t0))
    :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let cv := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords cv r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords cv r s l hl hls (Sum.inl a)
    let xx := fun z => WrapActual.rowCoords cv r s l hl hls (Sum.inr z)
    let yy := fun z => WrapActual.colCoords cv r s l hl hls (Sum.inr z)
    let A := WrapActual.reordered cv r s l hl hls (hint_of_poleData D hN hc hx hy)
    let Q := A.toBlocks₁₁
    let Qorig := (sLift cv (WrapActual.xs r) (WrapActual.ys r) (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr cv Qorig t0 (loewRow p Fr cv t0)
    let n := (rfH p (red p Fr.norm))⁻¹
    let K0 := -(rfH p (cauchyH (wT p q o) ((t0:ℕ):ZMod p)))*n
    let W := fun c' => rfH p (wT p q o c')*n-C0
    let v := WrapResponse.mixedV Fr cr cc Q d W
    ∀ z∈Jr, ∀ y∈Jc, ∃ q : (LocRing p)[X],
      WrapResponse.dispNum A Fr cr cc xx yy z y=Polynomial.C ((p:ℕ):LocRing p)^2*q ∧
      phiP p q=phiP p Q.det*
        (phiP p (rowMomA A z)/phiP p Q.det*phiP p (colMomA A y)*
          (hDer univ v ((yy y:ℕ):ZMod p)-hDer univ v ((xx z:ℕ):ZMod p))) := by
  intro D cv cr cc xx yy A Q Qorig d n K0 W v
  have hrow : ∀ z∈Jr, ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (rowMomB A Fr cr xx z)=
        algebraMap _ (GaussLoc p) (rowMomA A z)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ v ((xx z:ℕ):ZMod p) := by
    intro z hz
    have hZ := hJr z hz
    have heq : t0+(xx z-t0)=xx z := Nat.add_sub_of_le hZ.1
    have htN := WrapCell.rowCoords_lt r s l hl hls hc hx hy (Sum.inr z)
    have hh := WrapCell.actual_row_moment_source T hqp hN hsq hnorm hnorm0 hp2 ho hq0
      r s l hl hls hp hsize hc hx hy t0 (xx z-t0) ht0
      (by rw [heq]; exact hZ.2.1) (by rw [heq]; exact hZ.2.2.1)
      (by rw [heq]; exact htN) hZ.2.2.2 C0 z heq
    dsimp only at hh
    simpa only [heq] using hh
  have hcol : ∀ z∈Jc, ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (colMomB A Fr cc yy z)=
        algebraMap _ (GaussLoc p) (colMomA A z)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ v ((yy z:ℕ):ZMod p) := by
    intro z hz
    have hZ := hJc z hz
    have heq : t0+(yy z-t0)=yy z := Nat.add_sub_of_le hZ.1
    have htN := WrapCell.colCoords_lt r s l hl hls hc hx hy (Sum.inr z)
    have hh := WrapCell.actual_col_moment_source T hqp hN hsq hnorm hnorm0 hp2 ho hq0
      r s l hl hls hp hsize hc hx hy t0 (yy z-t0) ht0
      (by rw [heq]; exact hZ.2.1) (by rw [heq]; exact hZ.2.2.1)
      (by rw [heq]; exact htN) hZ.2.2.2 C0 z heq
    dsimp only at hh
    simpa only [heq] using hh
  classical
  choose! Φ hΦ1 hΦ2 using hrow
  choose! Φ' hΦ'1 hΦ'2 using hcol
  have hdet : phiP p Q.det≠0 :=
    WrapActual.core_primitive T hqp hN hsq hnorm hnorm0 cv r s l hl hls hp hsize _
  exact WrapResponse.hnum_of_local A cr cc xx yy Jr Jc _ Φ Φ' hΦ1 hΦ'1 univ v _ hΦ2 hΦ'2 hdet

section GenericLocal

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Local original polynomial moments supply the mixed J-block and both
first-order kill numerators, without separate divisibility hypotheses. -/
noncomputable def jblock_kill_of_local (D : PoleData Fr p N)
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (W : Matrix κ κ (LocRing p)[X])
    (cr cc : ι → ℕ) (xs ys : κ → ℕ)
    (hcr : ∀ a,cr a<N) (hcc : ∀ a,cc a<N) (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N)
    (hcomm : ∀ i j,nL p Fr*(nd p (colNode cc ys j)-nd p (rowNode cr xs i))*A i j=
      PF p Fr (colNode cc ys j)-PF p Fr (rowNode cr xs i))
    (hdet : phiP p A.toBlocks₁₁.det≠0)
    (hSch : A.toBlocks₁₁.det • A.toBlocks₂₂-A.toBlocks₂₁*A.toBlocks₁₁.adjugate*A.toBlocks₁₂=
      Polynomial.C ((p:ℕ):LocRing p) • W)
    (hdist : ∀ i j,((xs i:ℕ):ZMod p)≠((ys j:ℕ):ZMod p))
    (Jr Jc : Finset κ) (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p))
    (d : GaussLoc p) (K : RatFunc (ZMod p))
    (hrow : ∀ z∈Jr,∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (rowMomB A Fr cr xs z)=
        algebraMap _ (GaussLoc p) (rowMomA A z)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=K+hDer Ret v ((xs z:ℕ):ZMod p))
    (hcol : ∀ y∈Jc,∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (colMomB A Fr cc ys y)=
        algebraMap _ (GaussLoc p) (colMomA A y)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+
            CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=K+hDer Ret v ((ys y:ℕ):ZMod p))
    (hvr : ∀ z∈Jr,v ((xs z:ℕ):ZMod p)=0) (hvc : ∀ y∈Jc,v ((ys y:ℕ):ZMod p)=0)
    (TC TR : Finset κ)
    (hwC : ∀ t∈TC,wedgeC A Fr cc ys d t≠0)
    (hwR : ∀ t∈TR,wedgeR A Fr cr xs d t≠0)
    (hvR : ∀ t∈TR,v ((xs t:ℕ):ZMod p)≠0) : JBlockKill W := by
  classical
  let f := algebraMap (LocRing p)[X] (GaussLoc p)
  choose! Φ hΦ1 hΦ2 using hrow
  choose! Φ' hΦ'1 hΦ'2 using hcol
  have hnum := WrapResponse.hnum_of_local A cr cc xs ys Jr Jc _ Φ Φ' hΦ1 hΦ'1 Ret v K hΦ2 hΦ'2 hdet
  have hcB : ∀ t,colMomB A Fr cc ys t=Polynomial.C ((p:ℕ):LocRing p)*colMomB1 A Fr cc ys t :=
    fun t => colMomB_eq D A cc ys hcc hy t
  have hrB : ∀ t,rowMomB A Fr cr xs t=Polynomial.C ((p:ℕ):LocRing p)*rowMomB1 A Fr cr xs t :=
    fun t => rowMomB_eq D A cr xs hcr hx t
  have hpz : phiP p (Polynomial.C ((p:ℕ):LocRing p))=0 := (phiP_eq_zero_iff p _).2 dvd_rfl
  refine WrapResponse.jblock_kill_of_moments D A W cr cc xs ys hcomm hdet hSch hdist Jr Jc Ret v
    (fun z => phiP p (rowMomA A z)/phiP p A.toBlocks₁₁.det) (fun y => phiP p (colMomA A y)) hnum
    (fun z hz c _ hv hc => hv (by rw [hc]; exact hvr z hz))
    (fun y hy c _ hv hc => hv (by rw [hc]; exact hvc y hy))
    TC (wedgeC A Fr cc ys d) hwC ?_ TR (wedgeR A Fr cr xs d) hwR hvR ?_
  · intro t _ z hz
    have hloc : f (WrapResponse.dispNum A Fr cr cc xs ys z t)=
        CatalanCore.Uniform.Content.UFMoments.piL p^1*(f (rowMomA A z)*
          (f (colMomB1 A Fr cc ys t)-(f (nL p Fr)*d+
            CatalanCore.Uniform.Content.UFMoments.piL p*Φ z)*f (colMomA A t))) := by
      rw [WrapResponse.dispNum,map_sub,map_mul,map_mul,hΦ1 z hz,hcB t,map_mul]
      ring
    obtain ⟨q,hq1,hq2⟩ := dvd_of_local p _ 1 _ hloc
    refine ⟨q,by rw [hq1,pow_one],?_⟩
    rw [hq2]
    simp only [f,map_mul,map_sub,map_add,res_algebraMap,res_piL,hpz,zero_mul,add_zero]
    unfold wedgeC
    rw [map_mul,res_algebraMap]
    field_simp
  · intro t _ y hy
    have hloc : f (WrapResponse.dispNum A Fr cr cc xs ys t y)=
        CatalanCore.Uniform.Content.UFMoments.piL p^1*(f (colMomA A y)*
          (f (rowMomA A t)*(f (nL p Fr)*d+
            CatalanCore.Uniform.Content.UFMoments.piL p*Φ' y)-f (rowMomB1 A Fr cr xs t))) := by
      rw [WrapResponse.dispNum,map_sub,map_mul,map_mul,hΦ'1 y hy,hrB t,map_mul]
      ring
    obtain ⟨q,hq1,hq2⟩ := dvd_of_local p _ 1 _ hloc
    refine ⟨q,by rw [hq1,pow_one],?_⟩
    rw [hq2]
    simp only [f,map_mul,map_sub,map_add,res_algebraMap,res_piL,hpz,zero_mul,add_zero]
    unfold wedgeR
    rw [map_mul,res_algebraMap]
    field_simp

open Classical in
/-- Counting all outside row colours is valid even when their source
weight vanishes: those colours become zeros rather than retained kills. -/
theorem retained_union_bound (v : ZMod p → RatFunc (ZMod p))
    (Iset : Finset (ZMod p)) (TC TR : Finset κ) (xs ys : κ → ZMod p)
    (hzero : ∀ u∈Iset,v u=0) :
    let TR' := TR.filter (fun t => v (xs t)≠0)
    (retOf v \ (TC.image ys ∪ TR'.image xs)).card≤
      p-(Iset ∪ (TC.image ys ∪ TR.image xs)).card := by
  classical
  intro TR'
  have hzero' : ∀ u∈Iset ∪ (TR \ TR').image xs,v u=0 := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu|hu
    · exact hzero u hu
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨ht1,ht2⟩ := Finset.mem_sdiff.1 ht
      by_contra hne
      exact ht2 (Finset.mem_filter.2 ⟨ht1,hne⟩)
  have hh := card_retOf_sdiff_le v (Iset ∪ (TR \ TR').image xs) (TC.image ys ∪ TR'.image xs) hzero'
  have hsub : TR'⊆TR := Finset.filter_subset _ _
  have hpartition : (TR \ TR')∪TR'=TR := Finset.sdiff_union_of_subset hsub
  have hset : (Iset ∪ (TR \ TR').image xs) ∪ (TC.image ys ∪ TR'.image xs)=
      Iset ∪ (TC.image ys ∪ TR.image xs) := by
    calc
      _=Iset ∪ (TC.image ys ∪ ((TR \ TR').image xs ∪ TR'.image xs)) := by ac_rfl
      _=_ := by rw [← Finset.image_union,hpartition]
  rwa [hset] at hh

end GenericLocal

end CatalanCore.Uniform.Content.UFSimple.WrapJBlock
