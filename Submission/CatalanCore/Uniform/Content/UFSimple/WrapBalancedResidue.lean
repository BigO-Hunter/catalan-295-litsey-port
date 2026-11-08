module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPivot
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapBalancedTest

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapBalancedResidue

variable (p : ℕ) [Fact p.Prime]

/-- Original arithmetic and node geometry only; no core or source
invertibility is part of this data. -/
structure Hyp (q o k j0 gamma m N b : ℕ) (x y : Fin b → ℕ) : Prop where
  hq0 : 0<q
  hqp : q<p
  hq2 : 2≤q
  hoq : o<q
  hk0 : 0<k
  hk : k≤p
  hg : gamma<p
  hroot : q*k=j0*p+o
  hsize : 2*m≤N
  hN : q*N<p*p
  hb : b≤m/p+1
  hb0 : 1≤b
  hx : Function.Injective x
  hy : Function.Injective y
  hxN : ∀ i,gamma+x i*p<N
  hyN : ∀ i,gamma+y i*p<N
  hxy : ∀ i j,y j≠x i

namespace Hyp

variable {p} {q o k j0 gamma m N b : ℕ} {x y : Fin b → ℕ}
variable (H : Hyp p q o k j0 gamma m N b x y)

noncomputable def point (H : Hyp p q o k j0 gamma m N b x y) : GaussLoc p :=
  WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0)

noncomputable def matrix (u : GaussLoc p) : Matrix (Fin b) (Fin b) (GaussLoc p) :=
  Matrix.of fun i j => WrapEntryTest.value p q o H.point u (gamma+x i*p) (gamma+y j*p)

noncomputable def sigma (u : GaussLoc p) (t : ℕ) : Fin b → GaussLoc p :=
  fun j => WrapEntryTest.value p q o H.point u (gamma+t*p) (gamma+y j*p)

include H

theorem small (a : ℕ) (ha : gamma+a*p<N) : a+b<p := by
  have hh := WrapPrefixBounds.quotient_add_count p q m N (gamma+a*p) b
    (Fact.out : p.Prime).one_lt H.hq2 H.hsize H.hN ha H.hb
  have he : (gamma+a*p)/p=a := by
    rw [Nat.add_mul_div_right _ _ (Fact.out : p.Prime).pos,Nat.div_eq_of_lt H.hg,zero_add]
  simpa only [he] using hh

theorem b_small : b<p := by
  have := H.small (x ⟨0,H.hb0⟩) (H.hxN ⟨0,H.hb0⟩)
  omega

theorem matrix_residue (u : GaussLoc p) :
    (H.matrix u).map (res p)=res p u • WrapHarmonic.matrix (K:=RatFunc (ZMod p)) b (decide (k≤gamma)) x y := by
  apply Matrix.ext; intro i j
  exact WrapOwnEntry.residue p q o k j0 gamma m N b (x i) (y j) u H.hq0 H.hqp H.hq2 H.hoq
    H.hk0 H.hk H.hg H.hroot H.hsize H.hN (H.hxN i) (H.hyN j) H.hb H.hb0
    (by have := H.small (x i) (H.hxN i); omega)
    (by have := H.small (y j) (H.hyN j); omega) (Ne.symm (H.hxy i j))

theorem harmonic_det_ne :
    (WrapHarmonic.matrix (K:=RatFunc (ZMod p)) b (decide (k≤gamma)) x y).det≠0 := by
  have hfp := WrapHarmonicPivot.det_ne p b (decide (k≤gamma)) x y H.b_small H.hx H.hy
    (fun i => H.small (x i) (H.hxN i)) (fun i => H.small (y i) (H.hyN i)) H.hxy
  rw [← WrapHarmonicMap.matrix (RatFunc.C:ZMod p →+* RatFunc (ZMod p))]
  change ((RatFunc.C:ZMod p →+* RatFunc (ZMod p)).mapMatrix _).det≠0
  rw [← RingHom.map_det]
  exact fun hz => hfp ((RatFunc.C:ZMod p →+* RatFunc (ZMod p)).injective
    (by simpa only [map_zero] using hz))

theorem det_ne (u : GaussLoc p) (hu : res p u≠0) : res p (H.matrix u).det≠0 := by
  rw [RingHom.map_det (R:=GaussLoc p) (S:=RatFunc (ZMod p)) (res p) (H.matrix u)]
  change ((H.matrix u).map (res p)).det≠0
  rw [H.matrix_residue]
  exact WrapScale.det_ne _ hu _ H.harmonic_det_ne

theorem sigma_residue (u : GaussLoc p) (t : ℕ) (htN : gamma+t*p<N)
    (hyt : ∀ j,y j≠t) :
    (fun j => res p (H.sigma u t j))=res p u •
      (fun j => WrapHarmonic.entry (K:=RatFunc (ZMod p)) b (decide (k≤gamma)) t (y j)) := by
  funext j
  exact WrapOwnEntry.residue p q o k j0 gamma m N b t (y j) u H.hq0 H.hqp H.hq2 H.hoq
    H.hk0 H.hk H.hg H.hroot H.hsize H.hN htN (H.hyN j) H.hb H.hb0
    (by have := H.small t htN; omega)
    (by have := H.small (y j) (H.hyN j); omega) (Ne.symm (hyt j))

theorem harmonic_reference_ne (t : ℕ) (htN : gamma+t*p<N)
    (hxt : ∀ i,x i≠t) (hyt : ∀ j,y j≠t) :
    1-(fun j => WrapHarmonic.entry (K:=RatFunc (ZMod p)) b (decide (k≤gamma)) t (y j)) ⬝ᵥ
      ((WrapHarmonic.matrix b (decide (k≤gamma)) x y)⁻¹ *ᵥ 1)≠0 := by
  let Q := WrapHarmonic.matrix (K:=ZMod p) b (decide (k≤gamma)) x y
  let sigma := fun j => WrapHarmonic.entry (K:=ZMod p) b (decide (k≤gamma)) t (y j)
  have hD : Q.det≠0 := WrapHarmonicPivot.det_ne p b (decide (k≤gamma)) x y H.b_small H.hx H.hy
    (fun i => H.small (x i) (H.hxN i)) (fun i => H.small (y i) (H.hyN i)) H.hxy
  have hB : 1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1)≠0 :=
    WrapHarmonicPivot.reference_ne p b (decide (k≤gamma)) x y t H.b_small H.hx H.hy
      (fun i => H.small (x i) (H.hxN i)) (fun i => H.small (y i) (H.hyN i))
      (H.small t htN) H.hxy hxt hyt
  have hm := WrapHarmonicMap.reference (RatFunc.C:ZMod p →+* RatFunc (ZMod p)) Q
    (isUnit_iff_ne_zero.mpr hD) sigma
  have hQmap : Q.map (RatFunc.C:ZMod p →+* RatFunc (ZMod p))=
      WrapHarmonic.matrix (K:=RatFunc (ZMod p)) b (decide (k≤gamma)) x y :=
    WrapHarmonicMap.matrix _ b _ x y
  have hsmap : (fun j => (RatFunc.C:ZMod p →+* RatFunc (ZMod p)) (sigma j))=
      (fun j => WrapHarmonic.entry (K:=RatFunc (ZMod p)) b (decide (k≤gamma)) t (y j)) := by
    funext j
    exact WrapHarmonicMap.entry _ b t (y j) _
  rw [hQmap,hsmap] at hm
  intro hz
  apply hB
  apply (RatFunc.C:ZMod p →+* RatFunc (ZMod p)).injective
  simpa only [map_zero] using hm.trans hz

theorem reference_ne (u : GaussLoc p) (hu : res p u≠0) (t : ℕ) (htN : gamma+t*p<N)
    (hxt : ∀ i,x i≠t) (hyt : ∀ j,y j≠t) :
    1-(fun j => res p (H.sigma u t j)) ⬝ᵥ (((H.matrix u).map (res p))⁻¹ *ᵥ 1)≠0 := by
  rw [H.matrix_residue,H.sigma_residue u t htN hyt,
    WrapScale.reference _ hu _ (isUnit_iff_ne_zero.mpr H.harmonic_det_ne)]
  exact H.harmonic_reference_ne t htN hxt hyt

end Hyp
end CatalanCore.Uniform.Content.UFSimple.WrapBalancedResidue
