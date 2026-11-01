module

public import CatalanCore.Uniform.Content.UFSimple.WrapOriginalEntry
public import CatalanCore.Uniform.Content.UFMember.Gauge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Original family determinants from integral deformed entries -/

open Polynomial Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFMember CatalanCore.Rect

namespace CatalanCore.Uniform.Content.UFSimple.WrapDeformedFamily

variable (p : ℕ) [Fact p.Prime]

noncomputable def originalMap := algebraMap (LocRing p)[X] (GaussLoc p)
noncomputable def coefficient := (WrapDeform.embed p).comp
  ((Polynomial.C : GaussLoc p →+* (GaussLoc p)[X]).comp (originalMap p))

-- Freeze the concrete localization instances before applying matrix lemmas.
noncomputable def determinant_relation {τ : Type*} [Fintype τ] [DecidableEq τ] :=
  WrapSpecialization.determinant (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (ι:=τ) (res p)
noncomputable def descend_relation :=
  @WrapSpecialization.Rel.descend (GaussLoc p) (RatFunc (ZMod p)) _ _ _ (res p)


variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def spectral : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X] :=
  Matrix.fromBlocks ((Polynomial.X:(LocRing p)[X]) • (1:Matrix ι ι (LocRing p)[X])) 0 0 0

noncomputable def matrix (Fr : Frame) (q o : ℕ) (c : ι → ℕ) (xs ys : κ → ℕ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) (WrapDeform.Extension p) :=
  Matrix.of (fun i j => WrapDeformedEntry.entry p q o (WrapOriginalEntry.normInv p Fr)
    (rowNode c xs i) (colNode c ys j))+(spectral p).map (coefficient p)

/-- Every original common deletion is covered by taking c to be its actual
remaining common-node family. Independent border rows and columns are kept. -/
theorem entry_specializes {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (i j : ι ⊕ κ) :
    WrapPole.Specializes p (matrix p Fr q o c xs ys i j)
      (((sLift c xs ys (hint_of_poleData D hN hc hx hy)).map (originalMap p)) i j) := by
  let H := hint_of_poleData D hN hc hx hy
  have hh := WrapOriginalEntry.specializes p T D hqp hN hsq
    (rowNode c xs i) (colNode c ys j) (rowNode_lt hc hx i) (colNode_lt hc hy j)
  have he : Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn (rowNode c xs i) (colNode c ys j))=
      (⟨(p:ℚ)^2*Fr.Mn (rowNode c xs i) (colNode c ys j),H i j⟩:LocRing p) :=
    Subtype.ext (Hybrid.liftQ_val (H i j))
  rw [he] at hh
  change WrapPole.Specializes p
    (WrapDeformedEntry.entry p q o (WrapOriginalEntry.normInv p Fr) (rowNode c xs i) (colNode c ys j)+
      coefficient p (spectral p i j))
    (originalMap p (Polynomial.C (⟨(p:ℚ)^2*Fr.Mn (rowNode c xs i) (colNode c ys j),H i j⟩:LocRing p)+
      spectral p i j))
  rw [map_add]
  exact WrapSpecialization.Rel.add hh (WrapSpecialization.Rel.constant _)

noncomputable def determinant_specializes {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N) :=
  determinant_relation p
    (matrix p Fr q o c xs ys)
    ((sLift c xs ys (hint_of_poleData D hN hc hx hy)).map (originalMap p))
    (entry_specializes p T D hqp hN hsq c xs ys hc hx hy)

/-- Descend only the original scalar determinant. Generic elimination
pivots are absent from the original-unit specialization relation. -/
theorem original_dvr_dvd {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (k : ℕ) (hcontent : WrapDeform.uniformizer p^k∣(matrix p Fr q o c xs ys).det) :
    UFMoments.piL p^k∣((sLift c xs ys (hint_of_poleData D hN hc hx hy)).map (originalMap p)).det := by
  obtain ⟨y,hycontent⟩ := hcontent
  exact descend_relation p (UFMoments.piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p)
    (determinant_specializes p T D hqp hN hsq c xs ys hc hx hy) k y hycontent

theorem original_poly_dvd {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (k : ℕ) (hcontent : WrapDeform.uniformizer p^k∣(matrix p Fr q o c xs ys).det) :
    Polynomial.C ((p:ℕ):LocRing p)^k∣(sLift c xs ys (hint_of_poleData D hN hc hx hy)).det := by
  obtain ⟨x,hxcontent⟩ := original_dvr_dvd p T D hqp hN hsq c xs ys hc hx hy k hcontent
  have hloc : algebraMap (LocRing p)[X] (GaussLoc p)
      (sLift c xs ys (hint_of_poleData D hN hc hx hy)).det=UFMoments.piL p^k*x := by
    change originalMap p _=_
    rw [RingHom.map_det (R:=(LocRing p)[X]) (S:=GaussLoc p)]
    exact hxcontent
  obtain ⟨z,hz,_⟩ := UFMoments.dvd_of_local p _ k x hloc
  exact ⟨z,hz⟩

/-- Final bridge from deformed scalar content to the ORIGINAL unscaled
FullN family polynomial, with the same exponent for this actual member. -/
theorem original_gle {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (k : ℕ) (hcontent : WrapDeform.uniformizer p^k∣(matrix p Fr q o c xs ys).det) :
    GLE p (2*Fintype.card (ι ⊕ κ)-k) (FullN Fr c xs ys (Polynomial.X:ℚ[X])).det := by
  have hd := original_poly_dvd p T D hqp hN hsq c xs ys hc hx hy k hcontent
  have hh := gle_det_of_scaled_dvd p
    ((FullN Fr c xs ys (Polynomial.X:ℚ[X])).map (scaleU p))
    (sLift c xs ys (hint_of_poleData D hN hc hx hy)) (fun _ => 1) (fun _ => 1)
    (sLift_hB c xs ys (hint_of_poleData D hN hc hx hy)) k hd
  apply gle_of_gle_scaleU
  rw [← det_map_scaleU]
  simpa [two_mul] using hh

end CatalanCore.Uniform.Content.UFSimple.WrapDeformedFamily
