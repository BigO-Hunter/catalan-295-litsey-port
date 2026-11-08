module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapDisplacement
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapType
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapSchur

@[expose] public section

/-! # Mixed displacement source and the J-block rank interface

The core row and column prefix loads remain independent throughout the
cleared displacement identity, local source, and Cauchy factorization.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFSimple.WrapResponse

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Actual displacement numerator with independent core prefix loads. -/
noncomputable def dispNum (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (Fr : Frame) (cr cc : ι → ℕ) (xs ys : κ → ℕ) (z y : κ) : (LocRing p)[X] :=
  rowMomA A z * colMomB A Fr cc ys y - rowMomB A Fr cr xs z * colMomA A y

/-- The cleared Schur displacement identity for independent actual
row and column coordinates. -/
theorem displacement (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (cr cc : ι → ℕ) (xs ys : κ → ℕ)
    (hcomm : ∀ i j, nL p Fr * (nd p (colNode cc ys j)-nd p (rowNode cr xs i))*A i j =
      PF p Fr (colNode cc ys j)-PF p Fr (rowNode cr xs i)) (z y : κ) :
    A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y)-nd p (xs z))) *
      (A.toBlocks₁₁.det • A.toBlocks₂₂-A.toBlocks₂₁*A.toBlocks₁₁.adjugate*A.toBlocks₁₂) z y =
        dispNum A Fr cr cc xs ys z y := by
  have hh := WrapDisplacement.mixed_cleared_schur_displacement A.toBlocks₁₁
    A.toBlocks₁₁.adjugate A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂ A.toBlocks₁₁.det
    (nL p Fr) (Matrix.mul_adjugate _) (Matrix.adjugate_mul _)
    (fun i => nd p (cr i)) (fun i => nd p (cc i))
    (fun i => PF p Fr (cr i)) (fun i => PF p Fr (cc i))
    (fun i => nd p (xs i)) (fun i => PF p Fr (xs i))
    (fun i => nd p (ys i)) (fun i => PF p Fr (ys i))
    (fun i j => hcomm (Sum.inl i) (Sum.inl j))
    (fun i j => hcomm (Sum.inl i) (Sum.inr j))
    (fun i j => hcomm (Sum.inr i) (Sum.inl j))
    (fun i j => hcomm (Sum.inr i) (Sum.inr j)) z y
  exact hh

theorem hnum_of_local (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (cr cc : ι → ℕ)
    (xs ys : κ → ℕ) (Jr Jc : Finset κ) (dJ : GaussLoc p) (Φ Φ' : κ → GaussLoc p)
    (hr : ∀ z ∈ Jr, algebraMap _ (GaussLoc p) (rowMomB A Fr cr xs z) =
      algebraMap _ (GaussLoc p) (rowMomA A z) * (CatalanCore.Uniform.Content.UFMoments.piL p * dJ + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * Φ z))
    (hc : ∀ y ∈ Jc, algebraMap _ (GaussLoc p) (colMomB A Fr cc ys y) =
      algebraMap _ (GaussLoc p) (colMomA A y) * (CatalanCore.Uniform.Content.UFMoments.piL p * dJ + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * Φ' y))
    (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p)) (K : RatFunc (ZMod p))
    (hΦ : ∀ z ∈ Jr, res p (Φ z) = K + hDer Ret v ((xs z : ℕ) : ZMod p))
    (hΦ' : ∀ y ∈ Jc, res p (Φ' y) = K + hDer Ret v ((ys y : ℕ) : ZMod p))
    (hdet : phiP p A.toBlocks₁₁.det ≠ 0) :
    ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr cr cc xs ys z y = Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (phiP p (rowMomA A z) / phiP p A.toBlocks₁₁.det * phiP p (colMomA A y) *
          (hDer Ret v ((ys y : ℕ) : ZMod p) - hDer Ret v ((xs z : ℕ) : ZMod p))) := by
  intro z hz y hy
  set f := algebraMap (LocRing p)[X] (GaussLoc p)
  have hloc : f (dispNum A Fr cr cc xs ys z y) = CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 *
      (f (rowMomA A z) * f (colMomA A y) * (Φ' y - Φ z)) := by
    rw [dispNum, map_sub, map_mul, map_mul, hr z hz, hc y hy]
    ring
  obtain ⟨q, hq, hres⟩ := dvd_of_local p _ 2 _ hloc
  refine ⟨q, hq, ?_⟩
  rw [hres, map_mul, map_mul, map_sub, hΦ z hz, hΦ' y hy, res_algebraMap, res_algebraMap]
  field_simp
  ring

/-- Cauchy factorization of the actual mixed divided Schur J-block. -/
noncomputable def jblock_of_moments (D : PoleData Fr p N)
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (W : Matrix κ κ (LocRing p)[X])
    (cr cc : ι → ℕ) (xs ys : κ → ℕ)
    (hcomm : ∀ i j, nL p Fr * (nd p (colNode cc ys j)-nd p (rowNode cr xs i))*A i j =
      PF p Fr (colNode cc ys j)-PF p Fr (rowNode cr xs i))
    (hg : phiP p A.toBlocks₁₁.det≠0)
    (hSch : A.toBlocks₁₁.det • A.toBlocks₂₂-A.toBlocks₂₁*A.toBlocks₁₁.adjugate*A.toBlocks₁₂ =
      Polynomial.C ((p:ℕ):LocRing p) • W)
    (hdist : ∀ i j, ((xs i:ℕ):ZMod p)≠((ys j:ℕ):ZMod p))
    (Jr Jc : Finset κ) (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p))
    (mR mC : κ → RatFunc (ZMod p))
    (hnum : ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr cr cc xs ys z y = Polynomial.C ((p:ℕ):LocRing p)^2*q ∧
      phiP p q=phiP p A.toBlocks₁₁.det*
        (mR z*mC y*(hDer Ret v (ys y)-hDer Ret v (xs z))))
    (hRr : ∀ z ∈ Jr, ∀ c' ∈ Ret, v c'≠0 → c'≠((xs z:ℕ):ZMod p))
    (hRc : ∀ y ∈ Jc, ∀ c' ∈ Ret, v c'≠0 → c'≠((ys y:ℕ):ZMod p)) :
    JBlockCauchy W := by
  classical
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  have hπ : Prime π := Polynomial.prime_C_iff.2 (prime_p p)
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hn : red p Fr.norm ≠ 0 := D.norm_ne
  have hrel : ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) *
          W z y = π * q ∧
        phiP p q = phiP p A.toBlocks₁₁.det *
          (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z))) := by
    intro z hz y hy'
    obtain ⟨q, hq1, hq2⟩ := hnum z hz y hy'
    refine ⟨q, ?_, hq2⟩
    have hd := displacement A cr cc xs ys hcomm z y
    rw [hSch, Matrix.smul_apply, smul_eq_mul] at hd
    have e : A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) *
        (π * W z y) = π * (π * q) := by
      rw [hd]
      rw [hq1]; ring
    have e' : π * (A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) *
        W z y) = π * (π * q) := by rw [← e]; ring
    exact mul_left_cancel₀ hπ0 e'
  have hunit : ∀ z y, ((xs z : ℕ) : ZMod p) ≠ ((ys y : ℕ) : ZMod p) →
      phiP p (A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z)))) ≠ 0 := by
    intro z y h
    rw [map_mul, map_mul, phiP_nL D, phiP_natCast_sub]
    refine mul_ne_zero hg (mul_ne_zero ?_ ?_)
    · exact fun h0 => hn (rfH_injective (by rw [h0, map_zero]))
    · exact fun h0 => (sub_ne_zero.2 (Ne.symm h)) (rfH_injective (by rw [h0, map_zero]))
  have hdvd : ∀ z ∈ Jr, ∀ y ∈ Jc, π ∣ W z y := by
    intro z hz y hy'
    obtain ⟨q, hq1, -⟩ := hrel z hz y hy'
    have hnd : ¬ π ∣ A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) := by
      rw [← phiP_eq_zero_iff]; exact hunit z y (hdist z y)
    exact (hπ.dvd_or_dvd ⟨q, hq1⟩).resolve_left hnd
  let Hc : Matrix κ κ (LocRing p)[X] := Matrix.of fun z y => quotP p (W z y)
  have hHc : ∀ z ∈ Jr, ∀ y ∈ Jc, W z y = π * Hc z y := fun z hz y hy' =>
    (quotP_spec p (hdvd z hz y hy')).symm
  let nb : RatFunc (ZMod p) := rfH p (red p Fr.norm)
  have hnb : nb ≠ 0 := fun h0 => hn (rfH_injective (by rw [show rfH p _ = nb from rfl, h0,
    map_zero]))
  exact
  { Jr := Jr
    Jc := Jc
    Hc := Hc
    hJ := hHc
    Ret := Ret
    A := fun z c' => mR z / nb * rfH p (c' - ((xs z : ℕ) : ZMod p))⁻¹
    B := fun c' y => v c' * rfH p (c' - ((ys y : ℕ) : ZMod p))⁻¹ * mC y
    hcauchy := by
      intro z hz y hy'
      obtain ⟨q, hq1, hq2⟩ := hrel z hz y hy'
      rw [hHc z hz y hy'] at hq1
      have hq : A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) * Hc z y = q := by
        apply mul_left_cancel₀ hπ0
        rw [← hq1]; ring
      have hφ := congrArg (phiP p) hq
      rw [hq2, map_mul, map_mul, map_mul, phiP_nL D, phiP_natCast_sub] at hφ
      have hyz : ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (Ne.symm (hdist z y))
      have h2 : rfH p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) ≠ 0 :=
        fun h0 => hyz (rfH_injective (by rw [h0, map_zero]))
      have hsub := hDer_sub Ret v (hRr z hz) (hRc y hy')
      -- cancel `det Q`
      have hφ2 : nb * rfH p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) * phiP p (Hc z y) =
          mR z * mC y * (rfH p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) *
            ∑ c' ∈ Ret, v c' * rfH p ((c' - ((xs z : ℕ) : ZMod p))⁻¹ *
              (c' - ((ys y : ℕ) : ZMod p))⁻¹)) := by
        rw [← hsub]
        apply mul_left_cancel₀ hg
        rw [← hφ]; ring
      have hφ3 : phiP p (Hc z y) = mR z / nb * mC y *
          ∑ c' ∈ Ret, v c' * rfH p ((c' - ((xs z : ℕ) : ZMod p))⁻¹ *
            (c' - ((ys y : ℕ) : ZMod p))⁻¹) := by
        apply mul_left_cancel₀ (mul_ne_zero hnb h2)
        rw [hφ2]
        field_simp
      rw [hφ3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [map_mul]
      ring }


/-- Transposing the core converts column alpha into row alpha. -/
theorem rowMomA_transpose (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (y : κ) :
    rowMomA Aᵀ y=colMomA A y := by
  have hQ : Aᵀ.toBlocks₁₁=A.toBlocks₁₁ᵀ := rfl
  unfold rowMomA colMomA
  rw [hQ,Matrix.det_transpose,← Matrix.adjugate_transpose]
  simp only [Matrix.transpose_apply,Matrix.toBlocks₂₁,Matrix.toBlocks₁₂,Matrix.of_apply]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Transposing the core converts the independently loaded column beta
into row beta with the column prefix load. -/
theorem rowMomB_transpose (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (cc : ι → ℕ) (ys : κ → ℕ) (y : κ) :
    rowMomB Aᵀ Fr cc ys y=colMomB A Fr cc ys y := by
  have hQ : Aᵀ.toBlocks₁₁=A.toBlocks₁₁ᵀ := rfl
  unfold rowMomB colMomB
  rw [hQ,Matrix.det_transpose,← Matrix.adjugate_transpose]
  simp only [Matrix.transpose_apply,Matrix.toBlocks₂₁,Matrix.toBlocks₁₂,Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (A (Sum.inl i) (Sum.inr y))]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- Derived weights of the actual mixed core, with independent loads. -/
noncomputable def mixedV (Fr : Frame) (cr cc : ι → ℕ)
    (Q : Matrix ι ι (LocRing p)[X]) (d : GaussLoc p)
    (W : ZMod p → RatFunc (ZMod p)) (c' : ZMod p) : RatFunc (ZMod p) :=
  res p (algebraMap _ (GaussLoc p) (nL p Fr))*
    (W c'-WrapNodes.mixedFibMom cr (Dmat cr Q)
      (fun a => ellL p Fr (cr a)-d) (fun a => ellL p Fr (cc a)-d) c')

theorem mixed_jtype_node_hDer (D : PoleData Fr p N) (c cc : ι → ℕ) (hc : ∀ a, c a < N) (hcc : ∀ a, cc a < N)
    (hcol : ∀ a, colOf (p:=p) c a=colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr * (nd p (cc b) - nd p (c a)) * Q a b =
      PF p Fr (cc b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0) (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0 - d) -
      (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - d) = 0)
    (hB0 : res p (1 - ∑ j, (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) j) ≠ 0)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (cc a) - nd p t) * σ a = PF p Fr (cc a) - PF p Fr t)
    (momA momB : (LocRing p)[X])
    (hA : algebraMap _ (GaussLoc p) momA = (Q.map (algebraMap _ (GaussLoc p))).det *
      (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)))
    (hB : algebraMap _ (GaussLoc p) momB = CatalanCore.Uniform.Content.UFMoments.piL p * ((Q.map (algebraMap _ (GaussLoc p))).det *
      (algebraMap _ (GaussLoc p) (PF1 p Fr t) - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))))))
    (hT : TypeData Fr c Q t0 σ0 K0 W t σ) :
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) momB = algebraMap _ (GaussLoc p) momA *
        (CatalanCore.Uniform.Content.UFMoments.piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) * K0 +
        hDer univ (mixedV Fr c cc Q d W) ((t : ℕ) : ZMod p) := by
  obtain ⟨e, κ₁, hDD, hss, hℓ, hκ, hres⟩ := hT
  obtain ⟨Φ, h1, h2⟩ := WrapType.mixed_jtype_node D c cc hc hcc hcol Q hQ hdet t0 σ0 d hz hB0 t ht σ hσ momA momB hA hB
    e hDD hss hℓ κ₁ hκ
  refine ⟨Φ, h1, ?_⟩
  rw [h2, hres, hDer]
  simp only [mixedV, Finset.mul_sum, mul_add, mul_sub]
  have e2 : ∀ c' : ZMod p, res p (algebraMap _ (GaussLoc p) (nL p Fr)) * (W c' *
      rfH p (c' - ((t : ℕ) : ZMod p))⁻¹) - res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
      (WrapNodes.mixedFibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d)
            (fun a => ellL p Fr (cc a) - d) c' *
        rfH p (c' - ((t : ℕ) : ZMod p))⁻¹) =
      (res p (algebraMap _ (GaussLoc p) (nL p Fr)) * W c' -
        res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
          WrapNodes.mixedFibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d)
            (fun a => ellL p Fr (cc a) - d) c') *
        rfH p (c' - ((t : ℕ) : ZMod p))⁻¹ := fun c' => by ring
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  simp_rw [e2]

/-- Transposition preserves the derived mixed weight function after
exchanging the two coordinate and prefix families. -/
theorem mixedV_transpose (cr cc : ι → ℕ)
    (hcol : ∀ a, colOf (p:=p) cr a=colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hD : IsUnit (Dmat cr Q).det) (d : GaussLoc p)
    (W : ZMod p → RatFunc (ZMod p)) :
    mixedV Fr cc cr Qᵀ d W=mixedV Fr cr cc Q d W := by
  have hc : colOf (p:=p) cc=colOf cr := funext (fun a => (hcol a).symm)
  have hDT : Dmat cc Qᵀ=(Dmat cr Q)ᵀ := by
    ext a b
    simp only [Dmat,Matrix.of_apply,Matrix.transpose_apply,← hcol a,← hcol b]
    by_cases h : colOf (p:=p) cr a=colOf cr b
    · rw [if_pos h,if_pos h.symm]
    · rw [if_neg h,if_neg (Ne.symm h)]
  have hb : ∀ a b, colOf (p:=p) cr a≠colOf cr b → Dmat cr Q a b=0 := by
    intro a b h; simp [Dmat,h]
  funext tau
  unfold mixedV
  congr 1
  congr 1
  unfold WrapNodes.mixedFibMom
  rw [hDT,hc]
  exact WrapType.mixed_fiber_moment_transpose (Dmat cr Q) (colOf cr) hD hb tau
    (fun a => ellL p Fr (cr a)-d) (fun a => ellL p Fr (cc a)-d) (res p)

/-- The actual full commutator transposes with its coordinate families. -/
theorem commutator_transpose (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (rr cc : ι ⊕ κ → ℕ)
    (h : ∀ i j, nL p Fr*(nd p (cc j)-nd p (rr i))*A i j=PF p Fr (cc j)-PF p Fr (rr i)) :
    ∀ i j, nL p Fr*(nd p (rr j)-nd p (cc i))*Aᵀ i j=PF p Fr (rr j)-PF p Fr (cc i) := by
  intro i j
  have hh := h j i
  change nL p Fr*(nd p (rr j)-nd p (cc i))*A j i=PF p Fr (rr j)-PF p Fr (cc i)
  linear_combination -hh

/-- Reduction of the actual mixed divided Schur entry from its first
numerator quotient. -/
theorem W_reduction (D : PoleData Fr p N)
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (W : Matrix κ κ (LocRing p)[X])
    (cr cc : ι → ℕ) (xs ys : κ → ℕ)
    (hcomm : ∀ i j, nL p Fr*(nd p (colNode cc ys j)-nd p (rowNode cr xs i))*A i j=
      PF p Fr (colNode cc ys j)-PF p Fr (rowNode cr xs i))
    (hSch : A.toBlocks₁₁.det • A.toBlocks₂₂-A.toBlocks₂₁*A.toBlocks₁₁.adjugate*A.toBlocks₁₂=
      Polynomial.C ((p:ℕ):LocRing p) • W) (z y : κ) (q : (LocRing p)[X])
    (hq : dispNum A Fr cr cc xs ys z y=Polynomial.C ((p:ℕ):LocRing p)*q) :
    phiP p (W z y)*(phiP p A.toBlocks₁₁.det*
      rfH p (red p Fr.norm*(((ys y:ℕ):ZMod p)-((xs z:ℕ):ZMod p))))=phiP p q := by
  have hpi : (Polynomial.C ((p:ℕ):LocRing p):(LocRing p)[X])≠0 :=
    (Polynomial.prime_C_iff.2 (prime_p p)).ne_zero
  have hd := displacement A cr cc xs ys hcomm z y
  rw [hSch,Matrix.smul_apply,smul_eq_mul] at hd
  have he : Polynomial.C ((p:ℕ):LocRing p)*(A.toBlocks₁₁.det*
      (nL p Fr*(nd p (ys y)-nd p (xs z)))*W z y)=Polynomial.C ((p:ℕ):LocRing p)*q := by
    rw [← hq,← hd]
    ring
  have h2 := congrArg (phiP p) (mul_left_cancel₀ hpi he)
  rw [map_mul,map_mul,map_mul,phiP_nL D,phiP_natCast_sub] at h2
  rw [← h2,map_mul]
  ring

/-- The actual mixed J-block with all first-layer wedge kills. -/
noncomputable def jblock_kill_of_moments (D : PoleData Fr p N)
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (W : Matrix κ κ (LocRing p)[X])
    (cr cc : ι → ℕ) (xs ys : κ → ℕ)
    (hcomm : ∀ i j, nL p Fr * (nd p (colNode cc ys j)-nd p (rowNode cr xs i))*A i j =
      PF p Fr (colNode cc ys j)-PF p Fr (rowNode cr xs i))
    (hg : phiP p A.toBlocks₁₁.det≠0)
    (hSch : A.toBlocks₁₁.det • A.toBlocks₂₂-A.toBlocks₂₁*A.toBlocks₁₁.adjugate*A.toBlocks₁₂ =
      Polynomial.C ((p:ℕ):LocRing p) • W)
    (hdist : ∀ i j, ((xs i:ℕ):ZMod p)≠((ys j:ℕ):ZMod p))
    (Jr Jc : Finset κ) (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p))
    (mR mC : κ → RatFunc (ZMod p))
    (hnum : ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr cr cc xs ys z y =
        Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z))))
    (hRr : ∀ z ∈ Jr, ∀ c' ∈ Ret, v c' ≠ 0 → c' ≠ ((xs z : ℕ) : ZMod p))
    (hRc : ∀ y ∈ Jc, ∀ c' ∈ Ret, v c' ≠ 0 → c' ≠ ((ys y : ℕ) : ZMod p))
    (TC : Finset κ) (wC : κ → RatFunc (ZMod p)) (hwC : ∀ t ∈ TC, wC t ≠ 0)
    (hTC : ∀ t ∈ TC, ∀ z ∈ Jr, ∃ q : (LocRing p)[X],
      dispNum A Fr cr cc xs ys z t =
        Polynomial.C ((p : ℕ) : LocRing p) * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (mR z * wC t))
    (TR : Finset κ) (wR : κ → RatFunc (ZMod p)) (hwR : ∀ t ∈ TR, wR t ≠ 0)
    (hvR : ∀ t ∈ TR, v ((xs t : ℕ) : ZMod p) ≠ 0)
    (hTR : ∀ t ∈ TR, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr cr cc xs ys t y =
        Polynomial.C ((p : ℕ) : LocRing p) * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (wR t * mC y)) :
    JBlockKill (W) := by
  classical
  have hn : red p Fr.norm ≠ 0 := D.norm_ne
  have hrfH : ∀ u : ZMod p, u ≠ 0 → rfH p u ≠ 0 := fun u hu h0 =>
    hu (rfH_injective (by rw [h0, map_zero]))
  have hnb := hrfH _ hn
  exact
  { toJBlockCauchy := jblock_of_moments D A W cr cc xs ys hcomm hg hSch hdist Jr Jc Ret v mR mC
      hnum hRr hRc
    KillR := TC.image fun t => ((ys t : ℕ) : ZMod p)
    KillC := TR.image fun t => ((xs t : ℕ) : ZMod p)
    hKR := by
      intro c' hc'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
      refine ⟨t, wC t, hwC t ht, fun z hz => ?_⟩
      obtain ⟨q, hq1, hq2⟩ := hTC t ht z hz
      have h := W_reduction D A W cr cc xs ys hcomm hSch z t q hq1
      rw [hq2] at h
      have hyz : ((ys t : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (Ne.symm (hdist z t))
      have h2 := hrfH _ hyz
      have hden : phiP p A.toBlocks₁₁.det *
          rfH p (red p Fr.norm * (((ys t : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p))) ≠ 0 :=
        mul_ne_zero hg (hrfH _ (mul_ne_zero hn hyz))
      show _ = wC t * (mR z / rfH p (red p Fr.norm) *
        rfH p (((ys t : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p))⁻¹)
      apply mul_right_cancel₀ hden
      rw [h, map_mul, map_inv₀]
      field_simp
    hKC := by
      intro c' hc'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
      have hv := hvR t ht
      refine ⟨t, -(wR t) / (rfH p (red p Fr.norm) * v ((xs t : ℕ) : ZMod p)),
        div_ne_zero (neg_ne_zero.2 (hwR t ht)) (mul_ne_zero hnb hv), fun y hy' => ?_⟩
      obtain ⟨q, hq1, hq2⟩ := hTR t ht y hy'
      have h := W_reduction D A W cr cc xs ys hcomm hSch t y q hq1
      rw [hq2] at h
      have hyz : ((ys y : ℕ) : ZMod p) - ((xs t : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (Ne.symm (hdist t y))
      have hzy : ((xs t : ℕ) : ZMod p) - ((ys y : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (hdist t y)
      have h3 := hrfH _ hzy
      have hden : phiP p A.toBlocks₁₁.det *
          rfH p (red p Fr.norm * (((ys y : ℕ) : ZMod p) - ((xs t : ℕ) : ZMod p))) ≠ 0 :=
        mul_ne_zero hg (hrfH _ (mul_ne_zero hn hyz))
      show _ = -(wR t) / (rfH p (red p Fr.norm) * v ((xs t : ℕ) : ZMod p)) *
        (v ((xs t : ℕ) : ZMod p) * rfH p (((xs t : ℕ) : ZMod p) - ((ys y : ℕ) : ZMod p))⁻¹ * mC y)
      apply mul_right_cancel₀ hden
      have e : ((ys y : ℕ) : ZMod p) - ((xs t : ℕ) : ZMod p) =
          -(((xs t : ℕ) : ZMod p) - ((ys y : ℕ) : ZMod p)) := by ring
      rw [h, e, map_mul, map_neg, map_inv₀]
      field_simp }

/-- Polynomial moments of an independently loaded row of a mixed core. -/
noncomputable def prefixMomA (Q : Matrix ι ι (LocRing p)[X]) (σ : ι → (LocRing p)[X]) :=
  Q.det-∑ i, σ i*∑ k, Q.adjugate i k

noncomputable def prefixMomB (Q : Matrix ι ι (LocRing p)[X]) (c : ι → ℕ)
    (t : ℕ) (σ : ι → (LocRing p)[X]) :=
  Polynomial.C ((p:ℕ):LocRing p)*(Q.det*PF1 p Fr t-
    ∑ i, σ i*∑ k, Q.adjugate i k*PF1 p Fr (c k))

/-- Window transport supplies the second-order source without an extra
moment-map hypothesis. The moments here are the original polynomial ones. -/
theorem prefix_source (D : PoleData Fr p N) (c cc : ι → ℕ)
    (hc : ∀ a, c a<N) (hcc : ∀ a, cc a<N)
    (hcol : ∀ a, colOf (p:=p) c a=colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr*(nd p (cc b)-nd p (c a))*Q a b=PF p Fr (cc b)-PF p Fr (c a))
    (hdet : phiP p Q.det≠0) (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0-d)-(sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a)-d)=0)
    (hB0 : res p (1-∑ j, (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) j)≠0)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (t : ℕ) (ht : t<N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr*(nd p (cc a)-nd p t)*σ a=PF p Fr (cc a)-PF p Fr t)
    (hT : TypeData Fr c Q t0 σ0 K0 W t σ) :
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (prefixMomB (Fr:=Fr) Q c t σ)=
        algebraMap _ (GaussLoc p) (prefixMomA Q σ)*
          (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
      res p Φ=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (mixedV Fr c cc Q d W) ((t:ℕ):ZMod p) := by
  apply mixed_jtype_node_hDer D c cc hc hcc hcol Q hQ hdet t0 σ0 d hz hB0
    K0 W t ht σ hσ (prefixMomA Q σ) (prefixMomB (Fr:=Fr) Q c t σ)
  · exact momA_map _ Q (isUnit_map_det Q hdet) σ
  · unfold prefixMomB
    rw [map_mul]
    congr 1
    exact momB_map _ Q (isUnit_map_det Q hdet) σ _ _
  · exact hT

end CatalanCore.Uniform.Content.UFSimple.WrapResponse
