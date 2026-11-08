module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapSpectralTest
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapConstant

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix

namespace CatalanCore.Uniform.Content.UFSimple.WrapConstantMatrix

variable {K ι κ : Type*} [Field K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Actual constant residue entries determine prime-field blocks. No
coefficients or mixed pivot are supplied by the caller. -/
theorem spectral_det_ne (A : Matrix ι ι (RatFunc K)) (B : Matrix ι κ (RatFunc K))
    (E : Matrix κ ι (RatFunc K)) (D : Matrix κ κ (RatFunc K))
    (hA : ∀ i j,∃ a:K,A i j=RatFunc.C a)
    (hB : ∀ i j,∃ a:K,B i j=RatFunc.C a)
    (hE : ∀ i j,∃ a:K,E i j=RatFunc.C a)
    (hDc : ∀ i j,∃ a:K,D i j=RatFunc.C a) (hD : D.det≠0) :
    (Matrix.fromBlocks ((RatFunc.X:RatFunc K) • (1:Matrix ι ι (RatFunc K))+A) B E D).det≠0 := by
  classical
  choose A0 hA0 using hA
  choose B0 hB0 using hB
  choose E0 hE0 using hE
  choose D0 hD0 using hDc
  let AA : Matrix ι ι K := Matrix.of A0
  let BB : Matrix ι κ K := Matrix.of B0
  let EE : Matrix κ ι K := Matrix.of E0
  let DD : Matrix κ κ K := Matrix.of D0
  have hAm : A=AA.map RatFunc.C := by ext i j; exact hA0 i j
  have hBm : B=BB.map RatFunc.C := by ext i j; exact hB0 i j
  have hEm : E=EE.map RatFunc.C := by ext i j; exact hE0 i j
  have hDm : D=DD.map RatFunc.C := by ext i j; exact hD0 i j
  have hDD : DD.det≠0 := by
    intro hz
    apply hD
    rw [hDm]
    change ((RatFunc.C:K →+* RatFunc K).mapMatrix DD).det=0
    rw [← RingHom.map_det,hz,map_zero]
  rw [hAm,hBm,hEm,hDm]
  exact WrapSpectralTest.mixed_det_ne AA BB EE DD hDD

open CatalanCore.Uniform.Content.UFMoments

/-- The original Gauss-ring own-core test is nonzero once the actual
balanced test and elementary constant residues have been established. -/
theorem original_test_ne (p : ℕ) [Fact p.Prime]
    (A : Matrix ι ι (GaussLoc p)) (B : Matrix ι κ (GaussLoc p))
    (E : Matrix κ ι (GaussLoc p)) (D : Matrix κ κ (GaussLoc p))
    (s : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hA : ∀ i j,WrapConstant.Has p (A i j))
    (hB : ∀ i j,WrapConstant.Has p (B i j))
    (hE : ∀ i j,WrapConstant.Has p (E i j))
    (hDc : ∀ i j,WrapConstant.Has p (D i j)) (hD : res p D.det≠0) :
    res p (Matrix.fromBlocks (s • (1:Matrix ι ι (GaussLoc p))+A) B E D).det≠0 := by
  classical
  let Q := Matrix.fromBlocks (s • (1:Matrix ι ι (GaussLoc p))+A) B E D
  have hm : Q.map (res p)=Matrix.fromBlocks
      ((RatFunc.X:RatFunc (ZMod p)) • (1:Matrix ι ι (RatFunc (ZMod p)))+A.map (res p))
      (B.map (res p)) (E.map (res p)) (D.map (res p)) := by
    apply Matrix.ext; intro i j
    rcases i with i|i <;> rcases j with j|j
    · by_cases hij : i=j <;> simp [Q,Matrix.one_apply,hij,map_add,map_mul,hs]
    · simp [Q]
    · simp [Q]
    · simp [Q]
  rw [RingHom.map_det (R:=GaussLoc p) (S:=RatFunc (ZMod p))]
  change (Q.map (res p)).det≠0
  rw [hm]
  apply spectral_det_ne
  · intro i j; exact hA i j
  · intro i j; exact hB i j
  · intro i j; exact hE i j
  · intro i j; exact hDc i j
  · change ((res p).mapMatrix D).det≠0
    rw [← RingHom.map_det (R:=GaussLoc p) (S:=RatFunc (ZMod p))]
    exact hD

end CatalanCore.Uniform.Content.UFSimple.WrapConstantMatrix
