module

public import CatalanCore.Uniform.Content.UFSimple.WrapOriginalEntry
public import CatalanCore.Uniform.Content.UFSimple.WrapConstant

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapFrameResidue

variable (p : ℕ) [Fact p.Prime]

theorem embed (a : LocRing p) :
    res p (WrapOriginalLoad.embed p a)=
      Uniform.Content.Hybrid.rfH p (redQ p a) := by
  change res p (algebraMap (LocRing p)[X] (GaussLoc p) (Polynomial.C a))=_
  rw [res_algebraMap,phiP_C]
  rfl

/-- The original frame normalization is a nonzero constant residue. -/
theorem normInv {Fr : Frame} {N : ℕ} (D : PoleData Fr p N) :
    res p (WrapOriginalEntry.normInv p Fr)=
      Uniform.Content.Hybrid.rfH p ((red p Fr.norm)⁻¹) := by
  unfold WrapOriginalEntry.normInv
  rw [embed,Uniform.Content.Hybrid.redQ_liftQ ((good_red D.norm_mem).inv D.norm_ne)]

theorem normInv_constant {Fr : Frame} {N : ℕ} (D : PoleData Fr p N) :
    WrapConstant.Has p (WrapOriginalEntry.normInv p Fr) :=
  ⟨(red p Fr.norm)⁻¹,normInv p D⟩

theorem normInv_ne {Fr : Frame} {N : ℕ} (D : PoleData Fr p N) :
    res p (WrapOriginalEntry.normInv p Fr)≠0 := by
  rw [normInv p D]
  intro hz
  have hzero : (red p Fr.norm)⁻¹=0 :=
    Uniform.Content.Hybrid.rfH_injective (by simpa only [map_zero] using hz)
  exact inv_ne_zero D.norm_ne hzero

/-- The common-node spectral diagonal is the original spectral variable. -/
theorem spectral : res p (algebraMap (LocRing p)[X] (GaussLoc p) Polynomial.X)=
    (RatFunc.X:RatFunc (ZMod p)) := by
  rw [res_algebraMap,phiP_X]
  rfl

end CatalanCore.Uniform.Content.UFSimple.WrapFrameResidue
