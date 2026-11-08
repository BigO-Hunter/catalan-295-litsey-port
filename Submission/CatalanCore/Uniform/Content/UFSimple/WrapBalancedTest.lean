module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapOwnEntry
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapHarmonicMap
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapScale
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapUnits

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapBalancedTest

variable (p : ℕ) [Fact p.Prime]

noncomputable def det_relation {τ : Type*} [Fintype τ] [DecidableEq τ] :=
  WrapEvaluation.determinant (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p) (ι:=τ)
noncomputable def transfer := @WrapEvaluation.Rel.residue_ne (GaussLoc p) (RatFunc (ZMod p))
  _ _ _ (res p)
noncomputable def unit_ne :=
  WrapUnits.of_residue_ne (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)


end CatalanCore.Uniform.Content.UFSimple.WrapBalancedTest
