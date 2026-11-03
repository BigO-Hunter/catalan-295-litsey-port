module

public import CatalanMeasure.GenD.Signed.Davis.InverseImageWeights

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial CatalanMeasure.Parametric
noncomputable section

def inverseQuadratureLevel (P : Parameters) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    Fin ((P.n0 - P.g0) * N) → Fin (inverseImageDegree ((P.n0 - P.g0) * N) m) :=
  let J := (P.n0 - P.g0) * N
  let K := inverseImageDegree J m
  fun i => ((finProdFinEquiv : Fin K × Fin m ≃ Fin (K * m)).symm
    (Fin.cast (inverseImageCount_split J hm) (Fin.castAdd (K * m - J) i))).1

theorem inverseQuadratureNodes_eval_level (P : Parameters)
    {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hm : 0 < m) (N : ℕ)
    (i : Fin ((P.n0 - P.g0) * N)) :
    p.eval (inverseQuadratureNodes P cert hm N i) =
      CatalanMeasure.chebX (inverseImageDegree ((P.n0 - P.g0) * N) m)
        (inverseQuadratureLevel P hm N i) := by
  unfold inverseQuadratureNodes retainedNodes paddedInverseNodes inverseImageNodes inverseQuadratureLevel
  exact inverseImageNodePair_eval cert _ _

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.inverseQuadratureLevel
#print axioms CatalanMeasure.GenD.Analytic.inverseQuadratureNodes_eval_level
