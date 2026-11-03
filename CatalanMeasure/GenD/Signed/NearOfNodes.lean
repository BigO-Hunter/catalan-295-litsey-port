module
public import CatalanMeasure.GenD.Signed.NodeGeometry
public import CatalanMeasure.GenD.Signed.Phase2Contract
public import CatalanMeasure.GenD.Signed.DecayOfData

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Assembly.Generic
open Set Filter Polynomial
open CatalanMeasure.Signed CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

/-- Actual-node near-sheet adapter. Every structural identification is explicit;
the cap is eventual and the same tau is used in the node predicate and geometry. -/
theorem hnear_nodes (dc : CatalanMeasure.GenD.Signed.DesignConst) (I : ℕ)
    (H : NodeGeometryData dc) (D : Phase2DataAsym I H.gsN)
    (hgs : D.gs = H.gsP) (hxc : D.xc = H.xc) (hC1 : D.C1 = H.C1)
    (humin : ∀ N, D.umin N = H.umin N)
    {target0 c2 target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (hn : ∀ N, D.ncount N = dc.toParameters.n N)
    (hconst : ∀ N r a b, r + a + b = dc.toParameters.n N →
      D.constant N (((a + b : ℕ) : ℝ) / (dc.toParameters.n N : ℝ)) =
        groupedConstant dc.toParameters N r a b)
    (hRf : ∀ N, D.Rf N = populationPhysicalFreeField dc.toParameters N)
    (hRm : ∀ N, D.Rm N = groupedMarkedField dc.toParameters N)
    (hRn : ∀ N, D.Rn N = groupedNearField dc.toParameters N)
    (hCf : ∀ N, D.Cf N = populationPhysicalColumnField dc.toParameters N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', D.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - dc.toParameters.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : D.B = -target0 + Real.log 2 / 2)
    (hcost : D.cost * (dc.n0 : ℝ) ≤ c2)
    (D0 : SecondTrialBoundsEnd dc.toParameters 0 target residual nearCap cost G)
    {δ e : ℝ} (hδ : 0 < δ) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < δ / 2)
    (L : LinkCert D dc.toParameters target residual nearCap cost G D0 δ e target0 c2) :
    FreeNearBound dc.toParameters G (NodeSub H.tau) target0 c2 D.α1 := by
  refine Phase2DataCore.signedSecondSheetNearNd_nearOpt_of_cert D dc.admissible G target0 c2
    hn hconst hRf hRm hRn hCf hLRf hB hcost (NodeSub H.tau) ?_ ?_ ?_ D0 hδ he hec L
  · exact H.gsN_pos.le
  · rw [hgs]
    exact H.gsP_pos.le
  · filter_upwards [H.marked_cap] with N hN m y hy hsub
    have h := hN m y hy hsub
    simpa only [hgs, hxc, hC1, humin N, hn N, Parameters.n, Option.getD_some] using h

end
end CatalanMeasure.GenD.Signed.Data.Assembly.Generic
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hnear_nodes
