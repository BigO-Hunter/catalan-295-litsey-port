module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Phase2
public import CatalanMeasure.GenD.Signed.Data.Assembly.Decay
public import CatalanMeasure.GenD.Signed.NearOfNodes

@[expose] public section

/-!
# 410 assembly: `FreeNearBound` from the Phase 2 data and the class link

`hnear410`: `Phase2Data.signedSecondSheetNearNd_nearOpt_of_cert` for `D := phase2 R`, with the node
predicate `Nd := NodeSub nodesτ` of the real gap nodes (`markedCap_real`).  The remaining inputs are
the second-population End trial `D0`, the damping data `δ, e` and the `LinkCert` term `L`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter
open CatalanMeasure.Signed OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic

open CatalanMeasure.GenD.D58

noncomputable section

namespace Generic

open CatalanMeasure.GenD.Signed

/-- Assemble the near sheet on the exact Phase2 family and design nodes. -/
theorem hnear (dc : DesignConst) (I : Inputs dc) (R : Rows dc I)
    {target residual nearCap cost c2 : ℝ} {G : ℝ → Prop}
    (D0 : SecondTrialBoundsEnd dc.toParameters 0 target residual nearCap cost G)
    {δ e : ℝ} (hδ : 0 < δ) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < δ / 2)
    (hcost : I.cost * (dc.n0 : ℝ) ≤ c2)
    (L : LinkCert (phase2 dc I R) dc.toParameters target residual nearCap cost G D0 δ e
      I.target c2) :
    FreeNearBound dc.toParameters G (NodeSub (nodesτ dc)) I.target c2 I.α1 := by
  refine Phase2Data.signedSecondSheetNearNd_nearOpt_of_cert (phase2 dc I R)
    dc.admissible G I.target c2
    (fun N => rfl)
    (fun N r a b h => Glue410.hconst_closed dc.admissible N r a b h)
    (fun N => rfl) (fun N => rfl) (fun N => rfl) (fun N => rfl)
    (fun N k q m1 m2' xn gp yn yp' => rfl) rfl hcost
    (NodeSub (nodesτ dc)) (fun N m y hy h => markedCap_inputs dc I N hy h)
    D0 hδ he hec L

/-- The concrete Rows factory feeds the same actual-node near bridge. -/
theorem hnear_asym (dc : DesignConst) (H : NodeGeometryData dc) (I : InputsAsym dc H)
    (R : RowsAsym dc H I) {target residual nearCap cost c2 : ℝ} {G : ℝ → Prop}
    (D0 : SecondTrialBoundsEnd dc.toParameters 0 target residual nearCap cost G)
    {δ e : ℝ} (hδ : 0 < δ) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < δ / 2)
    (hcost : I.cost * (dc.n0 : ℝ) ≤ c2)
    (L : LinkCert (phase2Asym dc H I R) dc.toParameters target residual nearCap cost G D0 δ e
      I.target c2) : FreeNearBound dc.toParameters G (NodeSub H.tau) I.target c2 I.α1 := by
  refine hnear_nodes dc 2 H (phase2Asym dc H I R) I.gs_eq I.xc_eq I.hC I.humin
    (fun N => rfl)
    (fun N r a b h => Glue410.hconst_closed dc.admissible N r a b h)
    (fun N => rfl) (fun N => rfl) (fun N => rfl) (fun N => rfl)
    (fun N k q m1 m2' xn gp yn yp' => rfl) rfl hcost D0 hδ he hec L

end Generic


theorem hnear410 (R : Rows410) {residual nearCap : ℝ}
    (D0 : SecondTrialBoundsEnd P410 0 K590.target residual nearCap K590.secondCost' G410)
    {δ e : ℝ} (hδ : 0 < δ) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    (hec : e * (4 * (∑' j, |D0.p j|) + 4 * (∑' j, |D0.v j|) + |D0.p 1| + 20) < δ / 2)
    (L : LinkCert (phase2 R) P410 K590.target residual nearCap K590.secondCost' G410 D0 δ e
      K590.target0 c2_410) :
    FreeNearBound P410 G410 (NodeSub nodesτ) K590.target0 c2_410 (1 / 16)  := by
  have ha : (dc58.astar : ℝ) = S1.aGap := by norm_num [S1.aGap, S1.aQ]
  have hnodes : Generic.nodesτ dc58 = nodesτ := by
    simp only [Generic.nodesτ, nodesτ, dc58_toParameters, D58.Odd.design, ha] <;> rfl
  have hNd : NodeSub (Generic.nodesτ dc58) = NodeSub nodesτ := by
    funext N m y
    simp only [NodeSub, Generic.nodesτ, nodesτ, dc58_d0, dc58_toParameters,
      D58.Odd.design, ha] <;> rfl
  have h := Generic.hnear dc58 inputs410 (Rows410.toGeneric R) D0 hδ he hec
    (by norm_num [inputs410, c2_410]; linarith) L
  have hP : dc58.toParameters = P410 := rfl
  have ht : inputs410.target = K590.target0 := rfl
  have hα : inputs410.α1 = (1 / 16 : ℝ) := rfl
  simpa only [hNd, hP, ht, hα] using h

end

end CatalanMeasure.GenD.Signed.Data.Assembly

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hnear
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.hnear410

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.hnear_asym
