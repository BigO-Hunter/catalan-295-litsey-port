module

public import Submission.CatalanMeasure.GenD.Signed.DesignConst
public import Submission.CatalanMeasure.GenD.Analytic.GapWeights
public import Submission.CatalanMeasure.GenD.Signed.MarkedCap

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Assembly
open Set Filter
open CatalanMeasure.GenD.Analytic OAI.InternalCatalan
noncomputable section
namespace Generic
variable (dc : CatalanMeasure.GenD.Signed.DesignConst)

abbrev nodesτ : (N : ℕ) → Fin (dc.d0 * N) → ℝ :=
  gapNodesD dc.toParameters (dc.astar : ℝ)

def umin (N : ℕ) : ℝ :=
  Real.sqrt (1 - (dc.astar : ℝ) ^ 2) / (2 * (((dc.d0 * N : ℕ) : ℝ) + 1))

theorem astar_eq : (dc.astar : ℝ) =
    2 * (dc.gstar : ℝ) / (1 + (dc.gstar : ℝ) ^ 2) := by
  norm_num [CatalanMeasure.GenD.Signed.DesignConst.astar]

theorem astar_pos : 0 < (dc.astar : ℝ) := by
  rw [astar_eq]
  have hg : (0 : ℝ) < dc.gstar := by exact_mod_cast dc.gstar_mem.1
  positivity

theorem astar_lt_one : (dc.astar : ℝ) < 1 := by
  rw [astar_eq]
  have hg : (dc.gstar : ℝ) < 1 := by exact_mod_cast dc.gstar_mem.2
  apply (div_lt_one (by positivity : (0 : ℝ) < 1 + (dc.gstar : ℝ) ^ 2)).mpr
  have hs := mul_pos (sub_pos.mpr hg) (sub_pos.mpr hg)
  nlinarith only [hs]

theorem one_sub_astar_sq_pos : 0 < 1 - (dc.astar : ℝ) ^ 2 := by
  have h0 := astar_pos dc
  have h1 := astar_lt_one dc
  have hp := mul_pos (sub_pos.mpr h1) (by linarith only [h0] : 0 < (dc.astar : ℝ) + 1)
  nlinarith only [hp]

theorem umin_pos (N : ℕ) : 0 < umin dc N := by
  unfold umin
  have := Real.sqrt_pos.2 (one_sub_astar_sq_pos dc)
  positivity

theorem umin_le_one (N : ℕ) : umin dc N ≤ 1 := by
  unfold umin
  have hs : Real.sqrt (1 - (dc.astar : ℝ) ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith only [sq_nonneg (dc.astar : ℝ)]
  have hN : (0 : ℝ) ≤ ((dc.d0 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [div_le_one (by positivity)]
  linarith only [hs, hN]

theorem cast_nodes (N : ℕ) : ((dc.d0 * N : ℕ) : ℝ) = (dc.d0 : ℝ) * N := by
  simp only [Nat.cast_mul]


/-- Actual node geometry, independent of the fitted trial-density break.
The cap is eventual: the Davis certificate starts at N>=10. -/
structure NodeGeometryData (dc : CatalanMeasure.GenD.Signed.DesignConst) where
  tau : (N : ℕ) → Fin (dc.d0 * N) → ℝ
  gsN : ℝ
  gsP : ℝ
  xc : ℝ
  C1 : ℝ
  umin : ℕ → ℝ
  gsN_pos : 0 < gsN
  gsP_pos : 0 < gsP
  umin_pos : ∀ N, 0 < umin N
  umin_le_one : ∀ N, umin N ≤ 1
  hlogu : Tendsto (fun N : ℕ => -Real.log (umin N) / ((dc.n0 * N : ℕ) : ℝ)) atTop (nhds 0)
  cap : ∀ᶠ N : ℕ in atTop,
    CatalanMeasure.Signed.NodeCapAsym gsN gsP xc C1 ((dc.n0 * N : ℕ) : ℝ) (umin N)
      (fun a => realCoordinate (tau N a))

def NodeGeometryData.support {dc : CatalanMeasure.GenD.Signed.DesignConst}
    (H : NodeGeometryData dc) : ℝ → Prop := fun x => x ≤ -H.gsN ∨ H.gsP ≤ x

theorem NodeGeometryData.marked_cap {dc : CatalanMeasure.GenD.Signed.DesignConst}
    (H : NodeGeometryData dc) : ∀ᶠ N : ℕ in atTop, ∀ m (y : Fin m → ℝ),
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → CatalanMeasure.Signed.NodeSub H.tau N m y →
      CatalanMeasure.Signed.MarkedCapAsym H.gsN H.gsP H.xc H.C1
        ((dc.n0 * N : ℕ) : ℝ) (H.umin N) y := by
  filter_upwards [H.cap] with N hN m y hy hsub
  exact CatalanMeasure.Signed.markedCapAsym_of_nodeSub hN hy hsub

end Generic
end
end CatalanMeasure.GenD.Signed.Data.Assembly
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.astar_eq
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.astar_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.astar_lt_one
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.one_sub_astar_sq_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.umin_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.umin_le_one
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.cast_nodes

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.NodeGeometryData.marked_cap
