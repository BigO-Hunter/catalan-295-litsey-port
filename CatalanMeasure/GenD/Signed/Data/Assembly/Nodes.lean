module

public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.Glue410
public import CatalanMeasure.GenD.Signed.MarkedCap
public import CatalanMeasure.GenD.Signed.Data.S1.Gap
public import CatalanMeasure.GenD.Analytic.GapWeights
public import CatalanMeasure.GenD.DesignInstance.OddProfile

@[expose] public section

/-!
# 410 assembly, row P4: the cap data of the real marked nodes

The marked rows of the near-type sheet bound are `realCoordinate` images of distinct nodes
`τ N a`, `τ := gapNodesD Odd.design aGap` (gap `g = 401/2500`, `J = 53 N` nodes, `n = 58 N`).
* `nodeCap_real`: `NodeCap g xc C1 n umin` of `realCoordinate ∘ τ N` with the 410 constants
  `gs = 401/2500`, `xc = 999/1000`, `C1 = 9631/20000`, `umin N = √(1-a²)/(106 N + 2)`
  (from `nodeCap_gap` and `Glue410.nodeCap_gap_mono`, `gap_C1_le`).
* `markedCap_real`: `MarkedCap` of every `NodeSub τ` row set with `y ∈ (-1, 1)` (all `N`; for `N = 0` the
  node set is empty).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter
open CatalanMeasure.Signed CatalanMeasure.GenD.Analytic OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.S1

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

theorem nodeCap_real (C1 : ℝ)
    (hC : (dc.d0 : ℝ) / ((dc.n0 : ℝ) *
      (2 * (dc.xc : ℝ) * Real.sqrt (1 - (dc.astar : ℝ) ^ 2))) ≤ C1)
    {N : ℕ} (hN : 0 < N) :
    NodeCap (dc.gstar : ℝ) (dc.xc : ℝ) C1 ((dc.n0 : ℝ) * N) (umin dc N)
      (fun i => realCoordinate (nodesτ dc N i)) := by
  have hg0 : (0 : ℝ) < dc.gstar := by exact_mod_cast dc.gstar_mem.1
  have hg1 : (dc.gstar : ℝ) < 1 := by exact_mod_cast dc.gstar_mem.2
  have hxc : (0 : ℝ) < dc.xc := by exact_mod_cast dc.xc_mem.1
  have hn0 : (0 : ℝ) < dc.n0 := by exact_mod_cast dc.n0_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Glue410.nodeCap_gap_mono hg0 hg1 hxc (mul_pos hn0 hNr) (dc.d0 * N)
    (gs' := (dc.gstar : ℝ)) (xc' := (dc.xc : ℝ)) (C1' := C1) (umin' := umin dc N)
    le_rfl le_rfl
    (Glue410.Generic.gap_C1_le dc hN (cast_nodes dc N) rfl rfl (astar_eq dc).symm hC)
    (by rw [← astar_eq dc]; exact le_rfl)
  rw [← astar_eq dc] at h
  exact h

theorem markedCap_real (C1 : ℝ)
    (hC : (dc.d0 : ℝ) / ((dc.n0 : ℝ) *
      (2 * (dc.xc : ℝ) * Real.sqrt (1 - (dc.astar : ℝ) ^ 2))) ≤ C1)
    (N : ℕ) {m : ℕ} {y : Fin m → ℝ} (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (h : NodeSub (nodesτ dc) N m y) :
    MarkedCap (dc.gstar : ℝ) (dc.xc : ℝ) C1 ((dc.n0 : ℝ) * N) (umin dc N) y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨a, _, _⟩ := h
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩ <;>
      exact absurd (a j).isLt (by simp)
  · exact markedCap_of_nodeSub (nodeCap_real dc C1 hC hN) hy h

end Generic

/-- The gap nodes of the 410 design. -/
abbrev nodesτ : (N : ℕ) → Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N) → ℝ :=
  gapNodesD D58.Odd.design aGap

/-- The distance of the nodes from `1`: `umin N = √(1-a²) / (2 (53 N + 1))`. -/
def umin410 (N : ℕ) : ℝ := Real.sqrt (1 - aGap ^ 2) / (106 * (N : ℝ) + 2)

theorem one_sub_aGap_sq_pos : 0 < 1 - aGap ^ 2 := by
  have h0 := aGap_pos
  have h1 := aGap_lt_one
  nlinarith

theorem umin410_pos (N : ℕ) : 0 < umin410 N := by
  unfold umin410
  have := Real.sqrt_pos.2 one_sub_aGap_sq_pos
  positivity

theorem umin410_le_one (N : ℕ) : umin410 N ≤ 1 := by
  unfold umin410
  have hs : Real.sqrt (1 - aGap ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith [aGap_pos, sq_nonneg aGap]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [div_le_one (by positivity)]
  linarith

theorem cast_nodes (N : ℕ) :
    (((D58.Odd.design.n0 - D58.Odd.design.g0) * N : ℕ) : ℝ) = 53 * (N : ℝ) := by
  norm_num [D58.Odd.design]

/-- **`NodeCap` of the real nodes** (`N ≥ 1`). -/
theorem nodeCap_real {N : ℕ} (hN : 0 < N) :
    NodeCap (401 / 2500) (999 / 1000) (9631 / 20000) (58 * (N : ℝ)) (umin410 N)
      (fun i => realCoordinate (nodesτ N i))  := by
  have hC : (CatalanMeasure.GenD.Signed.dc58.d0 : ℝ) / ((CatalanMeasure.GenD.Signed.dc58.n0 : ℝ) *
      (2 * (CatalanMeasure.GenD.Signed.dc58.xc : ℝ) * Real.sqrt (1 - (CatalanMeasure.GenD.Signed.dc58.astar : ℝ) ^ 2))) ≤ 9631 / 20000 := by
    convert CatalanMeasure.Signed.Consts.C1_bound using 1 <;>
      norm_num [CatalanMeasure.GenD.Signed.dc58, CatalanMeasure.GenD.Signed.DesignConst.d0, CatalanMeasure.GenD.Signed.DesignConst.astar]
  have h := Generic.nodeCap_real CatalanMeasure.GenD.Signed.dc58 (9631 / 20000) hC hN
  convert h using 1 <;>
    norm_num [Generic.nodesτ, Generic.umin, nodesτ, umin410, aGap, aQ,
      CatalanMeasure.GenD.Signed.dc58, CatalanMeasure.GenD.Signed.DesignConst.d0, CatalanMeasure.GenD.Signed.DesignConst.astar,
      D58.Odd.design, mul_add, mul_assoc]
    <;> first | rfl | (congr 1 <;> ring)

/-- **`MarkedCap` of the actual marked rows** (every `N`). -/
theorem markedCap_real (N : ℕ) {m : ℕ} {y : Fin m → ℝ} (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (h : NodeSub nodesτ N m y) :
    MarkedCap (401 / 2500) (999 / 1000) (9631 / 20000) (58 * (N : ℝ)) (umin410 N) y := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨a, _, _⟩ := h
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩ <;>
      exact absurd (a j).isLt (by simp)
  · exact markedCap_of_nodeSub (nodeCap_real hN) hy h

end

end CatalanMeasure.GenD.Signed.Data.Assembly
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.nodeCap_real
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.markedCap_real

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.astar_eq
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.astar_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.astar_lt_one
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.one_sub_astar_sq_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.umin_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.umin_le_one
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.cast_nodes
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.nodeCap_real
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.markedCap_real
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.one_sub_aGap_sq_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.umin410_pos
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.umin410_le_one
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.cast_nodes
