module

public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE000
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB001
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB002
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB003
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB004
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB005
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB006
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB007
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB008
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB009
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB010
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB011
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB012
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB013
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB014
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB015
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB016
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB017
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB018
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB019
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB020
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB021
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB022
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB023
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB024
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB025
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB026
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB027
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB028
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB029
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB030
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB031
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB032
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB033
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB034
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB035
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB036
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB037
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB038
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB039
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB040
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB041
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB042
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB043
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB044
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB045
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB046
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB047
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB048
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB049
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB050
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE051
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB052
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB053
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB054
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB055
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB056
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB057
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB058
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB059
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB060
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB061
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB062
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB063
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnB064
public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.SnE065

@[expose] public section

/-! **SN, alpha = 0.005: the sup statement.**  `fieldTower q1snFq ... x <= q1snT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.823997049276, K = -18.926240533312 (NOTES-TRIAL; kappa_old = -18.926240532999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set

theorem q1snGlue0 : ∀ x ∈ Icc ((q1snBd.getD 0 0 : ℚ) : ℝ) ((q1snBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE000Full x hx
theorem q1snGlue1 : ∀ x ∈ Icc ((q1snBd.getD 1 0 : ℚ) : ℝ) ((q1snBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB001Bound x hx
theorem q1snGlue2 : ∀ x ∈ Icc ((q1snBd.getD 2 0 : ℚ) : ℝ) ((q1snBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB002Bound x hx
theorem q1snGlue3 : ∀ x ∈ Icc ((q1snBd.getD 3 0 : ℚ) : ℝ) ((q1snBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB003Bound x hx
theorem q1snGlue4 : ∀ x ∈ Icc ((q1snBd.getD 4 0 : ℚ) : ℝ) ((q1snBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB004Bound x hx
theorem q1snGlue5 : ∀ x ∈ Icc ((q1snBd.getD 5 0 : ℚ) : ℝ) ((q1snBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB005Bound x hx
theorem q1snGlue6 : ∀ x ∈ Icc ((q1snBd.getD 6 0 : ℚ) : ℝ) ((q1snBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB006Bound x hx
theorem q1snGlue7 : ∀ x ∈ Icc ((q1snBd.getD 7 0 : ℚ) : ℝ) ((q1snBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB007Bound x hx
theorem q1snGlue8 : ∀ x ∈ Icc ((q1snBd.getD 8 0 : ℚ) : ℝ) ((q1snBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB008Bound x hx
theorem q1snGlue9 : ∀ x ∈ Icc ((q1snBd.getD 9 0 : ℚ) : ℝ) ((q1snBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB009Bound x hx
theorem q1snGlue10 : ∀ x ∈ Icc ((q1snBd.getD 10 0 : ℚ) : ℝ) ((q1snBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB010Bound x hx
theorem q1snGlue11 : ∀ x ∈ Icc ((q1snBd.getD 11 0 : ℚ) : ℝ) ((q1snBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB011Bound x hx
theorem q1snGlue12 : ∀ x ∈ Icc ((q1snBd.getD 12 0 : ℚ) : ℝ) ((q1snBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB012Bound x hx
theorem q1snGlue13 : ∀ x ∈ Icc ((q1snBd.getD 13 0 : ℚ) : ℝ) ((q1snBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB013Bound x hx
theorem q1snGlue14 : ∀ x ∈ Icc ((q1snBd.getD 14 0 : ℚ) : ℝ) ((q1snBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB014Bound x hx
theorem q1snGlue15 : ∀ x ∈ Icc ((q1snBd.getD 15 0 : ℚ) : ℝ) ((q1snBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB015Bound x hx
theorem q1snGlue16 : ∀ x ∈ Icc ((q1snBd.getD 16 0 : ℚ) : ℝ) ((q1snBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB016Bound x hx
theorem q1snGlue17 : ∀ x ∈ Icc ((q1snBd.getD 17 0 : ℚ) : ℝ) ((q1snBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB017Bound x hx
theorem q1snGlue18 : ∀ x ∈ Icc ((q1snBd.getD 18 0 : ℚ) : ℝ) ((q1snBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB018Bound x hx
theorem q1snGlue19 : ∀ x ∈ Icc ((q1snBd.getD 19 0 : ℚ) : ℝ) ((q1snBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB019Bound x hx
theorem q1snGlue20 : ∀ x ∈ Icc ((q1snBd.getD 20 0 : ℚ) : ℝ) ((q1snBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB020Bound x hx
theorem q1snGlue21 : ∀ x ∈ Icc ((q1snBd.getD 21 0 : ℚ) : ℝ) ((q1snBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB021Bound x hx
theorem q1snGlue22 : ∀ x ∈ Icc ((q1snBd.getD 22 0 : ℚ) : ℝ) ((q1snBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB022Bound x hx
theorem q1snGlue23 : ∀ x ∈ Icc ((q1snBd.getD 23 0 : ℚ) : ℝ) ((q1snBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB023Bound x hx
theorem q1snGlue24 : ∀ x ∈ Icc ((q1snBd.getD 24 0 : ℚ) : ℝ) ((q1snBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB024Bound x hx
theorem q1snGlue25 : ∀ x ∈ Icc ((q1snBd.getD 25 0 : ℚ) : ℝ) ((q1snBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB025Bound x hx
theorem q1snGlue26 : ∀ x ∈ Icc ((q1snBd.getD 26 0 : ℚ) : ℝ) ((q1snBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB026Bound x hx
theorem q1snGlue27 : ∀ x ∈ Icc ((q1snBd.getD 27 0 : ℚ) : ℝ) ((q1snBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB027Bound x hx
theorem q1snGlue28 : ∀ x ∈ Icc ((q1snBd.getD 28 0 : ℚ) : ℝ) ((q1snBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB028Bound x hx
theorem q1snGlue29 : ∀ x ∈ Icc ((q1snBd.getD 29 0 : ℚ) : ℝ) ((q1snBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB029Bound x hx
theorem q1snGlue30 : ∀ x ∈ Icc ((q1snBd.getD 30 0 : ℚ) : ℝ) ((q1snBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB030Bound x hx
theorem q1snGlue31 : ∀ x ∈ Icc ((q1snBd.getD 31 0 : ℚ) : ℝ) ((q1snBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB031Bound x hx
theorem q1snGlue32 : ∀ x ∈ Icc ((q1snBd.getD 32 0 : ℚ) : ℝ) ((q1snBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB032Bound x hx
theorem q1snGlue33 : ∀ x ∈ Icc ((q1snBd.getD 33 0 : ℚ) : ℝ) ((q1snBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB033Bound x hx
theorem q1snGlue34 : ∀ x ∈ Icc ((q1snBd.getD 34 0 : ℚ) : ℝ) ((q1snBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB034Bound x hx
theorem q1snGlue35 : ∀ x ∈ Icc ((q1snBd.getD 35 0 : ℚ) : ℝ) ((q1snBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB035Bound x hx
theorem q1snGlue36 : ∀ x ∈ Icc ((q1snBd.getD 36 0 : ℚ) : ℝ) ((q1snBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB036Bound x hx
theorem q1snGlue37 : ∀ x ∈ Icc ((q1snBd.getD 37 0 : ℚ) : ℝ) ((q1snBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB037Bound x hx
theorem q1snGlue38 : ∀ x ∈ Icc ((q1snBd.getD 38 0 : ℚ) : ℝ) ((q1snBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB038Bound x hx
theorem q1snGlue39 : ∀ x ∈ Icc ((q1snBd.getD 39 0 : ℚ) : ℝ) ((q1snBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB039Bound x hx
theorem q1snGlue40 : ∀ x ∈ Icc ((q1snBd.getD 40 0 : ℚ) : ℝ) ((q1snBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB040Bound x hx
theorem q1snGlue41 : ∀ x ∈ Icc ((q1snBd.getD 41 0 : ℚ) : ℝ) ((q1snBd.getD 42 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB041Bound x hx
theorem q1snGlue42 : ∀ x ∈ Icc ((q1snBd.getD 42 0 : ℚ) : ℝ) ((q1snBd.getD 43 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB042Bound x hx
theorem q1snGlue43 : ∀ x ∈ Icc ((q1snBd.getD 43 0 : ℚ) : ℝ) ((q1snBd.getD 44 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB043Bound x hx
theorem q1snGlue44 : ∀ x ∈ Icc ((q1snBd.getD 44 0 : ℚ) : ℝ) ((q1snBd.getD 45 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB044Bound x hx
theorem q1snGlue45 : ∀ x ∈ Icc ((q1snBd.getD 45 0 : ℚ) : ℝ) ((q1snBd.getD 46 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB045Bound x hx
theorem q1snGlue46 : ∀ x ∈ Icc ((q1snBd.getD 46 0 : ℚ) : ℝ) ((q1snBd.getD 47 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB046Bound x hx
theorem q1snGlue47 : ∀ x ∈ Icc ((q1snBd.getD 47 0 : ℚ) : ℝ) ((q1snBd.getD 48 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB047Bound x hx
theorem q1snGlue48 : ∀ x ∈ Icc ((q1snBd.getD 48 0 : ℚ) : ℝ) ((q1snBd.getD 49 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB048Bound x hx
theorem q1snGlue49 : ∀ x ∈ Icc ((q1snBd.getD 49 0 : ℚ) : ℝ) ((q1snBd.getD 50 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB049Bound x hx
theorem q1snGlue50 : ∀ x ∈ Icc ((q1snBd.getD 50 0 : ℚ) : ℝ) ((q1snBd.getD 51 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB050Bound x hx
theorem q1snGlue51 : ∀ x ∈ Icc ((q1snBd.getD 51 0 : ℚ) : ℝ) ((q1snBd.getD 52 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snE051Full x hx
theorem q1snGlue52 : ∀ x ∈ Icc ((q1snBd.getD 52 0 : ℚ) : ℝ) ((q1snBd.getD 53 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB052Bound x hx
theorem q1snGlue53 : ∀ x ∈ Icc ((q1snBd.getD 53 0 : ℚ) : ℝ) ((q1snBd.getD 54 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB053Bound x hx
theorem q1snGlue54 : ∀ x ∈ Icc ((q1snBd.getD 54 0 : ℚ) : ℝ) ((q1snBd.getD 55 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB054Bound x hx
theorem q1snGlue55 : ∀ x ∈ Icc ((q1snBd.getD 55 0 : ℚ) : ℝ) ((q1snBd.getD 56 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB055Bound x hx
theorem q1snGlue56 : ∀ x ∈ Icc ((q1snBd.getD 56 0 : ℚ) : ℝ) ((q1snBd.getD 57 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB056Bound x hx
theorem q1snGlue57 : ∀ x ∈ Icc ((q1snBd.getD 57 0 : ℚ) : ℝ) ((q1snBd.getD 58 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB057Bound x hx
theorem q1snGlue58 : ∀ x ∈ Icc ((q1snBd.getD 58 0 : ℚ) : ℝ) ((q1snBd.getD 59 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB058Bound x hx
theorem q1snGlue59 : ∀ x ∈ Icc ((q1snBd.getD 59 0 : ℚ) : ℝ) ((q1snBd.getD 60 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB059Bound x hx
theorem q1snGlue60 : ∀ x ∈ Icc ((q1snBd.getD 60 0 : ℚ) : ℝ) ((q1snBd.getD 61 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB060Bound x hx
theorem q1snGlue61 : ∀ x ∈ Icc ((q1snBd.getD 61 0 : ℚ) : ℝ) ((q1snBd.getD 62 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB061Bound x hx
theorem q1snGlue62 : ∀ x ∈ Icc ((q1snBd.getD 62 0 : ℚ) : ℝ) ((q1snBd.getD 63 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB062Bound x hx
theorem q1snGlue63 : ∀ x ∈ Icc ((q1snBd.getD 63 0 : ℚ) : ℝ) ((q1snBd.getD 64 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB063Bound x hx
theorem q1snGlue64 : ∀ x ∈ Icc ((q1snBd.getD 64 0 : ℚ) : ℝ) ((q1snBd.getD 65 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx _ _ => q1snB064Bound x hx
theorem q1snGlue65 : ∀ x ∈ Icc ((q1snBd.getD 65 0 : ℚ) : ℝ) ((q1snBd.getD 66 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx hA hB => q1snE065Unif x hx (by rw [q1snE065Eq]; exact hB)
theorem q1snGlueAll : ∀ x ∈ Icc ((q1snBd.getD 0 0 : ℚ) : ℝ) ((q1snBd.getD 66 0 : ℚ) : ℝ), x ≠ ((q1snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q1snBd.getD 66 0 : ℚ) : ℝ) → fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q1snGlue0) q1snGlue1) q1snGlue2) q1snGlue3) q1snGlue4) q1snGlue5) q1snGlue6) q1snGlue7) q1snGlue8) q1snGlue9) q1snGlue10) q1snGlue11) q1snGlue12) q1snGlue13) q1snGlue14) q1snGlue15) q1snGlue16) q1snGlue17) q1snGlue18) q1snGlue19) q1snGlue20) q1snGlue21) q1snGlue22) q1snGlue23) q1snGlue24) q1snGlue25) q1snGlue26) q1snGlue27) q1snGlue28) q1snGlue29) q1snGlue30) q1snGlue31) q1snGlue32) q1snGlue33) q1snGlue34) q1snGlue35) q1snGlue36) q1snGlue37) q1snGlue38) q1snGlue39) q1snGlue40) q1snGlue41) q1snGlue42) q1snGlue43) q1snGlue44) q1snGlue45) q1snGlue46) q1snGlue47) q1snGlue48) q1snGlue49) q1snGlue50) q1snGlue51) q1snGlue52) q1snGlue53) q1snGlue54) q1snGlue55) q1snGlue56) q1snGlue57) q1snGlue58) q1snGlue59) q1snGlue60) q1snGlue61) q1snGlue62) q1snGlue63) q1snGlue64) q1snGlue65
/-- **Sup statement (SN, alpha = 0.005).** -/
theorem q1snSup : ∀ x ∈ Ioo ((q1snBd.getD 0 0 : ℚ) : ℝ) ((q1snBd.getD 66 0 : ℚ) : ℝ), fieldTower q1snFq (poleF q1snFq.poles) 0 x ≤ (q1snT : ℝ) :=
  fun x hx => q1snGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
