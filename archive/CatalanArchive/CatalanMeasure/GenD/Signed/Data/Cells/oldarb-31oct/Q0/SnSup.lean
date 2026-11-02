module

public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE000
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB001
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB002
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB003
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB004
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB005
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB006
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB007
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB008
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB009
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB010
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB011
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB012
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB013
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB014
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB015
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB016
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB017
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB018
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB019
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB020
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB021
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB022
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB023
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB024
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB025
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB026
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB027
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB028
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB029
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB030
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB031
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB032
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB033
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB034
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB035
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB036
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB037
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB038
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnB039
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SnE040

@[expose] public section

/-! **SN, alpha = 0.0: the sup statement.**  `fieldTower q0snFq ... x <= q0snT` on the open domain; `T = S - K` with S (design threshold, unlifted reference) = -1.740490366703, K = -18.914421678430 (NOTES-TRIAL; kappa_old = -18.914421677999). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set

theorem q0snGlue0 : ∀ x ∈ Icc ((q0snBd.getD 0 0 : ℚ) : ℝ) ((q0snBd.getD 1 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snE000Full x hx
theorem q0snGlue1 : ∀ x ∈ Icc ((q0snBd.getD 1 0 : ℚ) : ℝ) ((q0snBd.getD 2 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB001Bound x hx
theorem q0snGlue2 : ∀ x ∈ Icc ((q0snBd.getD 2 0 : ℚ) : ℝ) ((q0snBd.getD 3 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB002Bound x hx
theorem q0snGlue3 : ∀ x ∈ Icc ((q0snBd.getD 3 0 : ℚ) : ℝ) ((q0snBd.getD 4 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB003Bound x hx
theorem q0snGlue4 : ∀ x ∈ Icc ((q0snBd.getD 4 0 : ℚ) : ℝ) ((q0snBd.getD 5 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB004Bound x hx
theorem q0snGlue5 : ∀ x ∈ Icc ((q0snBd.getD 5 0 : ℚ) : ℝ) ((q0snBd.getD 6 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB005Bound x hx
theorem q0snGlue6 : ∀ x ∈ Icc ((q0snBd.getD 6 0 : ℚ) : ℝ) ((q0snBd.getD 7 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB006Bound x hx
theorem q0snGlue7 : ∀ x ∈ Icc ((q0snBd.getD 7 0 : ℚ) : ℝ) ((q0snBd.getD 8 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB007Bound x hx
theorem q0snGlue8 : ∀ x ∈ Icc ((q0snBd.getD 8 0 : ℚ) : ℝ) ((q0snBd.getD 9 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB008Bound x hx
theorem q0snGlue9 : ∀ x ∈ Icc ((q0snBd.getD 9 0 : ℚ) : ℝ) ((q0snBd.getD 10 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB009Bound x hx
theorem q0snGlue10 : ∀ x ∈ Icc ((q0snBd.getD 10 0 : ℚ) : ℝ) ((q0snBd.getD 11 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB010Bound x hx
theorem q0snGlue11 : ∀ x ∈ Icc ((q0snBd.getD 11 0 : ℚ) : ℝ) ((q0snBd.getD 12 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB011Bound x hx
theorem q0snGlue12 : ∀ x ∈ Icc ((q0snBd.getD 12 0 : ℚ) : ℝ) ((q0snBd.getD 13 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB012Bound x hx
theorem q0snGlue13 : ∀ x ∈ Icc ((q0snBd.getD 13 0 : ℚ) : ℝ) ((q0snBd.getD 14 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB013Bound x hx
theorem q0snGlue14 : ∀ x ∈ Icc ((q0snBd.getD 14 0 : ℚ) : ℝ) ((q0snBd.getD 15 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB014Bound x hx
theorem q0snGlue15 : ∀ x ∈ Icc ((q0snBd.getD 15 0 : ℚ) : ℝ) ((q0snBd.getD 16 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB015Bound x hx
theorem q0snGlue16 : ∀ x ∈ Icc ((q0snBd.getD 16 0 : ℚ) : ℝ) ((q0snBd.getD 17 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB016Bound x hx
theorem q0snGlue17 : ∀ x ∈ Icc ((q0snBd.getD 17 0 : ℚ) : ℝ) ((q0snBd.getD 18 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB017Bound x hx
theorem q0snGlue18 : ∀ x ∈ Icc ((q0snBd.getD 18 0 : ℚ) : ℝ) ((q0snBd.getD 19 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB018Bound x hx
theorem q0snGlue19 : ∀ x ∈ Icc ((q0snBd.getD 19 0 : ℚ) : ℝ) ((q0snBd.getD 20 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB019Bound x hx
theorem q0snGlue20 : ∀ x ∈ Icc ((q0snBd.getD 20 0 : ℚ) : ℝ) ((q0snBd.getD 21 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB020Bound x hx
theorem q0snGlue21 : ∀ x ∈ Icc ((q0snBd.getD 21 0 : ℚ) : ℝ) ((q0snBd.getD 22 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB021Bound x hx
theorem q0snGlue22 : ∀ x ∈ Icc ((q0snBd.getD 22 0 : ℚ) : ℝ) ((q0snBd.getD 23 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB022Bound x hx
theorem q0snGlue23 : ∀ x ∈ Icc ((q0snBd.getD 23 0 : ℚ) : ℝ) ((q0snBd.getD 24 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB023Bound x hx
theorem q0snGlue24 : ∀ x ∈ Icc ((q0snBd.getD 24 0 : ℚ) : ℝ) ((q0snBd.getD 25 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB024Bound x hx
theorem q0snGlue25 : ∀ x ∈ Icc ((q0snBd.getD 25 0 : ℚ) : ℝ) ((q0snBd.getD 26 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB025Bound x hx
theorem q0snGlue26 : ∀ x ∈ Icc ((q0snBd.getD 26 0 : ℚ) : ℝ) ((q0snBd.getD 27 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB026Bound x hx
theorem q0snGlue27 : ∀ x ∈ Icc ((q0snBd.getD 27 0 : ℚ) : ℝ) ((q0snBd.getD 28 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB027Bound x hx
theorem q0snGlue28 : ∀ x ∈ Icc ((q0snBd.getD 28 0 : ℚ) : ℝ) ((q0snBd.getD 29 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB028Bound x hx
theorem q0snGlue29 : ∀ x ∈ Icc ((q0snBd.getD 29 0 : ℚ) : ℝ) ((q0snBd.getD 30 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB029Bound x hx
theorem q0snGlue30 : ∀ x ∈ Icc ((q0snBd.getD 30 0 : ℚ) : ℝ) ((q0snBd.getD 31 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB030Bound x hx
theorem q0snGlue31 : ∀ x ∈ Icc ((q0snBd.getD 31 0 : ℚ) : ℝ) ((q0snBd.getD 32 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB031Bound x hx
theorem q0snGlue32 : ∀ x ∈ Icc ((q0snBd.getD 32 0 : ℚ) : ℝ) ((q0snBd.getD 33 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB032Bound x hx
theorem q0snGlue33 : ∀ x ∈ Icc ((q0snBd.getD 33 0 : ℚ) : ℝ) ((q0snBd.getD 34 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB033Bound x hx
theorem q0snGlue34 : ∀ x ∈ Icc ((q0snBd.getD 34 0 : ℚ) : ℝ) ((q0snBd.getD 35 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB034Bound x hx
theorem q0snGlue35 : ∀ x ∈ Icc ((q0snBd.getD 35 0 : ℚ) : ℝ) ((q0snBd.getD 36 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB035Bound x hx
theorem q0snGlue36 : ∀ x ∈ Icc ((q0snBd.getD 36 0 : ℚ) : ℝ) ((q0snBd.getD 37 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB036Bound x hx
theorem q0snGlue37 : ∀ x ∈ Icc ((q0snBd.getD 37 0 : ℚ) : ℝ) ((q0snBd.getD 38 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB037Bound x hx
theorem q0snGlue38 : ∀ x ∈ Icc ((q0snBd.getD 38 0 : ℚ) : ℝ) ((q0snBd.getD 39 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB038Bound x hx
theorem q0snGlue39 : ∀ x ∈ Icc ((q0snBd.getD 39 0 : ℚ) : ℝ) ((q0snBd.getD 40 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx _ _ => q0snB039Bound x hx
theorem q0snGlue40 : ∀ x ∈ Icc ((q0snBd.getD 40 0 : ℚ) : ℝ) ((q0snBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx hA hB => q0snE040Unif x hx (by rw [q0snE040Eq]; exact hB)
theorem q0snGlueAll : ∀ x ∈ Icc ((q0snBd.getD 0 0 : ℚ) : ℝ) ((q0snBd.getD 41 0 : ℚ) : ℝ), x ≠ ((q0snBd.getD 0 0 : ℚ) : ℝ) → x ≠ ((q0snBd.getD 41 0 : ℚ) : ℝ) → fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (cover_union (q0snGlue0) q0snGlue1) q0snGlue2) q0snGlue3) q0snGlue4) q0snGlue5) q0snGlue6) q0snGlue7) q0snGlue8) q0snGlue9) q0snGlue10) q0snGlue11) q0snGlue12) q0snGlue13) q0snGlue14) q0snGlue15) q0snGlue16) q0snGlue17) q0snGlue18) q0snGlue19) q0snGlue20) q0snGlue21) q0snGlue22) q0snGlue23) q0snGlue24) q0snGlue25) q0snGlue26) q0snGlue27) q0snGlue28) q0snGlue29) q0snGlue30) q0snGlue31) q0snGlue32) q0snGlue33) q0snGlue34) q0snGlue35) q0snGlue36) q0snGlue37) q0snGlue38) q0snGlue39) q0snGlue40
/-- **Sup statement (SN, alpha = 0.0).** -/
theorem q0snSup : ∀ x ∈ Ioo ((q0snBd.getD 0 0 : ℚ) : ℝ) ((q0snBd.getD 41 0 : ℚ) : ℝ), fieldTower q0snFq (poleF q0snFq.poles) 0 x ≤ (q0snT : ℝ) :=
  fun x hx => q0snGlueAll x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne

end CatalanMeasure.GenD.Signed.Data.Cells
