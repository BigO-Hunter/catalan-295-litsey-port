module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColData
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 127 per-index declarations, each 2 Horner evals + keep test (X measured 0.31 s each)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColBr
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.ColInst
open CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep
theorem y_b0 : bracketOK csY (LsY.getD 0 0)=true ∧ (keepB csY fsY (LsY.getD 0 0)=false ∨ LsY.getD 0 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b1 : bracketOK csY (LsY.getD 1 0)=true ∧ (keepB csY fsY (LsY.getD 1 0)=false ∨ LsY.getD 1 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b2 : bracketOK csY (LsY.getD 2 0)=true ∧ (keepB csY fsY (LsY.getD 2 0)=false ∨ LsY.getD 2 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b3 : bracketOK csY (LsY.getD 3 0)=true ∧ (keepB csY fsY (LsY.getD 3 0)=false ∨ LsY.getD 3 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b4 : bracketOK csY (LsY.getD 4 0)=true ∧ (keepB csY fsY (LsY.getD 4 0)=false ∨ LsY.getD 4 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b5 : bracketOK csY (LsY.getD 5 0)=true ∧ (keepB csY fsY (LsY.getD 5 0)=false ∨ LsY.getD 5 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b6 : bracketOK csY (LsY.getD 6 0)=true ∧ (keepB csY fsY (LsY.getD 6 0)=false ∨ LsY.getD 6 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b7 : bracketOK csY (LsY.getD 7 0)=true ∧ (keepB csY fsY (LsY.getD 7 0)=false ∨ LsY.getD 7 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b8 : bracketOK csY (LsY.getD 8 0)=true ∧ (keepB csY fsY (LsY.getD 8 0)=false ∨ LsY.getD 8 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b9 : bracketOK csY (LsY.getD 9 0)=true ∧ (keepB csY fsY (LsY.getD 9 0)=false ∨ LsY.getD 9 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b10 : bracketOK csY (LsY.getD 10 0)=true ∧ (keepB csY fsY (LsY.getD 10 0)=false ∨ LsY.getD 10 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b11 : bracketOK csY (LsY.getD 11 0)=true ∧ (keepB csY fsY (LsY.getD 11 0)=false ∨ LsY.getD 11 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b12 : bracketOK csY (LsY.getD 12 0)=true ∧ (keepB csY fsY (LsY.getD 12 0)=false ∨ LsY.getD 12 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b13 : bracketOK csY (LsY.getD 13 0)=true ∧ (keepB csY fsY (LsY.getD 13 0)=false ∨ LsY.getD 13 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b14 : bracketOK csY (LsY.getD 14 0)=true ∧ (keepB csY fsY (LsY.getD 14 0)=false ∨ LsY.getD 14 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b15 : bracketOK csY (LsY.getD 15 0)=true ∧ (keepB csY fsY (LsY.getD 15 0)=false ∨ LsY.getD 15 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b16 : bracketOK csY (LsY.getD 16 0)=true ∧ (keepB csY fsY (LsY.getD 16 0)=false ∨ LsY.getD 16 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b17 : bracketOK csY (LsY.getD 17 0)=true ∧ (keepB csY fsY (LsY.getD 17 0)=false ∨ LsY.getD 17 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b18 : bracketOK csY (LsY.getD 18 0)=true ∧ (keepB csY fsY (LsY.getD 18 0)=false ∨ LsY.getD 18 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b19 : bracketOK csY (LsY.getD 19 0)=true ∧ (keepB csY fsY (LsY.getD 19 0)=false ∨ LsY.getD 19 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b20 : bracketOK csY (LsY.getD 20 0)=true ∧ (keepB csY fsY (LsY.getD 20 0)=false ∨ LsY.getD 20 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b21 : bracketOK csY (LsY.getD 21 0)=true ∧ (keepB csY fsY (LsY.getD 21 0)=false ∨ LsY.getD 21 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b22 : bracketOK csY (LsY.getD 22 0)=true ∧ (keepB csY fsY (LsY.getD 22 0)=false ∨ LsY.getD 22 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b23 : bracketOK csY (LsY.getD 23 0)=true ∧ (keepB csY fsY (LsY.getD 23 0)=false ∨ LsY.getD 23 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b24 : bracketOK csY (LsY.getD 24 0)=true ∧ (keepB csY fsY (LsY.getD 24 0)=false ∨ LsY.getD 24 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b25 : bracketOK csY (LsY.getD 25 0)=true ∧ (keepB csY fsY (LsY.getD 25 0)=false ∨ LsY.getD 25 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b26 : bracketOK csY (LsY.getD 26 0)=true ∧ (keepB csY fsY (LsY.getD 26 0)=false ∨ LsY.getD 26 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b27 : bracketOK csY (LsY.getD 27 0)=true ∧ (keepB csY fsY (LsY.getD 27 0)=false ∨ LsY.getD 27 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b28 : bracketOK csY (LsY.getD 28 0)=true ∧ (keepB csY fsY (LsY.getD 28 0)=false ∨ LsY.getD 28 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b29 : bracketOK csY (LsY.getD 29 0)=true ∧ (keepB csY fsY (LsY.getD 29 0)=false ∨ LsY.getD 29 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b30 : bracketOK csY (LsY.getD 30 0)=true ∧ (keepB csY fsY (LsY.getD 30 0)=false ∨ LsY.getD 30 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b31 : bracketOK csY (LsY.getD 31 0)=true ∧ (keepB csY fsY (LsY.getD 31 0)=false ∨ LsY.getD 31 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b32 : bracketOK csY (LsY.getD 32 0)=true ∧ (keepB csY fsY (LsY.getD 32 0)=false ∨ LsY.getD 32 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b33 : bracketOK csY (LsY.getD 33 0)=true ∧ (keepB csY fsY (LsY.getD 33 0)=false ∨ LsY.getD 33 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b34 : bracketOK csY (LsY.getD 34 0)=true ∧ (keepB csY fsY (LsY.getD 34 0)=false ∨ LsY.getD 34 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b35 : bracketOK csY (LsY.getD 35 0)=true ∧ (keepB csY fsY (LsY.getD 35 0)=false ∨ LsY.getD 35 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b36 : bracketOK csY (LsY.getD 36 0)=true ∧ (keepB csY fsY (LsY.getD 36 0)=false ∨ LsY.getD 36 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b37 : bracketOK csY (LsY.getD 37 0)=true ∧ (keepB csY fsY (LsY.getD 37 0)=false ∨ LsY.getD 37 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b38 : bracketOK csY (LsY.getD 38 0)=true ∧ (keepB csY fsY (LsY.getD 38 0)=false ∨ LsY.getD 38 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b39 : bracketOK csY (LsY.getD 39 0)=true ∧ (keepB csY fsY (LsY.getD 39 0)=false ∨ LsY.getD 39 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b40 : bracketOK csY (LsY.getD 40 0)=true ∧ (keepB csY fsY (LsY.getD 40 0)=false ∨ LsY.getD 40 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b41 : bracketOK csY (LsY.getD 41 0)=true ∧ (keepB csY fsY (LsY.getD 41 0)=false ∨ LsY.getD 41 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b42 : bracketOK csY (LsY.getD 42 0)=true ∧ (keepB csY fsY (LsY.getD 42 0)=false ∨ LsY.getD 42 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b43 : bracketOK csY (LsY.getD 43 0)=true ∧ (keepB csY fsY (LsY.getD 43 0)=false ∨ LsY.getD 43 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b44 : bracketOK csY (LsY.getD 44 0)=true ∧ (keepB csY fsY (LsY.getD 44 0)=false ∨ LsY.getD 44 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b45 : bracketOK csY (LsY.getD 45 0)=true ∧ (keepB csY fsY (LsY.getD 45 0)=false ∨ LsY.getD 45 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b46 : bracketOK csY (LsY.getD 46 0)=true ∧ (keepB csY fsY (LsY.getD 46 0)=false ∨ LsY.getD 46 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b47 : bracketOK csY (LsY.getD 47 0)=true ∧ (keepB csY fsY (LsY.getD 47 0)=false ∨ LsY.getD 47 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b48 : bracketOK csY (LsY.getD 48 0)=true ∧ (keepB csY fsY (LsY.getD 48 0)=false ∨ LsY.getD 48 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b49 : bracketOK csY (LsY.getD 49 0)=true ∧ (keepB csY fsY (LsY.getD 49 0)=false ∨ LsY.getD 49 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b50 : bracketOK csY (LsY.getD 50 0)=true ∧ (keepB csY fsY (LsY.getD 50 0)=false ∨ LsY.getD 50 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b51 : bracketOK csY (LsY.getD 51 0)=true ∧ (keepB csY fsY (LsY.getD 51 0)=false ∨ LsY.getD 51 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b52 : bracketOK csY (LsY.getD 52 0)=true ∧ (keepB csY fsY (LsY.getD 52 0)=false ∨ LsY.getD 52 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b53 : bracketOK csY (LsY.getD 53 0)=true ∧ (keepB csY fsY (LsY.getD 53 0)=false ∨ LsY.getD 53 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b54 : bracketOK csY (LsY.getD 54 0)=true ∧ (keepB csY fsY (LsY.getD 54 0)=false ∨ LsY.getD 54 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b55 : bracketOK csY (LsY.getD 55 0)=true ∧ (keepB csY fsY (LsY.getD 55 0)=false ∨ LsY.getD 55 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b56 : bracketOK csY (LsY.getD 56 0)=true ∧ (keepB csY fsY (LsY.getD 56 0)=false ∨ LsY.getD 56 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b57 : bracketOK csY (LsY.getD 57 0)=true ∧ (keepB csY fsY (LsY.getD 57 0)=false ∨ LsY.getD 57 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b58 : bracketOK csY (LsY.getD 58 0)=true ∧ (keepB csY fsY (LsY.getD 58 0)=false ∨ LsY.getD 58 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b59 : bracketOK csY (LsY.getD 59 0)=true ∧ (keepB csY fsY (LsY.getD 59 0)=false ∨ LsY.getD 59 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b60 : bracketOK csY (LsY.getD 60 0)=true ∧ (keepB csY fsY (LsY.getD 60 0)=false ∨ LsY.getD 60 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b61 : bracketOK csY (LsY.getD 61 0)=true ∧ (keepB csY fsY (LsY.getD 61 0)=false ∨ LsY.getD 61 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b62 : bracketOK csY (LsY.getD 62 0)=true ∧ (keepB csY fsY (LsY.getD 62 0)=false ∨ LsY.getD 62 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b63 : bracketOK csY (LsY.getD 63 0)=true ∧ (keepB csY fsY (LsY.getD 63 0)=false ∨ LsY.getD 63 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b64 : bracketOK csY (LsY.getD 64 0)=true ∧ (keepB csY fsY (LsY.getD 64 0)=false ∨ LsY.getD 64 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b65 : bracketOK csY (LsY.getD 65 0)=true ∧ (keepB csY fsY (LsY.getD 65 0)=false ∨ LsY.getD 65 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b66 : bracketOK csY (LsY.getD 66 0)=true ∧ (keepB csY fsY (LsY.getD 66 0)=false ∨ LsY.getD 66 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b67 : bracketOK csY (LsY.getD 67 0)=true ∧ (keepB csY fsY (LsY.getD 67 0)=false ∨ LsY.getD 67 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b68 : bracketOK csY (LsY.getD 68 0)=true ∧ (keepB csY fsY (LsY.getD 68 0)=false ∨ LsY.getD 68 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b69 : bracketOK csY (LsY.getD 69 0)=true ∧ (keepB csY fsY (LsY.getD 69 0)=false ∨ LsY.getD 69 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b70 : bracketOK csY (LsY.getD 70 0)=true ∧ (keepB csY fsY (LsY.getD 70 0)=false ∨ LsY.getD 70 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b71 : bracketOK csY (LsY.getD 71 0)=true ∧ (keepB csY fsY (LsY.getD 71 0)=false ∨ LsY.getD 71 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b72 : bracketOK csY (LsY.getD 72 0)=true ∧ (keepB csY fsY (LsY.getD 72 0)=false ∨ LsY.getD 72 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b73 : bracketOK csY (LsY.getD 73 0)=true ∧ (keepB csY fsY (LsY.getD 73 0)=false ∨ LsY.getD 73 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b74 : bracketOK csY (LsY.getD 74 0)=true ∧ (keepB csY fsY (LsY.getD 74 0)=false ∨ LsY.getD 74 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b75 : bracketOK csY (LsY.getD 75 0)=true ∧ (keepB csY fsY (LsY.getD 75 0)=false ∨ LsY.getD 75 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b76 : bracketOK csY (LsY.getD 76 0)=true ∧ (keepB csY fsY (LsY.getD 76 0)=false ∨ LsY.getD 76 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b77 : bracketOK csY (LsY.getD 77 0)=true ∧ (keepB csY fsY (LsY.getD 77 0)=false ∨ LsY.getD 77 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b78 : bracketOK csY (LsY.getD 78 0)=true ∧ (keepB csY fsY (LsY.getD 78 0)=false ∨ LsY.getD 78 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b79 : bracketOK csY (LsY.getD 79 0)=true ∧ (keepB csY fsY (LsY.getD 79 0)=false ∨ LsY.getD 79 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b80 : bracketOK csY (LsY.getD 80 0)=true ∧ (keepB csY fsY (LsY.getD 80 0)=false ∨ LsY.getD 80 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b81 : bracketOK csY (LsY.getD 81 0)=true ∧ (keepB csY fsY (LsY.getD 81 0)=false ∨ LsY.getD 81 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b82 : bracketOK csY (LsY.getD 82 0)=true ∧ (keepB csY fsY (LsY.getD 82 0)=false ∨ LsY.getD 82 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b83 : bracketOK csY (LsY.getD 83 0)=true ∧ (keepB csY fsY (LsY.getD 83 0)=false ∨ LsY.getD 83 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b84 : bracketOK csY (LsY.getD 84 0)=true ∧ (keepB csY fsY (LsY.getD 84 0)=false ∨ LsY.getD 84 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b85 : bracketOK csY (LsY.getD 85 0)=true ∧ (keepB csY fsY (LsY.getD 85 0)=false ∨ LsY.getD 85 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b86 : bracketOK csY (LsY.getD 86 0)=true ∧ (keepB csY fsY (LsY.getD 86 0)=false ∨ LsY.getD 86 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b87 : bracketOK csY (LsY.getD 87 0)=true ∧ (keepB csY fsY (LsY.getD 87 0)=false ∨ LsY.getD 87 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b88 : bracketOK csY (LsY.getD 88 0)=true ∧ (keepB csY fsY (LsY.getD 88 0)=false ∨ LsY.getD 88 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b89 : bracketOK csY (LsY.getD 89 0)=true ∧ (keepB csY fsY (LsY.getD 89 0)=false ∨ LsY.getD 89 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b90 : bracketOK csY (LsY.getD 90 0)=true ∧ (keepB csY fsY (LsY.getD 90 0)=false ∨ LsY.getD 90 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b91 : bracketOK csY (LsY.getD 91 0)=true ∧ (keepB csY fsY (LsY.getD 91 0)=false ∨ LsY.getD 91 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b92 : bracketOK csY (LsY.getD 92 0)=true ∧ (keepB csY fsY (LsY.getD 92 0)=false ∨ LsY.getD 92 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b93 : bracketOK csY (LsY.getD 93 0)=true ∧ (keepB csY fsY (LsY.getD 93 0)=false ∨ LsY.getD 93 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b94 : bracketOK csY (LsY.getD 94 0)=true ∧ (keepB csY fsY (LsY.getD 94 0)=false ∨ LsY.getD 94 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b95 : bracketOK csY (LsY.getD 95 0)=true ∧ (keepB csY fsY (LsY.getD 95 0)=false ∨ LsY.getD 95 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b96 : bracketOK csY (LsY.getD 96 0)=true ∧ (keepB csY fsY (LsY.getD 96 0)=false ∨ LsY.getD 96 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b97 : bracketOK csY (LsY.getD 97 0)=true ∧ (keepB csY fsY (LsY.getD 97 0)=false ∨ LsY.getD 97 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b98 : bracketOK csY (LsY.getD 98 0)=true ∧ (keepB csY fsY (LsY.getD 98 0)=false ∨ LsY.getD 98 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b99 : bracketOK csY (LsY.getD 99 0)=true ∧ (keepB csY fsY (LsY.getD 99 0)=false ∨ LsY.getD 99 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b100 : bracketOK csY (LsY.getD 100 0)=true ∧ (keepB csY fsY (LsY.getD 100 0)=false ∨ LsY.getD 100 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b101 : bracketOK csY (LsY.getD 101 0)=true ∧ (keepB csY fsY (LsY.getD 101 0)=false ∨ LsY.getD 101 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b102 : bracketOK csY (LsY.getD 102 0)=true ∧ (keepB csY fsY (LsY.getD 102 0)=false ∨ LsY.getD 102 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b103 : bracketOK csY (LsY.getD 103 0)=true ∧ (keepB csY fsY (LsY.getD 103 0)=false ∨ LsY.getD 103 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b104 : bracketOK csY (LsY.getD 104 0)=true ∧ (keepB csY fsY (LsY.getD 104 0)=false ∨ LsY.getD 104 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b105 : bracketOK csY (LsY.getD 105 0)=true ∧ (keepB csY fsY (LsY.getD 105 0)=false ∨ LsY.getD 105 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b106 : bracketOK csY (LsY.getD 106 0)=true ∧ (keepB csY fsY (LsY.getD 106 0)=false ∨ LsY.getD 106 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b107 : bracketOK csY (LsY.getD 107 0)=true ∧ (keepB csY fsY (LsY.getD 107 0)=false ∨ LsY.getD 107 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b108 : bracketOK csY (LsY.getD 108 0)=true ∧ (keepB csY fsY (LsY.getD 108 0)=false ∨ LsY.getD 108 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b109 : bracketOK csY (LsY.getD 109 0)=true ∧ (keepB csY fsY (LsY.getD 109 0)=false ∨ LsY.getD 109 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b110 : bracketOK csY (LsY.getD 110 0)=true ∧ (keepB csY fsY (LsY.getD 110 0)=false ∨ LsY.getD 110 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b111 : bracketOK csY (LsY.getD 111 0)=true ∧ (keepB csY fsY (LsY.getD 111 0)=false ∨ LsY.getD 111 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b112 : bracketOK csY (LsY.getD 112 0)=true ∧ (keepB csY fsY (LsY.getD 112 0)=false ∨ LsY.getD 112 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b113 : bracketOK csY (LsY.getD 113 0)=true ∧ (keepB csY fsY (LsY.getD 113 0)=false ∨ LsY.getD 113 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b114 : bracketOK csY (LsY.getD 114 0)=true ∧ (keepB csY fsY (LsY.getD 114 0)=false ∨ LsY.getD 114 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b115 : bracketOK csY (LsY.getD 115 0)=true ∧ (keepB csY fsY (LsY.getD 115 0)=false ∨ LsY.getD 115 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b116 : bracketOK csY (LsY.getD 116 0)=true ∧ (keepB csY fsY (LsY.getD 116 0)=false ∨ LsY.getD 116 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b117 : bracketOK csY (LsY.getD 117 0)=true ∧ (keepB csY fsY (LsY.getD 117 0)=false ∨ LsY.getD 117 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b118 : bracketOK csY (LsY.getD 118 0)=true ∧ (keepB csY fsY (LsY.getD 118 0)=false ∨ LsY.getD 118 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b119 : bracketOK csY (LsY.getD 119 0)=true ∧ (keepB csY fsY (LsY.getD 119 0)=false ∨ LsY.getD 119 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b120 : bracketOK csY (LsY.getD 120 0)=true ∧ (keepB csY fsY (LsY.getD 120 0)=false ∨ LsY.getD 120 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b121 : bracketOK csY (LsY.getD 121 0)=true ∧ (keepB csY fsY (LsY.getD 121 0)=false ∨ LsY.getD 121 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b122 : bracketOK csY (LsY.getD 122 0)=true ∧ (keepB csY fsY (LsY.getD 122 0)=false ∨ LsY.getD 122 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b123 : bracketOK csY (LsY.getD 123 0)=true ∧ (keepB csY fsY (LsY.getD 123 0)=false ∨ LsY.getD 123 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b124 : bracketOK csY (LsY.getD 124 0)=true ∧ (keepB csY fsY (LsY.getD 124 0)=false ∨ LsY.getD 124 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b125 : bracketOK csY (LsY.getD 125 0)=true ∧ (keepB csY fsY (LsY.getD 125 0)=false ∨ LsY.getD 125 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_b126 : bracketOK csY (LsY.getD 126 0)=true ∧ (keepB csY fsY (LsY.getD 126 0)=false ∨ LsY.getD 126 0∈keepLsY) := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_hlen : LsY.length=127 := by decide +kernel -- kcost: 0.16 s each (20 s total, standalone 6 Nov)
theorem y_hall : ∀ i,i<LsY.length → (bracketOK csY (LsY.getD i 0)=true ∧ (keepB csY fsY (LsY.getD i 0)=false ∨ LsY.getD i 0∈keepLsY)) := by
  intro i hi
  rw [y_hlen] at hi
  interval_cases i
  · exact y_b0
  · exact y_b1
  · exact y_b2
  · exact y_b3
  · exact y_b4
  · exact y_b5
  · exact y_b6
  · exact y_b7
  · exact y_b8
  · exact y_b9
  · exact y_b10
  · exact y_b11
  · exact y_b12
  · exact y_b13
  · exact y_b14
  · exact y_b15
  · exact y_b16
  · exact y_b17
  · exact y_b18
  · exact y_b19
  · exact y_b20
  · exact y_b21
  · exact y_b22
  · exact y_b23
  · exact y_b24
  · exact y_b25
  · exact y_b26
  · exact y_b27
  · exact y_b28
  · exact y_b29
  · exact y_b30
  · exact y_b31
  · exact y_b32
  · exact y_b33
  · exact y_b34
  · exact y_b35
  · exact y_b36
  · exact y_b37
  · exact y_b38
  · exact y_b39
  · exact y_b40
  · exact y_b41
  · exact y_b42
  · exact y_b43
  · exact y_b44
  · exact y_b45
  · exact y_b46
  · exact y_b47
  · exact y_b48
  · exact y_b49
  · exact y_b50
  · exact y_b51
  · exact y_b52
  · exact y_b53
  · exact y_b54
  · exact y_b55
  · exact y_b56
  · exact y_b57
  · exact y_b58
  · exact y_b59
  · exact y_b60
  · exact y_b61
  · exact y_b62
  · exact y_b63
  · exact y_b64
  · exact y_b65
  · exact y_b66
  · exact y_b67
  · exact y_b68
  · exact y_b69
  · exact y_b70
  · exact y_b71
  · exact y_b72
  · exact y_b73
  · exact y_b74
  · exact y_b75
  · exact y_b76
  · exact y_b77
  · exact y_b78
  · exact y_b79
  · exact y_b80
  · exact y_b81
  · exact y_b82
  · exact y_b83
  · exact y_b84
  · exact y_b85
  · exact y_b86
  · exact y_b87
  · exact y_b88
  · exact y_b89
  · exact y_b90
  · exact y_b91
  · exact y_b92
  · exact y_b93
  · exact y_b94
  · exact y_b95
  · exact y_b96
  · exact y_b97
  · exact y_b98
  · exact y_b99
  · exact y_b100
  · exact y_b101
  · exact y_b102
  · exact y_b103
  · exact y_b104
  · exact y_b105
  · exact y_b106
  · exact y_b107
  · exact y_b108
  · exact y_b109
  · exact y_b110
  · exact y_b111
  · exact y_b112
  · exact y_b113
  · exact y_b114
  · exact y_b115
  · exact y_b116
  · exact y_b117
  · exact y_b118
  · exact y_b119
  · exact y_b120
  · exact y_b121
  · exact y_b122
  · exact y_b123
  · exact y_b124
  · exact y_b125
  · exact y_b126
theorem y_hbr : ∀ l∈LsY,bracketOK csY l=true := by
  intro l hl
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hl
  have := (y_hall i hi).1
  rw [show LsY.getD i 0=LsY[i] from by rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]; rfl] at this
  exact this
theorem y_hkeep : ∀ l∈LsY,keepB csY fsY l=true → l∈keepLsY := by
  intro l hl hk
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hl
  have := (y_hall i hi).2
  rw [show LsY.getD i 0=LsY[i] from by rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]; rfl] at this
  rcases this with h | h
  · rw [h] at hk; exact absurd hk (by decide)
  · exact h
#print axioms y_hbr
#print axioms y_hkeep
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColBr
