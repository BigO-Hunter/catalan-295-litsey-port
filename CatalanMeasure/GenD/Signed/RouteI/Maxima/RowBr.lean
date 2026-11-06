module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 198 per-index declarations, each 2 Horner evals + keep test (probe: 0.16 s per eval)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBr
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem x_b0 : bracketOK csX (LsX.getD 0 0)=true ∧ (keepB csX fsX (LsX.getD 0 0)=false ∨ LsX.getD 0 0∈keepLsX) := by decide +kernel
theorem x_b1 : bracketOK csX (LsX.getD 1 0)=true ∧ (keepB csX fsX (LsX.getD 1 0)=false ∨ LsX.getD 1 0∈keepLsX) := by decide +kernel
theorem x_b2 : bracketOK csX (LsX.getD 2 0)=true ∧ (keepB csX fsX (LsX.getD 2 0)=false ∨ LsX.getD 2 0∈keepLsX) := by decide +kernel
theorem x_b3 : bracketOK csX (LsX.getD 3 0)=true ∧ (keepB csX fsX (LsX.getD 3 0)=false ∨ LsX.getD 3 0∈keepLsX) := by decide +kernel
theorem x_b4 : bracketOK csX (LsX.getD 4 0)=true ∧ (keepB csX fsX (LsX.getD 4 0)=false ∨ LsX.getD 4 0∈keepLsX) := by decide +kernel
theorem x_b5 : bracketOK csX (LsX.getD 5 0)=true ∧ (keepB csX fsX (LsX.getD 5 0)=false ∨ LsX.getD 5 0∈keepLsX) := by decide +kernel
theorem x_b6 : bracketOK csX (LsX.getD 6 0)=true ∧ (keepB csX fsX (LsX.getD 6 0)=false ∨ LsX.getD 6 0∈keepLsX) := by decide +kernel
theorem x_b7 : bracketOK csX (LsX.getD 7 0)=true ∧ (keepB csX fsX (LsX.getD 7 0)=false ∨ LsX.getD 7 0∈keepLsX) := by decide +kernel
theorem x_b8 : bracketOK csX (LsX.getD 8 0)=true ∧ (keepB csX fsX (LsX.getD 8 0)=false ∨ LsX.getD 8 0∈keepLsX) := by decide +kernel
theorem x_b9 : bracketOK csX (LsX.getD 9 0)=true ∧ (keepB csX fsX (LsX.getD 9 0)=false ∨ LsX.getD 9 0∈keepLsX) := by decide +kernel
theorem x_b10 : bracketOK csX (LsX.getD 10 0)=true ∧ (keepB csX fsX (LsX.getD 10 0)=false ∨ LsX.getD 10 0∈keepLsX) := by decide +kernel
theorem x_b11 : bracketOK csX (LsX.getD 11 0)=true ∧ (keepB csX fsX (LsX.getD 11 0)=false ∨ LsX.getD 11 0∈keepLsX) := by decide +kernel
theorem x_b12 : bracketOK csX (LsX.getD 12 0)=true ∧ (keepB csX fsX (LsX.getD 12 0)=false ∨ LsX.getD 12 0∈keepLsX) := by decide +kernel
theorem x_b13 : bracketOK csX (LsX.getD 13 0)=true ∧ (keepB csX fsX (LsX.getD 13 0)=false ∨ LsX.getD 13 0∈keepLsX) := by decide +kernel
theorem x_b14 : bracketOK csX (LsX.getD 14 0)=true ∧ (keepB csX fsX (LsX.getD 14 0)=false ∨ LsX.getD 14 0∈keepLsX) := by decide +kernel
theorem x_b15 : bracketOK csX (LsX.getD 15 0)=true ∧ (keepB csX fsX (LsX.getD 15 0)=false ∨ LsX.getD 15 0∈keepLsX) := by decide +kernel
theorem x_b16 : bracketOK csX (LsX.getD 16 0)=true ∧ (keepB csX fsX (LsX.getD 16 0)=false ∨ LsX.getD 16 0∈keepLsX) := by decide +kernel
theorem x_b17 : bracketOK csX (LsX.getD 17 0)=true ∧ (keepB csX fsX (LsX.getD 17 0)=false ∨ LsX.getD 17 0∈keepLsX) := by decide +kernel
theorem x_b18 : bracketOK csX (LsX.getD 18 0)=true ∧ (keepB csX fsX (LsX.getD 18 0)=false ∨ LsX.getD 18 0∈keepLsX) := by decide +kernel
theorem x_b19 : bracketOK csX (LsX.getD 19 0)=true ∧ (keepB csX fsX (LsX.getD 19 0)=false ∨ LsX.getD 19 0∈keepLsX) := by decide +kernel
theorem x_b20 : bracketOK csX (LsX.getD 20 0)=true ∧ (keepB csX fsX (LsX.getD 20 0)=false ∨ LsX.getD 20 0∈keepLsX) := by decide +kernel
theorem x_b21 : bracketOK csX (LsX.getD 21 0)=true ∧ (keepB csX fsX (LsX.getD 21 0)=false ∨ LsX.getD 21 0∈keepLsX) := by decide +kernel
theorem x_b22 : bracketOK csX (LsX.getD 22 0)=true ∧ (keepB csX fsX (LsX.getD 22 0)=false ∨ LsX.getD 22 0∈keepLsX) := by decide +kernel
theorem x_b23 : bracketOK csX (LsX.getD 23 0)=true ∧ (keepB csX fsX (LsX.getD 23 0)=false ∨ LsX.getD 23 0∈keepLsX) := by decide +kernel
theorem x_b24 : bracketOK csX (LsX.getD 24 0)=true ∧ (keepB csX fsX (LsX.getD 24 0)=false ∨ LsX.getD 24 0∈keepLsX) := by decide +kernel
theorem x_b25 : bracketOK csX (LsX.getD 25 0)=true ∧ (keepB csX fsX (LsX.getD 25 0)=false ∨ LsX.getD 25 0∈keepLsX) := by decide +kernel
theorem x_b26 : bracketOK csX (LsX.getD 26 0)=true ∧ (keepB csX fsX (LsX.getD 26 0)=false ∨ LsX.getD 26 0∈keepLsX) := by decide +kernel
theorem x_b27 : bracketOK csX (LsX.getD 27 0)=true ∧ (keepB csX fsX (LsX.getD 27 0)=false ∨ LsX.getD 27 0∈keepLsX) := by decide +kernel
theorem x_b28 : bracketOK csX (LsX.getD 28 0)=true ∧ (keepB csX fsX (LsX.getD 28 0)=false ∨ LsX.getD 28 0∈keepLsX) := by decide +kernel
theorem x_b29 : bracketOK csX (LsX.getD 29 0)=true ∧ (keepB csX fsX (LsX.getD 29 0)=false ∨ LsX.getD 29 0∈keepLsX) := by decide +kernel
theorem x_b30 : bracketOK csX (LsX.getD 30 0)=true ∧ (keepB csX fsX (LsX.getD 30 0)=false ∨ LsX.getD 30 0∈keepLsX) := by decide +kernel
theorem x_b31 : bracketOK csX (LsX.getD 31 0)=true ∧ (keepB csX fsX (LsX.getD 31 0)=false ∨ LsX.getD 31 0∈keepLsX) := by decide +kernel
theorem x_b32 : bracketOK csX (LsX.getD 32 0)=true ∧ (keepB csX fsX (LsX.getD 32 0)=false ∨ LsX.getD 32 0∈keepLsX) := by decide +kernel
theorem x_b33 : bracketOK csX (LsX.getD 33 0)=true ∧ (keepB csX fsX (LsX.getD 33 0)=false ∨ LsX.getD 33 0∈keepLsX) := by decide +kernel
theorem x_b34 : bracketOK csX (LsX.getD 34 0)=true ∧ (keepB csX fsX (LsX.getD 34 0)=false ∨ LsX.getD 34 0∈keepLsX) := by decide +kernel
theorem x_b35 : bracketOK csX (LsX.getD 35 0)=true ∧ (keepB csX fsX (LsX.getD 35 0)=false ∨ LsX.getD 35 0∈keepLsX) := by decide +kernel
theorem x_b36 : bracketOK csX (LsX.getD 36 0)=true ∧ (keepB csX fsX (LsX.getD 36 0)=false ∨ LsX.getD 36 0∈keepLsX) := by decide +kernel
theorem x_b37 : bracketOK csX (LsX.getD 37 0)=true ∧ (keepB csX fsX (LsX.getD 37 0)=false ∨ LsX.getD 37 0∈keepLsX) := by decide +kernel
theorem x_b38 : bracketOK csX (LsX.getD 38 0)=true ∧ (keepB csX fsX (LsX.getD 38 0)=false ∨ LsX.getD 38 0∈keepLsX) := by decide +kernel
theorem x_b39 : bracketOK csX (LsX.getD 39 0)=true ∧ (keepB csX fsX (LsX.getD 39 0)=false ∨ LsX.getD 39 0∈keepLsX) := by decide +kernel
theorem x_b40 : bracketOK csX (LsX.getD 40 0)=true ∧ (keepB csX fsX (LsX.getD 40 0)=false ∨ LsX.getD 40 0∈keepLsX) := by decide +kernel
theorem x_b41 : bracketOK csX (LsX.getD 41 0)=true ∧ (keepB csX fsX (LsX.getD 41 0)=false ∨ LsX.getD 41 0∈keepLsX) := by decide +kernel
theorem x_b42 : bracketOK csX (LsX.getD 42 0)=true ∧ (keepB csX fsX (LsX.getD 42 0)=false ∨ LsX.getD 42 0∈keepLsX) := by decide +kernel
theorem x_b43 : bracketOK csX (LsX.getD 43 0)=true ∧ (keepB csX fsX (LsX.getD 43 0)=false ∨ LsX.getD 43 0∈keepLsX) := by decide +kernel
theorem x_b44 : bracketOK csX (LsX.getD 44 0)=true ∧ (keepB csX fsX (LsX.getD 44 0)=false ∨ LsX.getD 44 0∈keepLsX) := by decide +kernel
theorem x_b45 : bracketOK csX (LsX.getD 45 0)=true ∧ (keepB csX fsX (LsX.getD 45 0)=false ∨ LsX.getD 45 0∈keepLsX) := by decide +kernel
theorem x_b46 : bracketOK csX (LsX.getD 46 0)=true ∧ (keepB csX fsX (LsX.getD 46 0)=false ∨ LsX.getD 46 0∈keepLsX) := by decide +kernel
theorem x_b47 : bracketOK csX (LsX.getD 47 0)=true ∧ (keepB csX fsX (LsX.getD 47 0)=false ∨ LsX.getD 47 0∈keepLsX) := by decide +kernel
theorem x_b48 : bracketOK csX (LsX.getD 48 0)=true ∧ (keepB csX fsX (LsX.getD 48 0)=false ∨ LsX.getD 48 0∈keepLsX) := by decide +kernel
theorem x_b49 : bracketOK csX (LsX.getD 49 0)=true ∧ (keepB csX fsX (LsX.getD 49 0)=false ∨ LsX.getD 49 0∈keepLsX) := by decide +kernel
theorem x_b50 : bracketOK csX (LsX.getD 50 0)=true ∧ (keepB csX fsX (LsX.getD 50 0)=false ∨ LsX.getD 50 0∈keepLsX) := by decide +kernel
theorem x_b51 : bracketOK csX (LsX.getD 51 0)=true ∧ (keepB csX fsX (LsX.getD 51 0)=false ∨ LsX.getD 51 0∈keepLsX) := by decide +kernel
theorem x_b52 : bracketOK csX (LsX.getD 52 0)=true ∧ (keepB csX fsX (LsX.getD 52 0)=false ∨ LsX.getD 52 0∈keepLsX) := by decide +kernel
theorem x_b53 : bracketOK csX (LsX.getD 53 0)=true ∧ (keepB csX fsX (LsX.getD 53 0)=false ∨ LsX.getD 53 0∈keepLsX) := by decide +kernel
theorem x_b54 : bracketOK csX (LsX.getD 54 0)=true ∧ (keepB csX fsX (LsX.getD 54 0)=false ∨ LsX.getD 54 0∈keepLsX) := by decide +kernel
theorem x_b55 : bracketOK csX (LsX.getD 55 0)=true ∧ (keepB csX fsX (LsX.getD 55 0)=false ∨ LsX.getD 55 0∈keepLsX) := by decide +kernel
theorem x_b56 : bracketOK csX (LsX.getD 56 0)=true ∧ (keepB csX fsX (LsX.getD 56 0)=false ∨ LsX.getD 56 0∈keepLsX) := by decide +kernel
theorem x_b57 : bracketOK csX (LsX.getD 57 0)=true ∧ (keepB csX fsX (LsX.getD 57 0)=false ∨ LsX.getD 57 0∈keepLsX) := by decide +kernel
theorem x_b58 : bracketOK csX (LsX.getD 58 0)=true ∧ (keepB csX fsX (LsX.getD 58 0)=false ∨ LsX.getD 58 0∈keepLsX) := by decide +kernel
theorem x_b59 : bracketOK csX (LsX.getD 59 0)=true ∧ (keepB csX fsX (LsX.getD 59 0)=false ∨ LsX.getD 59 0∈keepLsX) := by decide +kernel
theorem x_b60 : bracketOK csX (LsX.getD 60 0)=true ∧ (keepB csX fsX (LsX.getD 60 0)=false ∨ LsX.getD 60 0∈keepLsX) := by decide +kernel
theorem x_b61 : bracketOK csX (LsX.getD 61 0)=true ∧ (keepB csX fsX (LsX.getD 61 0)=false ∨ LsX.getD 61 0∈keepLsX) := by decide +kernel
theorem x_b62 : bracketOK csX (LsX.getD 62 0)=true ∧ (keepB csX fsX (LsX.getD 62 0)=false ∨ LsX.getD 62 0∈keepLsX) := by decide +kernel
theorem x_b63 : bracketOK csX (LsX.getD 63 0)=true ∧ (keepB csX fsX (LsX.getD 63 0)=false ∨ LsX.getD 63 0∈keepLsX) := by decide +kernel
theorem x_b64 : bracketOK csX (LsX.getD 64 0)=true ∧ (keepB csX fsX (LsX.getD 64 0)=false ∨ LsX.getD 64 0∈keepLsX) := by decide +kernel
theorem x_b65 : bracketOK csX (LsX.getD 65 0)=true ∧ (keepB csX fsX (LsX.getD 65 0)=false ∨ LsX.getD 65 0∈keepLsX) := by decide +kernel
theorem x_b66 : bracketOK csX (LsX.getD 66 0)=true ∧ (keepB csX fsX (LsX.getD 66 0)=false ∨ LsX.getD 66 0∈keepLsX) := by decide +kernel
theorem x_b67 : bracketOK csX (LsX.getD 67 0)=true ∧ (keepB csX fsX (LsX.getD 67 0)=false ∨ LsX.getD 67 0∈keepLsX) := by decide +kernel
theorem x_b68 : bracketOK csX (LsX.getD 68 0)=true ∧ (keepB csX fsX (LsX.getD 68 0)=false ∨ LsX.getD 68 0∈keepLsX) := by decide +kernel
theorem x_b69 : bracketOK csX (LsX.getD 69 0)=true ∧ (keepB csX fsX (LsX.getD 69 0)=false ∨ LsX.getD 69 0∈keepLsX) := by decide +kernel
theorem x_b70 : bracketOK csX (LsX.getD 70 0)=true ∧ (keepB csX fsX (LsX.getD 70 0)=false ∨ LsX.getD 70 0∈keepLsX) := by decide +kernel
theorem x_b71 : bracketOK csX (LsX.getD 71 0)=true ∧ (keepB csX fsX (LsX.getD 71 0)=false ∨ LsX.getD 71 0∈keepLsX) := by decide +kernel
theorem x_b72 : bracketOK csX (LsX.getD 72 0)=true ∧ (keepB csX fsX (LsX.getD 72 0)=false ∨ LsX.getD 72 0∈keepLsX) := by decide +kernel
theorem x_b73 : bracketOK csX (LsX.getD 73 0)=true ∧ (keepB csX fsX (LsX.getD 73 0)=false ∨ LsX.getD 73 0∈keepLsX) := by decide +kernel
theorem x_b74 : bracketOK csX (LsX.getD 74 0)=true ∧ (keepB csX fsX (LsX.getD 74 0)=false ∨ LsX.getD 74 0∈keepLsX) := by decide +kernel
theorem x_b75 : bracketOK csX (LsX.getD 75 0)=true ∧ (keepB csX fsX (LsX.getD 75 0)=false ∨ LsX.getD 75 0∈keepLsX) := by decide +kernel
theorem x_b76 : bracketOK csX (LsX.getD 76 0)=true ∧ (keepB csX fsX (LsX.getD 76 0)=false ∨ LsX.getD 76 0∈keepLsX) := by decide +kernel
theorem x_b77 : bracketOK csX (LsX.getD 77 0)=true ∧ (keepB csX fsX (LsX.getD 77 0)=false ∨ LsX.getD 77 0∈keepLsX) := by decide +kernel
theorem x_b78 : bracketOK csX (LsX.getD 78 0)=true ∧ (keepB csX fsX (LsX.getD 78 0)=false ∨ LsX.getD 78 0∈keepLsX) := by decide +kernel
theorem x_b79 : bracketOK csX (LsX.getD 79 0)=true ∧ (keepB csX fsX (LsX.getD 79 0)=false ∨ LsX.getD 79 0∈keepLsX) := by decide +kernel
theorem x_b80 : bracketOK csX (LsX.getD 80 0)=true ∧ (keepB csX fsX (LsX.getD 80 0)=false ∨ LsX.getD 80 0∈keepLsX) := by decide +kernel
theorem x_b81 : bracketOK csX (LsX.getD 81 0)=true ∧ (keepB csX fsX (LsX.getD 81 0)=false ∨ LsX.getD 81 0∈keepLsX) := by decide +kernel
theorem x_b82 : bracketOK csX (LsX.getD 82 0)=true ∧ (keepB csX fsX (LsX.getD 82 0)=false ∨ LsX.getD 82 0∈keepLsX) := by decide +kernel
theorem x_b83 : bracketOK csX (LsX.getD 83 0)=true ∧ (keepB csX fsX (LsX.getD 83 0)=false ∨ LsX.getD 83 0∈keepLsX) := by decide +kernel
theorem x_b84 : bracketOK csX (LsX.getD 84 0)=true ∧ (keepB csX fsX (LsX.getD 84 0)=false ∨ LsX.getD 84 0∈keepLsX) := by decide +kernel
theorem x_b85 : bracketOK csX (LsX.getD 85 0)=true ∧ (keepB csX fsX (LsX.getD 85 0)=false ∨ LsX.getD 85 0∈keepLsX) := by decide +kernel
theorem x_b86 : bracketOK csX (LsX.getD 86 0)=true ∧ (keepB csX fsX (LsX.getD 86 0)=false ∨ LsX.getD 86 0∈keepLsX) := by decide +kernel
theorem x_b87 : bracketOK csX (LsX.getD 87 0)=true ∧ (keepB csX fsX (LsX.getD 87 0)=false ∨ LsX.getD 87 0∈keepLsX) := by decide +kernel
theorem x_b88 : bracketOK csX (LsX.getD 88 0)=true ∧ (keepB csX fsX (LsX.getD 88 0)=false ∨ LsX.getD 88 0∈keepLsX) := by decide +kernel
theorem x_b89 : bracketOK csX (LsX.getD 89 0)=true ∧ (keepB csX fsX (LsX.getD 89 0)=false ∨ LsX.getD 89 0∈keepLsX) := by decide +kernel
theorem x_b90 : bracketOK csX (LsX.getD 90 0)=true ∧ (keepB csX fsX (LsX.getD 90 0)=false ∨ LsX.getD 90 0∈keepLsX) := by decide +kernel
theorem x_b91 : bracketOK csX (LsX.getD 91 0)=true ∧ (keepB csX fsX (LsX.getD 91 0)=false ∨ LsX.getD 91 0∈keepLsX) := by decide +kernel
theorem x_b92 : bracketOK csX (LsX.getD 92 0)=true ∧ (keepB csX fsX (LsX.getD 92 0)=false ∨ LsX.getD 92 0∈keepLsX) := by decide +kernel
theorem x_b93 : bracketOK csX (LsX.getD 93 0)=true ∧ (keepB csX fsX (LsX.getD 93 0)=false ∨ LsX.getD 93 0∈keepLsX) := by decide +kernel
theorem x_b94 : bracketOK csX (LsX.getD 94 0)=true ∧ (keepB csX fsX (LsX.getD 94 0)=false ∨ LsX.getD 94 0∈keepLsX) := by decide +kernel
theorem x_b95 : bracketOK csX (LsX.getD 95 0)=true ∧ (keepB csX fsX (LsX.getD 95 0)=false ∨ LsX.getD 95 0∈keepLsX) := by decide +kernel
theorem x_b96 : bracketOK csX (LsX.getD 96 0)=true ∧ (keepB csX fsX (LsX.getD 96 0)=false ∨ LsX.getD 96 0∈keepLsX) := by decide +kernel
theorem x_b97 : bracketOK csX (LsX.getD 97 0)=true ∧ (keepB csX fsX (LsX.getD 97 0)=false ∨ LsX.getD 97 0∈keepLsX) := by decide +kernel
theorem x_b98 : bracketOK csX (LsX.getD 98 0)=true ∧ (keepB csX fsX (LsX.getD 98 0)=false ∨ LsX.getD 98 0∈keepLsX) := by decide +kernel
theorem x_b99 : bracketOK csX (LsX.getD 99 0)=true ∧ (keepB csX fsX (LsX.getD 99 0)=false ∨ LsX.getD 99 0∈keepLsX) := by decide +kernel
theorem x_b100 : bracketOK csX (LsX.getD 100 0)=true ∧ (keepB csX fsX (LsX.getD 100 0)=false ∨ LsX.getD 100 0∈keepLsX) := by decide +kernel
theorem x_b101 : bracketOK csX (LsX.getD 101 0)=true ∧ (keepB csX fsX (LsX.getD 101 0)=false ∨ LsX.getD 101 0∈keepLsX) := by decide +kernel
theorem x_b102 : bracketOK csX (LsX.getD 102 0)=true ∧ (keepB csX fsX (LsX.getD 102 0)=false ∨ LsX.getD 102 0∈keepLsX) := by decide +kernel
theorem x_b103 : bracketOK csX (LsX.getD 103 0)=true ∧ (keepB csX fsX (LsX.getD 103 0)=false ∨ LsX.getD 103 0∈keepLsX) := by decide +kernel
theorem x_b104 : bracketOK csX (LsX.getD 104 0)=true ∧ (keepB csX fsX (LsX.getD 104 0)=false ∨ LsX.getD 104 0∈keepLsX) := by decide +kernel
theorem x_b105 : bracketOK csX (LsX.getD 105 0)=true ∧ (keepB csX fsX (LsX.getD 105 0)=false ∨ LsX.getD 105 0∈keepLsX) := by decide +kernel
theorem x_b106 : bracketOK csX (LsX.getD 106 0)=true ∧ (keepB csX fsX (LsX.getD 106 0)=false ∨ LsX.getD 106 0∈keepLsX) := by decide +kernel
theorem x_b107 : bracketOK csX (LsX.getD 107 0)=true ∧ (keepB csX fsX (LsX.getD 107 0)=false ∨ LsX.getD 107 0∈keepLsX) := by decide +kernel
theorem x_b108 : bracketOK csX (LsX.getD 108 0)=true ∧ (keepB csX fsX (LsX.getD 108 0)=false ∨ LsX.getD 108 0∈keepLsX) := by decide +kernel
theorem x_b109 : bracketOK csX (LsX.getD 109 0)=true ∧ (keepB csX fsX (LsX.getD 109 0)=false ∨ LsX.getD 109 0∈keepLsX) := by decide +kernel
theorem x_b110 : bracketOK csX (LsX.getD 110 0)=true ∧ (keepB csX fsX (LsX.getD 110 0)=false ∨ LsX.getD 110 0∈keepLsX) := by decide +kernel
theorem x_b111 : bracketOK csX (LsX.getD 111 0)=true ∧ (keepB csX fsX (LsX.getD 111 0)=false ∨ LsX.getD 111 0∈keepLsX) := by decide +kernel
theorem x_b112 : bracketOK csX (LsX.getD 112 0)=true ∧ (keepB csX fsX (LsX.getD 112 0)=false ∨ LsX.getD 112 0∈keepLsX) := by decide +kernel
theorem x_b113 : bracketOK csX (LsX.getD 113 0)=true ∧ (keepB csX fsX (LsX.getD 113 0)=false ∨ LsX.getD 113 0∈keepLsX) := by decide +kernel
theorem x_b114 : bracketOK csX (LsX.getD 114 0)=true ∧ (keepB csX fsX (LsX.getD 114 0)=false ∨ LsX.getD 114 0∈keepLsX) := by decide +kernel
theorem x_b115 : bracketOK csX (LsX.getD 115 0)=true ∧ (keepB csX fsX (LsX.getD 115 0)=false ∨ LsX.getD 115 0∈keepLsX) := by decide +kernel
theorem x_b116 : bracketOK csX (LsX.getD 116 0)=true ∧ (keepB csX fsX (LsX.getD 116 0)=false ∨ LsX.getD 116 0∈keepLsX) := by decide +kernel
theorem x_b117 : bracketOK csX (LsX.getD 117 0)=true ∧ (keepB csX fsX (LsX.getD 117 0)=false ∨ LsX.getD 117 0∈keepLsX) := by decide +kernel
theorem x_b118 : bracketOK csX (LsX.getD 118 0)=true ∧ (keepB csX fsX (LsX.getD 118 0)=false ∨ LsX.getD 118 0∈keepLsX) := by decide +kernel
theorem x_b119 : bracketOK csX (LsX.getD 119 0)=true ∧ (keepB csX fsX (LsX.getD 119 0)=false ∨ LsX.getD 119 0∈keepLsX) := by decide +kernel
theorem x_b120 : bracketOK csX (LsX.getD 120 0)=true ∧ (keepB csX fsX (LsX.getD 120 0)=false ∨ LsX.getD 120 0∈keepLsX) := by decide +kernel
theorem x_b121 : bracketOK csX (LsX.getD 121 0)=true ∧ (keepB csX fsX (LsX.getD 121 0)=false ∨ LsX.getD 121 0∈keepLsX) := by decide +kernel
theorem x_b122 : bracketOK csX (LsX.getD 122 0)=true ∧ (keepB csX fsX (LsX.getD 122 0)=false ∨ LsX.getD 122 0∈keepLsX) := by decide +kernel
theorem x_b123 : bracketOK csX (LsX.getD 123 0)=true ∧ (keepB csX fsX (LsX.getD 123 0)=false ∨ LsX.getD 123 0∈keepLsX) := by decide +kernel
theorem x_b124 : bracketOK csX (LsX.getD 124 0)=true ∧ (keepB csX fsX (LsX.getD 124 0)=false ∨ LsX.getD 124 0∈keepLsX) := by decide +kernel
theorem x_b125 : bracketOK csX (LsX.getD 125 0)=true ∧ (keepB csX fsX (LsX.getD 125 0)=false ∨ LsX.getD 125 0∈keepLsX) := by decide +kernel
theorem x_b126 : bracketOK csX (LsX.getD 126 0)=true ∧ (keepB csX fsX (LsX.getD 126 0)=false ∨ LsX.getD 126 0∈keepLsX) := by decide +kernel
theorem x_b127 : bracketOK csX (LsX.getD 127 0)=true ∧ (keepB csX fsX (LsX.getD 127 0)=false ∨ LsX.getD 127 0∈keepLsX) := by decide +kernel
theorem x_b128 : bracketOK csX (LsX.getD 128 0)=true ∧ (keepB csX fsX (LsX.getD 128 0)=false ∨ LsX.getD 128 0∈keepLsX) := by decide +kernel
theorem x_b129 : bracketOK csX (LsX.getD 129 0)=true ∧ (keepB csX fsX (LsX.getD 129 0)=false ∨ LsX.getD 129 0∈keepLsX) := by decide +kernel
theorem x_b130 : bracketOK csX (LsX.getD 130 0)=true ∧ (keepB csX fsX (LsX.getD 130 0)=false ∨ LsX.getD 130 0∈keepLsX) := by decide +kernel
theorem x_b131 : bracketOK csX (LsX.getD 131 0)=true ∧ (keepB csX fsX (LsX.getD 131 0)=false ∨ LsX.getD 131 0∈keepLsX) := by decide +kernel
theorem x_b132 : bracketOK csX (LsX.getD 132 0)=true ∧ (keepB csX fsX (LsX.getD 132 0)=false ∨ LsX.getD 132 0∈keepLsX) := by decide +kernel
theorem x_b133 : bracketOK csX (LsX.getD 133 0)=true ∧ (keepB csX fsX (LsX.getD 133 0)=false ∨ LsX.getD 133 0∈keepLsX) := by decide +kernel
theorem x_b134 : bracketOK csX (LsX.getD 134 0)=true ∧ (keepB csX fsX (LsX.getD 134 0)=false ∨ LsX.getD 134 0∈keepLsX) := by decide +kernel
theorem x_b135 : bracketOK csX (LsX.getD 135 0)=true ∧ (keepB csX fsX (LsX.getD 135 0)=false ∨ LsX.getD 135 0∈keepLsX) := by decide +kernel
theorem x_b136 : bracketOK csX (LsX.getD 136 0)=true ∧ (keepB csX fsX (LsX.getD 136 0)=false ∨ LsX.getD 136 0∈keepLsX) := by decide +kernel
theorem x_b137 : bracketOK csX (LsX.getD 137 0)=true ∧ (keepB csX fsX (LsX.getD 137 0)=false ∨ LsX.getD 137 0∈keepLsX) := by decide +kernel
theorem x_b138 : bracketOK csX (LsX.getD 138 0)=true ∧ (keepB csX fsX (LsX.getD 138 0)=false ∨ LsX.getD 138 0∈keepLsX) := by decide +kernel
theorem x_b139 : bracketOK csX (LsX.getD 139 0)=true ∧ (keepB csX fsX (LsX.getD 139 0)=false ∨ LsX.getD 139 0∈keepLsX) := by decide +kernel
theorem x_b140 : bracketOK csX (LsX.getD 140 0)=true ∧ (keepB csX fsX (LsX.getD 140 0)=false ∨ LsX.getD 140 0∈keepLsX) := by decide +kernel
theorem x_b141 : bracketOK csX (LsX.getD 141 0)=true ∧ (keepB csX fsX (LsX.getD 141 0)=false ∨ LsX.getD 141 0∈keepLsX) := by decide +kernel
theorem x_b142 : bracketOK csX (LsX.getD 142 0)=true ∧ (keepB csX fsX (LsX.getD 142 0)=false ∨ LsX.getD 142 0∈keepLsX) := by decide +kernel
theorem x_b143 : bracketOK csX (LsX.getD 143 0)=true ∧ (keepB csX fsX (LsX.getD 143 0)=false ∨ LsX.getD 143 0∈keepLsX) := by decide +kernel
theorem x_b144 : bracketOK csX (LsX.getD 144 0)=true ∧ (keepB csX fsX (LsX.getD 144 0)=false ∨ LsX.getD 144 0∈keepLsX) := by decide +kernel
theorem x_b145 : bracketOK csX (LsX.getD 145 0)=true ∧ (keepB csX fsX (LsX.getD 145 0)=false ∨ LsX.getD 145 0∈keepLsX) := by decide +kernel
theorem x_b146 : bracketOK csX (LsX.getD 146 0)=true ∧ (keepB csX fsX (LsX.getD 146 0)=false ∨ LsX.getD 146 0∈keepLsX) := by decide +kernel
theorem x_b147 : bracketOK csX (LsX.getD 147 0)=true ∧ (keepB csX fsX (LsX.getD 147 0)=false ∨ LsX.getD 147 0∈keepLsX) := by decide +kernel
theorem x_b148 : bracketOK csX (LsX.getD 148 0)=true ∧ (keepB csX fsX (LsX.getD 148 0)=false ∨ LsX.getD 148 0∈keepLsX) := by decide +kernel
theorem x_b149 : bracketOK csX (LsX.getD 149 0)=true ∧ (keepB csX fsX (LsX.getD 149 0)=false ∨ LsX.getD 149 0∈keepLsX) := by decide +kernel
theorem x_b150 : bracketOK csX (LsX.getD 150 0)=true ∧ (keepB csX fsX (LsX.getD 150 0)=false ∨ LsX.getD 150 0∈keepLsX) := by decide +kernel
theorem x_b151 : bracketOK csX (LsX.getD 151 0)=true ∧ (keepB csX fsX (LsX.getD 151 0)=false ∨ LsX.getD 151 0∈keepLsX) := by decide +kernel
theorem x_b152 : bracketOK csX (LsX.getD 152 0)=true ∧ (keepB csX fsX (LsX.getD 152 0)=false ∨ LsX.getD 152 0∈keepLsX) := by decide +kernel
theorem x_b153 : bracketOK csX (LsX.getD 153 0)=true ∧ (keepB csX fsX (LsX.getD 153 0)=false ∨ LsX.getD 153 0∈keepLsX) := by decide +kernel
theorem x_b154 : bracketOK csX (LsX.getD 154 0)=true ∧ (keepB csX fsX (LsX.getD 154 0)=false ∨ LsX.getD 154 0∈keepLsX) := by decide +kernel
theorem x_b155 : bracketOK csX (LsX.getD 155 0)=true ∧ (keepB csX fsX (LsX.getD 155 0)=false ∨ LsX.getD 155 0∈keepLsX) := by decide +kernel
theorem x_b156 : bracketOK csX (LsX.getD 156 0)=true ∧ (keepB csX fsX (LsX.getD 156 0)=false ∨ LsX.getD 156 0∈keepLsX) := by decide +kernel
theorem x_b157 : bracketOK csX (LsX.getD 157 0)=true ∧ (keepB csX fsX (LsX.getD 157 0)=false ∨ LsX.getD 157 0∈keepLsX) := by decide +kernel
theorem x_b158 : bracketOK csX (LsX.getD 158 0)=true ∧ (keepB csX fsX (LsX.getD 158 0)=false ∨ LsX.getD 158 0∈keepLsX) := by decide +kernel
theorem x_b159 : bracketOK csX (LsX.getD 159 0)=true ∧ (keepB csX fsX (LsX.getD 159 0)=false ∨ LsX.getD 159 0∈keepLsX) := by decide +kernel
theorem x_b160 : bracketOK csX (LsX.getD 160 0)=true ∧ (keepB csX fsX (LsX.getD 160 0)=false ∨ LsX.getD 160 0∈keepLsX) := by decide +kernel
theorem x_b161 : bracketOK csX (LsX.getD 161 0)=true ∧ (keepB csX fsX (LsX.getD 161 0)=false ∨ LsX.getD 161 0∈keepLsX) := by decide +kernel
theorem x_b162 : bracketOK csX (LsX.getD 162 0)=true ∧ (keepB csX fsX (LsX.getD 162 0)=false ∨ LsX.getD 162 0∈keepLsX) := by decide +kernel
theorem x_b163 : bracketOK csX (LsX.getD 163 0)=true ∧ (keepB csX fsX (LsX.getD 163 0)=false ∨ LsX.getD 163 0∈keepLsX) := by decide +kernel
theorem x_b164 : bracketOK csX (LsX.getD 164 0)=true ∧ (keepB csX fsX (LsX.getD 164 0)=false ∨ LsX.getD 164 0∈keepLsX) := by decide +kernel
theorem x_b165 : bracketOK csX (LsX.getD 165 0)=true ∧ (keepB csX fsX (LsX.getD 165 0)=false ∨ LsX.getD 165 0∈keepLsX) := by decide +kernel
theorem x_b166 : bracketOK csX (LsX.getD 166 0)=true ∧ (keepB csX fsX (LsX.getD 166 0)=false ∨ LsX.getD 166 0∈keepLsX) := by decide +kernel
theorem x_b167 : bracketOK csX (LsX.getD 167 0)=true ∧ (keepB csX fsX (LsX.getD 167 0)=false ∨ LsX.getD 167 0∈keepLsX) := by decide +kernel
theorem x_b168 : bracketOK csX (LsX.getD 168 0)=true ∧ (keepB csX fsX (LsX.getD 168 0)=false ∨ LsX.getD 168 0∈keepLsX) := by decide +kernel
theorem x_b169 : bracketOK csX (LsX.getD 169 0)=true ∧ (keepB csX fsX (LsX.getD 169 0)=false ∨ LsX.getD 169 0∈keepLsX) := by decide +kernel
theorem x_b170 : bracketOK csX (LsX.getD 170 0)=true ∧ (keepB csX fsX (LsX.getD 170 0)=false ∨ LsX.getD 170 0∈keepLsX) := by decide +kernel
theorem x_b171 : bracketOK csX (LsX.getD 171 0)=true ∧ (keepB csX fsX (LsX.getD 171 0)=false ∨ LsX.getD 171 0∈keepLsX) := by decide +kernel
theorem x_b172 : bracketOK csX (LsX.getD 172 0)=true ∧ (keepB csX fsX (LsX.getD 172 0)=false ∨ LsX.getD 172 0∈keepLsX) := by decide +kernel
theorem x_b173 : bracketOK csX (LsX.getD 173 0)=true ∧ (keepB csX fsX (LsX.getD 173 0)=false ∨ LsX.getD 173 0∈keepLsX) := by decide +kernel
theorem x_b174 : bracketOK csX (LsX.getD 174 0)=true ∧ (keepB csX fsX (LsX.getD 174 0)=false ∨ LsX.getD 174 0∈keepLsX) := by decide +kernel
theorem x_b175 : bracketOK csX (LsX.getD 175 0)=true ∧ (keepB csX fsX (LsX.getD 175 0)=false ∨ LsX.getD 175 0∈keepLsX) := by decide +kernel
theorem x_b176 : bracketOK csX (LsX.getD 176 0)=true ∧ (keepB csX fsX (LsX.getD 176 0)=false ∨ LsX.getD 176 0∈keepLsX) := by decide +kernel
theorem x_b177 : bracketOK csX (LsX.getD 177 0)=true ∧ (keepB csX fsX (LsX.getD 177 0)=false ∨ LsX.getD 177 0∈keepLsX) := by decide +kernel
theorem x_b178 : bracketOK csX (LsX.getD 178 0)=true ∧ (keepB csX fsX (LsX.getD 178 0)=false ∨ LsX.getD 178 0∈keepLsX) := by decide +kernel
theorem x_b179 : bracketOK csX (LsX.getD 179 0)=true ∧ (keepB csX fsX (LsX.getD 179 0)=false ∨ LsX.getD 179 0∈keepLsX) := by decide +kernel
theorem x_b180 : bracketOK csX (LsX.getD 180 0)=true ∧ (keepB csX fsX (LsX.getD 180 0)=false ∨ LsX.getD 180 0∈keepLsX) := by decide +kernel
theorem x_b181 : bracketOK csX (LsX.getD 181 0)=true ∧ (keepB csX fsX (LsX.getD 181 0)=false ∨ LsX.getD 181 0∈keepLsX) := by decide +kernel
theorem x_b182 : bracketOK csX (LsX.getD 182 0)=true ∧ (keepB csX fsX (LsX.getD 182 0)=false ∨ LsX.getD 182 0∈keepLsX) := by decide +kernel
theorem x_b183 : bracketOK csX (LsX.getD 183 0)=true ∧ (keepB csX fsX (LsX.getD 183 0)=false ∨ LsX.getD 183 0∈keepLsX) := by decide +kernel
theorem x_b184 : bracketOK csX (LsX.getD 184 0)=true ∧ (keepB csX fsX (LsX.getD 184 0)=false ∨ LsX.getD 184 0∈keepLsX) := by decide +kernel
theorem x_b185 : bracketOK csX (LsX.getD 185 0)=true ∧ (keepB csX fsX (LsX.getD 185 0)=false ∨ LsX.getD 185 0∈keepLsX) := by decide +kernel
theorem x_b186 : bracketOK csX (LsX.getD 186 0)=true ∧ (keepB csX fsX (LsX.getD 186 0)=false ∨ LsX.getD 186 0∈keepLsX) := by decide +kernel
theorem x_b187 : bracketOK csX (LsX.getD 187 0)=true ∧ (keepB csX fsX (LsX.getD 187 0)=false ∨ LsX.getD 187 0∈keepLsX) := by decide +kernel
theorem x_b188 : bracketOK csX (LsX.getD 188 0)=true ∧ (keepB csX fsX (LsX.getD 188 0)=false ∨ LsX.getD 188 0∈keepLsX) := by decide +kernel
theorem x_b189 : bracketOK csX (LsX.getD 189 0)=true ∧ (keepB csX fsX (LsX.getD 189 0)=false ∨ LsX.getD 189 0∈keepLsX) := by decide +kernel
theorem x_b190 : bracketOK csX (LsX.getD 190 0)=true ∧ (keepB csX fsX (LsX.getD 190 0)=false ∨ LsX.getD 190 0∈keepLsX) := by decide +kernel
theorem x_b191 : bracketOK csX (LsX.getD 191 0)=true ∧ (keepB csX fsX (LsX.getD 191 0)=false ∨ LsX.getD 191 0∈keepLsX) := by decide +kernel
theorem x_b192 : bracketOK csX (LsX.getD 192 0)=true ∧ (keepB csX fsX (LsX.getD 192 0)=false ∨ LsX.getD 192 0∈keepLsX) := by decide +kernel
theorem x_b193 : bracketOK csX (LsX.getD 193 0)=true ∧ (keepB csX fsX (LsX.getD 193 0)=false ∨ LsX.getD 193 0∈keepLsX) := by decide +kernel
theorem x_b194 : bracketOK csX (LsX.getD 194 0)=true ∧ (keepB csX fsX (LsX.getD 194 0)=false ∨ LsX.getD 194 0∈keepLsX) := by decide +kernel
theorem x_b195 : bracketOK csX (LsX.getD 195 0)=true ∧ (keepB csX fsX (LsX.getD 195 0)=false ∨ LsX.getD 195 0∈keepLsX) := by decide +kernel
theorem x_b196 : bracketOK csX (LsX.getD 196 0)=true ∧ (keepB csX fsX (LsX.getD 196 0)=false ∨ LsX.getD 196 0∈keepLsX) := by decide +kernel
theorem x_b197 : bracketOK csX (LsX.getD 197 0)=true ∧ (keepB csX fsX (LsX.getD 197 0)=false ∨ LsX.getD 197 0∈keepLsX) := by decide +kernel
theorem x_hlen : LsX.length=198 := by decide +kernel
theorem x_hall : ∀ i,i<LsX.length → (bracketOK csX (LsX.getD i 0)=true ∧ (keepB csX fsX (LsX.getD i 0)=false ∨ LsX.getD i 0∈keepLsX)) := by
  intro i hi
  rw [x_hlen] at hi
  interval_cases i
  · exact x_b0
  · exact x_b1
  · exact x_b2
  · exact x_b3
  · exact x_b4
  · exact x_b5
  · exact x_b6
  · exact x_b7
  · exact x_b8
  · exact x_b9
  · exact x_b10
  · exact x_b11
  · exact x_b12
  · exact x_b13
  · exact x_b14
  · exact x_b15
  · exact x_b16
  · exact x_b17
  · exact x_b18
  · exact x_b19
  · exact x_b20
  · exact x_b21
  · exact x_b22
  · exact x_b23
  · exact x_b24
  · exact x_b25
  · exact x_b26
  · exact x_b27
  · exact x_b28
  · exact x_b29
  · exact x_b30
  · exact x_b31
  · exact x_b32
  · exact x_b33
  · exact x_b34
  · exact x_b35
  · exact x_b36
  · exact x_b37
  · exact x_b38
  · exact x_b39
  · exact x_b40
  · exact x_b41
  · exact x_b42
  · exact x_b43
  · exact x_b44
  · exact x_b45
  · exact x_b46
  · exact x_b47
  · exact x_b48
  · exact x_b49
  · exact x_b50
  · exact x_b51
  · exact x_b52
  · exact x_b53
  · exact x_b54
  · exact x_b55
  · exact x_b56
  · exact x_b57
  · exact x_b58
  · exact x_b59
  · exact x_b60
  · exact x_b61
  · exact x_b62
  · exact x_b63
  · exact x_b64
  · exact x_b65
  · exact x_b66
  · exact x_b67
  · exact x_b68
  · exact x_b69
  · exact x_b70
  · exact x_b71
  · exact x_b72
  · exact x_b73
  · exact x_b74
  · exact x_b75
  · exact x_b76
  · exact x_b77
  · exact x_b78
  · exact x_b79
  · exact x_b80
  · exact x_b81
  · exact x_b82
  · exact x_b83
  · exact x_b84
  · exact x_b85
  · exact x_b86
  · exact x_b87
  · exact x_b88
  · exact x_b89
  · exact x_b90
  · exact x_b91
  · exact x_b92
  · exact x_b93
  · exact x_b94
  · exact x_b95
  · exact x_b96
  · exact x_b97
  · exact x_b98
  · exact x_b99
  · exact x_b100
  · exact x_b101
  · exact x_b102
  · exact x_b103
  · exact x_b104
  · exact x_b105
  · exact x_b106
  · exact x_b107
  · exact x_b108
  · exact x_b109
  · exact x_b110
  · exact x_b111
  · exact x_b112
  · exact x_b113
  · exact x_b114
  · exact x_b115
  · exact x_b116
  · exact x_b117
  · exact x_b118
  · exact x_b119
  · exact x_b120
  · exact x_b121
  · exact x_b122
  · exact x_b123
  · exact x_b124
  · exact x_b125
  · exact x_b126
  · exact x_b127
  · exact x_b128
  · exact x_b129
  · exact x_b130
  · exact x_b131
  · exact x_b132
  · exact x_b133
  · exact x_b134
  · exact x_b135
  · exact x_b136
  · exact x_b137
  · exact x_b138
  · exact x_b139
  · exact x_b140
  · exact x_b141
  · exact x_b142
  · exact x_b143
  · exact x_b144
  · exact x_b145
  · exact x_b146
  · exact x_b147
  · exact x_b148
  · exact x_b149
  · exact x_b150
  · exact x_b151
  · exact x_b152
  · exact x_b153
  · exact x_b154
  · exact x_b155
  · exact x_b156
  · exact x_b157
  · exact x_b158
  · exact x_b159
  · exact x_b160
  · exact x_b161
  · exact x_b162
  · exact x_b163
  · exact x_b164
  · exact x_b165
  · exact x_b166
  · exact x_b167
  · exact x_b168
  · exact x_b169
  · exact x_b170
  · exact x_b171
  · exact x_b172
  · exact x_b173
  · exact x_b174
  · exact x_b175
  · exact x_b176
  · exact x_b177
  · exact x_b178
  · exact x_b179
  · exact x_b180
  · exact x_b181
  · exact x_b182
  · exact x_b183
  · exact x_b184
  · exact x_b185
  · exact x_b186
  · exact x_b187
  · exact x_b188
  · exact x_b189
  · exact x_b190
  · exact x_b191
  · exact x_b192
  · exact x_b193
  · exact x_b194
  · exact x_b195
  · exact x_b196
  · exact x_b197
theorem x_hbr : ∀ l∈LsX,bracketOK csX l=true := by
  intro l hl
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hl
  have := (x_hall i hi).1
  rw [show LsX.getD i 0=LsX[i] from by rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]; rfl] at this
  exact this
theorem x_hkeep : ∀ l∈LsX,keepB csX fsX l=true → l∈keepLsX := by
  intro l hl hk
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hl
  have := (x_hall i hi).2
  rw [show LsX.getD i 0=LsX[i] from by rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]; rfl] at this
  rcases this with h | h
  · rw [h] at hk; exact absurd hk (by decide)
  · exact h
#print axioms x_hbr
#print axioms x_hkeep
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBr
