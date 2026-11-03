module
public import CatalanMeasure.GenD.ResInv
public import CatalanMeasure.GenD.Nonvanishing
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.Data.C3.Data
public import Mathlib.Tactic.NormNum.Prime
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.C3
open Polynomial CatalanMeasure.GenD ResCheck ResBase ResInv ResRec CatalanMeasure.Parametric
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50
instance fact1009' : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

theorem cIV : chkIV 1009 98 ivT = true := by decide +kernel
-- kcost: 1 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cMS : chkMS 1009 97 msT = true := by decide +kernel
-- kcost: 1 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cBM : chkBM 1009 97 msT bmT = true := by decide +kernel
-- kcost: 1 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cBP : chkBP 1009 87 bpT ivT = true := by decide +kernel
-- kcost: 1 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cH1 : chkH1 1009 97 h1T ivT = true := by decide +kernel
-- kcost: 1 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cMT : chkMT 1009 97 87 msT bmT bpT ivT momT = true := by decide +kernel
-- kcost: 15 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cZT : chkZT 1009 97 87 h1T ivT zetT = true := by decide +kernel
-- kcost: 15 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cPoly : chkPoly dc72.toParameters 1009 prT drT = true := by decide +kernel
-- kcost: 60 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cFM : chkF 1009 4 11 72 97 wT momT fmT = true := by decide +kernel
-- kcost: 15 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cFZ : chkF 1009 4 11 72 97 wT zetT fzT = true := by decide +kernel
-- kcost: 15 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem cLen : chkLen 72 97 prT drT fmT fzT = true := by decide +kernel
-- kcost: 2 s estimated; shared once per table (H97,L87,n72,q4), no repeated moment construction.

theorem hW : ∀ v, v < dc72.toParameters.q0 + 1 →
    (nth wT v : ZMod 1009) = baseFilterWeight dc72.toParameters 1009 v := by decide +kernel
-- kcost: 1 s estimated; five filter values modulo1009, not1009 iterations.
theorem hcN : ((2 * 503 + 3) % 1009 == 0 % 1009) = true := by decide +kernel

-- kcost: 0.01 s estimated; one scalar residue equality.
theorem cBase_0 : chkBase 1009 72 503 baseT prT drT fmT fzT 0 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_1 : chkBase 1009 72 503 baseT prT drT fmT fzT 1 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_2 : chkBase 1009 72 503 baseT prT drT fmT fzT 2 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_3 : chkBase 1009 72 503 baseT prT drT fmT fzT 3 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_4 : chkBase 1009 72 503 baseT prT drT fmT fzT 4 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_5 : chkBase 1009 72 503 baseT prT drT fmT fzT 5 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_6 : chkBase 1009 72 503 baseT prT drT fmT fzT 6 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_7 : chkBase 1009 72 503 baseT prT drT fmT fzT 7 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_8 : chkBase 1009 72 503 baseT prT drT fmT fzT 8 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_9 : chkBase 1009 72 503 baseT prT drT fmT fzT 9 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_10 : chkBase 1009 72 503 baseT prT drT fmT fzT 10 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_11 : chkBase 1009 72 503 baseT prT drT fmT fzT 11 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_12 : chkBase 1009 72 503 baseT prT drT fmT fzT 12 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_13 : chkBase 1009 72 503 baseT prT drT fmT fzT 13 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_14 : chkBase 1009 72 503 baseT prT drT fmT fzT 14 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_15 : chkBase 1009 72 503 baseT prT drT fmT fzT 15 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_16 : chkBase 1009 72 503 baseT prT drT fmT fzT 16 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_17 : chkBase 1009 72 503 baseT prT drT fmT fzT 17 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_18 : chkBase 1009 72 503 baseT prT drT fmT fzT 18 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_19 : chkBase 1009 72 503 baseT prT drT fmT fzT 19 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_20 : chkBase 1009 72 503 baseT prT drT fmT fzT 20 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_21 : chkBase 1009 72 503 baseT prT drT fmT fzT 21 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_22 : chkBase 1009 72 503 baseT prT drT fmT fzT 22 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_23 : chkBase 1009 72 503 baseT prT drT fmT fzT 23 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_24 : chkBase 1009 72 503 baseT prT drT fmT fzT 24 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_25 : chkBase 1009 72 503 baseT prT drT fmT fzT 25 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_26 : chkBase 1009 72 503 baseT prT drT fmT fzT 26 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_27 : chkBase 1009 72 503 baseT prT drT fmT fzT 27 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_28 : chkBase 1009 72 503 baseT prT drT fmT fzT 28 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_29 : chkBase 1009 72 503 baseT prT drT fmT fzT 29 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_30 : chkBase 1009 72 503 baseT prT drT fmT fzT 30 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_31 : chkBase 1009 72 503 baseT prT drT fmT fzT 31 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_32 : chkBase 1009 72 503 baseT prT drT fmT fzT 32 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_33 : chkBase 1009 72 503 baseT prT drT fmT fzT 33 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_34 : chkBase 1009 72 503 baseT prT drT fmT fzT 34 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_35 : chkBase 1009 72 503 baseT prT drT fmT fzT 35 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_36 : chkBase 1009 72 503 baseT prT drT fmT fzT 36 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_37 : chkBase 1009 72 503 baseT prT drT fmT fzT 37 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_38 : chkBase 1009 72 503 baseT prT drT fmT fzT 38 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_39 : chkBase 1009 72 503 baseT prT drT fmT fzT 39 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_40 : chkBase 1009 72 503 baseT prT drT fmT fzT 40 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_41 : chkBase 1009 72 503 baseT prT drT fmT fzT 41 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_42 : chkBase 1009 72 503 baseT prT drT fmT fzT 42 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_43 : chkBase 1009 72 503 baseT prT drT fmT fzT 43 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_44 : chkBase 1009 72 503 baseT prT drT fmT fzT 44 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_45 : chkBase 1009 72 503 baseT prT drT fmT fzT 45 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_46 : chkBase 1009 72 503 baseT prT drT fmT fzT 46 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_47 : chkBase 1009 72 503 baseT prT drT fmT fzT 47 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_48 : chkBase 1009 72 503 baseT prT drT fmT fzT 48 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_49 : chkBase 1009 72 503 baseT prT drT fmT fzT 49 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_50 : chkBase 1009 72 503 baseT prT drT fmT fzT 50 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_51 : chkBase 1009 72 503 baseT prT drT fmT fzT 51 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_52 : chkBase 1009 72 503 baseT prT drT fmT fzT 52 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_53 : chkBase 1009 72 503 baseT prT drT fmT fzT 53 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_54 : chkBase 1009 72 503 baseT prT drT fmT fzT 54 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_55 : chkBase 1009 72 503 baseT prT drT fmT fzT 55 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_56 : chkBase 1009 72 503 baseT prT drT fmT fzT 56 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_57 : chkBase 1009 72 503 baseT prT drT fmT fzT 57 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_58 : chkBase 1009 72 503 baseT prT drT fmT fzT 58 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_59 : chkBase 1009 72 503 baseT prT drT fmT fzT 59 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_60 : chkBase 1009 72 503 baseT prT drT fmT fzT 60 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_61 : chkBase 1009 72 503 baseT prT drT fmT fzT 61 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_62 : chkBase 1009 72 503 baseT prT drT fmT fzT 62 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_63 : chkBase 1009 72 503 baseT prT drT fmT fzT 63 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_64 : chkBase 1009 72 503 baseT prT drT fmT fzT 64 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_65 : chkBase 1009 72 503 baseT prT drT fmT fzT 65 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_66 : chkBase 1009 72 503 baseT prT drT fmT fzT 66 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_67 : chkBase 1009 72 503 baseT prT drT fmT fzT 67 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_68 : chkBase 1009 72 503 baseT prT drT fmT fzT 68 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_69 : chkBase 1009 72 503 baseT prT drT fmT fzT 69 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_70 : chkBase 1009 72 503 baseT prT drT fmT fzT 70 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_71 : chkBase 1009 72 503 baseT prT drT fmT fzT 71 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cBase_72 : chkBase 1009 72 503 baseT prT drT fmT fzT 72 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns, two97-term Nat dot products each (13968 multiply/add terms), one row per declaration.

theorem cLenZero : chkInvLen 72 baseT invZeroT = true := by decide +kernel
-- kcost: 1 s estimated;73+72 row-length checks.

theorem cRowZero_0 : chkInvRow 1009 72 0 baseT invZeroT 0 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_1 : chkInvRow 1009 72 0 baseT invZeroT 1 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_2 : chkInvRow 1009 72 0 baseT invZeroT 2 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_3 : chkInvRow 1009 72 0 baseT invZeroT 3 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_4 : chkInvRow 1009 72 0 baseT invZeroT 4 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_5 : chkInvRow 1009 72 0 baseT invZeroT 5 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_6 : chkInvRow 1009 72 0 baseT invZeroT 6 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_7 : chkInvRow 1009 72 0 baseT invZeroT 7 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_8 : chkInvRow 1009 72 0 baseT invZeroT 8 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_9 : chkInvRow 1009 72 0 baseT invZeroT 9 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_10 : chkInvRow 1009 72 0 baseT invZeroT 10 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_11 : chkInvRow 1009 72 0 baseT invZeroT 11 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_12 : chkInvRow 1009 72 0 baseT invZeroT 12 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_13 : chkInvRow 1009 72 0 baseT invZeroT 13 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_14 : chkInvRow 1009 72 0 baseT invZeroT 14 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_15 : chkInvRow 1009 72 0 baseT invZeroT 15 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_16 : chkInvRow 1009 72 0 baseT invZeroT 16 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_17 : chkInvRow 1009 72 0 baseT invZeroT 17 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_18 : chkInvRow 1009 72 0 baseT invZeroT 18 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_19 : chkInvRow 1009 72 0 baseT invZeroT 19 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_20 : chkInvRow 1009 72 0 baseT invZeroT 20 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_21 : chkInvRow 1009 72 0 baseT invZeroT 21 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_22 : chkInvRow 1009 72 0 baseT invZeroT 22 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_23 : chkInvRow 1009 72 0 baseT invZeroT 23 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_24 : chkInvRow 1009 72 0 baseT invZeroT 24 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_25 : chkInvRow 1009 72 0 baseT invZeroT 25 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_26 : chkInvRow 1009 72 0 baseT invZeroT 26 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_27 : chkInvRow 1009 72 0 baseT invZeroT 27 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_28 : chkInvRow 1009 72 0 baseT invZeroT 28 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_29 : chkInvRow 1009 72 0 baseT invZeroT 29 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_30 : chkInvRow 1009 72 0 baseT invZeroT 30 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_31 : chkInvRow 1009 72 0 baseT invZeroT 31 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_32 : chkInvRow 1009 72 0 baseT invZeroT 32 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_33 : chkInvRow 1009 72 0 baseT invZeroT 33 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_34 : chkInvRow 1009 72 0 baseT invZeroT 34 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_35 : chkInvRow 1009 72 0 baseT invZeroT 35 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_36 : chkInvRow 1009 72 0 baseT invZeroT 36 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_37 : chkInvRow 1009 72 0 baseT invZeroT 37 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_38 : chkInvRow 1009 72 0 baseT invZeroT 38 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_39 : chkInvRow 1009 72 0 baseT invZeroT 39 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_40 : chkInvRow 1009 72 0 baseT invZeroT 40 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_41 : chkInvRow 1009 72 0 baseT invZeroT 41 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_42 : chkInvRow 1009 72 0 baseT invZeroT 42 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_43 : chkInvRow 1009 72 0 baseT invZeroT 43 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_44 : chkInvRow 1009 72 0 baseT invZeroT 44 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_45 : chkInvRow 1009 72 0 baseT invZeroT 45 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_46 : chkInvRow 1009 72 0 baseT invZeroT 46 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_47 : chkInvRow 1009 72 0 baseT invZeroT 47 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_48 : chkInvRow 1009 72 0 baseT invZeroT 48 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_49 : chkInvRow 1009 72 0 baseT invZeroT 49 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_50 : chkInvRow 1009 72 0 baseT invZeroT 50 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_51 : chkInvRow 1009 72 0 baseT invZeroT 51 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_52 : chkInvRow 1009 72 0 baseT invZeroT 52 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_53 : chkInvRow 1009 72 0 baseT invZeroT 53 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_54 : chkInvRow 1009 72 0 baseT invZeroT 54 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_55 : chkInvRow 1009 72 0 baseT invZeroT 55 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_56 : chkInvRow 1009 72 0 baseT invZeroT 56 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_57 : chkInvRow 1009 72 0 baseT invZeroT 57 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_58 : chkInvRow 1009 72 0 baseT invZeroT 58 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_59 : chkInvRow 1009 72 0 baseT invZeroT 59 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_60 : chkInvRow 1009 72 0 baseT invZeroT 60 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_61 : chkInvRow 1009 72 0 baseT invZeroT 61 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_62 : chkInvRow 1009 72 0 baseT invZeroT 62 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_63 : chkInvRow 1009 72 0 baseT invZeroT 63 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_64 : chkInvRow 1009 72 0 baseT invZeroT 64 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_65 : chkInvRow 1009 72 0 baseT invZeroT 65 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_66 : chkInvRow 1009 72 0 baseT invZeroT 66 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_67 : chkInvRow 1009 72 0 baseT invZeroT 67 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_68 : chkInvRow 1009 72 0 baseT invZeroT 68 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_69 : chkInvRow 1009 72 0 baseT invZeroT 69 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_70 : chkInvRow 1009 72 0 baseT invZeroT 70 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowZero_71 : chkInvRow 1009 72 0 baseT invZeroT 71 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cLenPlus : chkInvLen 72 baseT invPlusT = true := by decide +kernel
-- kcost: 1 s estimated;73+72 row-length checks.

theorem cRowPlus_0 : chkInvRow 1009 72 1 baseT invPlusT 0 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_1 : chkInvRow 1009 72 1 baseT invPlusT 1 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_2 : chkInvRow 1009 72 1 baseT invPlusT 2 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_3 : chkInvRow 1009 72 1 baseT invPlusT 3 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_4 : chkInvRow 1009 72 1 baseT invPlusT 4 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_5 : chkInvRow 1009 72 1 baseT invPlusT 5 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_6 : chkInvRow 1009 72 1 baseT invPlusT 6 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_7 : chkInvRow 1009 72 1 baseT invPlusT 7 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_8 : chkInvRow 1009 72 1 baseT invPlusT 8 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_9 : chkInvRow 1009 72 1 baseT invPlusT 9 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_10 : chkInvRow 1009 72 1 baseT invPlusT 10 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_11 : chkInvRow 1009 72 1 baseT invPlusT 11 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_12 : chkInvRow 1009 72 1 baseT invPlusT 12 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_13 : chkInvRow 1009 72 1 baseT invPlusT 13 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_14 : chkInvRow 1009 72 1 baseT invPlusT 14 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_15 : chkInvRow 1009 72 1 baseT invPlusT 15 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_16 : chkInvRow 1009 72 1 baseT invPlusT 16 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_17 : chkInvRow 1009 72 1 baseT invPlusT 17 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_18 : chkInvRow 1009 72 1 baseT invPlusT 18 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_19 : chkInvRow 1009 72 1 baseT invPlusT 19 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_20 : chkInvRow 1009 72 1 baseT invPlusT 20 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_21 : chkInvRow 1009 72 1 baseT invPlusT 21 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_22 : chkInvRow 1009 72 1 baseT invPlusT 22 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_23 : chkInvRow 1009 72 1 baseT invPlusT 23 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_24 : chkInvRow 1009 72 1 baseT invPlusT 24 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_25 : chkInvRow 1009 72 1 baseT invPlusT 25 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_26 : chkInvRow 1009 72 1 baseT invPlusT 26 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_27 : chkInvRow 1009 72 1 baseT invPlusT 27 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_28 : chkInvRow 1009 72 1 baseT invPlusT 28 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_29 : chkInvRow 1009 72 1 baseT invPlusT 29 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_30 : chkInvRow 1009 72 1 baseT invPlusT 30 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_31 : chkInvRow 1009 72 1 baseT invPlusT 31 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_32 : chkInvRow 1009 72 1 baseT invPlusT 32 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_33 : chkInvRow 1009 72 1 baseT invPlusT 33 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_34 : chkInvRow 1009 72 1 baseT invPlusT 34 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_35 : chkInvRow 1009 72 1 baseT invPlusT 35 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_36 : chkInvRow 1009 72 1 baseT invPlusT 36 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_37 : chkInvRow 1009 72 1 baseT invPlusT 37 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_38 : chkInvRow 1009 72 1 baseT invPlusT 38 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_39 : chkInvRow 1009 72 1 baseT invPlusT 39 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_40 : chkInvRow 1009 72 1 baseT invPlusT 40 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_41 : chkInvRow 1009 72 1 baseT invPlusT 41 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_42 : chkInvRow 1009 72 1 baseT invPlusT 42 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_43 : chkInvRow 1009 72 1 baseT invPlusT 43 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_44 : chkInvRow 1009 72 1 baseT invPlusT 44 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_45 : chkInvRow 1009 72 1 baseT invPlusT 45 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_46 : chkInvRow 1009 72 1 baseT invPlusT 46 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_47 : chkInvRow 1009 72 1 baseT invPlusT 47 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_48 : chkInvRow 1009 72 1 baseT invPlusT 48 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_49 : chkInvRow 1009 72 1 baseT invPlusT 49 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_50 : chkInvRow 1009 72 1 baseT invPlusT 50 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_51 : chkInvRow 1009 72 1 baseT invPlusT 51 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_52 : chkInvRow 1009 72 1 baseT invPlusT 52 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_53 : chkInvRow 1009 72 1 baseT invPlusT 53 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_54 : chkInvRow 1009 72 1 baseT invPlusT 54 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_55 : chkInvRow 1009 72 1 baseT invPlusT 55 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_56 : chkInvRow 1009 72 1 baseT invPlusT 56 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_57 : chkInvRow 1009 72 1 baseT invPlusT 57 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_58 : chkInvRow 1009 72 1 baseT invPlusT 58 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_59 : chkInvRow 1009 72 1 baseT invPlusT 59 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_60 : chkInvRow 1009 72 1 baseT invPlusT 60 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_61 : chkInvRow 1009 72 1 baseT invPlusT 61 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_62 : chkInvRow 1009 72 1 baseT invPlusT 62 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_63 : chkInvRow 1009 72 1 baseT invPlusT 63 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_64 : chkInvRow 1009 72 1 baseT invPlusT 64 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_65 : chkInvRow 1009 72 1 baseT invPlusT 65 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_66 : chkInvRow 1009 72 1 baseT invPlusT 66 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_67 : chkInvRow 1009 72 1 baseT invPlusT 67 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_68 : chkInvRow 1009 72 1 baseT invPlusT 68 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_69 : chkInvRow 1009 72 1 baseT invPlusT 69 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_70 : chkInvRow 1009 72 1 baseT invPlusT 70 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowPlus_71 : chkInvRow 1009 72 1 baseT invPlusT 71 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cLenMinus : chkInvLen 72 baseT invMinusT = true := by decide +kernel
-- kcost: 1 s estimated;73+72 row-length checks.

theorem cRowMinus_0 : chkInvRow 1009 72 1008 baseT invMinusT 0 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_1 : chkInvRow 1009 72 1008 baseT invMinusT 1 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_2 : chkInvRow 1009 72 1008 baseT invMinusT 2 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_3 : chkInvRow 1009 72 1008 baseT invMinusT 3 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_4 : chkInvRow 1009 72 1008 baseT invMinusT 4 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_5 : chkInvRow 1009 72 1008 baseT invMinusT 5 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_6 : chkInvRow 1009 72 1008 baseT invMinusT 6 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_7 : chkInvRow 1009 72 1008 baseT invMinusT 7 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_8 : chkInvRow 1009 72 1008 baseT invMinusT 8 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_9 : chkInvRow 1009 72 1008 baseT invMinusT 9 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_10 : chkInvRow 1009 72 1008 baseT invMinusT 10 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_11 : chkInvRow 1009 72 1008 baseT invMinusT 11 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_12 : chkInvRow 1009 72 1008 baseT invMinusT 12 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_13 : chkInvRow 1009 72 1008 baseT invMinusT 13 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_14 : chkInvRow 1009 72 1008 baseT invMinusT 14 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_15 : chkInvRow 1009 72 1008 baseT invMinusT 15 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_16 : chkInvRow 1009 72 1008 baseT invMinusT 16 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_17 : chkInvRow 1009 72 1008 baseT invMinusT 17 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_18 : chkInvRow 1009 72 1008 baseT invMinusT 18 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_19 : chkInvRow 1009 72 1008 baseT invMinusT 19 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_20 : chkInvRow 1009 72 1008 baseT invMinusT 20 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_21 : chkInvRow 1009 72 1008 baseT invMinusT 21 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_22 : chkInvRow 1009 72 1008 baseT invMinusT 22 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_23 : chkInvRow 1009 72 1008 baseT invMinusT 23 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_24 : chkInvRow 1009 72 1008 baseT invMinusT 24 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_25 : chkInvRow 1009 72 1008 baseT invMinusT 25 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_26 : chkInvRow 1009 72 1008 baseT invMinusT 26 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_27 : chkInvRow 1009 72 1008 baseT invMinusT 27 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_28 : chkInvRow 1009 72 1008 baseT invMinusT 28 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_29 : chkInvRow 1009 72 1008 baseT invMinusT 29 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_30 : chkInvRow 1009 72 1008 baseT invMinusT 30 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_31 : chkInvRow 1009 72 1008 baseT invMinusT 31 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_32 : chkInvRow 1009 72 1008 baseT invMinusT 32 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_33 : chkInvRow 1009 72 1008 baseT invMinusT 33 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_34 : chkInvRow 1009 72 1008 baseT invMinusT 34 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_35 : chkInvRow 1009 72 1008 baseT invMinusT 35 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_36 : chkInvRow 1009 72 1008 baseT invMinusT 36 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_37 : chkInvRow 1009 72 1008 baseT invMinusT 37 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_38 : chkInvRow 1009 72 1008 baseT invMinusT 38 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_39 : chkInvRow 1009 72 1008 baseT invMinusT 39 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_40 : chkInvRow 1009 72 1008 baseT invMinusT 40 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_41 : chkInvRow 1009 72 1008 baseT invMinusT 41 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_42 : chkInvRow 1009 72 1008 baseT invMinusT 42 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_43 : chkInvRow 1009 72 1008 baseT invMinusT 43 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_44 : chkInvRow 1009 72 1008 baseT invMinusT 44 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_45 : chkInvRow 1009 72 1008 baseT invMinusT 45 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_46 : chkInvRow 1009 72 1008 baseT invMinusT 46 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_47 : chkInvRow 1009 72 1008 baseT invMinusT 47 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_48 : chkInvRow 1009 72 1008 baseT invMinusT 48 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_49 : chkInvRow 1009 72 1008 baseT invMinusT 49 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_50 : chkInvRow 1009 72 1008 baseT invMinusT 50 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_51 : chkInvRow 1009 72 1008 baseT invMinusT 51 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_52 : chkInvRow 1009 72 1008 baseT invMinusT 52 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_53 : chkInvRow 1009 72 1008 baseT invMinusT 53 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_54 : chkInvRow 1009 72 1008 baseT invMinusT 54 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_55 : chkInvRow 1009 72 1008 baseT invMinusT 55 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_56 : chkInvRow 1009 72 1008 baseT invMinusT 56 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_57 : chkInvRow 1009 72 1008 baseT invMinusT 57 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_58 : chkInvRow 1009 72 1008 baseT invMinusT 58 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_59 : chkInvRow 1009 72 1008 baseT invMinusT 59 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_60 : chkInvRow 1009 72 1008 baseT invMinusT 60 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_61 : chkInvRow 1009 72 1008 baseT invMinusT 61 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_62 : chkInvRow 1009 72 1008 baseT invMinusT 62 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_63 : chkInvRow 1009 72 1008 baseT invMinusT 63 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_64 : chkInvRow 1009 72 1008 baseT invMinusT 64 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_65 : chkInvRow 1009 72 1008 baseT invMinusT 65 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_66 : chkInvRow 1009 72 1008 baseT invMinusT 66 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_67 : chkInvRow 1009 72 1008 baseT invMinusT 67 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_68 : chkInvRow 1009 72 1008 baseT invMinusT 68 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_69 : chkInvRow 1009 72 1008 baseT invMinusT 69 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_70 : chkInvRow 1009 72 1008 baseT invMinusT 70 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cRowMinus_71 : chkInvRow 1009 72 1008 baseT invMinusT 71 = true := by decide +kernel
-- kcost: 2 s estimated;72 columns times72-term Nat dot products, one inverse row per declaration.

theorem cBase_all : ∀ r, r < 72+1 → chkBase 1009 72 503 baseT prT drT fmT fzT r = true := by
  intro r hr
  interval_cases r
  · exact cBase_0
  · exact cBase_1
  · exact cBase_2
  · exact cBase_3
  · exact cBase_4
  · exact cBase_5
  · exact cBase_6
  · exact cBase_7
  · exact cBase_8
  · exact cBase_9
  · exact cBase_10
  · exact cBase_11
  · exact cBase_12
  · exact cBase_13
  · exact cBase_14
  · exact cBase_15
  · exact cBase_16
  · exact cBase_17
  · exact cBase_18
  · exact cBase_19
  · exact cBase_20
  · exact cBase_21
  · exact cBase_22
  · exact cBase_23
  · exact cBase_24
  · exact cBase_25
  · exact cBase_26
  · exact cBase_27
  · exact cBase_28
  · exact cBase_29
  · exact cBase_30
  · exact cBase_31
  · exact cBase_32
  · exact cBase_33
  · exact cBase_34
  · exact cBase_35
  · exact cBase_36
  · exact cBase_37
  · exact cBase_38
  · exact cBase_39
  · exact cBase_40
  · exact cBase_41
  · exact cBase_42
  · exact cBase_43
  · exact cBase_44
  · exact cBase_45
  · exact cBase_46
  · exact cBase_47
  · exact cBase_48
  · exact cBase_49
  · exact cBase_50
  · exact cBase_51
  · exact cBase_52
  · exact cBase_53
  · exact cBase_54
  · exact cBase_55
  · exact cBase_56
  · exact cBase_57
  · exact cBase_58
  · exact cBase_59
  · exact cBase_60
  · exact cBase_61
  · exact cBase_62
  · exact cBase_63
  · exact cBase_64
  · exact cBase_65
  · exact cBase_66
  · exact cBase_67
  · exact cBase_68
  · exact cBase_69
  · exact cBase_70
  · exact cBase_71
  · exact cBase_72

theorem cRowZero_all : ∀ r, r < 72 → chkInvRow 1009 72 0 baseT invZeroT r = true := by
  intro r hr
  interval_cases r
  · exact cRowZero_0
  · exact cRowZero_1
  · exact cRowZero_2
  · exact cRowZero_3
  · exact cRowZero_4
  · exact cRowZero_5
  · exact cRowZero_6
  · exact cRowZero_7
  · exact cRowZero_8
  · exact cRowZero_9
  · exact cRowZero_10
  · exact cRowZero_11
  · exact cRowZero_12
  · exact cRowZero_13
  · exact cRowZero_14
  · exact cRowZero_15
  · exact cRowZero_16
  · exact cRowZero_17
  · exact cRowZero_18
  · exact cRowZero_19
  · exact cRowZero_20
  · exact cRowZero_21
  · exact cRowZero_22
  · exact cRowZero_23
  · exact cRowZero_24
  · exact cRowZero_25
  · exact cRowZero_26
  · exact cRowZero_27
  · exact cRowZero_28
  · exact cRowZero_29
  · exact cRowZero_30
  · exact cRowZero_31
  · exact cRowZero_32
  · exact cRowZero_33
  · exact cRowZero_34
  · exact cRowZero_35
  · exact cRowZero_36
  · exact cRowZero_37
  · exact cRowZero_38
  · exact cRowZero_39
  · exact cRowZero_40
  · exact cRowZero_41
  · exact cRowZero_42
  · exact cRowZero_43
  · exact cRowZero_44
  · exact cRowZero_45
  · exact cRowZero_46
  · exact cRowZero_47
  · exact cRowZero_48
  · exact cRowZero_49
  · exact cRowZero_50
  · exact cRowZero_51
  · exact cRowZero_52
  · exact cRowZero_53
  · exact cRowZero_54
  · exact cRowZero_55
  · exact cRowZero_56
  · exact cRowZero_57
  · exact cRowZero_58
  · exact cRowZero_59
  · exact cRowZero_60
  · exact cRowZero_61
  · exact cRowZero_62
  · exact cRowZero_63
  · exact cRowZero_64
  · exact cRowZero_65
  · exact cRowZero_66
  · exact cRowZero_67
  · exact cRowZero_68
  · exact cRowZero_69
  · exact cRowZero_70
  · exact cRowZero_71

theorem cRowPlus_all : ∀ r, r < 72 → chkInvRow 1009 72 1 baseT invPlusT r = true := by
  intro r hr
  interval_cases r
  · exact cRowPlus_0
  · exact cRowPlus_1
  · exact cRowPlus_2
  · exact cRowPlus_3
  · exact cRowPlus_4
  · exact cRowPlus_5
  · exact cRowPlus_6
  · exact cRowPlus_7
  · exact cRowPlus_8
  · exact cRowPlus_9
  · exact cRowPlus_10
  · exact cRowPlus_11
  · exact cRowPlus_12
  · exact cRowPlus_13
  · exact cRowPlus_14
  · exact cRowPlus_15
  · exact cRowPlus_16
  · exact cRowPlus_17
  · exact cRowPlus_18
  · exact cRowPlus_19
  · exact cRowPlus_20
  · exact cRowPlus_21
  · exact cRowPlus_22
  · exact cRowPlus_23
  · exact cRowPlus_24
  · exact cRowPlus_25
  · exact cRowPlus_26
  · exact cRowPlus_27
  · exact cRowPlus_28
  · exact cRowPlus_29
  · exact cRowPlus_30
  · exact cRowPlus_31
  · exact cRowPlus_32
  · exact cRowPlus_33
  · exact cRowPlus_34
  · exact cRowPlus_35
  · exact cRowPlus_36
  · exact cRowPlus_37
  · exact cRowPlus_38
  · exact cRowPlus_39
  · exact cRowPlus_40
  · exact cRowPlus_41
  · exact cRowPlus_42
  · exact cRowPlus_43
  · exact cRowPlus_44
  · exact cRowPlus_45
  · exact cRowPlus_46
  · exact cRowPlus_47
  · exact cRowPlus_48
  · exact cRowPlus_49
  · exact cRowPlus_50
  · exact cRowPlus_51
  · exact cRowPlus_52
  · exact cRowPlus_53
  · exact cRowPlus_54
  · exact cRowPlus_55
  · exact cRowPlus_56
  · exact cRowPlus_57
  · exact cRowPlus_58
  · exact cRowPlus_59
  · exact cRowPlus_60
  · exact cRowPlus_61
  · exact cRowPlus_62
  · exact cRowPlus_63
  · exact cRowPlus_64
  · exact cRowPlus_65
  · exact cRowPlus_66
  · exact cRowPlus_67
  · exact cRowPlus_68
  · exact cRowPlus_69
  · exact cRowPlus_70
  · exact cRowPlus_71

theorem cRowMinus_all : ∀ r, r < 72 → chkInvRow 1009 72 1008 baseT invMinusT r = true := by
  intro r hr
  interval_cases r
  · exact cRowMinus_0
  · exact cRowMinus_1
  · exact cRowMinus_2
  · exact cRowMinus_3
  · exact cRowMinus_4
  · exact cRowMinus_5
  · exact cRowMinus_6
  · exact cRowMinus_7
  · exact cRowMinus_8
  · exact cRowMinus_9
  · exact cRowMinus_10
  · exact cRowMinus_11
  · exact cRowMinus_12
  · exact cRowMinus_13
  · exact cRowMinus_14
  · exact cRowMinus_15
  · exact cRowMinus_16
  · exact cRowMinus_17
  · exact cRowMinus_18
  · exact cRowMinus_19
  · exact cRowMinus_20
  · exact cRowMinus_21
  · exact cRowMinus_22
  · exact cRowMinus_23
  · exact cRowMinus_24
  · exact cRowMinus_25
  · exact cRowMinus_26
  · exact cRowMinus_27
  · exact cRowMinus_28
  · exact cRowMinus_29
  · exact cRowMinus_30
  · exact cRowMinus_31
  · exact cRowMinus_32
  · exact cRowMinus_33
  · exact cRowMinus_34
  · exact cRowMinus_35
  · exact cRowMinus_36
  · exact cRowMinus_37
  · exact cRowMinus_38
  · exact cRowMinus_39
  · exact cRowMinus_40
  · exact cRowMinus_41
  · exact cRowMinus_42
  · exact cRowMinus_43
  · exact cRowMinus_44
  · exact cRowMinus_45
  · exact cRowMinus_46
  · exact cRowMinus_47
  · exact cRowMinus_48
  · exact cRowMinus_49
  · exact cRowMinus_50
  · exact cRowMinus_51
  · exact cRowMinus_52
  · exact cRowMinus_53
  · exact cRowMinus_54
  · exact cRowMinus_55
  · exact cRowMinus_56
  · exact cRowMinus_57
  · exact cRowMinus_58
  · exact cRowMinus_59
  · exact cRowMinus_60
  · exact cRowMinus_61
  · exact cRowMinus_62
  · exact cRowMinus_63
  · exact cRowMinus_64
  · exact cRowMinus_65
  · exact cRowMinus_66
  · exact cRowMinus_67
  · exact cRowMinus_68
  · exact cRowMinus_69
  · exact cRowMinus_70
  · exact cRowMinus_71

theorem hE : ∀ (r k : ℕ) (hk : k < dc72.toParameters.n0), r < dc72.toParameters.n0 + 1 →
    baseFilteredContraction dc72.toParameters 1009 r ⟨k, hk⟩ = CertMod.entry 1009 baseT r k :=
  base_sound dc72.toParameters 1009 (by norm_num) (by decide) (by decide) msT bmT bpT ivT h1T wT momT zetT fmT fzT
    prT drT baseT 503 hW hcN cIV cMS cBM cBP cMT cH1 cZT cPoly cFM cFZ cLen cBase_all

/-- **D72.C3.**  The three residue determinants of the base matrices are nonzero modulo 1009. -/
theorem c3_dc72 :
    (baseB0Residue dc72.toParameters 1009).det ≠ 0 ∧
      (baseB0Residue dc72.toParameters 1009 + baseB1Residue dc72.toParameters 1009).det ≠ 0 ∧
      (baseB0Residue dc72.toParameters 1009 - baseB1Residue dc72.toParameters 1009).det ≠ 0 :=
  c3_of_certificate' dc72.toParameters 1009 baseT _ _ _ hE
    (chkInv_sound 0 0 (by simp) cLenZero cRowZero_all)
    (chkInv_sound 1 1 (by simp) cLenPlus cRowPlus_all)
    (chkInv_sound 1008 (-1) (by
      have : ((1008 : ℕ) : ZMod 1009) = -1 := by decide
      exact this) cLenMinus cRowMinus_all)

theorem nonvanishing_dc72 :
    ∃ N1 : ℕ, ∀ p : ℕ, N1 ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ),
      0 < b → ¬ p^2 ∣ b → aeval ((a : ℝ)/b) (Parametric.deltaPoly dc72.toParameters p) ≠ 0 := by
  exact nonvanishing_of_c3 dc72.toParameters dc72.admissible (by decide : 1009 ≠ 2)
    (by decide) c3_dc72.1 c3_dc72.2.1 c3_dc72.2.2
end CatalanMeasure.GenD.Signed.Data.C3

#print axioms CatalanMeasure.GenD.Signed.Data.C3.cIV
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cMS
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBM
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBP
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cH1
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cMT
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cZT
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cPoly
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cFM
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cFZ
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cLen
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_0
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_1
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_2
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_3
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_4
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_5
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_6
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_7
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_8
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_9
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_10
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_11
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_12
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_13
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_14
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_15
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_16
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_17
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_18
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_19
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_20
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_21
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_22
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_23
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_24
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_25
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_26
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_27
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_28
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_29
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_30
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_31
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_32
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_33
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_34
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_35
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_36
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_37
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_38
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_39
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_40
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_41
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_42
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_43
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_44
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_45
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_46
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_47
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_48
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_49
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_50
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_51
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_52
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_53
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_54
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_55
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_56
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_57
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_58
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_59
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_60
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_61
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_62
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_63
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_64
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_65
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_66
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_67
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_68
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_69
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_70
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_71
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_72
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cLenZero
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_0
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_1
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_2
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_3
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_4
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_5
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_6
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_7
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_8
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_9
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_10
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_11
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_12
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_13
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_14
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_15
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_16
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_17
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_18
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_19
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_20
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_21
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_22
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_23
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_24
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_25
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_26
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_27
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_28
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_29
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_30
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_31
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_32
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_33
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_34
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_35
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_36
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_37
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_38
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_39
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_40
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_41
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_42
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_43
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_44
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_45
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_46
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_47
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_48
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_49
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_50
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_51
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_52
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_53
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_54
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_55
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_56
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_57
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_58
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_59
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_60
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_61
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_62
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_63
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_64
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_65
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_66
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_67
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_68
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_69
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_70
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_71
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cLenPlus
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_0
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_1
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_2
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_3
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_4
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_5
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_6
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_7
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_8
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_9
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_10
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_11
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_12
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_13
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_14
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_15
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_16
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_17
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_18
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_19
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_20
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_21
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_22
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_23
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_24
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_25
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_26
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_27
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_28
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_29
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_30
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_31
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_32
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_33
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_34
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_35
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_36
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_37
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_38
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_39
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_40
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_41
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_42
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_43
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_44
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_45
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_46
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_47
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_48
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_49
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_50
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_51
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_52
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_53
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_54
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_55
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_56
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_57
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_58
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_59
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_60
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_61
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_62
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_63
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_64
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_65
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_66
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_67
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_68
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_69
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_70
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_71
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cLenMinus
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_0
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_1
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_2
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_3
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_4
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_5
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_6
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_7
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_8
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_9
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_10
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_11
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_12
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_13
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_14
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_15
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_16
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_17
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_18
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_19
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_20
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_21
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_22
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_23
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_24
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_25
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_26
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_27
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_28
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_29
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_30
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_31
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_32
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_33
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_34
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_35
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_36
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_37
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_38
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_39
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_40
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_41
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_42
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_43
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_44
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_45
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_46
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_47
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_48
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_49
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_50
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_51
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_52
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_53
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_54
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_55
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_56
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_57
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_58
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_59
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_60
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_61
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_62
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_63
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_64
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_65
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_66
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_67
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_68
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_69
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_70
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_71
#print axioms CatalanMeasure.GenD.Signed.Data.C3.hW
#print axioms CatalanMeasure.GenD.Signed.Data.C3.hcN
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cBase_all
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowZero_all
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowPlus_all
#print axioms CatalanMeasure.GenD.Signed.Data.C3.cRowMinus_all
#print axioms CatalanMeasure.GenD.Signed.Data.C3.hE
#print axioms CatalanMeasure.GenD.Signed.Data.C3.c3_dc72
#print axioms CatalanMeasure.GenD.Signed.Data.C3.nonvanishing_dc72
