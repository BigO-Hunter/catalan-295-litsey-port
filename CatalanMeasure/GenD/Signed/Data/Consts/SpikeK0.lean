module

public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialB0
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialA0
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeD
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeA

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed OAI.InternalCatalan

theorem A_0 : absq as0 ≤ (887 / 1024 : ℚ) := by decide +kernel
theorem A1_0 : absSq as0 ≤ (81 / 256 : ℚ) := by decide +kernel
theorem B1_0 : absSq bs0 ≤ (197 / 256 : ℚ) := by decide +kernel

theorem Lc0_div : (List.range 120).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ 955888052326228459513511038256280353796626534577600)) = true := by decide +kernel

theorem K0_0_0 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((76 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs0) s' m (((2040 / 2048 : ℚ)) : ℝ) ≤ (((-1103 / 128 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD0_0 : List ℤ := raw_ints% []
theorem De2cov0_0 : zNonnegCov (zAdd [847883422218960127957007036441142230135273256921532355934256575283200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_0 (1024) = true := by decide +kernel
theorem De2sig0_0 : ((197907 / 262144 : ℚ)) ≤ Sbq bs0 (-(2040 / 2048 : ℚ)) := by decide +kernel
theorem De2_0_0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((2040 / 2048 : ℚ)) : ℝ)) ≤
      (((59 / 4096 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (2040 / 2048 : ℚ)) (σ := (197907 / 262144 : ℚ))
    (De2 := (59 / 4096 : ℚ)) (847883422218960127957007036441142230135273256921532355934256575283200) (by norm_num) De2sig0_0 (S := 10) (A := 1023) (B := 1024)
    De2cov0_0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_0_1 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((152 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs0) s' m (((2038 / 2048 : ℚ)) : ℝ) ≤ (((-3921 / 512 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD0_1 : List ℤ := raw_ints% []
theorem De2cov0_1 : zNonnegCov (zAdd [847866606058505970489536659522186420429345929913169300399463176601600] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_1 (1024) = true := by decide +kernel
theorem De2sig0_1 : ((197023 / 262144 : ℚ)) ≤ Sbq bs0 (-(2038 / 2048 : ℚ)) := by decide +kernel
theorem De2_0_1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((2038 / 2048 : ℚ)) : ℝ)) ≤
      (((291 / 16384 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (2038 / 2048 : ℚ)) (σ := (197023 / 262144 : ℚ))
    (De2 := (291 / 16384 : ℚ)) (847866606058505970489536659522186420429345929913169300399463176601600) (by norm_num) De2sig0_1 (S := 10) (A := 1023) (B := 1024)
    De2cov0_1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_0_2 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((228 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs0) s' m (((2036 / 2048 : ℚ)) : ℝ) ≤ (((-7111 / 1024 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD0_2 : List ℤ := raw_ints% []
theorem De2cov0_2 : zNonnegCov (zAdd [847859248988307276597518369620143253683002724347010463602991064678400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_2 (1024) = true := by decide +kernel
theorem De2sig0_2 : ((784629 / 1048576 : ℚ)) ≤ Sbq bs0 (-(2036 / 2048 : ℚ)) := by decide +kernel
theorem De2_0_2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((2036 / 2048 : ℚ)) : ℝ)) ≤
      (((345 / 16384 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (2036 / 2048 : ℚ)) (σ := (784629 / 1048576 : ℚ))
    (De2 := (345 / 16384 : ℚ)) (847859248988307276597518369620143253683002724347010463602991064678400) (by norm_num) De2sig0_2 (S := 10) (A := 1023) (B := 1024)
    De2cov0_2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_0_3 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((304 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs0) s' m (((2033 / 2048 : ℚ)) : ℝ) ≤ (((-6587 / 1024 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD0_3 : List ℤ := raw_ints% []
theorem De2cov0_3 : zNonnegCov (zAdd [847847687877995043338632485488361134510177687028760862922820603084800] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN0))) 10 (1023) cutsD0_3 (1024) = true := by decide +kernel
theorem De2sig0_3 : ((389781 / 524288 : ℚ)) ≤ Sbq bs0 (-(2033 / 2048 : ℚ)) := by decide +kernel
theorem De2_0_3 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs0) (-y) - barrierTrialS (bSeq bs0) (-(((2033 / 2048 : ℚ)) : ℝ)) ≤
      (((53 / 2048 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN0) (divAll Lc0_div) (by norm_num) (ρ := (2033 / 2048 : ℚ)) (σ := (389781 / 524288 : ℚ))
    (De2 := (53 / 2048 : ℚ)) (847847687877995043338632485488361134510177687028760862922820603084800) (by norm_num) De2sig0_3 (S := 10) (A := 1023) (B := 1024)
    De2cov0_3 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

end CatalanMeasure.Signed.Consts
