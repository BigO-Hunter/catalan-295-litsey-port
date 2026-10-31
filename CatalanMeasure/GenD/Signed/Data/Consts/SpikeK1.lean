module

public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialB1
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialA1
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeD
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeA

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed OAI.InternalCatalan

theorem A_1 : absq as1 ≤ (399 / 512 : ℚ) := by decide +kernel
theorem A1_1 : absSq as1 ≤ (335 / 1024 : ℚ) := by decide +kernel
theorem B1_1 : absSq bs1 ≤ (785 / 1024 : ℚ) := by decide +kernel

theorem Lc1_div : (List.range 120).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ 955888052326228459513511038256280353796626534577600)) = true := by decide +kernel

theorem K0_1_0 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((76 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs1) s' m (((2040 / 2048 : ℚ)) : ℝ) ≤ (((-8757 / 1024 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD1_0 : List ℤ := raw_ints% []
theorem De2cov1_0 : zNonnegCov (zAdd [844504424977702861837178174288459217350500986178580884411708027699200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_0 (1024) = true := by decide +kernel
theorem De2sig1_0 : ((788541 / 1048576 : ℚ)) ≤ Sbq bs1 (-(2040 / 2048 : ℚ)) := by decide +kernel
theorem De2_1_0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((2040 / 2048 : ℚ)) : ℝ)) ≤
      (((117 / 8192 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (2040 / 2048 : ℚ)) (σ := (788541 / 1048576 : ℚ))
    (De2 := (117 / 8192 : ℚ)) (844504424977702861837178174288459217350500986178580884411708027699200) (by norm_num) De2sig1_0 (S := 10) (A := 1023) (B := 1024)
    De2cov1_0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_1_1 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((152 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs1) s' m (((2038 / 2048 : ℚ)) : ℝ) ≤ (((-7777 / 1024 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD1_1 : List ℤ := raw_ints% []
theorem De2cov1_1 : zNonnegCov (zAdd [844509680027844786045762667075632907883603275868694339266330964787200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_1 (1024) = true := by decide +kernel
theorem De2sig1_1 : ((392513 / 524288 : ℚ)) ≤ Sbq bs1 (-(2038 / 2048 : ℚ)) := by decide +kernel
theorem De2_1_1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((2038 / 2048 : ℚ)) : ℝ)) ≤
      (((289 / 16384 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (2038 / 2048 : ℚ)) (σ := (392513 / 524288 : ℚ))
    (De2 := (289 / 16384 : ℚ)) (844509680027844786045762667075632907883603275868694339266330964787200) (by norm_num) De2sig1_1 (S := 10) (A := 1023) (B := 1024)
    De2cov1_1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_1_2 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((228 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs1) s' m (((2036 / 2048 : ℚ)) : ℝ) ≤ (((-881 / 128 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD1_2 : List ℤ := raw_ints% []
theorem De2cov1_2 : zNonnegCov (zAdd [844523343158213788988082348322284503269669229062989321888350601216000] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_2 (1024) = true := by decide +kernel
theorem De2sig1_2 : ((781583 / 1048576 : ℚ)) ≤ Sbq bs1 (-(2036 / 2048 : ℚ)) := by decide +kernel
theorem De2_1_2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((2036 / 2048 : ℚ)) : ℝ)) ≤
      (((343 / 16384 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (2036 / 2048 : ℚ)) (σ := (781583 / 1048576 : ℚ))
    (De2 := (343 / 16384 : ℚ)) (844523343158213788988082348322284503269669229062989321888350601216000) (by norm_num) De2sig1_2 (S := 10) (A := 1023) (B := 1024)
    De2cov1_2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_1_3 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((304 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs1) s' m (((2033 / 2048 : ℚ)) : ℝ) ≤ (((-51 / 8 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD1_3 : List ℤ := raw_ints% []
theorem De2cov1_3 : zNonnegCov (zAdd [844541210328696331297269623798675051082217014009375068394068587315200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN1))) 10 (1023) cutsD1_3 (1024) = true := by decide +kernel
theorem De2sig1_3 : ((24267 / 32768 : ℚ)) ≤ Sbq bs1 (-(2033 / 2048 : ℚ)) := by decide +kernel
theorem De2_1_3 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs1) (-y) - barrierTrialS (bSeq bs1) (-(((2033 / 2048 : ℚ)) : ℝ)) ≤
      (((211 / 8192 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN1) (divAll Lc1_div) (by norm_num) (ρ := (2033 / 2048 : ℚ)) (σ := (24267 / 32768 : ℚ))
    (De2 := (211 / 8192 : ℚ)) (844541210328696331297269623798675051082217014009375068394068587315200) (by norm_num) De2sig1_3 (S := 10) (A := 1023) (B := 1024)
    De2cov1_3 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

end CatalanMeasure.Signed.Consts
