module

public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Signed.Data.Consts.PolyPos
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialB2
public import CatalanMeasure.GenD.Signed.Data.Consts.TrialA2
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeD
public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeA

@[expose] public section

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert

set_option maxRecDepth 1000000
set_option Elab.async false

open CatalanMeasure.Signed OAI.InternalCatalan

theorem A_2 : absq as2 ≤ (855 / 1024 : ℚ) := by decide +kernel
theorem A1_2 : absSq as2 ≤ (327 / 1024 : ℚ) := by decide +kernel
theorem B1_2 : absSq bs2 ≤ (375 / 512 : ℚ) := by decide +kernel

theorem Lc2_div : (List.range 120).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ 955888052326228459513511038256280353796626534577600)) = true := by decide +kernel

theorem K0_2_0 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((76 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs2) s' m (((2039 / 2048 : ℚ)) : ℝ) ≤ (((-4055 / 512 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD2_0 : List ℤ := raw_ints% []
theorem De2cov2_0 : zNonnegCov (zAdd [807074804836833493773269848365131026276132439376487336874376324710400] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_0 (1024) = true := by decide +kernel
theorem De2sig2_0 : ((23503 / 32768 : ℚ)) ≤ Sbq bs2 (-(2039 / 2048 : ℚ)) := by decide +kernel
theorem De2_2_0 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((2039 / 2048 : ℚ)) : ℝ)) ≤
      (((247 / 16384 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (2039 / 2048 : ℚ)) (σ := (23503 / 32768 : ℚ))
    (De2 := (247 / 16384 : ℚ)) (807074804836833493773269848365131026276132439376487336874376324710400) (by norm_num) De2sig2_0 (S := 10) (A := 1023) (B := 1024)
    De2cov2_0 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_2_1 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((152 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs2) s' m (((2037 / 2048 : ℚ)) : ℝ) ≤ (((-7197 / 1024 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD2_1 : List ℤ := raw_ints% []
theorem De2cov2_1 : zNonnegCov (zAdd [807061141706464490830950167118479430890066486182192354252356688281600] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_1 (1024) = true := by decide +kernel
theorem De2sig2_1 : ((748819 / 1048576 : ℚ)) ≤ Sbq bs2 (-(2037 / 2048 : ℚ)) := by decide +kernel
theorem De2_2_1 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((2037 / 2048 : ℚ)) : ℝ)) ≤
      (((149 / 8192 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (2037 / 2048 : ℚ)) (σ := (748819 / 1048576 : ℚ))
    (De2 := (149 / 8192 : ℚ)) (807061141706464490830950167118479430890066486182192354252356688281600) (by norm_num) De2sig2_1 (S := 10) (A := 1023) (B := 1024)
    De2cov2_1 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_2_2 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((228 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs2) s' m (((2034 / 2048 : ℚ)) : ℝ) ≤ (((-6543 / 1024 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD2_2 : List ℤ := raw_ints% []
theorem De2cov2_2 : zNonnegCov (zAdd [807065345746578030197817761348218383316548317934283118136055037952000] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_2 (1024) = true := by decide +kernel
theorem De2sig2_2 : ((744023 / 1048576 : ℚ)) ≤ Sbq bs2 (-(2034 / 2048 : ℚ)) := by decide +kernel
theorem De2_2_2 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((2034 / 2048 : ℚ)) : ℝ)) ≤
      (((373 / 16384 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (2034 / 2048 : ℚ)) (σ := (744023 / 1048576 : ℚ))
    (De2 := (373 / 16384 : ℚ)) (807065345746578030197817761348218383316548317934283118136055037952000) (by norm_num) De2sig2_2 (S := 10) (A := 1023) (B := 1024)
    De2cov2_2 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

theorem K0_2_3 {s' m : ℕ} (hs : 0 < s') (hm : (m : ℝ) ≤ (((304 / 16384 : ℚ)) : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs2) s' m (((2031 / 2048 : ℚ)) : ℝ) ≤ (((-6023 / 1024 : ℚ)) : ℝ) :=
  costRem_le (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) hs hm

def cutsD2_3 : List ℤ := raw_ints% []
theorem De2cov2_3 : zNonnegCov (zAdd [807077957866918648298420544037435240595993813190555409787150086963200] (zSmul (-1) (sbNegInt 955888052326228459513511038256280353796626534577600 bsN2))) 10 (1023) cutsD2_3 (1024) = true := by decide +kernel
theorem De2sig2_3 : ((739363 / 1048576 : ℚ)) ≤ Sbq bs2 (-(2031 / 2048 : ℚ)) := by decide +kernel
theorem De2_2_3 {y : ℝ} (h1 : (1023 : ℝ) / 1024 ≤ y) (h2 : y ≤ 1) :
    barrierTrialS (bSeq bs2) (-y) - barrierTrialS (bSeq bs2) (-(((2031 / 2048 : ℚ)) : ℝ)) ≤
      (((223 / 8192 : ℚ)) : ℝ) :=
  De2_of_cov (Lc := 955888052326228459513511038256280353796626534577600) (Bn := bsN2) (divAll Lc2_div) (by norm_num) (ρ := (2031 / 2048 : ℚ)) (σ := (739363 / 1048576 : ℚ))
    (De2 := (223 / 8192 : ℚ)) (807077957866918648298420544037435240595993813190555409787150086963200) (by norm_num) De2sig2_3 (S := 10) (A := 1023) (B := 1024)
    De2cov2_3 (by push_cast; norm_num; linarith) (by push_cast; norm_num; linarith)

end CatalanMeasure.Signed.Consts
