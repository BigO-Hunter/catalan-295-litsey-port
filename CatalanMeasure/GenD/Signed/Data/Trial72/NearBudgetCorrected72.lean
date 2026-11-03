module

public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetBridges72
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionInput

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetCorrected72
open Set CatalanMeasure.Signed
open NearBudgetBridges72
noncomputable section

theorem bernstein_upper {t A B C D : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hA : A ≤ D) (hB : B ≤ D) (hC : C ≤ D) :
    (1-t)^2*A + 2*t*(1-t)*B + t^2*C ≤ D := by
  have h1 := mul_le_mul_of_nonneg_left hA (sq_nonneg (1-t))
  have h2 := mul_le_mul_of_nonneg_left hB (mul_nonneg (mul_nonneg (by norm_num) ht.1) (sub_nonneg.mpr ht.2))
  have h3 := mul_le_mul_of_nonneg_left hC (sq_nonneg t)
  exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)

def gapP0 (x : ℝ) : ℝ := (((-131584789/268435456 : ℚ) : ℝ))*x^0 + (((576751/1073741824 : ℚ) : ℝ))*x^1 + (((0/1 : ℚ) : ℝ))*x^2
def gapS0 (x : ℝ) : ℝ := (((-400161525/1073741824 : ℚ) : ℝ))*x^0 + (((1695/1048576 : ℚ) : ℝ))*x^1 + (((-3429/1073741824 : ℚ) : ℝ))*x^2
def correction0 (x β : ℝ) : ℝ := (467829/1000000) *
  (capInt (gapP0 x) (11/8 * a0 x) (1/1000) + capInt (gapS0 x) (5/11*β+1/1000000) (1/1000))

theorem cell0_7 {x β : ℝ} (hx : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/128 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_7.capUpper : ℝ) := by
  let t : ℝ := (x-(((0/1 : ℚ) : ℝ)))/((((1/128 : ℚ) : ℝ))-(((0/1 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_7.cP : ℝ) := by
    have h := bernstein_upper (A := (((-131584789/268435456 : ℚ) : ℝ))) (B := (((-134742247185/274877906944 : ℚ) : ℝ))) (C := (((-67370835217/137438953472 : ℚ) : ℝ))) (D := (((-67370835217/137438953472 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-131584789/268435456 : ℚ) : ℝ))+2*t*(1-t)*(((-134742247185/274877906944 : ℚ) : ℝ))+t^2*(((-67370835217/137438953472 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_7.cP : ℝ) = (((-67370835217/137438953472 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_7.cP = (-67370835217/137438953472 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_7.cS : ℝ) := by
    have h := bernstein_upper (A := (((-400161525/1073741824 : ℚ) : ℝ))) (B := (((-400154745/1073741824 : ℚ) : ℝ))) (C := (((-6556024261989/17592186044416 : ℚ) : ℝ))) (D := (((-6556024261989/17592186044416 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-400161525/1073741824 : ℚ) : ℝ))+2*t*(1-t)*(((-400154745/1073741824 : ℚ) : ℝ))+t^2*(((-6556024261989/17592186044416 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_7.cS : ℝ) = (((-6556024261989/17592186044416 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_7.cS = (-6556024261989/17592186044416 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_7.rP : ℝ) := by
    have h : (NearCorrection0_7.rP : ℝ) = (((11/204800 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_7.rP = (11/204800 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_7.rS : ℝ) := by
    have h : (NearCorrection0_7.rS : ℝ) = (((3301/176000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_7.rS = (3301/176000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_7.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_7.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_7.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_7.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_7.combined

theorem cell0_6 {x β : ℝ} (hx : x ∈ Icc (((1/128 : ℚ) : ℝ)) (((1/64 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_6.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/128 : ℚ) : ℝ)))/((((1/64 : ℚ) : ℝ))-(((1/128 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_6.cP : ℝ) := by
    have h := bernstein_upper (A := (((-67370835217/137438953472 : ℚ) : ℝ))) (B := (((-134741093683/274877906944 : ℚ) : ℝ))) (C := (((-33685129233/68719476736 : ℚ) : ℝ))) (D := (((-33685129233/68719476736 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-67370835217/137438953472 : ℚ) : ℝ))+2*t*(1-t)*(((-134741093683/274877906944 : ℚ) : ℝ))+t^2*(((-33685129233/68719476736 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_6.cP : ℝ) = (((-33685129233/68719476736 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_6.cP = (-33685129233/68719476736 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_6.cS : ℝ) := by
    have h := bernstein_upper (A := (((-6556024261989/17592186044416 : ℚ) : ℝ))) (B := (((-3277956590949/8796093022208 : ℚ) : ℝ))) (C := (((-1638950526309/4398046511104 : ℚ) : ℝ))) (D := (((-1638950526309/4398046511104 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-6556024261989/17592186044416 : ℚ) : ℝ))+2*t*(1-t)*(((-3277956590949/8796093022208 : ℚ) : ℝ))+t^2*(((-1638950526309/4398046511104 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_6.cS : ℝ) = (((-1638950526309/4398046511104 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_6.cS = (-1638950526309/4398046511104 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_6.rP : ℝ) := by
    have h : (NearCorrection0_6.rP : ℝ) = (((11/102400 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_6.rP = (11/102400 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_6.rS : ℝ) := by
    have h : (NearCorrection0_6.rS : ℝ) = (((3213/88000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_6.rS = (3213/88000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_6.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_6.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_6.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_6.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_6.combined

theorem cell0_5 {x β : ℝ} (hx : x ∈ Icc (((1/64 : ℚ) : ℝ)) (((1/32 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_5.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/64 : ℚ) : ℝ)))/((((1/32 : ℚ) : ℝ))-(((1/64 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_5.cP : ℝ) := by
    have h := bernstein_upper (A := (((-33685129233/68719476736 : ℚ) : ℝ))) (B := (((-67369681715/137438953472 : ℚ) : ℝ))) (C := (((-16842276241/34359738368 : ℚ) : ℝ))) (D := (((-16842276241/34359738368 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-33685129233/68719476736 : ℚ) : ℝ))+2*t*(1-t)*(((-67369681715/137438953472 : ℚ) : ℝ))+t^2*(((-16842276241/34359738368 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_5.cP : ℝ) = (((-16842276241/34359738368 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_5.cP = (-16842276241/34359738368 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_5.cS : ℝ) := by
    have h := bernstein_upper (A := (((-1638950526309/4398046511104 : ℚ) : ℝ))) (B := (((-819447493989/2199023255552 : ℚ) : ℝ))) (C := (((-409709863269/1099511627776 : ℚ) : ℝ))) (D := (((-409709863269/1099511627776 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-1638950526309/4398046511104 : ℚ) : ℝ))+2*t*(1-t)*(((-819447493989/2199023255552 : ℚ) : ℝ))+t^2*(((-409709863269/1099511627776 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_5.cS : ℝ) = (((-409709863269/1099511627776 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_5.cS = (-409709863269/1099511627776 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_5.rP : ℝ) := by
    have h : (NearCorrection0_5.rP : ℝ) = (((11/51200 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_5.rP = (11/51200 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_5.rS : ℝ) := by
    have h : (NearCorrection0_5.rS : ℝ) = (((3169/44000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_5.rS = (3169/44000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_5.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_5.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_5.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_5.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_5.combined

theorem cell0_4 {x β : ℝ} (hx : x ∈ Icc (((1/32 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_4.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/32 : ℚ) : ℝ)))/((((1/16 : ℚ) : ℝ))-(((1/32 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_4.cP : ℝ) := by
    have h := bernstein_upper (A := (((-16842276241/34359738368 : ℚ) : ℝ))) (B := (((-33683975731/68719476736 : ℚ) : ℝ))) (C := (((-8420849745/17179869184 : ℚ) : ℝ))) (D := (((-8420849745/17179869184 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-16842276241/34359738368 : ℚ) : ℝ))+2*t*(1-t)*(((-33683975731/68719476736 : ℚ) : ℝ))+t^2*(((-8420849745/17179869184 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_4.cP : ℝ) = (((-8420849745/17179869184 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_4.cP = (-8420849745/17179869184 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_4.cS : ℝ) := by
    have h := bernstein_upper (A := (((-409709863269/1099511627776 : ℚ) : ℝ))) (B := (((-204841047909/549755813888 : ℚ) : ℝ))) (C := (((-102413582949/274877906944 : ℚ) : ℝ))) (D := (((-102413582949/274877906944 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-409709863269/1099511627776 : ℚ) : ℝ))+2*t*(1-t)*(((-204841047909/549755813888 : ℚ) : ℝ))+t^2*(((-102413582949/274877906944 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_4.cS : ℝ) = (((-102413582949/274877906944 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_4.cS = (-102413582949/274877906944 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_4.rP : ℝ) := by
    have h : (NearCorrection0_4.rP : ℝ) = (((11/25600 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_4.rP = (11/25600 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_4.rS : ℝ) := by
    have h : (NearCorrection0_4.rS : ℝ) = (((3147/22000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_4.rS = (3147/22000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_4.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_4.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_4.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_4.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_4.combined

theorem cell0_3 {x β : ℝ} (hx : x ∈ Icc (((1/16 : ℚ) : ℝ)) (((1/8 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_3.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/16 : ℚ) : ℝ)))/((((1/8 : ℚ) : ℝ))-(((1/16 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_3.cP : ℝ) := by
    have h := bernstein_upper (A := (((-8420849745/17179869184 : ℚ) : ℝ))) (B := (((-16841122739/34359738368 : ℚ) : ℝ))) (C := (((-4210136497/8589934592 : ℚ) : ℝ))) (D := (((-4210136497/8589934592 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-8420849745/17179869184 : ℚ) : ℝ))+2*t*(1-t)*(((-16841122739/34359738368 : ℚ) : ℝ))+t^2*(((-4210136497/8589934592 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_3.cP : ℝ) = (((-4210136497/8589934592 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_3.cP = (-4210136497/8589934592 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_3.cS : ℝ) := by
    have h := bernstein_upper (A := (((-102413582949/274877906944 : ℚ) : ℝ))) (B := (((-51199850469/137438953472 : ℚ) : ℝ))) (C := (((-25596455589/68719476736 : ℚ) : ℝ))) (D := (((-25596455589/68719476736 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-102413582949/274877906944 : ℚ) : ℝ))+2*t*(1-t)*(((-51199850469/137438953472 : ℚ) : ℝ))+t^2*(((-25596455589/68719476736 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_3.cS : ℝ) = (((-25596455589/68719476736 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_3.cS = (-25596455589/68719476736 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_3.rP : ℝ) := by
    have h : (NearCorrection0_3.rP : ℝ) = (((11/12800 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_3.rP = (11/12800 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_3.rS : ℝ) := by
    have h : (NearCorrection0_3.rS : ℝ) = (((49/171875 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_3.rS = (49/171875 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_3.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_3.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_3.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_3.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_3.combined

theorem cell0_2 {x β : ℝ} (hx : x ∈ Icc (((1/8 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_2.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/8 : ℚ) : ℝ)))/((((1/4 : ℚ) : ℝ))-(((1/8 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_2.cP : ℝ) := by
    have h := bernstein_upper (A := (((-4210136497/8589934592 : ℚ) : ℝ))) (B := (((-8419696243/17179869184 : ℚ) : ℝ))) (C := (((-2104779873/4294967296 : ℚ) : ℝ))) (D := (((-2104779873/4294967296 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-4210136497/8589934592 : ℚ) : ℝ))+2*t*(1-t)*(((-8419696243/17179869184 : ℚ) : ℝ))+t^2*(((-2104779873/4294967296 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_2.cP : ℝ) = (((-2104779873/4294967296 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_2.cP = (-2104779873/4294967296 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_2.cS : ℝ) := by
    have h := bernstein_upper (A := (((-25596455589/68719476736 : ℚ) : ℝ))) (B := (((-12794758149/34359738368 : ℚ) : ℝ))) (C := (((-6395645109/17179869184 : ℚ) : ℝ))) (D := (((-6395645109/17179869184 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-25596455589/68719476736 : ℚ) : ℝ))+2*t*(1-t)*(((-12794758149/34359738368 : ℚ) : ℝ))+t^2*(((-6395645109/17179869184 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_2.cS : ℝ) = (((-6395645109/17179869184 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_2.cS = (-6395645109/17179869184 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_2.rP : ℝ) := by
    have h : (NearCorrection0_2.rP : ℝ) = (((11/6400 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_2.rP = (11/6400 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_2.rS : ℝ) := by
    have h : (NearCorrection0_2.rS : ℝ) = (((6261/11000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_2.rS = (6261/11000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_2.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_2.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_2.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_2.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_2.combined

theorem cell0_1 {x β : ℝ} (hx : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_1.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/4 : ℚ) : ℝ)))/((((1/2 : ℚ) : ℝ))-(((1/4 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_1.cP : ℝ) := by
    have h := bernstein_upper (A := (((-2104779873/4294967296 : ℚ) : ℝ))) (B := (((-4208982995/8589934592 : ℚ) : ℝ))) (C := (((-1052101561/2147483648 : ℚ) : ℝ))) (D := (((-1052101561/2147483648 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-2104779873/4294967296 : ℚ) : ℝ))+2*t*(1-t)*(((-4208982995/8589934592 : ℚ) : ℝ))+t^2*(((-1052101561/2147483648 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_1.cP : ℝ) = (((-1052101561/2147483648 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_1.cP = (-1052101561/2147483648 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_1.cS : ℝ) := by
    have h := bernstein_upper (A := (((-6395645109/17179869184 : ℚ) : ℝ))) (B := (((-3196088589/8589934592 : ℚ) : ℝ))) (C := (((-1597178169/4294967296 : ℚ) : ℝ))) (D := (((-1597178169/4294967296 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-6395645109/17179869184 : ℚ) : ℝ))+2*t*(1-t)*(((-3196088589/8589934592 : ℚ) : ℝ))+t^2*(((-1597178169/4294967296 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_1.cS : ℝ) = (((-1597178169/4294967296 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_1.cS = (-1597178169/4294967296 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_1.rP : ℝ) := by
    have h : (NearCorrection0_1.rP : ℝ) = (((11/3200 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_1.rP = (11/3200 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_1.rS : ℝ) := by
    have h : (NearCorrection0_1.rS : ℝ) = (((12511/11000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_1.rS = (12511/11000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_1.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_1.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_1.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_1.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_1.combined

theorem cell0_0 {x β : ℝ} (hx : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a0 x)) :
    correction0 x β ≤ (NearCorrection0_0.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/2 : ℚ) : ℝ)))/((((1/1 : ℚ) : ℝ))-(((1/2 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP0 x ≤ (NearCorrection0_0.cP : ℝ) := by
    have h := bernstein_upper (A := (((-1052101561/2147483648 : ℚ) : ℝ))) (B := (((-2103626371/4294967296 : ℚ) : ℝ))) (C := (((-525762405/1073741824 : ℚ) : ℝ))) (D := (((-525762405/1073741824 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP0 x = (1-t)^2*(((-1052101561/2147483648 : ℚ) : ℝ))+2*t*(1-t)*(((-2103626371/4294967296 : ℚ) : ℝ))+t^2*(((-525762405/1073741824 : ℚ) : ℝ)) := by
      unfold gapP0 t
      push_cast
      ring
    have hD : (NearCorrection0_0.cP : ℝ) = (((-525762405/1073741824 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_0.cP = (-525762405/1073741824 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS0 x ≤ (NearCorrection0_0.cS : ℝ) := by
    have h := bernstein_upper (A := (((-1597178169/4294967296 : ℚ) : ℝ))) (B := (((-797722959/2147483648 : ℚ) : ℝ))) (C := (((-199214637/536870912 : ℚ) : ℝ))) (D := (((-199214637/536870912 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS0 x = (1-t)^2*(((-1597178169/4294967296 : ℚ) : ℝ))+2*t*(1-t)*(((-797722959/2147483648 : ℚ) : ℝ))+t^2*(((-199214637/536870912 : ℚ) : ℝ)) := by
      unfold gapS0 t
      push_cast
      ring
    have hD : (NearCorrection0_0.cS : ℝ) = (((-199214637/536870912 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_0.cS = (-199214637/536870912 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a0_mem hx0
  have hp : 11/8*a0 x ≤ (NearCorrection0_0.rP : ℝ) := by
    have h : (NearCorrection0_0.rP : ℝ) = (((11/1600 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_0.rP = (11/1600 : ℚ) by decide +kernel)
    rw [h]; unfold a0 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection0_0.rS : ℝ) := by
    have h : (NearCorrection0_0.rS : ℝ) = (((25011/11000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection0_0.rS = (25011/11000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a0 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection0_0.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection0_0.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection0_0.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection0_0.rS by decide +kernel))
  unfold correction0
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection0_0.combined

theorem actual0_low {x β : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc 0 (a0 x)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + correction0 x β ≤ -reserve :=
  budget0_low hx (fun hc => cell0_7 hc hβ) (fun hc => cell0_6 hc hβ) (fun hc => cell0_5 hc hβ) (fun hc => cell0_4 hc hβ) (fun hc => cell0_3 hc hβ) (fun hc => cell0_2 hc hβ) (fun hc => cell0_1 hc hβ) (fun hc => cell0_0 hc hβ)

theorem actual0_high {x β : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc 0 (a0 x)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + correction0 x β ≤ -reserve :=
  budget0_high hx (fun hc => cell0_7 hc hβ) (fun hc => cell0_6 hc hβ) (fun hc => cell0_5 hc hβ) (fun hc => cell0_4 hc hβ) (fun hc => cell0_3 hc hβ) (fun hc => cell0_2 hc hβ) (fun hc => cell0_1 hc hβ) (fun hc => cell0_0 hc hβ)

def gapP1 (x : ℝ) : ℝ := (((-525762405/1073741824 : ℚ) : ℝ))*x^0 + (((-979529/67108864 : ℚ) : ℝ))*x^1 + (((-4285711/536870912 : ℚ) : ℝ))*x^2
def gapS1 (x : ℝ) : ℝ := (((-199214637/536870912 : ℚ) : ℝ))*x^0 + (((555617/33554432 : ℚ) : ℝ))*x^1 + (((-132091/268435456 : ℚ) : ℝ))*x^2
def correction1 (x β : ℝ) : ℝ := (467829/1000000) *
  (capInt (gapP1 x) (11/8 * a1 x) (1/1000) + capInt (gapS1 x) (5/11*β+1/1000000) (1/1000))

theorem cell1_2 {x β : ℝ} (hx : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a1 x)) :
    correction1 x β ≤ (NearCorrection1_2.capUpper : ℝ) := by
  let t : ℝ := (x-(((0/1 : ℚ) : ℝ)))/((((1/4 : ℚ) : ℝ))-(((0/1 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP1 x ≤ (NearCorrection1_2.cP : ℝ) := by
    have h := bernstein_upper (A := (((-525762405/1073741824 : ℚ) : ℝ))) (B := (((-527721463/1073741824 : ℚ) : ℝ))) (C := (((-4241729879/8589934592 : ℚ) : ℝ))) (D := (((-525762405/1073741824 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP1 x = (1-t)^2*(((-525762405/1073741824 : ℚ) : ℝ))+2*t*(1-t)*(((-527721463/1073741824 : ℚ) : ℝ))+t^2*(((-4241729879/8589934592 : ℚ) : ℝ)) := by
      unfold gapP1 t
      push_cast
      ring
    have hD : (NearCorrection1_2.cP : ℝ) = (((-525762405/1073741824 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_2.cP = (-525762405/1073741824 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS1 x ≤ (NearCorrection1_2.cS : ℝ) := by
    have h := bernstein_upper (A := (((-199214637/536870912 : ℚ) : ℝ))) (B := (((-198103403/536870912 : ℚ) : ℝ))) (C := (((-1576069443/4294967296 : ℚ) : ℝ))) (D := (((-1576069443/4294967296 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS1 x = (1-t)^2*(((-199214637/536870912 : ℚ) : ℝ))+2*t*(1-t)*(((-198103403/536870912 : ℚ) : ℝ))+t^2*(((-1576069443/4294967296 : ℚ) : ℝ)) := by
      unfold gapS1 t
      push_cast
      ring
    have hD : (NearCorrection1_2.cS : ℝ) = (((-1576069443/4294967296 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_2.cS = (-1576069443/4294967296 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a1_mem hx0
  have hp : 11/8*a1 x ≤ (NearCorrection1_2.rP : ℝ) := by
    have h : (NearCorrection1_2.rP : ℝ) = (((341/12800 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_2.rP = (341/12800 : ℚ) by decide +kernel)
    rw [h]; unfold a1 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection1_2.rS : ℝ) := by
    have h : (NearCorrection1_2.rS : ℝ) = (((48443/5500000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_2.rS = (48443/5500000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a1 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection1_2.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection1_2.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection1_2.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection1_2.rS by decide +kernel))
  unfold correction1
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection1_2.combined

theorem cell1_1 {x β : ℝ} (hx : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a1 x)) :
    correction1 x β ≤ (NearCorrection1_1.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/4 : ℚ) : ℝ)))/((((1/2 : ℚ) : ℝ))-(((1/4 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP1 x ≤ (NearCorrection1_1.cP : ℝ) := by
    have h := bernstein_upper (A := (((-4241729879/8589934592 : ℚ) : ℝ))) (B := (((-2130844027/4294967296 : ℚ) : ℝ))) (C := (((-1071482985/2147483648 : ℚ) : ℝ))) (D := (((-4241729879/8589934592 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP1 x = (1-t)^2*(((-4241729879/8589934592 : ℚ) : ℝ))+2*t*(1-t)*(((-2130844027/4294967296 : ℚ) : ℝ))+t^2*(((-1071482985/2147483648 : ℚ) : ℝ)) := by
      unfold gapP1 t
      push_cast
      ring
    have hD : (NearCorrection1_1.cP : ℝ) = (((-4241729879/8589934592 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_1.cP = (-4241729879/8589934592 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS1 x ≤ (NearCorrection1_1.cS : ℝ) := by
    have h := bernstein_upper (A := (((-1576069443/4294967296 : ℚ) : ℝ))) (B := (((-783655831/2147483648 : ℚ) : ℝ))) (C := (((-389671493/1073741824 : ℚ) : ℝ))) (D := (((-389671493/1073741824 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS1 x = (1-t)^2*(((-1576069443/4294967296 : ℚ) : ℝ))+2*t*(1-t)*(((-783655831/2147483648 : ℚ) : ℝ))+t^2*(((-389671493/1073741824 : ℚ) : ℝ)) := by
      unfold gapS1 t
      push_cast
      ring
    have hD : (NearCorrection1_1.cS : ℝ) = (((-389671493/1073741824 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_1.cS = (-389671493/1073741824 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a1_mem hx0
  have hp : 11/8*a1 x ≤ (NearCorrection1_1.rP : ℝ) := by
    have h : (NearCorrection1_1.rP : ℝ) = (((297/6400 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_1.rP = (297/6400 : ℚ) by decide +kernel)
    rw [h]; unfold a1 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection1_1.rS : ℝ) := by
    have h : (NearCorrection1_1.rS : ℝ) = (((168761/11000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_1.rS = (168761/11000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a1 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection1_1.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection1_1.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection1_1.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection1_1.rS by decide +kernel))
  unfold correction1
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection1_1.combined

theorem cell1_0 {x β : ℝ} (hx : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ))) (hβ : β ∈ Icc 0 (a1 x)) :
    correction1 x β ≤ (NearCorrection1_0.capUpper : ℝ) := by
  let t : ℝ := (x-(((1/2 : ℚ) : ℝ)))/((((1/1 : ℚ) : ℝ))-(((1/2 : ℚ) : ℝ)))
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> first | positivity | apply (div_le_iff₀ (by norm_num)).mpr | apply div_nonneg _ (by norm_num)
    all_goals linarith [hx.1,hx.2]

  have hP : gapP1 x ≤ (NearCorrection1_0.cP : ℝ) := by
    have h := bernstein_upper (A := (((-1071482985/2147483648 : ℚ) : ℝ))) (B := (((-16931327/33554432 : ℚ) : ℝ))) (C := (((-550006291/1073741824 : ℚ) : ℝ))) (D := (((-1071482985/2147483648 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapP1 x = (1-t)^2*(((-1071482985/2147483648 : ℚ) : ℝ))+2*t*(1-t)*(((-16931327/33554432 : ℚ) : ℝ))+t^2*(((-550006291/1073741824 : ℚ) : ℝ)) := by
      unfold gapP1 t
      push_cast
      ring
    have hD : (NearCorrection1_0.cP : ℝ) = (((-1071482985/2147483648 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_0.cP = (-1071482985/2147483648 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hS : gapS1 x ≤ (NearCorrection1_0.cS : ℝ) := by
    have h := bernstein_upper (A := (((-389671493/1073741824 : ℚ) : ℝ))) (B := (((-48169831/134217728 : ℚ) : ℝ))) (C := (((-190588947/536870912 : ℚ) : ℝ))) (D := (((-190588947/536870912 : ℚ) : ℝ))) ht (by norm_num) (by norm_num) (by norm_num)
    have he : gapS1 x = (1-t)^2*(((-389671493/1073741824 : ℚ) : ℝ))+2*t*(1-t)*(((-48169831/134217728 : ℚ) : ℝ))+t^2*(((-190588947/536870912 : ℚ) : ℝ)) := by
      unfold gapS1 t
      push_cast
      ring
    have hD : (NearCorrection1_0.cS : ℝ) = (((-190588947/536870912 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_0.cS = (-190588947/536870912 : ℚ) by decide +kernel)
    rwa [← he, ← hD] at h

  have hx0 : x ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hb0 := hβ.1
  have ha := a1_mem hx0
  have hp : 11/8*a1 x ≤ (NearCorrection1_0.rP : ℝ) := by
    have h : (NearCorrection1_0.rP : ℝ) = (((11/128 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_0.rP = (11/128 : ℚ) by decide +kernel)
    rw [h]; unfold a1 mix; linarith [hx.2]
  have hs : 5/11*β+1/1000000 ≤ (NearCorrection1_0.rS : ℝ) := by
    have h : (NearCorrection1_0.rS : ℝ) = (((312511/11000000 : ℚ) : ℝ)) := by exact_mod_cast (show NearCorrection1_0.rS = (312511/11000000 : ℚ) by decide +kernel)
    rw [h]; have hb := hβ.2; unfold a1 mix at hb; linarith [hx.2]
  have ha0 := ha.1
  have bp := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hP
    (by exact_mod_cast (show NearCorrection1_0.cP ≤ 0 by decide +kernel)) (by positivity) hp
    (by exact_mod_cast (show 0 < NearCorrection1_0.rP by decide +kernel))
  have bs := NearCorrectionInput.monotone (θ := (1/1000 : ℝ)) (by norm_num) (by norm_num) hS
    (by exact_mod_cast (show NearCorrection1_0.cS ≤ 0 by decide +kernel)) (by positivity) hs
    (by exact_mod_cast (show 0 < NearCorrection1_0.rS by decide +kernel))
  unfold correction1
  exact (mul_le_mul_of_nonneg_left (add_le_add bp bs) (by norm_num)).trans NearCorrection1_0.combined

theorem actual1_low {x β : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc 0 (a1 x)) :
    core1 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + correction1 x β ≤ -reserve :=
  budget1_low hx (fun hc => cell1_2 hc hβ) (fun hc => cell1_1 hc hβ) (fun hc => cell1_0 hc hβ)

theorem actual1_high {x β : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc 0 (a1 x)) :
    core1 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + correction1 x β ≤ -reserve :=
  budget1_high hx (fun hc => cell1_2 hc hβ) (fun hc => cell1_1 hc hβ) (fun hc => cell1_0 hc hβ)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetCorrected72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetCorrected72.actual0_low
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetCorrected72.actual0_high
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetCorrected72.actual1_low
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetCorrected72.actual1_high
