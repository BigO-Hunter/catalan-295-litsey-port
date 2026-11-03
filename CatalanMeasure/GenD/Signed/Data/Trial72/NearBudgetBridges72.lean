module

public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget03
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget08
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetPilot
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_3
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_4
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_5
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_6
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_7
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetBridges72
open Set
noncomputable section

def mix (a b x : ℝ) : ℝ := (1-x)*a+x*b
def logCoeff (a : ℝ) : ℝ := 31/24 + 43/40*a - 69/80*a^2
def logUpper : ℝ := (((108304247/156250000 : ℚ) : ℝ))
def reserve : ℝ := 1/(200*72^2)
theorem logUpper_sound : Real.log 2 ≤ logUpper := by
  have h := Real.log_two_lt_d9
  norm_num [logUpper] at h ⊢
  linarith
theorem logCoeff_nonneg {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (1/16)) : 0 ≤ logCoeff a := by
  unfold logCoeff
  nlinarith [ha.1, ha.2, mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]

theorem take_max {B a N P S K : ℝ} (hN : B+a*N+K+reserve≤0) (hP : B+a*P+K+reserve≤0)
    (hS : B+a*S+K+reserve≤0) : B+a*max N (max P S)+K+reserve≤0 := by
  rcases le_total P S with hp | hs
  · rw [max_eq_right hp]
    rcases le_total N S with h | h
    · simpa only [max_eq_right h] using hS
    · simpa only [max_eq_left h] using hN
  · rw [max_eq_left hs]
    rcases le_total N P with h | h
    · simpa only [max_eq_right h] using hP
    · simpa only [max_eq_left h] using hN

def a0 (x : ℝ) : ℝ := mix (((0/1 : ℚ) : ℝ)) (((1/200 : ℚ) : ℝ)) x
def markN0 (x : ℝ) : ℝ := mix (((-4374168466726137/9007199254740992 : ℚ) : ℝ)) (((-4367641230028111/9007199254740992 : ℚ) : ℝ)) x
def markP0 (x : ℝ) : ℝ := mix (((-256471011/536870912 : ℚ) : ℝ)) (((-511384157/1073741824 : ℚ) : ℝ)) x
def markS0 (x : ℝ) : ℝ := (1-x)*(mix (((-158556287/268435456 : ℚ) : ℝ)) (((-154938851/268435456 : ℚ) : ℝ)) x) + x*(mix (((-316571149/536870912 : ℚ) : ℝ)) (((-618669125/1073741824 : ℚ) : ℝ)) x)
def core0 (k x L : ℝ) : ℝ :=
  mix (((86517434737/549755813888 : ℚ) : ℝ)) (((163208789379/1099511627776 : ℚ) : ℝ)) x - (((3774131/274877906944 : ℚ) : ℝ))*x*(1-x) +
  L*logCoeff (a0 x) + (((122434648561/54000000000 : ℚ) : ℝ)) - (((3604373/1000000 : ℚ) : ℝ))*(a0 x) +
  k*(mix (((-1919817152395/1099511627776 : ℚ) : ℝ)) (((-1917131856951/1099511627776 : ℚ) : ℝ)) x) + (1-k-a0 x)*(mix (((-937405127/536870912 : ℚ) : ℝ)) (((-936093947/536870912 : ℚ) : ℝ)) x) + (1-a0 x)*(mix (((-1730573409881/1099511627776 : ℚ) : ℝ)) (((-430851364427/274877906944 : ℚ) : ℝ)) x)

theorem a0_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : a0 x ∈ Icc (0 : ℝ) (1/16) := by
  unfold a0 mix
  constructor <;> norm_num <;> linarith [hx.1,hx.2]

theorem cell0_low_7 {x cap : ℝ} (hx : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/128 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_7.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row42.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row43.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row44.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_7.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_7.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_low_6 {x cap : ℝ} (hx : x ∈ Icc (((1/128 : ℚ) : ℝ)) (((1/64 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_6.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row36.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row37.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row38.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_6.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_6.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_low_5 {x cap : ℝ} (hx : x ∈ Icc (((1/64 : ℚ) : ℝ)) (((1/32 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_5.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row30.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row31.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row32.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_5.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_5.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_low_4 {x cap : ℝ} (hx : x ∈ Icc (((1/32 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_4.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row24.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row25.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row26.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_4.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_4.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_low_3 {x cap : ℝ} (hx : x ∈ Icc (((1/16 : ℚ) : ℝ)) (((1/8 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_3.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row18.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row19.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row20.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_3.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_3.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_low_2 {x cap : ℝ} (hx : x ∈ Icc (((1/8 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_2.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row12.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row13.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row14.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_2.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_2.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_low_1 {x cap : ℝ} (hx : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_1.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row6.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row7.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row8.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_1.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_1.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_low_0 {x cap : ℝ} (hx : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_0.capUpper : ℝ)) :
    core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row0.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row1.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((0/1 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row2.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_0.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_0.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem budget0_low {x cap : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (h7 : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/128 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_7.capUpper : ℝ))
    (h6 : x ∈ Icc (((1/128 : ℚ) : ℝ)) (((1/64 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_6.capUpper : ℝ))
    (h5 : x ∈ Icc (((1/64 : ℚ) : ℝ)) (((1/32 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_5.capUpper : ℝ))
    (h4 : x ∈ Icc (((1/32 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_4.capUpper : ℝ))
    (h3 : x ∈ Icc (((1/16 : ℚ) : ℝ)) (((1/8 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_3.capUpper : ℝ))
    (h2 : x ∈ Icc (((1/8 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_2.capUpper : ℝ))
    (h1 : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_1.capUpper : ℝ))
    (h0 : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_0.capUpper : ℝ))
    : core0 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  by_cases b0 : x ≤ (((1/128 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/128 : ℚ) : ℝ)) := ⟨by simpa using hx.1, b0⟩
    exact cell0_low_7 hcell hx (h7 hcell)
  by_cases b1 : x ≤ (((1/64 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/128 : ℚ) : ℝ)) (((1/64 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b0), b1⟩
    exact cell0_low_6 hcell hx (h6 hcell)
  by_cases b2 : x ≤ (((1/32 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/64 : ℚ) : ℝ)) (((1/32 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b1), b2⟩
    exact cell0_low_5 hcell hx (h5 hcell)
  by_cases b3 : x ≤ (((1/16 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/32 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b2), b3⟩
    exact cell0_low_4 hcell hx (h4 hcell)
  by_cases b4 : x ≤ (((1/8 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/16 : ℚ) : ℝ)) (((1/8 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b3), b4⟩
    exact cell0_low_3 hcell hx (h3 hcell)
  by_cases b5 : x ≤ (((1/4 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/8 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b4), b5⟩
    exact cell0_low_2 hcell hx (h2 hcell)
  by_cases b6 : x ≤ (((1/2 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b5), b6⟩
    exact cell0_low_1 hcell hx (h1 hcell)
  have hcell : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b6), by simpa using hx.2⟩
  exact cell0_low_0 hcell hx (h0 hcell)

theorem cell0_high_7 {x cap : ℝ} (hx : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/128 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_7.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row45.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row46.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row47.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_7.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_7.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_high_6 {x cap : ℝ} (hx : x ∈ Icc (((1/128 : ℚ) : ℝ)) (((1/64 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_6.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row39.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row40.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget05.Row41.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_6.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_6.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_high_5 {x cap : ℝ} (hx : x ∈ Icc (((1/64 : ℚ) : ℝ)) (((1/32 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_5.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row33.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row34.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget04.Row35.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_5.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_5.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_high_4 {x cap : ℝ} (hx : x ∈ Icc (((1/32 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_4.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row27.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row28.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget03.Row29.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_4.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_4.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_high_3 {x cap : ℝ} (hx : x ∈ Icc (((1/16 : ℚ) : ℝ)) (((1/8 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_3.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row21.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row22.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row23.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_3.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_3.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_high_2 {x cap : ℝ} (hx : x ∈ Icc (((1/8 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_2.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row15.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row16.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget02.Row17.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_2.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_2.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_high_1 {x cap : ℝ} (hx : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_1.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row9.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row10.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget01.Row11.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_1.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_1.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem cell0_high_0 {x cap : ℝ} (hx : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection0_0.capUpper : ℝ)) :
    core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  have hN : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markN0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row3.condition x hx
    convert h using 1 <;> simp only [core0, a0, markN0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markP0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row4.condition x hx
    convert h using 1 <;> simp only [core0, a0, markP0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core0 (((1/2 : ℚ) : ℝ)) x logUpper + a0 x * markS0 x + (((467829/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget00.Row5.condition x hx
    convert h using 1 <;> simp only [core0, a0, markS0, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a0_mem h01))
  have hcap : (NearCorrection0_0.capUpper : ℝ) = (((467829/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection0_0.capUpper = (467829/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core0 at h ⊢
  linarith only [h,hL,hc]

theorem budget0_high {x cap : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (h7 : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/128 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_7.capUpper : ℝ))
    (h6 : x ∈ Icc (((1/128 : ℚ) : ℝ)) (((1/64 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_6.capUpper : ℝ))
    (h5 : x ∈ Icc (((1/64 : ℚ) : ℝ)) (((1/32 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_5.capUpper : ℝ))
    (h4 : x ∈ Icc (((1/32 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_4.capUpper : ℝ))
    (h3 : x ∈ Icc (((1/16 : ℚ) : ℝ)) (((1/8 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_3.capUpper : ℝ))
    (h2 : x ∈ Icc (((1/8 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_2.capUpper : ℝ))
    (h1 : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_1.capUpper : ℝ))
    (h0 : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) → cap ≤ (NearCorrection0_0.capUpper : ℝ))
    : core0 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a0 x * max (markN0 x) (max (markP0 x) (markS0 x)) + cap ≤ -reserve := by
  by_cases b0 : x ≤ (((1/128 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/128 : ℚ) : ℝ)) := ⟨by simpa using hx.1, b0⟩
    exact cell0_high_7 hcell hx (h7 hcell)
  by_cases b1 : x ≤ (((1/64 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/128 : ℚ) : ℝ)) (((1/64 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b0), b1⟩
    exact cell0_high_6 hcell hx (h6 hcell)
  by_cases b2 : x ≤ (((1/32 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/64 : ℚ) : ℝ)) (((1/32 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b1), b2⟩
    exact cell0_high_5 hcell hx (h5 hcell)
  by_cases b3 : x ≤ (((1/16 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/32 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b2), b3⟩
    exact cell0_high_4 hcell hx (h4 hcell)
  by_cases b4 : x ≤ (((1/8 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/16 : ℚ) : ℝ)) (((1/8 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b3), b4⟩
    exact cell0_high_3 hcell hx (h3 hcell)
  by_cases b5 : x ≤ (((1/4 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/8 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b4), b5⟩
    exact cell0_high_2 hcell hx (h2 hcell)
  by_cases b6 : x ≤ (((1/2 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b5), b6⟩
    exact cell0_high_1 hcell hx (h1 hcell)
  have hcell : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b6), by simpa using hx.2⟩
  exact cell0_high_0 hcell hx (h0 hcell)

def a1 (x : ℝ) : ℝ := mix (((1/200 : ℚ) : ℝ)) (((1/16 : ℚ) : ℝ)) x
def markN1 (x : ℝ) : ℝ := mix (((-4367641230028111/9007199254740992 : ℚ) : ℝ)) (((-4333909755572637/9007199254740992 : ℚ) : ℝ)) x
def markP1 (x : ℝ) : ℝ := (1-x)*(mix (((-511384157/1073741824 : ℚ) : ℝ)) (((-487700071/1073741824 : ℚ) : ℝ)) x) + x*(mix (((-493153623/1073741824 : ℚ) : ℝ)) (((-460898115/1073741824 : ℚ) : ℝ)) x)
def markS1 (x : ℝ) : ℝ := (1-x)*(mix (((-618669125/1073741824 : ℚ) : ℝ)) (((-225764819/536870912 : ℚ) : ℝ)) x) + x*(mix (((-303045805/536870912 : ℚ) : ℝ)) (((-27401485/67108864 : ℚ) : ℝ)) x)
def core1 (k x L : ℝ) : ℝ :=
  mix (((163208789379/1099511627776 : ℚ) : ℝ)) (((26542512455/549755813888 : ℚ) : ℝ)) x - (((3073407623/1099511627776 : ℚ) : ℝ))*x*(1-x) +
  L*logCoeff (a1 x) + (((122434648561/54000000000 : ℚ) : ℝ)) - (((3604373/1000000 : ℚ) : ℝ))*(a1 x) +
  k*(mix (((-1917131856951/1099511627776 : ℚ) : ℝ)) (((-1885879722183/1099511627776 : ℚ) : ℝ)) x) + (1-k-a1 x)*(mix (((-936093947/536870912 : ℚ) : ℝ)) (((-1841668247/1073741824 : ℚ) : ℝ)) x) + (1-a1 x)*(mix (((-430851364427/274877906944 : ℚ) : ℝ)) (((-1639939960001/1099511627776 : ℚ) : ℝ)) x)

theorem a1_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : a1 x ∈ Icc (0 : ℝ) (1/16) := by
  unfold a1 mix
  constructor <;> norm_num <;> linarith [hx.1,hx.2]

theorem cell1_low_2 {x cap : ℝ} (hx : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection1_2.capUpper : ℝ)) :
    core1 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  have hN : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markN1 x + (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row60.condition x hx
    convert h using 1 <;> simp only [core1, a1, markN1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markP1 x + (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudgetPilot.condition x hx
    convert h using 1 <;> simp only [core1, a1, markP1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markS1 x + (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row62.condition x hx
    convert h using 1 <;> simp only [core1, a1, markS1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a1_mem h01))
  have hcap : (NearCorrection1_2.capUpper : ℝ) = (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection1_2.capUpper = (156929057309652869349/1208925819614629174706176000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core1 at h ⊢
  linarith only [h,hL,hc]

theorem cell1_low_1 {x cap : ℝ} (hx : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection1_1.capUpper : ℝ)) :
    core1 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  have hN : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markN1 x + (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row54.condition x hx
    convert h using 1 <;> simp only [core1, a1, markN1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markP1 x + (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row55.condition x hx
    convert h using 1 <;> simp only [core1, a1, markP1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markS1 x + (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row56.condition x hx
    convert h using 1 <;> simp only [core1, a1, markS1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a1_mem h01))
  have hcap : (NearCorrection1_1.capUpper : ℝ) = (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection1_1.capUpper = (313882698034621109556243/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core1 at h ⊢
  linarith only [h,hL,hc]

theorem cell1_low_0 {x cap : ℝ} (hx : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection1_0.capUpper : ℝ)) :
    core1 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  have hN : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markN1 x + (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row48.condition x hx
    convert h using 1 <;> simp only [core1, a1, markN1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markP1 x + (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row49.condition x hx
    convert h using 1 <;> simp only [core1, a1, markP1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core1 (((0/1 : ℚ) : ℝ)) x logUpper + a1 x * markS1 x + (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row50.condition x hx
    convert h using 1 <;> simp only [core1, a1, markS1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a1_mem h01))
  have hcap : (NearCorrection1_0.capUpper : ℝ) = (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection1_0.capUpper = (10221608737238770342805697/120892581961462917470617600000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core1 at h ⊢
  linarith only [h,hL,hc]

theorem budget1_low {x cap : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (h2 : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) → cap ≤ (NearCorrection1_2.capUpper : ℝ))
    (h1 : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) → cap ≤ (NearCorrection1_1.capUpper : ℝ))
    (h0 : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) → cap ≤ (NearCorrection1_0.capUpper : ℝ))
    : core1 (((0/1 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  by_cases b0 : x ≤ (((1/4 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) := ⟨by simpa using hx.1, b0⟩
    exact cell1_low_2 hcell hx (h2 hcell)
  by_cases b1 : x ≤ (((1/2 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b0), b1⟩
    exact cell1_low_1 hcell hx (h1 hcell)
  have hcell : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b1), by simpa using hx.2⟩
  exact cell1_low_0 hcell hx (h0 hcell)

theorem cell1_high_2 {x cap : ℝ} (hx : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection1_2.capUpper : ℝ)) :
    core1 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  have hN : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markN1 x + (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row63.condition x hx
    convert h using 1 <;> simp only [core1, a1, markN1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markP1 x + (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row64.condition x hx
    convert h using 1 <;> simp only [core1, a1, markP1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markS1 x + (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget08.Row65.condition x hx
    convert h using 1 <;> simp only [core1, a1, markS1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a1_mem h01))
  have hcap : (NearCorrection1_2.capUpper : ℝ) = (((156929057309652869349/1208925819614629174706176000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection1_2.capUpper = (156929057309652869349/1208925819614629174706176000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core1 at h ⊢
  linarith only [h,hL,hc]

theorem cell1_high_1 {x cap : ℝ} (hx : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection1_1.capUpper : ℝ)) :
    core1 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  have hN : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markN1 x + (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row57.condition x hx
    convert h using 1 <;> simp only [core1, a1, markN1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markP1 x + (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row58.condition x hx
    convert h using 1 <;> simp only [core1, a1, markP1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markS1 x + (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget07.Row59.condition x hx
    convert h using 1 <;> simp only [core1, a1, markS1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a1_mem h01))
  have hcap : (NearCorrection1_1.capUpper : ℝ) = (((313882698034621109556243/604462909807314587353088000000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection1_1.capUpper = (313882698034621109556243/604462909807314587353088000000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core1 at h ⊢
  linarith only [h,hL,hc]

theorem cell1_high_0 {x cap : ℝ} (hx : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)))
    (h01 : x ∈ Icc (0 : ℝ) 1) (hc : cap ≤ (NearCorrection1_0.capUpper : ℝ)) :
    core1 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  have hN : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markN1 x + (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row51.condition x hx
    convert h using 1 <;> simp only [core1, a1, markN1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hP : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markP1 x + (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row52.condition x hx
    convert h using 1 <;> simp only [core1, a1, markP1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have hS : core1 (((1/2 : ℚ) : ℝ)) x logUpper + a1 x * markS1 x + (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) + reserve ≤ 0 := by
    have h := NearBudget06.Row53.condition x hx
    convert h using 1 <;> simp only [core1, a1, markS1, mix, logCoeff, logUpper, reserve] <;> push_cast <;> ring
  have h := take_max hN hP hS
  have hL := mul_le_mul_of_nonneg_right logUpper_sound (logCoeff_nonneg (a1_mem h01))
  have hcap : (NearCorrection1_0.capUpper : ℝ) = (((10221608737238770342805697/120892581961462917470617600000 : ℚ) : ℝ)) := by
    exact_mod_cast (show NearCorrection1_0.capUpper = (10221608737238770342805697/120892581961462917470617600000 : ℚ) by decide +kernel)
  rw [hcap] at hc
  unfold core1 at h ⊢
  linarith only [h,hL,hc]

theorem budget1_high {x cap : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (h2 : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) → cap ≤ (NearCorrection1_2.capUpper : ℝ))
    (h1 : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) → cap ≤ (NearCorrection1_1.capUpper : ℝ))
    (h0 : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) → cap ≤ (NearCorrection1_0.capUpper : ℝ))
    : core1 (((1/2 : ℚ) : ℝ)) x (Real.log 2) + a1 x * max (markN1 x) (max (markP1 x) (markS1 x)) + cap ≤ -reserve := by
  by_cases b0 : x ≤ (((1/4 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((0/1 : ℚ) : ℝ)) (((1/4 : ℚ) : ℝ)) := ⟨by simpa using hx.1, b0⟩
    exact cell1_high_2 hcell hx (h2 hcell)
  by_cases b1 : x ≤ (((1/2 : ℚ) : ℝ))
  · have hcell : x ∈ Icc (((1/4 : ℚ) : ℝ)) (((1/2 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b0), b1⟩
    exact cell1_high_1 hcell hx (h1 hcell)
  have hcell : x ∈ Icc (((1/2 : ℚ) : ℝ)) (((1/1 : ℚ) : ℝ)) := ⟨by simpa using (le_of_not_ge b1), by simpa using hx.2⟩
  exact cell1_high_0 hcell hx (h0 hcell)

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetBridges72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetBridges72.budget0_low
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetBridges72.budget0_high
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetBridges72.budget1_low
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetBridges72.budget1_high
