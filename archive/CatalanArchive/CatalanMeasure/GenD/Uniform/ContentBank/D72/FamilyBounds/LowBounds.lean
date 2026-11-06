module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowEndpoint
public import CatalanMeasure.GenD.Uniform.W.TheoremC.LBP
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.TheoremC
noncomputable section

private theorem p72_q (N : Nat) : P72.q N = 4 * N := rfl
private theorem p72_h (N : Nat) : P72.h N = 4 * N := rfl
private theorem p72_b (N : Nat) : P72.b N = 11 * N := rfl
private theorem p72_g (N : Nat) : P72.g N = 6 * N := rfl
private theorem p72_n (N : Nat) : P72.n N = 72 * N := rfl

private theorem room_to_kap (value : ℝ) (lo hi cost kap : Nat)
    (hroom : value - 2 ≤ (hi : ℝ) - lo - cost)
    (hkap : hi - lo - cost ≤ kap) : value - 2 ≤ (kap : ℝ) := by
  have hb : hi ≤ lo + cost + kap := by omega
  have hbR : (hi : ℝ) ≤ (lo : ℝ) + cost + kap := by exact_mod_cast hb
  linarith

theorem lowC_kap72 (c : CCell) {N p : Nat} {value : ℝ}
    (hN : 0 < N) (hphase : 4 * N ≤ p) (hcop : Nat.Coprime p c.modulus)
    (hle : value ≤ (lowHi2_72 c.S c.Jhi c.K c.k0 N p : ℝ) / 2 -
      (lowLo72 c.S c.Jlo N p : ℝ) - lowCost72 N p) :
    value - 2 ≤ ((cCellLB c P72 p72_admissible).kap N p : ℝ) := by
  by_cases hp : 2 < value
  · obtain ⟨lo, hi, he⟩ := low_endpoints72 c.S c.Jlo c.Jhi c.K c.k0 N p value hp hle
    have hz : ((hi + (p - 4 * N) : Nat) : Int) = (hi : Int) + p - 4 * N := by
      push_cast [Nat.cast_sub hphase] <;> ring
    have hc : cCond c P72 N p lo hi := by
      unfold cCond
      rw [p72_h, p72_g, p72_n]
      refine ⟨he.ordered, he.upper, hphase, ?_, ?_, ?_, ?_⟩
      · exact_mod_cast (show ((hi + (p - 4 * N) : Nat) : Int) ≤ ((p - 1) / 2 : Nat) by
          rw [hz]; exact he.half)
      · rw [hz]; push_cast; linarith [he.bottom]
      · rw [hz]; push_cast; linarith [he.top]
      · rw [p72_H, p72_L, p72_b]; exact he.window
    have hq : 0 < P72.q N := by rw [p72_q]; omega
    have hk := cCellLB_kap_ge c P72 p72_admissible hcop hq hc
    rw [p72_q] at hk
    have hcost : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
    exact room_to_kap value lo hi _ _ he.room (by rwa [hcost])
  · have hn : (0 : ℝ) ≤ (cCellLB c P72 p72_admissible).kap N p := by positivity
    linarith

theorem lowCp_kap72 (c : CCell2) {N p : Nat} {value : ℝ}
    (hN : 0 < N) (hphase : p ≤ 4 * N) (hcop : Nat.Coprime p c.modulus)
    (hle : value ≤ (lowHi2_72 c.S c.Jhi c.K c.k0 N p : ℝ) / 2 -
      (lowLo72 c.S c.Jlo N p : ℝ) - lowCost72 N p) :
    value - 2 ≤ ((cCellLBP c P72 p72_admissible).kap N p : ℝ) := by
  by_cases hp : 2 < value
  · obtain ⟨lo, hi, he⟩ := low_endpoints72 c.S c.Jlo c.Jhi c.K c.k0 N p value hp hle
    have hshift := he.shift_nonneg
    have hnat : 4 * N - p ≤ hi := by omega
    have hz : ((hi - (4 * N - p) : Nat) : Int) = (hi : Int) + p - 4 * N := by
      rw [Nat.cast_sub hnat, Nat.cast_sub hphase]
      push_cast <;> ring
    have hc : cCondP c P72 N p lo hi := by
      unfold cCondP
      rw [p72_h, p72_g, p72_n]
      refine ⟨he.upper, hphase, ?_, ?_, ?_, ?_⟩
      · exact_mod_cast (show ((hi - (4 * N - p) : Nat) : Int) ≤ ((p - 1) / 2 : Nat) by
          rw [hz]; exact he.half)
      · rw [hz]; push_cast; linarith [he.bottom]
      · rw [hz]; push_cast; linarith [he.top]
      · rw [p72_H, p72_L, p72_b]; exact he.window
    have hq : 0 < P72.q N := by rw [p72_q]; omega
    have hk := cCellLBP_kap_ge c P72 p72_admissible hcop hq hc
    rw [p72_q, p72_h] at hk
    have hcost : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
    have hzq : p - 4 * N = 0 := by omega
    rw [hzq, Nat.sub_zero] at hk
    exact room_to_kap value lo hi _ _ he.room (by rwa [hcost])
  · have hn : (0 : ℝ) ≤ (cCellLBP c P72 p72_admissible).kap N p := by positivity
    linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
