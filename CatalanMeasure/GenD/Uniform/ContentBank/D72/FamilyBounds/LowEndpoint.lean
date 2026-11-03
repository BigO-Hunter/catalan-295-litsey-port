module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
@[expose] public section
set_option Elab.async false
/-! Exact finite endpoints for the single-cell D72 C and C-prime windows. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
noncomputable section

def lowLo72 (S Jlo N p : Nat) : Int :=
  max 0 (max (97 * (N : Int) - ((S + 1) * p : Nat))
    (86 * (N : Int) + ((Jlo - 1) * p : Nat) - (S * p : Nat)))

/-- Twice the leading upper endpoint; the half-integer guard is exact. -/
def lowHi2_72 (S Jhi K : Nat) (k0 : Int) (N p : Nat) : Int :=
  min (2 * (p : Int)) (min (194 * (N : Int) - 2 * (S * p : Nat))
    (min (20 * (N : Int) + 2 * ((Jhi + 1) * p : Nat) - 2 * (S * p : Nat))
      (min (8 * (N : Int) - p)
        (min (20 * (N : Int) + 2 * (k0 * p) - 2 * p)
          (140 * (N : Int) - 2 * ((k0 + K) * p))))))

def lowCost72 (N p : Nat) : Nat := (p - 4 * N) + (4 * N - p)

structure LowEndpoints72 (S Jlo Jhi K : Nat) (k0 : Int) (N p lo hi : Nat)
    (value : ℝ) : Prop where
  ordered : lo ≤ hi
  upper : hi ≤ p
  shift_nonneg : 0 ≤ (hi : Int) + p - 4 * N
  half : (hi : Int) + p - 4 * N ≤ ((p - 1) / 2 : Nat)
  bottom : -6 * (N : Int) ≤ k0 * p - ((hi : Int) + p - 4 * N)
  top : (k0 + K - 1) * p + ((hi : Int) + p - 4 * N) < 66 * (N : Int)
  window : ∀ e, lo ≤ e → e < hi →
    S * p + e + 1 ≤ 97 * N ∧ 97 * N ≤ (S + 1) * p + e ∧
    (Jlo - 1) * p + (97 * N - 1 - e - S * p) < 11 * N ∧
    87 * N ≤ (Jhi + 1) * p + (97 * N - 1 - e - S * p)
  room : value - 2 ≤ (hi : ℝ) - lo - lowCost72 N p

/-- For a positive requested bound choose `floor(hiLeading) - 1`.
All slot and digit guards then hold with strictly less than two units of loss. -/
theorem low_endpoints72 (S Jlo Jhi K : Nat) (k0 : Int) (N p : Nat) (value : ℝ)
    (hpos : 2 < value)
    (hle : value ≤ (lowHi2_72 S Jhi K k0 N p : ℝ) / 2 -
      (lowLo72 S Jlo N p : ℝ) - lowCost72 N p) :
    ∃ lo hi : Nat, LowEndpoints72 S Jlo Jhi K k0 N p lo hi value := by
  let il := lowLo72 S Jlo N p
  let iu := lowHi2_72 S Jhi K k0 N p / 2 - 1
  have il0 : 0 ≤ il := by unfold il lowLo72; exact le_max_left _ _
  have ilW : 97 * (N : Int) - ((S + 1) * p : Nat) ≤ il := by unfold il lowLo72; omega
  have ilJ : 86 * (N : Int) + ((Jlo - 1) * p : Nat) - (S * p : Nat) ≤ il := by
    unfold il lowLo72; omega
  have hf : lowHi2_72 S Jhi K k0 N p ≤ 2 * iu + 3 := by dsimp only [iu]; omega
  have hu : 2 * iu + 2 ≤ lowHi2_72 S Jhi K k0 N p := by dsimp only [iu]; omega
  have hfR : (lowHi2_72 S Jhi K k0 N p : ℝ) ≤ 2 * (iu : ℝ) + 3 := by exact_mod_cast hf
  have hroom : value - 2 ≤ (iu : ℝ) - (il : ℝ) - lowCost72 N p := by
    change value ≤ (lowHi2_72 S Jhi K k0 N p : ℝ) / 2 - (il : ℝ) - lowCost72 N p at hle
    linarith
  have il0R : (0 : ℝ) ≤ il := by exact_mod_cast il0
  have hc0 : (0 : ℝ) ≤ lowCost72 N p := by positivity
  have iu0 : 0 ≤ iu := by exact_mod_cast (show (0 : ℝ) ≤ iu by linarith)
  let lo := il.toNat
  let hi := iu.toNat
  have hlo : (lo : Int) = il := Int.toNat_of_nonneg il0
  have hhi : (hi : Int) = iu := Int.toNat_of_nonneg iu0
  have hloR : (lo : ℝ) = il := by exact_mod_cast hlo
  have hhiR : (hi : ℝ) = iu := by exact_mod_cast hhi
  rw [← hloR, ← hhiR] at hroom
  have hsize : lo + lowCost72 N p ≤ hi := by
    exact_mod_cast (show (lo : ℝ) + lowCost72 N p ≤ hi by linarith)
  simp only [lowHi2_72, le_min_iff] at hu
  obtain ⟨huP, huW, huJ, huHalf, huBot, huTop⟩ := hu
  have hsz : lowCost72 N p ≤ hi := by omega
  unfold lowCost72 at hsz
  have hlW : 97 * N ≤ (S + 1) * p + lo := by omega
  have hlJ : (Jlo - 1) * p + 97 * N ≤ 11 * N + lo + S * p := by omega
  have hhW : S * p + hi ≤ 97 * N := by omega
  have hhJ : 87 * N + hi + S * p ≤ (Jhi + 1) * p + 97 * N := by omega
  refine ⟨lo, hi, ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_, hroom⟩⟩
  · rw [sub_mul, one_mul]
    omega
  · intro e hel heu
    omega

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
