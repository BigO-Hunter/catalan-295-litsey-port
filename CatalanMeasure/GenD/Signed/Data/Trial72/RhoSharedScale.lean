module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP

@[expose] public section
set_option Elab.async false
set_option profiler true

namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

/-- The integer inequality tested by shareN is the exact rational rho
inequality multiplied by its positive common denominator. -/
theorem sound {P x p q U v D : ℝ} (hq : 0 < q) (hv : 0 < v) (hD : 0 < D)
    (h : 0 ≤ v * P * (2 * (q + p) + q * x) - 2 * q * D * U) :
    U / v ≤ (P / D) * (1 + p / q + x / 2) := by
  have he : v * P * (2 * (q + p) + q * x) - 2 * q * D * U =
      (2 * q * D * v) * ((P / D) * (1 + p / q + x / 2) - U / v) := by
    field_simp [hq.ne', hv.ne', hD.ne']
    <;> ring
  rw [he] at h
  have hp : 0 < 2 * q * D * v := by positivity
  apply sub_nonneg.mp
  by_contra! hn
  exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hp hn)

end CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale.sound
