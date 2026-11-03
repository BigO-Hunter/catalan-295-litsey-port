module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.WindowPrice
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD.Uniform.LedgerW

-- Exact decoded rational (133-bit numerator, 128-bit denominator), no rounding.
theorem fullLedgerQ_value72 :
    fullLedgerQ = (8933203334180631204080621086471618701667 /
      258903586359571936582800000000000000000 : Rat) := by
  decide +kernel

theorem full_content_beta72 :
    19129 / 2 - (fullLedgerQ : ℝ) =
      2467350148401945156242109978913528381298333 /
        258903586359571936582800000000000000000 := by
  rw [fullLedgerQ_value72]
  norm_num

theorem full_content_beta72_le :
    19129 / 2 - (fullLedgerQ : ℝ) ≤ (4291778436568158111689440044740051097612623 /
      450344200156521455970900000000000000000 : ℝ) := by
  rw [full_content_beta72]
  norm_num

theorem full_content_price72_le :
    gD P72 f72 kappa072 (windows72 fullWindowTape) ≤
      (1057 / 2 : ℝ) * Real.log 2 +
        4291778436568158111689440044740051097612623 /
          450344200156521455970900000000000000000 := by
  rw [full_window_price72]
  exact add_le_add le_rfl full_content_beta72_le

#print axioms full_content_price72_le
end CatalanMeasure.GenD.Uniform.ContentBank.D72
