module
public import Mathlib.Tactic.IntervalCases
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows00
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows01
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows02
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows03
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows04
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows05
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows06
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows07
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows08
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows09
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040HeadRows11
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.HeadParts

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040
open CatalanMeasure.GenD.Uniform.W.Prof


private theorem checkedRows (i : Nat) (hi : i < 90) : headRowOK i = true := by
  interval_cases i
  · exact List.all_eq_true.mp headRows00 0 (by decide)
  · exact List.all_eq_true.mp headRows00 1 (by decide)
  · exact List.all_eq_true.mp headRows00 2 (by decide)
  · exact List.all_eq_true.mp headRows00 3 (by decide)
  · exact List.all_eq_true.mp headRows00 4 (by decide)
  · exact List.all_eq_true.mp headRows00 5 (by decide)
  · exact List.all_eq_true.mp headRows00 6 (by decide)
  · exact List.all_eq_true.mp headRows00 7 (by decide)
  · exact List.all_eq_true.mp headRows01 8 (by decide)
  · exact List.all_eq_true.mp headRows01 9 (by decide)
  · exact List.all_eq_true.mp headRows01 10 (by decide)
  · exact List.all_eq_true.mp headRows01 11 (by decide)
  · exact List.all_eq_true.mp headRows01 12 (by decide)
  · exact List.all_eq_true.mp headRows01 13 (by decide)
  · exact List.all_eq_true.mp headRows01 14 (by decide)
  · exact List.all_eq_true.mp headRows01 15 (by decide)
  · exact List.all_eq_true.mp headRows02 16 (by decide)
  · exact List.all_eq_true.mp headRows02 17 (by decide)
  · exact List.all_eq_true.mp headRows02 18 (by decide)
  · exact List.all_eq_true.mp headRows02 19 (by decide)
  · exact List.all_eq_true.mp headRows02 20 (by decide)
  · exact List.all_eq_true.mp headRows02 21 (by decide)
  · exact List.all_eq_true.mp headRows02 22 (by decide)
  · exact List.all_eq_true.mp headRows02 23 (by decide)
  · exact List.all_eq_true.mp headRows03 24 (by decide)
  · exact List.all_eq_true.mp headRows03 25 (by decide)
  · exact List.all_eq_true.mp headRows03 26 (by decide)
  · exact List.all_eq_true.mp headRows03 27 (by decide)
  · exact List.all_eq_true.mp headRows03 28 (by decide)
  · exact List.all_eq_true.mp headRows03 29 (by decide)
  · exact List.all_eq_true.mp headRows03 30 (by decide)
  · exact List.all_eq_true.mp headRows03 31 (by decide)
  · exact List.all_eq_true.mp headRows04 32 (by decide)
  · exact List.all_eq_true.mp headRows04 33 (by decide)
  · exact List.all_eq_true.mp headRows04 34 (by decide)
  · exact List.all_eq_true.mp headRows04 35 (by decide)
  · exact List.all_eq_true.mp headRows04 36 (by decide)
  · exact List.all_eq_true.mp headRows04 37 (by decide)
  · exact List.all_eq_true.mp headRows04 38 (by decide)
  · exact List.all_eq_true.mp headRows04 39 (by decide)
  · exact List.all_eq_true.mp headRows05 40 (by decide)
  · exact List.all_eq_true.mp headRows05 41 (by decide)
  · exact List.all_eq_true.mp headRows05 42 (by decide)
  · exact List.all_eq_true.mp headRows05 43 (by decide)
  · exact List.all_eq_true.mp headRows05 44 (by decide)
  · exact List.all_eq_true.mp headRows05 45 (by decide)
  · exact List.all_eq_true.mp headRows05 46 (by decide)
  · exact List.all_eq_true.mp headRows05 47 (by decide)
  · exact List.all_eq_true.mp headRows06 48 (by decide)
  · exact List.all_eq_true.mp headRows06 49 (by decide)
  · exact List.all_eq_true.mp headRows06 50 (by decide)
  · exact List.all_eq_true.mp headRows06 51 (by decide)
  · exact List.all_eq_true.mp headRows06 52 (by decide)
  · exact List.all_eq_true.mp headRows06 53 (by decide)
  · exact List.all_eq_true.mp headRows06 54 (by decide)
  · exact List.all_eq_true.mp headRows06 55 (by decide)
  · exact List.all_eq_true.mp headRows07 56 (by decide)
  · exact List.all_eq_true.mp headRows07 57 (by decide)
  · exact List.all_eq_true.mp headRows07 58 (by decide)
  · exact List.all_eq_true.mp headRows07 59 (by decide)
  · exact List.all_eq_true.mp headRows07 60 (by decide)
  · exact List.all_eq_true.mp headRows07 61 (by decide)
  · exact List.all_eq_true.mp headRows07 62 (by decide)
  · exact List.all_eq_true.mp headRows07 63 (by decide)
  · exact List.all_eq_true.mp headRows08 64 (by decide)
  · exact List.all_eq_true.mp headRows08 65 (by decide)
  · exact List.all_eq_true.mp headRows08 66 (by decide)
  · exact List.all_eq_true.mp headRows08 67 (by decide)
  · exact List.all_eq_true.mp headRows08 68 (by decide)
  · exact List.all_eq_true.mp headRows08 69 (by decide)
  · exact List.all_eq_true.mp headRows08 70 (by decide)
  · exact List.all_eq_true.mp headRows08 71 (by decide)
  · exact List.all_eq_true.mp headRows09 72 (by decide)
  · exact List.all_eq_true.mp headRows09 73 (by decide)
  · exact List.all_eq_true.mp headRows09 74 (by decide)
  · exact List.all_eq_true.mp headRows09 75 (by decide)
  · exact List.all_eq_true.mp headRows09 76 (by decide)
  · exact List.all_eq_true.mp headRows09 77 (by decide)
  · exact List.all_eq_true.mp headRows09 78 (by decide)
  · exact List.all_eq_true.mp headRows09 79 (by decide)
  · exact List.all_eq_true.mp headRows10 80 (by decide)
  · exact List.all_eq_true.mp headRows10 81 (by decide)
  · exact List.all_eq_true.mp headRows10 82 (by decide)
  · exact List.all_eq_true.mp headRows10 83 (by decide)
  · exact List.all_eq_true.mp headRows10 84 (by decide)
  · exact List.all_eq_true.mp headRows10 85 (by decide)
  · exact List.all_eq_true.mp headRows10 86 (by decide)
  · exact List.all_eq_true.mp headRows10 87 (by decide)
  · exact List.all_eq_true.mp headRows11 88 (by decide)
  · exact List.all_eq_true.mp headRows11 89 (by decide)

theorem inputHeadChecked : input.packet.checkHead = true := by
  have hv : input.packet.v.length = 90 := by decide +kernel
  apply checkHead_of_rows
  · decide +kernel
  · intro i hi
    change headRowOK i = true
    exact checkedRows i (by simpa only [hv] using hi)
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P040
