module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.AffineTape
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine005
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

namespace P040
def win : List Aff := [⟨1, 0, -49600000001⟩, ⟨-279500001, 221000000, 110499999⟩, ⟨2533333333, -2000000000, -1000000000⟩]
#time def cert : Cert := [
  (⟨-97, 78, 39⟩, [.hyp 0, .scale 14000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 8500000 4]),
  (⟨-93, 74, 36⟩, [.hyp 0, .scale 65000037 0, .hyp 1, .scale 37 2, .add 1 3, .tighten 110500000 4]),
  (⟨-87, 70, 35⟩, [.hyp 0, .scale 33800007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 22100000 4]),
  (⟨-86, 68, 34⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3250000 4]),
  (⟨-70, 56, 29⟩, [.hyp 0, .scale 22750007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 27625000 4]),
  (⟨-66, 54, 27⟩, [.hyp 0, .scale 253500027 0, .hyp 1, .scale 27 2, .add 1 3, .tighten 110500000 4]),
  (⟨-60, 48, 25⟩, [.hyp 0, .scale 9750003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 13812500 4]),
  (⟨-11, 10, 4⟩, [.hyp 0, .scale 36400001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 22100000 4]),
  (⟨-11, 10, 5⟩, [.hyp 0, .scale 36400001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 22100000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 3250001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 27625000 4]),
  (⟨-8, 7, 4⟩, [.hyp 0, .scale 188500007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 221000000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 175500003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 110500000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 58500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 55250000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 58500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 55250000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 58500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 55250000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 279500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 221000000 4]),
  (⟨4, -3, -2⟩, [.hyp 0, .scale 400000001 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2000000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 1466666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 1466666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 466666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 500000000 4]),
  (⟨8, -6, -3⟩, [.hyp 0, .scale 400000001 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 1000000000 4]),
  (⟨11, -8, -4⟩, [.hyp 0, .scale 216666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 250000000 4]),
  (⟨66, -52, -27⟩, [.hyp 0, .scale 66666671 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 500000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 68400000001 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 1000000000 4]),
  (⟨86, -66, -33⟩, [.hyp 0, .scale 2400000011 0, .hyp 2, .scale 33 2, .add 1 3, .tighten 1000000000 4]),
  (⟨87, -68, -35⟩, [.hyp 0, .scale 433333339 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 500000000 4]),
  (⟨97, -76, -39⟩, [.hyp 0, .scale 366666673 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 500000000 4]),
  (⟨97, -76, -38⟩, [.hyp 0, .scale 366666673 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 500000000 4]),
]
-- kcost: 0.1032 s conservative; 172 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P040

namespace P041
def win : List Aff := [⟨1, 0, -450000001⟩, ⟨-7600000001, 4600000000, 2299999999⟩, ⟨33076923, -20000000, -10000000⟩]
#time def cert : Cert := [
  (⟨-97, 60, 30⟩, [.hyp 0, .scale 490000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 230000000 4]),
  (⟨-87, 54, 27⟩, [.hyp 0, .scale 5100000027 0, .hyp 1, .scale 27 2, .add 1 3, .tighten 2300000000 4]),
  (⟨-70, 44, 23⟩, [.hyp 0, .scale 3100000011 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 1150000000 4]),
  (⟨-66, 40, 20⟩, [.hyp 0, .scale 10000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 115000000 4]),
  (⟨-11, 8, 3⟩, [.hyp 0, .scale 1275000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 575000000 4]),
  (⟨-8, 5, 3⟩, [.hyp 0, .scale 240000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 920000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 700000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1150000000 4]),
  (⟨-4, 3, 1⟩, [.hyp 0, .scale 4400000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 4600000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 3000000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1150000000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 3000000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1150000000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 3000000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1150000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 7600000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4600000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 6923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 6923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 46923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 20000000 4]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 26923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨10, -6, -3⟩, [.hyp 0, .scale 769231 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 10000000 4]),
  (⟨11, -6, -3⟩, [.hyp 0, .scale 10769231 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 10000000 4]),
  (⟨60, -36, -19⟩, [.hyp 0, .scale 2307693 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 5000000 4]),
  (⟨66, -38, -20⟩, [.hyp 0, .scale 31538463 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 10000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 660769231 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 10000000 4]),
  (⟨86, -52, -26⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 5000000 4]),
  (⟨87, -52, -27⟩, [.hyp 0, .scale 5000001 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 5000000 4]),
  (⟨93, -56, -28⟩, [.hyp 0, .scale 961539 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 2500000 4]),
  (⟨97, -58, -30⟩, [.hyp 0, .scale 10769233 0, .hyp 2, .scale 29 2, .add 1 3, .tighten 10000000 4]),
]
-- kcost: 0.0924 s conservative; 154 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P041

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine005
