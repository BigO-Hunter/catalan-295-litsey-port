module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.AffineTape
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine006
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

namespace P042
def win : List Aff := [⟨1, 0, -1000000001⟩, ⟨-96666667, 20000000, 9999999⟩, ⟨290999999, -60000000, -30000000⟩]
#time def cert : Cert := [
  (⟨-97, 22, 11⟩, [.hyp 0, .scale 93333337 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 10000000 4]),
  (⟨-87, 18, 9⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 10000000 4]),
  (⟨-86, 18, 9⟩, [.hyp 0, .scale 10000003 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 10000000 4]),
  (⟨-70, 16, 9⟩, [.hyp 0, .scale 9166667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1250000 4]),
  (⟨-66, 14, 7⟩, [.hyp 0, .scale 16666669 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 10000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 41666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 41666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 46666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-8, 2, 1⟩, [.hyp 0, .scale 16666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 36666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 1, 0⟩, [.hyp 0, .scale 16666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 56666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 56666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 56666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 96666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -1, -1⟩, [.hyp 0, .scale 189000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 60000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 39000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 30000000 4]),
  (⟨60, -12, -7⟩, [.hyp 0, .scale 9000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨66, -12, -7⟩, [.hyp 0, .scale 39000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 849000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15000000 4]),
  (⟨87, -16, -9⟩, [.hyp 0, .scale 35250001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3750000 4]),
  (⟨97, -20, -11⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨97, -20, -10⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3000000 4]),
]
-- kcost: 0.0888 s conservative; 148 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P042

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine006
