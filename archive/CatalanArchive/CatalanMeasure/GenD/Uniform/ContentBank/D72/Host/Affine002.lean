module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.AffineTape
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine002
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

namespace P016
def win : List Aff := [⟨1, 0, -1450000001⟩, ⟨-30000001, 8000000, 3999999⟩, ⟨2633333333, -700000000, -350000000⟩]
#time def cert : Cert := [
  (⟨-97, 26, 13⟩, [.hyp 0, .scale 2000013 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 4000000 4]),
  (⟨-87, 24, 12⟩, [.hyp 0, .scale 3000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 1000000 4]),
  (⟨-66, 18, 9⟩, [.hyp 0, .scale 6000009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 4000000 4]),
  (⟨-60, 16, 9⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 8000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 10000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 26000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 8000000 4]),
  (⟨-6, 2, 0⟩, [.hyp 0, .scale 6000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 6000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 14000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 14000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 14000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 30000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 166666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 700000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 166666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 350000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 866666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 350000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 1216666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 350000000 4]),
  (⟨66, -16, -9⟩, [.hyp 0, .scale 254166667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 43750000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 10666666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 175000000 4]),
  (⟨86, -22, -11⟩, [.hyp 0, .scale 1133333337 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 350000000 4]),
  (⟨87, -22, -12⟩, [.hyp 0, .scale 1483333337 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 350000000 4]),
  (⟨93, -24, -12⟩, [.hyp 0, .scale 237500001 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 87500000 4]),
  (⟨97, -24, -13⟩, [.hyp 0, .scale 587500001 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 87500000 4]),
]
-- kcost: 0.0888 s conservative; 148 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P016

namespace P017
def win : List Aff := [⟨1, 0, -450000001⟩, ⟨-429000001, 130000000, 64999999⟩, ⟨33076923, -10000000, -5000000⟩]
#time def cert : Cert := [
  (⟨-97, 30, 15⟩, [.hyp 0, .scale 26000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 13000000 4]),
  (⟨-87, 28, 14⟩, [.hyp 0, .scale 175500007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 32500000 4]),
  (⟨-70, 22, 12⟩, [.hyp 0, .scale 169000011 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 65000000 4]),
  (⟨-66, 20, 10⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6500000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 71500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 32500000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 247000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 130000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 39000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 65000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 169000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 65000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 169000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 65000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 169000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 65000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 429000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 130000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 6923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 6923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 16923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 21923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨60, -18, -10⟩, [.hyp 0, .scale 2307693 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 5000000 4]),
  (⟨66, -18, -10⟩, [.hyp 0, .scale 32307693 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 5000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 156923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2500000 4]),
  (⟨86, -26, -13⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 5000000 4]),
  (⟨87, -26, -14⟩, [.hyp 0, .scale 5000001 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 5000000 4]),
  (⟨93, -28, -14⟩, [.hyp 0, .scale 961539 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 2500000 4]),
  (⟨97, -28, -15⟩, [.hyp 0, .scale 10961539 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 2500000 4]),
]
-- kcost: 0.0852 s conservative; 142 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P017

namespace P018
def win : List Aff := [⟨1, 0, -550000001⟩, ⟨-26769231, 8000000, 3999999⟩, ⟨7399999999, -2200000000, -1100000000⟩]
#time def cert : Cert := [
  (⟨-97, 30, 15⟩, [.hyp 0, .scale 2707693 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 800000 4]),
  (⟨-87, 26, 13⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 4000000 4]),
  (⟨-86, 26, 13⟩, [.hyp 0, .scale 4000003 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 4000000 4]),
  (⟨-66, 20, 10⟩, [.hyp 0, .scale 369231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 400000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 4769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 4769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 6769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 16307693 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 8000000 4]),
  (⟨-6, 2, 0⟩, [.hyp 0, .scale 2769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 2769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 10769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 10769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 10769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 26769231 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 1400000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2200000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 1400000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 4700000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨27, -8, -3⟩, [.hyp 0, .scale 25000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 275000000 4]),
  (⟨66, -18, -10⟩, [.hyp 0, .scale 6000000009 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 1100000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 34400000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 550000000 4]),
  (⟨87, -24, -13⟩, [.hyp 0, .scale 1725000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 275000000 4]),
  (⟨97, -28, -15⟩, [.hyp 0, .scale 1550000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 550000000 4]),
  (⟨97, -28, -14⟩, [.hyp 0, .scale 1550000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 550000000 4]),
]
-- kcost: 0.0888 s conservative; 148 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P018

namespace P019
def win : List Aff := [⟨1, 0, -17700000001⟩, ⟨-279500001, 110500000, 55249999⟩, ⟨21576923, -8500000, -4250000⟩]
#time def cert : Cert := [
  (⟨-97, 40, 20⟩, [.hyp 0, .scale 11537501 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2762500 4]),
  (⟨-93, 38, 18⟩, [.hyp 0, .scale 172250019 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 55250000 4]),
  (⟨-87, 36, 18⟩, [.hyp 0, .scale 112125009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 27625000 4]),
  (⟨-86, 34, 17⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3250000 4]),
  (⟨-70, 28, 15⟩, [.hyp 0, .scale 22750007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 27625000 4]),
  (⟨-66, 28, 14⟩, [.hyp 0, .scale 133250007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 27625000 4]),
  (⟨-60, 24, 13⟩, [.hyp 0, .scale 9750003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 13812500 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 230750003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 55250000 4]),
  (⟨-11, 6, 3⟩, [.hyp 0, .scale 230750003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 55250000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 3250001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 27625000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 113750001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 27625000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 58500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 55250000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 58500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 55250000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 58500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 55250000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 279500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 110500000 4]),
  (⟨0, 1, 1⟩, [.hyp 0, .scale 279500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 110500000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 12423077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 8500000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 3923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4250000 4]),
  (⟨8, -3, -2⟩, [.hyp 0, .scale 3269231 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 8500000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 1798077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2125000 4]),
  (⟨66, -26, -14⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 4250000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 139923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2125000 4]),
  (⟨86, -32, -16⟩, [.hyp 0, .scale 1266827 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 265625 4]),
  (⟨87, -34, -18⟩, [.hyp 0, .scale 173077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 250000 4]),
  (⟨97, -38, -20⟩, [.hyp 0, .scale 2288463 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 4250000 4]),
  (⟨97, -38, -19⟩, [.hyp 0, .scale 2288463 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 4250000 4]),
]
-- kcost: 0.0984 s conservative; 164 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P019

namespace P020
def win : List Aff := [⟨1, 0, -600000001⟩, ⟨-412250001, 161500000, 80749999⟩, ⟨413249999, -161500000, -80750000⟩]
#time def cert : Cert := [
  (⟨-97, 38, 19⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4250000 4]),
  (⟨-87, 36, 18⟩, [.hyp 0, .scale 197625009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 40375000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 29750013 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 80750000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 348500003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 80750000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 8500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40375000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 170000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40375000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 89250001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80750000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 89250001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80750000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 89250001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80750000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 412250001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 161500000 4]),
  (⟨0, 1, 1⟩, [.hyp 0, .scale 412250001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 161500000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 232750001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 161500000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 71250001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80750000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 71250001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80750000 4]),
  (⟨8, -3, -2⟩, [.hyp 0, .scale 52250003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 161500000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 394250001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80750000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 30875001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 40375000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 92625003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 20187500 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 2655250001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 40375000 4]),
  (⟨86, -32, -16⟩, [.hyp 0, .scale 20781251 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5046875 4]),
  (⟨87, -34, -18⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4750000 4]),
  (⟨87, -34, -17⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4750000 4]),
  (⟨97, -36, -19⟩, [.hyp 0, .scale 197125009 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 40375000 4]),
  (⟨97, -36, -18⟩, [.hyp 0, .scale 197125009 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 40375000 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P020

namespace P021
def win : List Aff := [⟨1, 0, -47950000001⟩, ⟨-2220000011, 1702000000, 850999999⟩, ⟨7599999999, -5800000000, -2900000000⟩]
#time def cert : Cert := [
  (⟨-97, 76, 38⟩, [.hyp 0, .scale 906500209 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 425500000 4]),
  (⟨-93, 72, 35⟩, [.hyp 0, .scale 194250099 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 212750000 4]),
  (⟨-87, 68, 34⟩, [.hyp 0, .scale 721500187 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 425500000 4]),
  (⟨-86, 66, 33⟩, [.hyp 0, .scale 74000363 0, .hyp 1, .scale 33 2, .add 1 3, .tighten 851000000 4]),
  (⟨-70, 54, 28⟩, [.hyp 0, .scale 370000297 0, .hyp 1, .scale 27 2, .add 1 3, .tighten 851000000 4]),
  (⟨-66, 52, 26⟩, [.hyp 0, .scale 777000143 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 425500000 4]),
  (⟨-60, 46, 24⟩, [.hyp 0, .scale 11 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 37000000 4]),
  (⟨-11, 10, 4⟩, [.hyp 0, .scale 347800011 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 170200000 4]),
  (⟨-11, 10, 5⟩, [.hyp 0, .scale 347800011 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 170200000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 92500011 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 212750000 4]),
  (⟨-8, 7, 4⟩, [.hyp 0, .scale 1924000077 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 1702000000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 1554000033 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 851000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 518000011 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 425500000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 518000011 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 425500000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 518000011 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 425500000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 2220000011 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1702000000 4]),
  (⟨4, -3, -2⟩, [.hyp 0, .scale 400000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 5800000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 4000000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2900000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 4000000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2900000000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 1100000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1450000000 4]),
  (⟨8, -6, -3⟩, [.hyp 0, .scale 400000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2900000000 4]),
  (⟨11, -8, -4⟩, [.hyp 0, .scale 375000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 725000000 4]),
  (⟨66, -50, -26⟩, [.hyp 0, .scale 56000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 116000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 197600000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2900000000 4]),
  (⟨86, -64, -32⟩, [.hyp 0, .scale 193750001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 90625000 4]),
  (⟨87, -66, -34⟩, [.hyp 0, .scale 1500000033 0, .hyp 2, .scale 33 2, .add 1 3, .tighten 2900000000 4]),
  (⟨97, -74, -38⟩, [.hyp 0, .scale 100000037 0, .hyp 2, .scale 37 2, .add 1 3, .tighten 2900000000 4]),
  (⟨97, -74, -37⟩, [.hyp 0, .scale 100000037 0, .hyp 2, .scale 37 2, .add 1 3, .tighten 2900000000 4]),
]
-- kcost: 0.1032 s conservative; 172 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P021

namespace P022
def win : List Aff := [⟨1, 0, -1600000001⟩, ⟨-104400001, 40800000, 20399999⟩, ⟨7199999999, -2800000000, -1400000000⟩]
#time def cert : Cert := [
  (⟨-97, 38, 19⟩, [.hyp 0, .scale 4800019 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 20400000 4]),
  (⟨-87, 34, 17⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1200000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 10800013 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 20400000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 29600001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6800000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 2400001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10200000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 43200001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10200000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 22800001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20400000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 22800001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20400000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 22800001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20400000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 104400001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40800000 4]),
  (⟨0, 1, 1⟩, [.hyp 0, .scale 104400001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40800000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 4000000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2800000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 1200000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1400000000 4]),
  (⟨8, -3, -2⟩, [.hyp 0, .scale 800000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2800000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 500000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 700000000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 1500000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 350000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 46000000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 700000000 4]),
  (⟨86, -32, -16⟩, [.hyp 0, .scale 325000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 87500000 4]),
  (⟨87, -32, -17⟩, [.hyp 0, .scale 412500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 87500000 4]),
  (⟨93, -36, -18⟩, [.hyp 0, .scale 300000009 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 700000000 4]),
  (⟨97, -36, -19⟩, [.hyp 0, .scale 3100000009 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 700000000 4]),
  (⟨97, -36, -18⟩, [.hyp 0, .scale 3100000009 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 700000000 4]),
]
-- kcost: 0.0840 s conservative; 140 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P022

namespace P023
def win : List Aff := [⟨1, 0, -26500000001⟩, ⟨-85000001, 34000000, 16999999⟩, ⟨85999999, -34000000, -17000000⟩]
#time def cert : Cert := [
  (⟨-97, 40, 20⟩, [.hyp 0, .scale 2550001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 850000 4]),
  (⟨-93, 38, 18⟩, [.hyp 0, .scale 34000019 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 17000000 4]),
  (⟨-87, 36, 18⟩, [.hyp 0, .scale 25500009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 8500000 4]),
  (⟨-70, 28, 15⟩, [.hyp 0, .scale 7 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 8500000 4]),
  (⟨-66, 28, 14⟩, [.hyp 0, .scale 34000007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 8500000 4]),
  (⟨-60, 24, 13⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 4250000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 68000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 17000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8500000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 34000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8500000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 17000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 17000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 17000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 85000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨0, 1, 1⟩, [.hyp 0, .scale 85000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 50000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 16000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨8, -3, -2⟩, [.hyp 0, .scale 14000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 34000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 7500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 8500000 4]),
  (⟨66, -26, -14⟩, [.hyp 0, .scale 4000013 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 17000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 560000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 8500000 4]),
  (⟨86, -34, -17⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨87, -34, -18⟩, [.hyp 0, .scale 1000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨97, -38, -20⟩, [.hyp 0, .scale 15000019 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 17000000 4]),
  (⟨97, -38, -19⟩, [.hyp 0, .scale 15000019 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 17000000 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P023

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine002
