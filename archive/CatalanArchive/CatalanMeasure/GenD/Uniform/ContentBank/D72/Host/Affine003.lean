module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.AffineTape
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine003
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

namespace P024
def win : List Aff := [⟨1, 0, -17700000001⟩, ⟨-11100000001, 4400000000, 2199999999⟩, ⟨85999999, -34000000, -17000000⟩]
#time def cert : Cert := [
  (⟨-97, 40, 20⟩, [.hyp 0, .scale 430000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 110000000 4]),
  (⟨-93, 38, 18⟩, [.hyp 0, .scale 6300000019 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 2200000000 4]),
  (⟨-87, 36, 18⟩, [.hyp 0, .scale 4200000009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-70, 28, 15⟩, [.hyp 0, .scale 700000007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-66, 28, 14⟩, [.hyp 0, .scale 5100000007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-60, 24, 13⟩, [.hyp 0, .scale 300000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 550000000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 9100000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 2200000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 100000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 4500000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 2300000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2200000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 2300000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2200000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 2300000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2200000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 11100000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4400000000 4]),
  (⟨0, 1, 1⟩, [.hyp 0, .scale 11100000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4400000000 4]),
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
end P024

namespace P025
def win : List Aff := [⟨1, 0, -2800000001⟩, ⟨-10100000001, 3800000000, 1899999999⟩, ⟨31999999, -12000000, -6000000⟩]
#time def cert : Cert := [
  (⟨-97, 38, 19⟩, [.hyp 0, .scale 400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-93, 36, 17⟩, [.hyp 0, .scale 2550000009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 950000000 4]),
  (⟨-87, 34, 17⟩, [.hyp 0, .scale 6400000017 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 1900000000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 5900000013 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 1900000000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 9400000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 1900000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 600000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 950000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 4400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 950000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 2500000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1900000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 2500000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1900000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 2500000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1900000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 10100000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3800000000 4]),
  (⟨0, 1, 1⟩, [.hyp 0, .scale 10100000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3800000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 16000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 12000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 4000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 4000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨8, -3, -2⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 1000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨27, -10, -4⟩, [.hyp 0, .scale 400001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1200000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 1000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 196000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨86, -32, -16⟩, [.hyp 0, .scale 250001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 375000 4]),
  (⟨87, -32, -17⟩, [.hyp 0, .scale 625001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 375000 4]),
  (⟨97, -36, -19⟩, [.hyp 0, .scale 1000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 1000000 4]),
  (⟨97, -36, -18⟩, [.hyp 0, .scale 1000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 1000000 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P025

namespace P026
def win : List Aff := [⟨1, 0, -600000001⟩, ⟨-1142857143, 400000000, 199999999⟩, ⟨487333331, -170000000, -85000000⟩]
#time def cert : Cert := [
  (⟨-97, 34, 17⟩, [.hyp 0, .scale 28571431 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 200000000 4]),
  (⟨-87, 32, 16⟩, [.hyp 0, .scale 55357143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 12500000 4]),
  (⟨-66, 24, 12⟩, [.hyp 0, .scale 128571429 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 50000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 42857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 142857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 228571429 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 400000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 542857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 342857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 200000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 342857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 200000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 342857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 200000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 1142857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 400000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 192666669 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 170000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 22666669 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 85000000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 22666669 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 85000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 192666669 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 85000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 362666669 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 85000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 447666669 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 85000000 4]),
  (⟨66, -22, -12⟩, [.hyp 0, .scale 249333359 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 85000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 2742666669 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 42500000 4]),
  (⟨86, -30, -15⟩, [.hyp 0, .scale 7 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 17000000 4]),
  (⟨87, -30, -16⟩, [.hyp 0, .scale 17000007 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 17000000 4]),
  (⟨87, -30, -15⟩, [.hyp 0, .scale 17000007 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 17000000 4]),
  (⟨97, -32, -17⟩, [.hyp 0, .scale 27979169 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5312500 4]),
  (⟨97, -32, -16⟩, [.hyp 0, .scale 27979169 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5312500 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P026

namespace P027
def win : List Aff := [⟨1, 0, -47950000001⟩, ⟨-21388889, 16500000, 8249999⟩, ⟨17590909, -13500000, -6750000⟩]
#time def cert : Cert := [
  (⟨-97, 76, 38⟩, [.hyp 0, .scale 6263891 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 4125000 4]),
  (⟨-93, 72, 35⟩, [.hyp 0, .scale 229167 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 687500 4]),
  (⟨-87, 68, 34⟩, [.hyp 0, .scale 4736113 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 4125000 4]),
  (⟨-70, 54, 28⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 2750000 4]),
  (⟨-66, 52, 26⟩, [.hyp 0, .scale 5805557 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 4125000 4]),
  (⟨-11, 10, 4⟩, [.hyp 0, .scale 3238889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1650000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 763889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2062500 4]),
  (⟨-8, 7, 4⟩, [.hyp 0, .scale 17722223 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 16500000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 4888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2750000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 4888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4125000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 4888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4125000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 4888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4125000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 21388889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16500000 4]),
  (⟨4, -3, -2⟩, [.hyp 0, .scale 409091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4500000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 9409091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 6750000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 9409091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 6750000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 2659091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3375000 4]),
  (⟨6, -4, -2⟩, [.hyp 0, .scale 2659091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3375000 4]),
  (⟨8, -6, -3⟩, [.hyp 0, .scale 409091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2250000 4]),
  (⟨11, -8, -4⟩, [.hyp 0, .scale 971591 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1687500 4]),
  (⟨60, -46, -24⟩, [.hyp 0, .scale 409093 0, .hyp 2, .scale 23 2, .add 1 3, .tighten 6750000 4]),
  (⟨66, -50, -26⟩, [.hyp 0, .scale 229091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 270000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 153409091 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2250000 4]),
  (⟨86, -66, -33⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 2250000 4]),
  (⟨87, -66, -34⟩, [.hyp 0, .scale 2250001 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 2250000 4]),
  (⟨97, -74, -38⟩, [.hyp 0, .scale 3886367 0, .hyp 2, .scale 37 2, .add 1 3, .tighten 6750000 4]),
  (⟨97, -74, -37⟩, [.hyp 0, .scale 3886367 0, .hyp 2, .scale 37 2, .add 1 3, .tighten 6750000 4]),
]
-- kcost: 0.0996 s conservative; 166 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P027

namespace P028
def win : List Aff := [⟨1, 0, -650000001⟩, ⟨-39857143, 24000000, 11999999⟩, ⟨93333333, -56000000, -28000000⟩]
#time def cert : Cert := [
  (⟨-97, 60, 30⟩, [.hyp 0, .scale 1057143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 400000 4]),
  (⟨-93, 56, 27⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 3000000 4]),
  (⟨-87, 54, 27⟩, [.hyp 0, .scale 10714287 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 4000000 4]),
  (⟨-86, 52, 26⟩, [.hyp 0, .scale 2142859 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 6000000 4]),
  (⟨-70, 44, 23⟩, [.hyp 0, .scale 18428573 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 6000000 4]),
  (⟨-66, 40, 20⟩, [.hyp 0, .scale 257143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 600000 4]),
  (⟨-11, 8, 3⟩, [.hyp 0, .scale 6857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨-11, 8, 4⟩, [.hyp 0, .scale 6857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨-8, 5, 3⟩, [.hyp 0, .scale 1457143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4800000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 3857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨-4, 3, 1⟩, [.hyp 0, .scale 7857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 15857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 15857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 15857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 39857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 24000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 18666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 28000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 18666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 28000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 130666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 56000000 4]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 74666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 28000000 4]),
  (⟨10, -6, -3⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 28000000 4]),
  (⟨11, -6, -3⟩, [.hyp 0, .scale 28000001 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 28000000 4]),
  (⟨27, -16, -7⟩, [.hyp 0, .scale 1166667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3500000 4]),
  (⟨60, -36, -19⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 14000000 4]),
  (⟨66, -38, -20⟩, [.hyp 0, .scale 74666673 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 28000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 1848000001 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 28000000 4]),
  (⟨87, -52, -27⟩, [.hyp 0, .scale 4666671 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 14000000 4]),
  (⟨97, -58, -30⟩, [.hyp 0, .scale 9333343 0, .hyp 2, .scale 29 2, .add 1 3, .tighten 28000000 4]),
  (⟨97, -58, -29⟩, [.hyp 0, .scale 9333343 0, .hyp 2, .scale 29 2, .add 1 3, .tighten 28000000 4]),
]
-- kcost: 0.1032 s conservative; 172 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P028

namespace P029
def win : List Aff := [⟨1, 0, -14950000001⟩, ⟨-96000001, 32000000, 15999999⟩, ⟨96999999, -32000000, -16000000⟩]
#time def cert : Cert := [
  (⟨-97, 34, 17⟩, [.hyp 0, .scale 80000017 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 16000000 4]),
  (⟨-87, 30, 15⟩, [.hyp 0, .scale 9600003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 3200000 4]),
  (⟨-86, 30, 15⟩, [.hyp 0, .scale 12800003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 3200000 4]),
  (⟨-70, 24, 13⟩, [.hyp 0, .scale 8000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 4000000 4]),
  (⟨-66, 22, 11⟩, [.hyp 0, .scale 11 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 16000000 4]),
  (⟨-60, 20, 11⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1600000 4]),
  (⟨-27, 10, 4⟩, [.hyp 0, .scale 9600001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3200000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 8000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 8000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 16000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 32000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 32000000 4]),
  (⟨-6, 2, 0⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 32000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 32000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 32000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 96000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 32000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 31000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 32000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 31000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 79000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨66, -20, -11⟩, [.hyp 0, .scale 8600001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1600000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 511000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨87, -28, -15⟩, [.hyp 0, .scale 17000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 8000000 4]),
  (⟨97, -32, -17⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨97, -32, -16⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
]
-- kcost: 0.0960 s conservative; 160 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P029

namespace P030
def win : List Aff := [⟨1, 0, -49600000001⟩, ⟨-4272973, 3400000, 1699999⟩, ⟨159099999, -125800000, -62900000⟩]
#time def cert : Cert := [
  (⟨-97, 78, 39⟩, [.hyp 0, .scale 1745947 0, .hyp 1, .scale 39 2, .add 1 3, .tighten 1700000 4]),
  (⟨-93, 74, 36⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 37 2, .add 1 3, .tighten 1700000 4]),
  (⟨-87, 70, 35⟩, [.hyp 0, .scale 330811 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 340000 4]),
  (⟨-70, 56, 29⟩, [.hyp 0, .scale 160811 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 425000 4]),
  (⟨-66, 54, 27⟩, [.hyp 0, .scale 3170271 0, .hyp 1, .scale 27 2, .add 1 3, .tighten 1700000 4]),
  (⟨-60, 48, 25⟩, [.hyp 0, .scale 68919 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 212500 4]),
  (⟨-11, 10, 4⟩, [.hyp 0, .scale 532973 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 340000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 22973 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 425000 4]),
  (⟨-8, 7, 4⟩, [.hyp 0, .scale 2710811 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 3400000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 2618919 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 1700000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 872973 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 850000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 872973 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 850000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 872973 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 850000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 4272973 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3400000 4]),
  (⟨4, -3, -2⟩, [.hyp 0, .scale 25900003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 125800000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 92500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 62900000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 92500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 62900000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 29600001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 31450000 4]),
  (⟨8, -6, -3⟩, [.hyp 0, .scale 25900003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 62900000 4]),
  (⟨11, -8, -4⟩, [.hyp 0, .scale 13875001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15725000 4]),
  (⟨66, -52, -27⟩, [.hyp 0, .scale 7400013 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 31450000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 4303100003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 62900000 4]),
  (⟨86, -68, -34⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1850000 4]),
  (⟨87, -68, -35⟩, [.hyp 0, .scale 1850001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1850000 4]),
  (⟨97, -76, -39⟩, [.hyp 0, .scale 27750019 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 31450000 4]),
  (⟨97, -76, -38⟩, [.hyp 0, .scale 27750019 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 31450000 4]),
]
-- kcost: 0.0960 s conservative; 160 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P030

namespace P031
def win : List Aff := [⟨1, 0, -600000001⟩, ⟨-464000001, 160000000, 79999999⟩, ⟨464999999, -160000000, -80000000⟩]
#time def cert : Cert := [
  (⟨-97, 34, 17⟩, [.hyp 0, .scale 128000017 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 80000000 4]),
  (⟨-87, 30, 15⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 16000000 4]),
  (⟨-86, 30, 15⟩, [.hyp 0, .scale 16000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 16000000 4]),
  (⟨-66, 24, 12⟩, [.hyp 0, .scale 72000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 20000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 24000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 24000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 64000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 112000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 160000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 224000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 144000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 144000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 144000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 464000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 160000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 175000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 160000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 15000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 175000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 415000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨66, -22, -12⟩, [.hyp 0, .scale 165000011 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 80000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 2575000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨86, -28, -14⟩, [.hyp 0, .scale 185000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 40000000 4]),
  (⟨87, -28, -15⟩, [.hyp 0, .scale 225000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 40000000 4]),
  (⟨93, -32, -16⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨97, -32, -17⟩, [.hyp 0, .scale 20000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨97, -32, -16⟩, [.hyp 0, .scale 20000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P031

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine003
