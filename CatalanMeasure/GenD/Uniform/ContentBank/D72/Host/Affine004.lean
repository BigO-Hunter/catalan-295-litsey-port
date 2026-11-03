module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.AffineTape
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine004
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

namespace P032
def win : List Aff := [⟨1, 0, -38100000001⟩, ⟨-96000001, 64000000, 31999999⟩, ⟨96999999, -64000000, -32000000⟩]
#time def cert : Cert := [
  (⟨-97, 66, 33⟩, [.hyp 0, .scale 64000033 0, .hyp 1, .scale 33 2, .add 1 3, .tighten 32000000 4]),
  (⟨-87, 58, 29⟩, [.hyp 0, .scale 29 0, .hyp 1, .scale 29 2, .add 1 3, .tighten 32000000 4]),
  (⟨-86, 58, 29⟩, [.hyp 0, .scale 32000029 0, .hyp 1, .scale 29 2, .add 1 3, .tighten 32000000 4]),
  (⟨-70, 48, 25⟩, [.hyp 0, .scale 8000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 4000000 4]),
  (⟨-66, 44, 22⟩, [.hyp 0, .scale 11 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 16000000 4]),
  (⟨-60, 40, 21⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1600000 4]),
  (⟨-27, 18, 8⟩, [.hyp 0, .scale 9 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 32000000 4]),
  (⟨-11, 8, 3⟩, [.hyp 0, .scale 8000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-11, 8, 4⟩, [.hyp 0, .scale 8000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 16000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-8, 6, 3⟩, [.hyp 0, .scale 32000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 32000000 4]),
  (⟨-6, 4, 1⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-4, 3, 1⟩, [.hyp 0, .scale 32000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 64000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 32000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 32000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 32000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 96000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 64000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 31000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 32000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 31000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 32000000 4]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 95000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 32000000 4]),
  (⟨8, -5, -3⟩, [.hyp 0, .scale 5400001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 12800000 4]),
  (⟨11, -6, -3⟩, [.hyp 0, .scale 61000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 32000000 4]),
  (⟨66, -42, -22⟩, [.hyp 0, .scale 75000021 0, .hyp 2, .scale 21 2, .add 1 3, .tighten 32000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 2141000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 32000000 4]),
  (⟨87, -56, -29⟩, [.hyp 0, .scale 17000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 8000000 4]),
  (⟨97, -64, -33⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨97, -64, -32⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
]
-- kcost: 0.1032 s conservative; 172 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P032

namespace P033
def win : List Aff := [⟨1, 0, -47950000001⟩, ⟨-29969697, 23000000, 11499999⟩, ⟨989999999, -759000000, -379500000⟩]
#time def cert : Cert := [
  (⟨-97, 76, 38⟩, [.hyp 0, .scale 11674243 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 5750000 4]),
  (⟨-93, 72, 35⟩, [.hyp 0, .scale 2352273 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 2875000 4]),
  (⟨-87, 68, 34⟩, [.hyp 0, .scale 9234849 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 5750000 4]),
  (⟨-86, 66, 33⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 33 2, .add 1 3, .tighten 11500000 4]),
  (⟨-70, 54, 28⟩, [.hyp 0, .scale 4181819 0, .hyp 1, .scale 27 2, .add 1 3, .tighten 11500000 4]),
  (⟨-66, 52, 26⟩, [.hyp 0, .scale 10106061 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 5750000 4]),
  (⟨-11, 10, 4⟩, [.hyp 0, .scale 4669697 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2300000 4]),
  (⟨-11, 10, 5⟩, [.hyp 0, .scale 4669697 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2300000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 1219697 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2875000 4]),
  (⟨-8, 7, 4⟩, [.hyp 0, .scale 25787879 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 23000000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 20909091 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 11500000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 6969697 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5750000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 6969697 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5750000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 6969697 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5750000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 29969697 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 23000000 4]),
  (⟨4, -3, -2⟩, [.hyp 0, .scale 22000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 253000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 528000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 379500000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 528000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 379500000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 148500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 189750000 4]),
  (⟨6, -4, -2⟩, [.hyp 0, .scale 148500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 189750000 4]),
  (⟨8, -6, -3⟩, [.hyp 0, .scale 22000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 126500000 4]),
  (⟨11, -8, -4⟩, [.hyp 0, .scale 53625001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 94875000 4]),
  (⟨60, -46, -24⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 16500000 4]),
  (⟨66, -50, -26⟩, [.hyp 0, .scale 11880001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15180000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 8624000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 126500000 4]),
  (⟨86, -64, -32⟩, [.hyp 0, .scale 29906251 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 11859375 4]),
  (⟨87, -66, -34⟩, [.hyp 0, .scale 10500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 11500000 4]),
  (⟨97, -74, -38⟩, [.hyp 0, .scale 181500037 0, .hyp 2, .scale 37 2, .add 1 3, .tighten 379500000 4]),
  (⟨97, -74, -37⟩, [.hyp 0, .scale 181500037 0, .hyp 2, .scale 37 2, .add 1 3, .tighten 379500000 4]),
]
-- kcost: 0.1068 s conservative; 178 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P033

namespace P034
def win : List Aff := [⟨1, 0, -450000001⟩, ⟨-18523077, 11200000, 5599999⟩, ⟨34542857, -20800000, -10400000⟩]
#time def cert : Cert := [
  (⟨-97, 60, 30⟩, [.hyp 0, .scale 1249231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 560000 4]),
  (⟨-87, 54, 27⟩, [.hyp 0, .scale 12923079 0, .hyp 1, .scale 27 2, .add 1 3, .tighten 5600000 4]),
  (⟨-86, 52, 26⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 2800000 4]),
  (⟨-70, 44, 23⟩, [.hyp 0, .scale 7753847 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 2800000 4]),
  (⟨-66, 40, 20⟩, [.hyp 0, .scale 43077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 280000 4]),
  (⟨-11, 8, 3⟩, [.hyp 0, .scale 3123077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1400000 4]),
  (⟨-11, 8, 4⟩, [.hyp 0, .scale 3123077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1400000 4]),
  (⟨-8, 5, 3⟩, [.hyp 0, .scale 603077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2240000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 1723077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨-4, 3, 1⟩, [.hyp 0, .scale 10769231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 11200000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 7323077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 7323077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 7323077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 18523077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 11200000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 7057143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10400000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 7057143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10400000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 48657143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 20800000 4]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 27857143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10400000 4]),
  (⟨10, -6, -3⟩, [.hyp 0, .scale 371429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 10400000 4]),
  (⟨11, -6, -3⟩, [.hyp 0, .scale 10771429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 10400000 4]),
  (⟨60, -36, -19⟩, [.hyp 0, .scale 1114287 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 5200000 4]),
  (⟨66, -38, -20⟩, [.hyp 0, .scale 30085717 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 10400000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 686771429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 10400000 4]),
  (⟨87, -52, -27⟩, [.hyp 0, .scale 257143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 400000 4]),
  (⟨93, -56, -28⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 2600000 4]),
  (⟨97, -58, -30⟩, [.hyp 0, .scale 7057147 0, .hyp 2, .scale 29 2, .add 1 3, .tighten 10400000 4]),
  (⟨97, -58, -29⟩, [.hyp 0, .scale 7057147 0, .hyp 2, .scale 29 2, .add 1 3, .tighten 10400000 4]),
]
-- kcost: 0.0996 s conservative; 166 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P034

namespace P035
def win : List Aff := [⟨1, 0, -2500000001⟩, ⟨-679000001, 476000000, 237999999⟩, ⟨97142857, -68000000, -34000000⟩]
#time def cert : Cert := [
  (⟨-97, 68, 34⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 7000000 4]),
  (⟨-87, 62, 31⟩, [.hyp 0, .scale 343000031 0, .hyp 1, .scale 31 2, .add 1 3, .tighten 238000000 4]),
  (⟨-70, 50, 26⟩, [.hyp 0, .scale 12600001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 9520000 4]),
  (⟨-66, 48, 24⟩, [.hyp 0, .scale 73500003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 29750000 4]),
  (⟨-11, 8, 3⟩, [.hyp 0, .scale 24500001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 59500000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 84000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 59500000 4]),
  (⟨-8, 6, 3⟩, [.hyp 0, .scale 133000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 238000000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 609000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 238000000 4]),
  (⟨-4, 3, 1⟩, [.hyp 0, .scale 133000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 476000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 203000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 119000000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 203000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 119000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 679000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 476000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 38857143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 38857143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 4857143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨6, -4, -2⟩, [.hyp 0, .scale 4857143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨8, -5, -3⟩, [.hyp 0, .scale 11657143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 13600000 4]),
  (⟨10, -6, -3⟩, [.hyp 0, .scale 48571429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 34000000 4]),
  (⟨11, -6, -3⟩, [.hyp 0, .scale 82571429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 34000000 4]),
  (⟨27, -18, -8⟩, [.hyp 0, .scale 43714287 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 34000000 4]),
  (⟨60, -42, -22⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 21 2, .add 1 3, .tighten 34000000 4]),
  (⟨66, -46, -24⟩, [.hyp 0, .scale 9714289 0, .hyp 2, .scale 23 2, .add 1 3, .tighten 34000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 2292571429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 34000000 4]),
  (⟨86, -60, -30⟩, [.hyp 0, .scale 971429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 3400000 4]),
  (⟨87, -60, -31⟩, [.hyp 0, .scale 4371429 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 3400000 4]),
  (⟨97, -66, -34⟩, [.hyp 0, .scale 92285719 0, .hyp 2, .scale 33 2, .add 1 3, .tighten 34000000 4]),
  (⟨97, -66, -33⟩, [.hyp 0, .scale 92285719 0, .hyp 2, .scale 33 2, .add 1 3, .tighten 34000000 4]),
]
-- kcost: 0.0996 s conservative; 166 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P035

namespace P036
def win : List Aff := [⟨1, 0, -3600000001⟩, ⟨-7400000001, 5200000000, 2599999999⟩, ⟨1066999987, -748000000, -374000000⟩]
#time def cert : Cert := [
  (⟨-97, 70, 35⟩, [.hyp 0, .scale 1360000007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 520000000 4]),
  (⟨-93, 66, 32⟩, [.hyp 0, .scale 2400000033 0, .hyp 1, .scale 33 2, .add 1 3, .tighten 2600000000 4]),
  (⟨-87, 62, 31⟩, [.hyp 0, .scale 3200000031 0, .hyp 1, .scale 31 2, .add 1 3, .tighten 2600000000 4]),
  (⟨-86, 62, 31⟩, [.hyp 0, .scale 5800000031 0, .hyp 1, .scale 31 2, .add 1 3, .tighten 2600000000 4]),
  (⟨-70, 50, 26⟩, [.hyp 0, .scale 120000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 104000000 4]),
  (⟨-66, 48, 24⟩, [.hyp 0, .scale 750000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 325000000 4]),
  (⟨-11, 8, 3⟩, [.hyp 0, .scale 250000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 650000000 4]),
  (⟨-11, 8, 4⟩, [.hyp 0, .scale 250000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 650000000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 900000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 650000000 4]),
  (⟨-8, 6, 3⟩, [.hyp 0, .scale 1400000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 2600000000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 6600000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 2600000000 4]),
  (⟨-4, 3, 1⟩, [.hyp 0, .scale 1400000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 5200000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 2200000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1300000000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 2200000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1300000000 4]),
  (⟨-4, 4, 3⟩, [.hyp 0, .scale 2200000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1300000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 7400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5200000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 429000013 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 374000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 429000013 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 374000000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 55000013 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 187000000 4]),
  (⟨6, -4, -2⟩, [.hyp 0, .scale 55000013 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 187000000 4]),
  (⟨8, -5, -3⟩, [.hyp 0, .scale 129800013 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 149600000 4]),
  (⟨11, -6, -3⟩, [.hyp 0, .scale 913000039 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 374000000 4]),
  (⟨60, -42, -22⟩, [.hyp 0, .scale 33000273 0, .hyp 2, .scale 21 2, .add 1 3, .tighten 374000000 4]),
  (⟨66, -46, -24⟩, [.hyp 0, .scale 143000299 0, .hyp 2, .scale 23 2, .add 1 3, .tighten 374000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 25223000039 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 374000000 4]),
  (⟨86, -60, -30⟩, [.hyp 0, .scale 15400039 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 37400000 4]),
  (⟨87, -60, -31⟩, [.hyp 0, .scale 52800039 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 37400000 4]),
  (⟨97, -68, -35⟩, [.hyp 0, .scale 13 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 11000000 4]),
  (⟨97, -68, -34⟩, [.hyp 0, .scale 13 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 11000000 4]),
]
-- kcost: 0.1068 s conservative; 178 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P036

namespace P037
def win : List Aff := [⟨1, 0, -10450000001⟩, ⟨-776923077, 200000000, 99999999⟩, ⟨31111111, -8000000, -4000000⟩]
#time def cert : Cert := [
  (⟨-97, 26, 13⟩, [.hyp 0, .scale 400000001 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 100000000 4]),
  (⟨-93, 24, 11⟩, [.hyp 0, .scale 5769231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 25000000 4]),
  (⟨-87, 24, 12⟩, [.hyp 0, .scale 155769231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 25000000 4]),
  (⟨-66, 18, 9⟩, [.hyp 0, .scale 392307693 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 100000000 4]),
  (⟨-60, 16, 9⟩, [.hyp 0, .scale 26923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 12500000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 226923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 50000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 276923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 50000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 730769231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 200000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 176923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 376923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 376923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 376923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 776923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 200000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 888889 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 888889 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 8888889 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 12888889 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨66, -16, -9⟩, [.hyp 0, .scale 1888889 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 120888889 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨86, -22, -11⟩, [.hyp 0, .scale 1777779 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 4000000 4]),
  (⟨87, -22, -12⟩, [.hyp 0, .scale 5777779 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 4000000 4]),
  (⟨87, -22, -11⟩, [.hyp 0, .scale 5777779 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 4000000 4]),
  (⟨97, -24, -13⟩, [.hyp 0, .scale 3666667 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 1000000 4]),
]
-- kcost: 0.0888 s conservative; 148 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P037

namespace P038
def win : List Aff := [⟨1, 0, -40600000001⟩, ⟨-185000001, 148000000, 73999999⟩, ⟨5027027, -4000000, -2000000⟩]
#time def cert : Cert := [
  (⟨-97, 78, 39⟩, [.hyp 0, .scale 37000039 0, .hyp 1, .scale 39 2, .add 1 3, .tighten 74000000 4]),
  (⟨-87, 70, 35⟩, [.hyp 0, .scale 7400007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 14800000 4]),
  (⟨-70, 56, 29⟩, [.hyp 0, .scale 7 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 18500000 4]),
  (⟨-66, 54, 27⟩, [.hyp 0, .scale 111000027 0, .hyp 1, .scale 27 2, .add 1 3, .tighten 74000000 4]),
  (⟨-60, 48, 25⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 9250000 4]),
  (⟨-27, 22, 10⟩, [.hyp 0, .scale 37000011 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 74000000 4]),
  (⟨-11, 10, 4⟩, [.hyp 0, .scale 22200001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 14800000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 18500000 4]),
  (⟨-8, 7, 4⟩, [.hyp 0, .scale 111000007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 148000000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 111000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 74000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 37000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 37000000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 37000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 37000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 185000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 148000000 4]),
  (⟨4, -3, -2⟩, [.hyp 0, .scale 918919 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 4000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 2972973 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 2972973 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 972973 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨8, -6, -3⟩, [.hyp 0, .scale 918919 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2000000 4]),
  (⟨11, -8, -4⟩, [.hyp 0, .scale 472973 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨66, -52, -27⟩, [.hyp 0, .scale 648649 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 1000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 136918919 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2000000 4]),
  (⟨86, -68, -34⟩, [.hyp 0, .scale 540541 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 1000000 4]),
  (⟨87, -68, -35⟩, [.hyp 0, .scale 1540541 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 1000000 4]),
  (⟨93, -74, -37⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 37 2, .add 1 3, .tighten 2000000 4]),
  (⟨97, -76, -39⟩, [.hyp 0, .scale 1486487 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 1000000 4]),
  (⟨97, -76, -38⟩, [.hyp 0, .scale 1486487 0, .hyp 2, .scale 19 2, .add 1 3, .tighten 1000000 4]),
]
-- kcost: 0.0960 s conservative; 160 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P038

namespace P039
def win : List Aff := [⟨1, 0, -2500000001⟩, ⟨-42857143, 30000000, 14999999⟩, ⟨8299999999, -5800000000, -2900000000⟩]
#time def cert : Cert := [
  (⟨-97, 68, 34⟩, [.hyp 0, .scale 1071431 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 7500000 4]),
  (⟨-87, 62, 31⟩, [.hyp 0, .scale 23571433 0, .hyp 1, .scale 31 2, .add 1 3, .tighten 15000000 4]),
  (⟨-70, 50, 26⟩, [.hyp 0, .scale 857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 600000 4]),
  (⟨-66, 48, 24⟩, [.hyp 0, .scale 1607143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 625000 4]),
  (⟨-60, 42, 22⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 5000000 4]),
  (⟨-11, 8, 3⟩, [.hyp 0, .scale 1607143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3750000 4]),
  (⟨-10, 8, 4⟩, [.hyp 0, .scale 5357143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3750000 4]),
  (⟨-8, 6, 3⟩, [.hyp 0, .scale 2857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-6, 6, 3⟩, [.hyp 0, .scale 12857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-4, 3, 1⟩, [.hyp 0, .scale 2857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 4, 1⟩, [.hyp 0, .scale 12857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 7500000 4]),
  (⟨-4, 4, 2⟩, [.hyp 0, .scale 12857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 7500000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 42857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 30000000 4]),
  (⟨4, -2, -2⟩, [.hyp 0, .scale 3300000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2900000000 4]),
  (⟨4, -2, -1⟩, [.hyp 0, .scale 3300000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2900000000 4]),
  (⟨6, -4, -3⟩, [.hyp 0, .scale 400000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1450000000 4]),
  (⟨8, -5, -3⟩, [.hyp 0, .scale 980000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1160000000 4]),
  (⟨10, -6, -3⟩, [.hyp 0, .scale 4100000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2900000000 4]),
  (⟨11, -6, -3⟩, [.hyp 0, .scale 7000000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2900000000 4]),
  (⟨66, -46, -24⟩, [.hyp 0, .scale 500000023 0, .hyp 2, .scale 23 2, .add 1 3, .tighten 2900000000 4]),
  (⟨76, -6, -3⟩, [.hyp 0, .scale 195500000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 2900000000 4]),
  (⟨86, -60, -30⟩, [.hyp 0, .scale 40000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 290000000 4]),
  (⟨87, -60, -31⟩, [.hyp 0, .scale 330000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 290000000 4]),
  (⟨87, -60, -30⟩, [.hyp 0, .scale 330000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 290000000 4]),
  (⟨97, -66, -34⟩, [.hyp 0, .scale 7400000033 0, .hyp 2, .scale 33 2, .add 1 3, .tighten 2900000000 4]),
  (⟨97, -66, -33⟩, [.hyp 0, .scale 7400000033 0, .hyp 2, .scale 33 2, .add 1 3, .tighten 2900000000 4]),
]
-- kcost: 0.0960 s conservative; 160 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P039

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine004
