module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.AffineTape
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine000
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

namespace P000
def win : List Aff := [⟨1, 0, -2500000001⟩, ⟨-97000003, 20000000, 9999999⟩, ⟨99999997, -20000000, -10000000⟩]
#time def cert : Cert := [
  (⟨-97, 20, 10⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨-87, 18, 9⟩, [.hyp 0, .scale 3000027 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 10000000 4]),
  (⟨-70, 16, 9⟩, [.hyp 0, .scale 9500003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1250000 4]),
  (⟨-66, 14, 7⟩, [.hyp 0, .scale 19000021 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 10000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 42000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-8, 2, 1⟩, [.hyp 0, .scale 17000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 37000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 1, 0⟩, [.hyp 0, .scale 17000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 57000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 57000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 57000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 97000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -1, -1⟩, [.hyp 0, .scale 60000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 20000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 10000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨60, -12, -7⟩, [.hyp 0, .scale 9 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 5000000 4]),
  (⟨66, -12, -7⟩, [.hyp 0, .scale 30000009 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 5000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 280000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨86, -16, -8⟩, [.hyp 0, .scale 7500003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1250000 4]),
  (⟨87, -16, -9⟩, [.hyp 0, .scale 8750003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1250000 4]),
  (⟨93, -18, -9⟩, [.hyp 0, .scale 30000027 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 10000000 4]),
  (⟨97, -18, -10⟩, [.hyp 0, .scale 70000027 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 10000000 4]),
]
-- kcost: 0.0852 s conservative; 142 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P000

namespace P001
def win : List Aff := [⟨1, 0, -1900000001⟩, ⟨-432000003, 160000000, 79999999⟩, ⟨434999997, -160000000, -80000000⟩]
#time def cert : Cert := [
  (⟨-97, 36, 18⟩, [.hyp 0, .scale 8000027 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 40000000 4]),
  (⟨-87, 34, 17⟩, [.hyp 0, .scale 384000051 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 80000000 4]),
  (⟨-70, 26, 14⟩, [.hyp 0, .scale 16000039 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 80000000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 336000039 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 80000000 4]),
  (⟨-27, 10, 4⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 416000009 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 80000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 32000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 16000009 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 160000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 192000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 112000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 112000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 432000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 160000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 205000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 160000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 45000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 45000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 205000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 365000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 80000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 5000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 15000009 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 20000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 2605000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 40000000 4]),
  (⟨86, -30, -15⟩, [.hyp 0, .scale 71000009 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 16000000 4]),
  (⟨87, -32, -17⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨87, -32, -16⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨97, -34, -18⟩, [.hyp 0, .scale 365000051 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 80000000 4]),
  (⟨97, -34, -17⟩, [.hyp 0, .scale 365000051 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 80000000 4]),
]
-- kcost: 0.0948 s conservative; 158 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P001

namespace P002
def win : List Aff := [⟨1, 0, -2800000001⟩, ⟨-42666667, 16000000, 7999999⟩, ⟨128999999, -48000000, -24000000⟩]
#time def cert : Cert := [
  (⟨-97, 38, 19⟩, [.hyp 0, .scale 34666673 0, .hyp 1, .scale 19 2, .add 1 3, .tighten 8000000 4]),
  (⟨-93, 36, 17⟩, [.hyp 0, .scale 12000003 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 4000000 4]),
  (⟨-87, 34, 17⟩, [.hyp 0, .scale 29333339 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 8000000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 26666671 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 8000000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 40000001 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 8000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 2666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 16000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 18666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 10666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 10666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 10666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 42666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 63000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 48000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 15000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 24000000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 15000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 24000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 63000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 24000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 3000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 12000000 4]),
  (⟨27, -10, -4⟩, [.hyp 0, .scale 600001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 4800000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 3000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 783000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 12000000 4]),
  (⟨86, -32, -16⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1500000 4]),
  (⟨87, -32, -17⟩, [.hyp 0, .scale 1500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1500000 4]),
  (⟨97, -36, -19⟩, [.hyp 0, .scale 1000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 4000000 4]),
  (⟨97, -36, -18⟩, [.hyp 0, .scale 1000003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 4000000 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P002

namespace P003
def win : List Aff := [⟨1, 0, -3600000001⟩, ⟨-4409091, 1000000, 499999⟩, ⟨7999999999, -1800000000, -900000000⟩]
#time def cert : Cert := [
  (⟨-97, 22, 11⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 500000 4]),
  (⟨-87, 20, 10⟩, [.hyp 0, .scale 59091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 50000 4]),
  (⟨-70, 16, 9⟩, [.hyp 0, .scale 34091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 62500 4]),
  (⟨-66, 16, 8⟩, [.hyp 0, .scale 284091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 62500 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 1659091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 250000 4]),
  (⟨-8, 2, 1⟩, [.hyp 0, .scale 409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨-6, 2, 0⟩, [.hyp 0, .scale 1409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 1409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨-4, 1, 0⟩, [.hyp 0, .scale 409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 2409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 2409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 2409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 4409091 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -1, -1⟩, [.hyp 0, .scale 6400000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1800000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 1000000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 900000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 1900000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 900000000 4]),
  (⟨27, -6, -2⟩, [.hyp 0, .scale 100000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 300000000 4]),
  (⟨66, -14, -8⟩, [.hyp 0, .scale 3400000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 900000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 26200000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 450000000 4]),
  (⟨86, -18, -9⟩, [.hyp 0, .scale 600000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨87, -18, -10⟩, [.hyp 0, .scale 700000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨97, -20, -11⟩, [.hyp 0, .scale 730000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 90000000 4]),
  (⟨97, -20, -10⟩, [.hyp 0, .scale 730000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 90000000 4]),
]
-- kcost: 0.0888 s conservative; 148 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P003

namespace P004
def win : List Aff := [⟨1, 0, -1150000001⟩, ⟨-14923077, 4000000, 1999999⟩, ⟨194999999, -52000000, -26000000⟩]
#time def cert : Cert := [
  (⟨-97, 26, 13⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 2000000 4]),
  (⟨-87, 24, 12⟩, [.hyp 0, .scale 1269231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 500000 4]),
  (⟨-70, 20, 11⟩, [.hyp 0, .scale 923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 200000 4]),
  (⟨-66, 18, 9⟩, [.hyp 0, .scale 2307693 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 2000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 3923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 12769231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 4000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 2923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 6923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 6923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 6923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 14923077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 13000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 52000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 13000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 26000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 65000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 26000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 91000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 26000000 4]),
  (⟨60, -16, -9⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3250000 4]),
  (⟨66, -16, -9⟩, [.hyp 0, .scale 19500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3250000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 793000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 13000000 4]),
  (⟨86, -22, -11⟩, [.hyp 0, .scale 91000011 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 26000000 4]),
  (⟨87, -22, -12⟩, [.hyp 0, .scale 117000011 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 26000000 4]),
  (⟨93, -24, -12⟩, [.hyp 0, .scale 19500003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 6500000 4]),
  (⟨97, -24, -13⟩, [.hyp 0, .scale 45500003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 6500000 4]),
]
-- kcost: 0.0852 s conservative; 142 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P004

namespace P005
def win : List Aff := [⟨1, 0, -450000001⟩, ⟨-18523077, 5600000, 2799999⟩, ⟨34542857, -10400000, -5200000⟩]
#time def cert : Cert := [
  (⟨-97, 30, 15⟩, [.hyp 0, .scale 1249231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 560000 4]),
  (⟨-87, 28, 14⟩, [.hyp 0, .scale 1123077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 200000 4]),
  (⟨-86, 26, 13⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 2800000 4]),
  (⟨-70, 22, 12⟩, [.hyp 0, .scale 7753847 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 2800000 4]),
  (⟨-66, 20, 10⟩, [.hyp 0, .scale 43077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 280000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 3123077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1400000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 3123077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1400000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 10769231 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 5600000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 1723077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 7323077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 7323077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 7323077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2800000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 18523077 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5600000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 7057143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 10400000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 7057143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5200000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 17457143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5200000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 22657143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5200000 4]),
  (⟨60, -18, -10⟩, [.hyp 0, .scale 1114287 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 5200000 4]),
  (⟨66, -18, -10⟩, [.hyp 0, .scale 32314287 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 5200000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 163057143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2600000 4]),
  (⟨87, -26, -14⟩, [.hyp 0, .scale 257143 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 400000 4]),
  (⟨93, -28, -14⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 2600000 4]),
  (⟨97, -28, -15⟩, [.hyp 0, .scale 10400001 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 2600000 4]),
  (⟨97, -28, -14⟩, [.hyp 0, .scale 10400001 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 2600000 4]),
]
-- kcost: 0.0924 s conservative; 154 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P005

namespace P006
def win : List Aff := [⟨1, 0, -1850000001⟩, ⟨-7400000001, 2000000000, 999999999⟩, ⟨4476923, -1200000, -600000⟩]
#time def cert : Cert := [
  (⟨-97, 28, 14⟩, [.hyp 0, .scale 3300000007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 500000000 4]),
  (⟨-87, 24, 12⟩, [.hyp 0, .scale 450000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 250000000 4]),
  (⟨-86, 24, 12⟩, [.hyp 0, .scale 700000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 250000000 4]),
  (⟨-70, 20, 11⟩, [.hyp 0, .scale 400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-66, 18, 9⟩, [.hyp 0, .scale 600000009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 1000000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 1900000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 1900000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 2400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 500000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 6200000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 2000000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 1400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 3400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 3400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 3400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 7400000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 323077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1200000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 323077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 600000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 2123077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 600000 4]),
  (⟨60, -16, -9⟩, [.hyp 0, .scale 23077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 75000 4]),
  (⟨66, -16, -9⟩, [.hyp 0, .scale 473077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 75000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 18323077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 300000 4]),
  (⟨87, -22, -12⟩, [.hyp 0, .scale 2953847 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 600000 4]),
  (⟨97, -26, -14⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 600000 4]),
  (⟨97, -26, -13⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 600000 4]),
]
-- kcost: 0.0888 s conservative; 148 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P006

namespace P007
def win : List Aff := [⟨1, 0, -650000001⟩, ⟨-39857143, 12000000, 5999999⟩, ⟨93333333, -28000000, -14000000⟩]
#time def cert : Cert := [
  (⟨-97, 30, 15⟩, [.hyp 0, .scale 1057143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 400000 4]),
  (⟨-93, 28, 13⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 3000000 4]),
  (⟨-87, 28, 14⟩, [.hyp 0, .scale 18000001 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 3000000 4]),
  (⟨-86, 26, 13⟩, [.hyp 0, .scale 2142859 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 6000000 4]),
  (⟨-70, 22, 12⟩, [.hyp 0, .scale 18428573 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 6000000 4]),
  (⟨-66, 20, 10⟩, [.hyp 0, .scale 257143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 600000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 6857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 6857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 7857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 4000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 3857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 15857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 15857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 15857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 39857143 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 12000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 18666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 28000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 18666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 14000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 46666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 14000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 60666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 14000000 4]),
  (⟨27, -8, -3⟩, [.hyp 0, .scale 1166667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3500000 4]),
  (⟨60, -18, -10⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 14000000 4]),
  (⟨66, -18, -10⟩, [.hyp 0, .scale 84000003 0, .hyp 2, .scale 9 2, .add 1 3, .tighten 14000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 438666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 7000000 4]),
  (⟨87, -26, -14⟩, [.hyp 0, .scale 4666671 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 14000000 4]),
  (⟨97, -28, -15⟩, [.hyp 0, .scale 3666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨97, -28, -14⟩, [.hyp 0, .scale 3666667 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
]
-- kcost: 0.0960 s conservative; 160 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P007

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine000
