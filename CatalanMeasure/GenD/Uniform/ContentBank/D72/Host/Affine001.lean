module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.AffineTape
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine001
open CatalanMeasure.GenD.Uniform.W.Charts6.Check

namespace P008
def win : List Aff := [⟨1, 0, -650000001⟩, ⟨-7200000001, 2200000000, 1099999999⟩, ⟨49499999, -15000000, -7500000⟩]
#time def cert : Cert := [
  (⟨-97, 30, 15⟩, [.hyp 0, .scale 260000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 220000000 4]),
  (⟨-87, 28, 14⟩, [.hyp 0, .scale 2550000007 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 550000000 4]),
  (⟨-70, 22, 12⟩, [.hyp 0, .scale 200000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-66, 22, 11⟩, [.hyp 0, .scale 600000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 100000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 1150000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 550000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 4000000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 2200000000 4]),
  (⟨-6, 2, 0⟩, [.hyp 0, .scale 600000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 600000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 2800000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 2800000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 2800000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1100000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 7200000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2200000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 10500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 10500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 7500000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 25500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 7500000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 33000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 7500000 4]),
  (⟨27, -8, -3⟩, [.hyp 0, .scale 1125001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1875000 4]),
  (⟨66, -20, -11⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 750000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 235500001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3750000 4]),
  (⟨86, -26, -13⟩, [.hyp 0, .scale 1500013 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 7500000 4]),
  (⟨87, -26, -14⟩, [.hyp 0, .scale 9000013 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 7500000 4]),
  (⟨97, -28, -15⟩, [.hyp 0, .scale 17250007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 3750000 4]),
  (⟨97, -28, -14⟩, [.hyp 0, .scale 17250007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 3750000 4]),
]
-- kcost: 0.0888 s conservative; 148 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P008

namespace P009
def win : List Aff := [⟨1, 0, -3700000001⟩, ⟨-957000003, 352000000, 175999999⟩, ⟨87272727, -32000000, -16000000⟩]
#time def cert : Cert := [
  (⟨-97, 36, 18⟩, [.hyp 0, .scale 77000027 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 88000000 4]),
  (⟨-87, 32, 16⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 11000000 4]),
  (⟨-70, 26, 14⟩, [.hyp 0, .scale 121000039 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 176000000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 825000039 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 176000000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 935000009 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 176000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 77000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 88000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 55000009 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 352000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 429000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 88000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 253000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 176000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 253000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 176000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 957000003 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 352000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 40727273 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 32000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 8727273 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 40727273 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 16000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 727273 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨60, -22, -12⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 16000000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 2181819 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 4000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 520727273 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 8000000 4]),
  (⟨86, -30, -15⟩, [.hyp 0, .scale 13381819 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 3200000 4]),
  (⟨87, -30, -16⟩, [.hyp 0, .scale 16581819 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 3200000 4]),
  (⟨93, -34, -17⟩, [.hyp 0, .scale 4363641 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 16000000 4]),
  (⟨97, -34, -18⟩, [.hyp 0, .scale 68363641 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 16000000 4]),
  (⟨97, -34, -17⟩, [.hyp 0, .scale 68363641 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 16000000 4]),
]
-- kcost: 0.0876 s conservative; 146 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P009

namespace P010
def win : List Aff := [⟨1, 0, -600000001⟩, ⟨-28666667, 10000000, 4999999⟩, ⟨86999999, -30000000, -15000000⟩]
#time def cert : Cert := [
  (⟨-97, 34, 17⟩, [.hyp 0, .scale 2333339 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 5000000 4]),
  (⟨-87, 32, 16⟩, [.hyp 0, .scale 1479167 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 312500 4]),
  (⟨-86, 30, 15⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 1000000 4]),
  (⟨-66, 24, 12⟩, [.hyp 0, .scale 3500001 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 1250000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 1166667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2500000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 1166667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2500000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 3666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2500000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 6000001 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 10000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 13666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2500000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 8666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 8666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 8666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 28666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 33000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 30000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 3000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15000000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 3000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 33000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 63000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 78000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15000000 4]),
  (⟨66, -22, -12⟩, [.hyp 0, .scale 33000011 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 15000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 483000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 7500000 4]),
  (⟨86, -28, -14⟩, [.hyp 0, .scale 36000007 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 7500000 4]),
  (⟨87, -30, -16⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨87, -30, -15⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨97, -32, -17⟩, [.hyp 0, .scale 3937501 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 937500 4]),
  (⟨97, -32, -16⟩, [.hyp 0, .scale 3937501 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 937500 4]),
]
-- kcost: 0.0984 s conservative; 164 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P010

namespace P011
def win : List Aff := [⟨1, 0, -3400000001⟩, ⟨-186000001, 68000000, 33999999⟩, ⟨186999999, -68000000, -34000000⟩]
#time def cert : Cert := [
  (⟨-97, 36, 18⟩, [.hyp 0, .scale 25000009 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 17000000 4]),
  (⟨-93, 34, 16⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨-87, 32, 16⟩, [.hyp 0, .scale 1125001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 2125000 4]),
  (⟨-70, 26, 14⟩, [.hyp 0, .scale 38000013 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 34000000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 174000013 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 34000000 4]),
  (⟨-60, 22, 12⟩, [.hyp 0, .scale 6000011 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 34000000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 184000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 34000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 16000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 14000003 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 68000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 84000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 50000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 50000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 50000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 186000001 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 68000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 85000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 68000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 17000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 85000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 8500000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 1105000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨86, -30, -15⟩, [.hyp 0, .scale 23800003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 6800000 4]),
  (⟨87, -30, -16⟩, [.hyp 0, .scale 30600003 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 6800000 4]),
  (⟨97, -34, -18⟩, [.hyp 0, .scale 7000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2000000 4]),
  (⟨97, -34, -17⟩, [.hyp 0, .scale 7000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 2000000 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P011

namespace P012
def win : List Aff := [⟨1, 0, -550000001⟩, ⟨-86666667, 26000000, 12999999⟩, ⟨20076923, -6000000, -3000000⟩]
#time def cert : Cert := [
  (⟨-97, 30, 15⟩, [.hyp 0, .scale 7800001 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 2600000 4]),
  (⟨-93, 28, 13⟩, [.hyp 0, .scale 2166669 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 6500000 4]),
  (⟨-87, 28, 14⟩, [.hyp 0, .scale 41166669 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 6500000 4]),
  (⟨-86, 26, 13⟩, [.hyp 0, .scale 666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1000000 4]),
  (⟨-66, 20, 10⟩, [.hyp 0, .scale 866667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1300000 4]),
  (⟨-60, 18, 10⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 13000000 4]),
  (⟨-11, 4, 1⟩, [.hyp 0, .scale 15166667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6500000 4]),
  (⟨-11, 4, 2⟩, [.hyp 0, .scale 15166667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6500000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 21666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 6500000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 52000001 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 26000000 4]),
  (⟨-6, 2, 1⟩, [.hyp 0, .scale 8666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 13000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 34666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 13000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 34666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 13000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 34666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 13000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 86666667 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 26000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 3923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, 0, -1⟩, [.hyp 0, .scale 6 0]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 3923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 9923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨11, -2, -1⟩, [.hyp 0, .scale 12923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 3000000 4]),
  (⟨66, -18, -10⟩, [.hyp 0, .scale 5769231 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 1000000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 93923077 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 1500000 4]),
  (⟨87, -26, -14⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 3000000 4]),
  (⟨87, -26, -13⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 13 2, .add 1 3, .tighten 3000000 4]),
  (⟨97, -28, -15⟩, [.hyp 0, .scale 4961539 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 1500000 4]),
  (⟨97, -28, -14⟩, [.hyp 0, .scale 4961539 0, .hyp 2, .scale 7 2, .add 1 3, .tighten 1500000 4]),
]
-- kcost: 0.0960 s conservative; 160 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P012

namespace P013
def win : List Aff := [⟨1, 0, -800000001⟩, ⟨-96461539, 38000000, 18999999⟩, ⟨1260999993, -494000000, -247000000⟩]
#time def cert : Cert := [
  (⟨-97, 40, 20⟩, [.hyp 0, .scale 4311539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 950000 4]),
  (⟨-87, 36, 18⟩, [.hyp 0, .scale 41653851 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 9500000 4]),
  (⟨-86, 34, 17⟩, [.hyp 0, .scale 5846163 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 19000000 4]),
  (⟨-70, 28, 15⟩, [.hyp 0, .scale 10230773 0, .hyp 1, .scale 7 2, .add 1 3, .tighten 9500000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 7 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 19000000 4]),
  (⟨-27, 12, 5⟩, [.hyp 0, .scale 32884617 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 9500000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 80384617 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 19000000 4]),
  (⟨-11, 6, 3⟩, [.hyp 0, .scale 80384617 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 19000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 1461539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 9500000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 39461539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 9500000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 20461539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 19000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 20461539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 19000000 4]),
  (⟨-4, 2, 2⟩, [.hyp 0, .scale 20461539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 19000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 96461539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 38000000 4]),
  (⟨0, 1, 1⟩, [.hyp 0, .scale 96461539 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 38000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 715000007 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 494000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 221000007 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 247000000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 221000007 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 247000000 4]),
  (⟨8, -3, -2⟩, [.hyp 0, .scale 169000021 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 494000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 97500007 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 123500000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 292500021 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 61750000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 8125000007 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 123500000 4]),
  (⟨86, -32, -16⟩, [.hyp 0, .scale 66625007 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 15437500 4]),
  (⟨87, -34, -18⟩, [.hyp 0, .scale 52000119 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 247000000 4]),
  (⟨97, -38, -20⟩, [.hyp 0, .scale 7 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 13000000 4]),
  (⟨97, -38, -19⟩, [.hyp 0, .scale 7 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 13000000 4]),
]
-- kcost: 0.0984 s conservative; 164 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P013

namespace P014
def win : List Aff := [⟨1, 0, -3700000001⟩, ⟨-92727273, 34000000, 16999999⟩, ⟨1022999997, -374000000, -187000000⟩]
#time def cert : Cert := [
  (⟨-97, 36, 18⟩, [.hyp 0, .scale 10045457 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 8500000 4]),
  (⟨-87, 32, 16⟩, [.hyp 0, .scale 289773 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 1062500 4]),
  (⟨-70, 26, 14⟩, [.hyp 0, .scale 15454549 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 17000000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 83454549 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 17000000 4]),
  (⟨-60, 22, 12⟩, [.hyp 0, .scale 3 0, .hyp 1, .scale 11 2, .add 1 3, .tighten 17000000 4]),
  (⟨-27, 10, 4⟩, [.hyp 0, .scale 927273 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 3400000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 91181819 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 17000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 7727273 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8500000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 6181819 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 34000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 41727273 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 8500000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 24727273 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 24727273 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 17000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 92727273 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 34000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 473000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 374000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 99000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 187000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 473000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 187000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 5500003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 93500000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 16500009 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 46750000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 6083000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 93500000 4]),
  (⟨86, -30, -15⟩, [.hyp 0, .scale 147400009 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 37400000 4]),
  (⟨87, -30, -16⟩, [.hyp 0, .scale 184800009 0, .hyp 2, .scale 3 2, .add 1 3, .tighten 37400000 4]),
  (⟨93, -34, -17⟩, [.hyp 0, .scale 3 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 11000000 4]),
  (⟨97, -34, -18⟩, [.hyp 0, .scale 44000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 11000000 4]),
  (⟨97, -34, -17⟩, [.hyp 0, .scale 44000003 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 11000000 4]),
]
-- kcost: 0.0912 s conservative; 152 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P014

namespace P015
def win : List Aff := [⟨1, 0, -1900000001⟩, ⟨-53888889, 20000000, 9999999⟩, ⟨485999999, -180000000, -90000000⟩]
#time def cert : Cert := [
  (⟨-97, 36, 18⟩, [.hyp 0, .scale 1 0, .hyp 1, .scale 9 2, .add 1 3, .tighten 5000000 4]),
  (⟨-87, 34, 17⟩, [.hyp 0, .scale 46111113 0, .hyp 1, .scale 17 2, .add 1 3, .tighten 10000000 4]),
  (⟨-70, 26, 14⟩, [.hyp 0, .scale 555557 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 10000000 4]),
  (⟨-66, 26, 13⟩, [.hyp 0, .scale 40555557 0, .hyp 1, .scale 13 2, .add 1 3, .tighten 10000000 4]),
  (⟨-11, 6, 2⟩, [.hyp 0, .scale 51666667 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 10000000 4]),
  (⟨-10, 4, 2⟩, [.hyp 0, .scale 3888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-8, 3, 2⟩, [.hyp 0, .scale 1666667 0, .hyp 1, .scale 3 2, .add 1 3, .tighten 20000000 4]),
  (⟨-6, 4, 2⟩, [.hyp 0, .scale 23888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 5000000 4]),
  (⟨-4, 2, 0⟩, [.hyp 0, .scale 13888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨-4, 2, 1⟩, [.hyp 0, .scale 13888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 10000000 4]),
  (⟨0, 0, 0⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 0, 1⟩, [.hyp 0, .scale 0 0]),
  (⟨0, 1, 0⟩, [.hyp 0, .scale 53888889 0, .hyp 1, .scale 1 2, .add 1 3, .tighten 20000000 4]),
  (⟨4, -1, -1⟩, [.hyp 0, .scale 234000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 180000000 4]),
  (⟨4, 0, -1⟩, [.hyp 0, .scale 4 0]),
  (⟨4, 0, 0⟩, [.hyp 0, .scale 4 0]),
  (⟨6, -2, -2⟩, [.hyp 0, .scale 54000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 90000000 4]),
  (⟨6, -2, -1⟩, [.hyp 0, .scale 54000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 90000000 4]),
  (⟨8, -2, -1⟩, [.hyp 0, .scale 234000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 90000000 4]),
  (⟨10, -2, -1⟩, [.hyp 0, .scale 414000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 90000000 4]),
  (⟨11, -4, -2⟩, [.hyp 0, .scale 9000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 45000000 4]),
  (⟨27, -10, -4⟩, [.hyp 0, .scale 1 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 18000000 4]),
  (⟨60, -22, -12⟩, [.hyp 0, .scale 54000011 0, .hyp 2, .scale 11 2, .add 1 3, .tighten 90000000 4]),
  (⟨66, -24, -13⟩, [.hyp 0, .scale 9000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 7500000 4]),
  (⟨76, -4, -2⟩, [.hyp 0, .scale 2934000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 45000000 4]),
  (⟨86, -30, -15⟩, [.hyp 0, .scale 30000001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 6000000 4]),
  (⟨87, -32, -17⟩, [.hyp 0, .scale 3375001 0, .hyp 2, .scale 1 2, .add 1 3, .tighten 5625000 4]),
  (⟨97, -34, -18⟩, [.hyp 0, .scale 468000017 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 90000000 4]),
  (⟨97, -34, -17⟩, [.hyp 0, .scale 468000017 0, .hyp 2, .scale 17 2, .add 1 3, .tighten 90000000 4]),
]
-- kcost: 0.0948 s conservative; 158 exact affine operations.
#time theorem verified : affineTapeCheck win cert = true := by decide +kernel
end P015

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Affine001
