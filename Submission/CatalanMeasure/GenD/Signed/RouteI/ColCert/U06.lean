module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V181 : UnitD := ⟨731090909093, 3727272727, [K7, K276, K424, K496, K532, K551, K560, K563, K565], [K583, K586, K590, K599, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 314, 320, false, false⟩

theorem V181_ok : V181.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V181_fin : V181.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V181_V : V181.V where
  ok := V181_ok
  fin := V181_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K551_chk, List.forall_mem_cons.2 ⟨K560_chk, List.forall_mem_cons.2 ⟨K563_chk, List.forall_mem_cons.2 ⟨K565_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K583_chk, List.forall_mem_cons.2 ⟨K586_chk, List.forall_mem_cons.2 ⟨K590_chk, List.forall_mem_cons.2 ⟨K599_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V182 : UnitD := ⟨738545454547, 3727272727, [K7, K276, K424, K496, K532, K551, K561, K567], [K587, K589, K594, K599, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 316, 322, false, false⟩

theorem V182_ok : V182.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V182_fin : V182.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V182_V : V182.V where
  ok := V182_ok
  fin := V182_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K551_chk, List.forall_mem_cons.2 ⟨K561_chk, List.forall_mem_cons.2 ⟨K567_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K587_chk, List.forall_mem_cons.2 ⟨K589_chk, List.forall_mem_cons.2 ⟨K594_chk, List.forall_mem_cons.2 ⟨K599_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V183 : UnitD := ⟨746000000001, 3727272727, [K7, K276, K424, K496, K532, K552, K567, K577], [K592, K594, K599, K608, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 318, 324, false, false⟩

theorem V183_ok : V183.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V183_fin : V183.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V183_V : V183.V where
  ok := V183_ok
  fin := V183_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K567_chk, List.forall_mem_cons.2 ⟨K577_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K592_chk, List.forall_mem_cons.2 ⟨K594_chk, List.forall_mem_cons.2 ⟨K599_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V184 : UnitD := ⟨753454545455, 3727272727, [K7, K276, K424, K496, K532, K552, K568, K580], [K595, K597, K599, K608, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 320, 326, false, false⟩

theorem V184_ok : V184.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V184_fin : V184.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V184_V : V184.V where
  ok := V184_ok
  fin := V184_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K568_chk, List.forall_mem_cons.2 ⟨K580_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K595_chk, List.forall_mem_cons.2 ⟨K597_chk, List.forall_mem_cons.2 ⟨K599_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V185 : UnitD := ⟨760909090909, 3727272727, [K7, K276, K424, K496, K532, K552, K568, K580, K583, K585], [K598, K601, K608, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 322, 328, false, false⟩

theorem V185_ok : V185.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V185_fin : V185.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V185_V : V185.V where
  ok := V185_ok
  fin := V185_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K568_chk, List.forall_mem_cons.2 ⟨K580_chk, List.forall_mem_cons.2 ⟨K583_chk, List.forall_mem_cons.2 ⟨K585_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K598_chk, List.forall_mem_cons.2 ⟨K601_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V186 : UnitD := ⟨768363636365, 3727272729, [K7, K276, K424, K496, K533, K568, K580, K584, K588], [K600, K603, K607, K618, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 324, 330, false, false⟩

theorem V186_ok : V186.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V186_fin : V186.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V186_V : V186.V where
  ok := V186_ok
  fin := V186_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K568_chk, List.forall_mem_cons.2 ⟨K580_chk, List.forall_mem_cons.2 ⟨K584_chk, List.forall_mem_cons.2 ⟨K588_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K600_chk, List.forall_mem_cons.2 ⟨K603_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V187 : UnitD := ⟨775818181821, 3727272727, [K7, K276, K424, K496, K533, K568, K581, K589, K593], [K604, K606, K612, K618, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 326, 332, false, false⟩

theorem V187_ok : V187.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V187_fin : V187.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V187_V : V187.V where
  ok := V187_ok
  fin := V187_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K568_chk, List.forall_mem_cons.2 ⟨K581_chk, List.forall_mem_cons.2 ⟨K589_chk, List.forall_mem_cons.2 ⟨K593_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K604_chk, List.forall_mem_cons.2 ⟨K606_chk, List.forall_mem_cons.2 ⟨K612_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V188 : UnitD := ⟨783272727275, 3727272727, [K7, K276, K424, K496, K533, K569, K589, K593, K596], [K610, K612, K618, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 328, 334, false, false⟩

theorem V188_ok : V188.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V188_fin : V188.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V188_V : V188.V where
  ok := V188_ok
  fin := V188_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K589_chk, List.forall_mem_cons.2 ⟨K593_chk, List.forall_mem_cons.2 ⟨K596_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K610_chk, List.forall_mem_cons.2 ⟨K612_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V189 : UnitD := ⟨790727272729, 3727272727, [K7, K276, K424, K496, K533, K569, K590, K598], [K613, K615, K618, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 330, 336, false, false⟩

theorem V189_ok : V189.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V189_fin : V189.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V189_V : V189.V where
  ok := V189_ok
  fin := V189_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K590_chk, List.forall_mem_cons.2 ⟨K598_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K613_chk, List.forall_mem_cons.2 ⟨K615_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V190 : UnitD := ⟨798181818183, 3727272727, [K7, K276, K424, K496, K533, K569, K590, K598, K600, K602], [K616, K619, K621, K628, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 332, 338, false, false⟩

theorem V190_ok : V190.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V190_fin : V190.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V190_V : V190.V where
  ok := V190_ok
  fin := V190_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K590_chk, List.forall_mem_cons.2 ⟨K598_chk, List.forall_mem_cons.2 ⟨K600_chk, List.forall_mem_cons.2 ⟨K602_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K616_chk, List.forall_mem_cons.2 ⟨K619_chk, List.forall_mem_cons.2 ⟨K621_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V191 : UnitD := ⟨805636363637, 3727272727, [K7, K276, K424, K497, K569, K590, K598, K601, K605], [K620, K623, K627, K636, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 334, 340, false, false⟩

theorem V191_ok : V191.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V191_fin : V191.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V191_V : V191.V where
  ok := V191_ok
  fin := V191_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K590_chk, List.forall_mem_cons.2 ⟨K598_chk, List.forall_mem_cons.2 ⟨K601_chk, List.forall_mem_cons.2 ⟨K605_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K620_chk, List.forall_mem_cons.2 ⟨K623_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V192 : UnitD := ⟨813090909091, 3727272727, [K7, K276, K424, K497, K569, K590, K599, K606, K611], [K624, K626, K631, K636, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 336, 342, false, false⟩

theorem V192_ok : V192.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V192_fin : V192.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V192_V : V192.V where
  ok := V192_ok
  fin := V192_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K590_chk, List.forall_mem_cons.2 ⟨K599_chk, List.forall_mem_cons.2 ⟨K606_chk, List.forall_mem_cons.2 ⟨K611_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K624_chk, List.forall_mem_cons.2 ⟨K626_chk, List.forall_mem_cons.2 ⟨K631_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V193 : UnitD := ⟨818681818183, 1863636365, [K7, K276, K424, K497, K569, K591, K606, K611, K614], [K626, K631, K636, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 338, 343, false, false⟩

theorem V193_ok : V193.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V193_fin : V193.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V193_V : V193.V where
  ok := V193_ok
  fin := V193_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K606_chk, List.forall_mem_cons.2 ⟨K611_chk, List.forall_mem_cons.2 ⟨K614_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K626_chk, List.forall_mem_cons.2 ⟨K631_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V194 : UnitD := ⟨822409090911, 1863636363, [K7, K276, K424, K497, K569, K591, K607, K616, K619], [K629, K631, K636, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 340, 344, false, false⟩

theorem V194_ok : V194.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V194_fin : V194.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V194_V : V194.V where
  ok := V194_ok
  fin := V194_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K616_chk, List.forall_mem_cons.2 ⟨K619_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K629_chk, List.forall_mem_cons.2 ⟨K631_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V195 : UnitD := ⟨828000000001, 3727272727, [K7, K276, K424, K497, K569, K591, K607, K617], [K632, K633, K636, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 340, 346, false, false⟩

theorem V195_ok : V195.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V195_fin : V195.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V195_V : V195.V where
  ok := V195_ok
  fin := V195_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K617_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K632_chk, List.forall_mem_cons.2 ⟨K633_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V196 : UnitD := ⟨833590909093, 1863636365, [K7, K276, K424, K497, K570, K607, K617, K620, K622], [K633, K635, K639, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 342, 347, false, false⟩

theorem V196_ok : V196.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V196_fin : V196.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V196_V : V196.V where
  ok := V196_ok
  fin := V196_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K617_chk, List.forall_mem_cons.2 ⟨K620_chk, List.forall_mem_cons.2 ⟨K622_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K633_chk, List.forall_mem_cons.2 ⟨K635_chk, List.forall_mem_cons.2 ⟨K639_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V197 : UnitD := ⟨837318181821, 1863636363, [K7, K276, K424, K497, K570, K607, K617, K621, K625], [K635, K639, K648, K713, K850], [K1116, K1118, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 344, 348, false, false⟩

theorem V197_ok : V197.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V197_fin : V197.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V197_V : V197.V where
  ok := V197_ok
  fin := V197_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K617_chk, List.forall_mem_cons.2 ⟨K621_chk, List.forall_mem_cons.2 ⟨K625_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K635_chk, List.forall_mem_cons.2 ⟨K639_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V198 : UnitD := ⟨841045454547, 1863636363, [K7, K276, K424, K497, K570, K607, K618, K625, K629], [K637, K639, K647, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 345, 349, false, false⟩

theorem V198_ok : V198.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V198_fin : V198.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V198_V : V198.V where
  ok := V198_ok
  fin := V198_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K625_chk, List.forall_mem_cons.2 ⟨K629_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K637_chk, List.forall_mem_cons.2 ⟨K639_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V199 : UnitD := ⟨843840909091, 931818181, [K7, K276, K424, K497, K570, K607, K618, K626, K630], [K637, K639, K647, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 346, 349, false, false⟩

theorem V199_ok : V199.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V199_fin : V199.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V199_V : V199.V where
  ok := V199_ok
  fin := V199_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K626_chk, List.forall_mem_cons.2 ⟨K630_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K637_chk, List.forall_mem_cons.2 ⟨K639_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V200 : UnitD := ⟨845704545455, 931818183, [K7, K276, K424, K497, K570, K607, K618, K626, K630], [K637, K639, K646, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 346, 349, false, false⟩

theorem V200_ok : V200.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V200_fin : V200.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V200_V : V200.V where
  ok := V200_ok
  fin := V200_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K626_chk, List.forall_mem_cons.2 ⟨K630_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K637_chk, List.forall_mem_cons.2 ⟨K639_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V201 : UnitD := ⟨848500000001, 1863636363, [K7, K276, K424, K497, K570, K607, K618, K626, K630, K632], [K638, K641, K645, K655, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 347, 350, false, false⟩

theorem V201_ok : V201.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V201_fin : V201.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V201_V : V201.V where
  ok := V201_ok
  fin := V201_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K607_chk, List.forall_mem_cons.2 ⟨K618_chk, List.forall_mem_cons.2 ⟨K626_chk, List.forall_mem_cons.2 ⟨K630_chk, List.forall_mem_cons.2 ⟨K632_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K638_chk, List.forall_mem_cons.2 ⟨K641_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V202 : UnitD := ⟨852227272729, 1863636365, [K7, K276, K424, K497, K570, K608, K626, K630, K632], [K642, K645, K655, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 347, 352, false, false⟩

theorem V202_ok : V202.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V202_fin : V202.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V202_V : V202.V where
  ok := V202_ok
  fin := V202_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K626_chk, List.forall_mem_cons.2 ⟨K630_chk, List.forall_mem_cons.2 ⟨K632_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K642_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V203 : UnitD := ⟨855954545457, 1863636363, [K7, K276, K424, K497, K570, K608, K626, K631, K634], [K644, K651, K655, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 349, 353, false, false⟩

theorem V203_ok : V203.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V203_fin : V203.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V203_V : V203.V where
  ok := V203_ok
  fin := V203_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K626_chk, List.forall_mem_cons.2 ⟨K631_chk, List.forall_mem_cons.2 ⟨K634_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K644_chk, List.forall_mem_cons.2 ⟨K651_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V204 : UnitD := ⟨859681818183, 1863636363, [K7, K276, K424, K497, K570, K608, K627, K634, K637], [K643, K649, K651, K655, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 350, 353, false, false⟩

theorem V204_ok : V204.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V204_fin : V204.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V204_V : V204.V where
  ok := V204_ok
  fin := V204_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K634_chk, List.forall_mem_cons.2 ⟨K637_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K643_chk, List.forall_mem_cons.2 ⟨K649_chk, List.forall_mem_cons.2 ⟨K651_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V205 : UnitD := ⟨863409090911, 1863636365, [K7, K276, K424, K497, K570, K608, K627, K635], [K651, K655, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 350, 355, false, false⟩

theorem V205_ok : V205.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V205_fin : V205.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V205_V : V205.V where
  ok := V205_ok
  fin := V205_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K635_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K651_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V206 : UnitD := ⟨867136363639, 1863636363, [K7, K276, K424, K497, K570, K608, K627, K635, K638, K640], [K652, K655, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 352, 356, false, false⟩

theorem V206_ok : V206.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V206_fin : V206.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V206_V : V206.V where
  ok := V206_ok
  fin := V206_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K635_chk, List.forall_mem_cons.2 ⟨K638_chk, List.forall_mem_cons.2 ⟨K640_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K652_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V207 : UnitD := ⟨870863636365, 1863636363, [K7, K276, K425, K570, K608, K627, K635, K638, K640, K642], [K652, K654, K658, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 353, 356, false, false⟩

theorem V207_ok : V207.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V207_fin : V207.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V207_V : V207.V where
  ok := V207_ok
  fin := V207_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K635_chk, List.forall_mem_cons.2 ⟨K638_chk, List.forall_mem_cons.2 ⟨K640_chk, List.forall_mem_cons.2 ⟨K642_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K652_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K658_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V208 : UnitD := ⟨874590909093, 1863636365, [K7, K276, K425, K570, K608, K627, K635, K638, K641], [K656, K658, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 353, 358, false, false⟩

theorem V208_ok : V208.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V208_fin : V208.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V208_V : V208.V where
  ok := V208_ok
  fin := V208_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K635_chk, List.forall_mem_cons.2 ⟨K638_chk, List.forall_mem_cons.2 ⟨K641_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K656_chk, List.forall_mem_cons.2 ⟨K658_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V209 : UnitD := ⟨878318181821, 1863636363, [K7, K276, K425, K570, K608, K627, K636, K643, K649], [K658, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 355, 359, false, false⟩

theorem V209_ok : V209.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V209_fin : V209.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V209_V : V209.V where
  ok := V209_ok
  fin := V209_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K643_chk, List.forall_mem_cons.2 ⟨K649_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K658_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V210 : UnitD := ⟨882045454547, 1863636363, [K7, K276, K425, K570, K608, K627, K636, K644, K650], [K659, K663, K681, K713, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 356, 360, false, false⟩

theorem V210_ok : V210.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V210_fin : V210.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V210_V : V210.V where
  ok := V210_ok
  fin := V210_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K644_chk, List.forall_mem_cons.2 ⟨K650_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K659_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def L6 : List UnitD := [V181, V182, V183, V184, V185, V186, V187, V188, V189, V190, V191, V192, V193, V194, V195, V196, V197, V198, V199, V200, V201, V202, V203, V204, V205, V206, V207, V208, V209, V210]

theorem L6_V : ∀ u ∈ L6, u.V :=
  List.forall_mem_cons.2 ⟨V181_V, List.forall_mem_cons.2 ⟨V182_V, List.forall_mem_cons.2 ⟨V183_V, List.forall_mem_cons.2 ⟨V184_V, List.forall_mem_cons.2 ⟨V185_V, List.forall_mem_cons.2 ⟨V186_V, List.forall_mem_cons.2 ⟨V187_V, List.forall_mem_cons.2 ⟨V188_V, List.forall_mem_cons.2 ⟨V189_V, List.forall_mem_cons.2 ⟨V190_V, List.forall_mem_cons.2 ⟨V191_V, List.forall_mem_cons.2 ⟨V192_V, List.forall_mem_cons.2 ⟨V193_V, List.forall_mem_cons.2 ⟨V194_V, List.forall_mem_cons.2 ⟨V195_V, List.forall_mem_cons.2 ⟨V196_V, List.forall_mem_cons.2 ⟨V197_V, List.forall_mem_cons.2 ⟨V198_V, List.forall_mem_cons.2 ⟨V199_V, List.forall_mem_cons.2 ⟨V200_V, List.forall_mem_cons.2 ⟨V201_V, List.forall_mem_cons.2 ⟨V202_V, List.forall_mem_cons.2 ⟨V203_V, List.forall_mem_cons.2 ⟨V204_V, List.forall_mem_cons.2 ⟨V205_V, List.forall_mem_cons.2 ⟨V206_V, List.forall_mem_cons.2 ⟨V207_V, List.forall_mem_cons.2 ⟨V208_V, List.forall_mem_cons.2 ⟨V209_V, List.forall_mem_cons.2 ⟨V210_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
