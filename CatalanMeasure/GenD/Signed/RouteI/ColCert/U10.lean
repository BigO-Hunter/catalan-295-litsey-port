module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V301 : UnitD := ⟨985250000001, 249999999, [K7, K276, K425, K571, K648, K713, K847, K880, K897, K912, K928, K932, K934], [K948, K950, K953, K961, K982, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 524, 531, false, false⟩

theorem V301_ok : V301.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V301_fin : V301.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V301_V : V301.V where
  ok := V301_ok
  fin := V301_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K928_chk, List.forall_mem_cons.2 ⟨K932_chk, List.forall_mem_cons.2 ⟨K934_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K948_chk, List.forall_mem_cons.2 ⟨K950_chk, List.forall_mem_cons.2 ⟨K953_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K982_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V302 : UnitD := ⟨985630494251, 130494251, [K7, K276, K425, K571, K648, K713, K847, K880, K897, K912, K929, K936], [K950, K953, K961, K982, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 526, 532, false, false⟩

theorem V302_ok : V302.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V302_fin : V302.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V302_V : V302.V where
  ok := V302_ok
  fin := V302_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K929_chk, List.forall_mem_cons.2 ⟨K936_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K950_chk, List.forall_mem_cons.2 ⟨K953_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K982_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V303 : UnitD := ⟨986005494251, 244505749, [K7, K276, K425, K571, K648, K713, K847, K880, K897, K912, K929, K936, K938], [K952, K955, K961, K981, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 527, 534, false, false⟩

theorem V303_ok : V303.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V303_fin : V303.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V303_V : V303.V where
  ok := V303_ok
  fin := V303_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K929_chk, List.forall_mem_cons.2 ⟨K936_chk, List.forall_mem_cons.2 ⟨K938_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K952_chk, List.forall_mem_cons.2 ⟨K955_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V304 : UnitD := ⟨986500000001, 250000001, [K7, K276, K425, K571, K648, K713, K847, K880, K897, K912, K929, K936, K938, K940, K942, K943], [K954, K957, K960, K970, K981, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 530, 536, false, false⟩

theorem V304_ok : V304.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V304_fin : V304.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V304_V : V304.V where
  ok := V304_ok
  fin := V304_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K929_chk, List.forall_mem_cons.2 ⟨K936_chk, List.forall_mem_cons.2 ⟨K938_chk, List.forall_mem_cons.2 ⟨K940_chk, List.forall_mem_cons.2 ⟨K942_chk, List.forall_mem_cons.2 ⟨K943_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K954_chk, List.forall_mem_cons.2 ⟨K957_chk, List.forall_mem_cons.2 ⟨K960_chk, List.forall_mem_cons.2 ⟨K970_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V305 : UnitD := ⟨987000000001, 249999999, [K7, K276, K425, K571, K648, K713, K847, K880, K897, K912, K929, K937, K944, K948], [K959, K964, K970, K981, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 532, 539, false, false⟩

theorem V305_ok : V305.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V305_fin : V305.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V305_V : V305.V where
  ok := V305_ok
  fin := V305_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K929_chk, List.forall_mem_cons.2 ⟨K937_chk, List.forall_mem_cons.2 ⟨K944_chk, List.forall_mem_cons.2 ⟨K948_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K959_chk, List.forall_mem_cons.2 ⟨K964_chk, List.forall_mem_cons.2 ⟨K970_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V306 : UnitD := ⟨987375000001, 125000001, [K7, K276, K425, K571, K648, K713, K847, K880, K897, K912, K930, K944, K948, K950], [K962, K964, K970, K981, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 534, 540, false, false⟩

theorem V306_ok : V306.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V306_fin : V306.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V306_V : V306.V where
  ok := V306_ok
  fin := V306_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K944_chk, List.forall_mem_cons.2 ⟨K948_chk, List.forall_mem_cons.2 ⟨K950_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K962_chk, List.forall_mem_cons.2 ⟨K964_chk, List.forall_mem_cons.2 ⟨K970_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V307 : UnitD := ⟨987750000001, 249999999, [K7, K276, K425, K571, K648, K713, K847, K880, K897, K912, K930, K945, K951], [K966, K970, K980, K997, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 535, 542, false, false⟩

theorem V307_ok : V307.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V307_fin : V307.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V307_V : V307.V where
  ok := V307_ok
  fin := V307_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K945_chk, List.forall_mem_cons.2 ⟨K951_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K966_chk, List.forall_mem_cons.2 ⟨K970_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V308 : UnitD := ⟨988250000001, 250000001, [K7, K276, K425, K571, K648, K713, K847, K881, K912, K930, K945, K952, K954, K956], [K968, K971, K973, K980, K997, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 538, 544, false, false⟩

theorem V308_ok : V308.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V308_fin : V308.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V308_V : V308.V where
  ok := V308_ok
  fin := V308_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K945_chk, List.forall_mem_cons.2 ⟨K952_chk, List.forall_mem_cons.2 ⟨K954_chk, List.forall_mem_cons.2 ⟨K956_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K968_chk, List.forall_mem_cons.2 ⟨K971_chk, List.forall_mem_cons.2 ⟨K973_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V309 : UnitD := ⟨988682227405, 182227403, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K945, K953, K958], [K972, K975, K980, K997, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 540, 546, false, false⟩

theorem V309_ok : V309.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V309_fin : V309.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V309_V : V309.V where
  ok := V309_ok
  fin := V309_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K945_chk, List.forall_mem_cons.2 ⟨K953_chk, List.forall_mem_cons.2 ⟨K958_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K972_chk, List.forall_mem_cons.2 ⟨K975_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V310 : UnitD := ⟨989057227405, 192772597, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K945, K953, K959, K963], [K976, K979, K989, K997, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 542, 548, false, false⟩

theorem V310_ok : V310.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V310_fin : V310.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V310_V : V310.V where
  ok := V310_ok
  fin := V310_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K945_chk, List.forall_mem_cons.2 ⟨K953_chk, List.forall_mem_cons.2 ⟨K959_chk, List.forall_mem_cons.2 ⟨K963_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K976_chk, List.forall_mem_cons.2 ⟨K979_chk, List.forall_mem_cons.2 ⟨K989_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V311 : UnitD := ⟨989500000001, 249999999, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K959, K963, K965, K967], [K984, K986, K989, K997, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 544, 550, false, false⟩

theorem V311_ok : V311.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V311_fin : V311.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V311_V : V311.V where
  ok := V311_ok
  fin := V311_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K959_chk, List.forall_mem_cons.2 ⟨K963_chk, List.forall_mem_cons.2 ⟨K965_chk, List.forall_mem_cons.2 ⟨K967_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K984_chk, List.forall_mem_cons.2 ⟨K986_chk, List.forall_mem_cons.2 ⟨K989_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V312 : UnitD := ⟨989951235065, 201235065, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K960, K969], [K987, K988, K992, K997, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 546, 552, false, false⟩

theorem V312_ok : V312.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V312_fin : V312.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V312_V : V312.V where
  ok := V312_ok
  fin := V312_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K960_chk, List.forall_mem_cons.2 ⟨K969_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K987_chk, List.forall_mem_cons.2 ⟨K988_chk, List.forall_mem_cons.2 ⟨K992_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V313 : UnitD := ⟨990326235065, 173764935, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K960, K969, K972, K974], [K990, K992, K997, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 548, 554, false, false⟩

theorem V313_ok : V313.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V313_fin : V313.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V313_V : V313.V where
  ok := V313_ok
  fin := V313_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K960_chk, List.forall_mem_cons.2 ⟨K969_chk, List.forall_mem_cons.2 ⟨K972_chk, List.forall_mem_cons.2 ⟨K974_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K990_chk, List.forall_mem_cons.2 ⟨K992_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V314 : UnitD := ⟨990750000001, 250000001, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K960, K969, K972, K974, K976, K977], [K993, K995, K999, K1002, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 550, 557, false, false⟩

theorem V314_ok : V314.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V314_fin : V314.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V314_V : V314.V where
  ok := V314_ok
  fin := V314_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K960_chk, List.forall_mem_cons.2 ⟨K969_chk, List.forall_mem_cons.2 ⟨K972_chk, List.forall_mem_cons.2 ⟨K974_chk, List.forall_mem_cons.2 ⟨K976_chk, List.forall_mem_cons.2 ⟨K977_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K993_chk, List.forall_mem_cons.2 ⟨K995_chk, List.forall_mem_cons.2 ⟨K999_chk, List.forall_mem_cons.2 ⟨K1002_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V315 : UnitD := ⟨991145752279, 145752277, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K960, K970, K978, K985], [K995, K999, K1002, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 552, 558, false, false⟩

theorem V315_ok : V315.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V315_fin : V315.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V315_V : V315.V where
  ok := V315_ok
  fin := V315_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K960_chk, List.forall_mem_cons.2 ⟨K970_chk, List.forall_mem_cons.2 ⟨K978_chk, List.forall_mem_cons.2 ⟨K985_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K995_chk, List.forall_mem_cons.2 ⟨K999_chk, List.forall_mem_cons.2 ⟨K1002_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V316 : UnitD := ⟨991520752279, 229247723, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K960, K970, K978, K986], [K999, K1002, K1012, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 553, 560, false, false⟩

theorem V316_ok : V316.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V316_fin : V316.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V316_V : V316.V where
  ok := V316_ok
  fin := V316_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K960_chk, List.forall_mem_cons.2 ⟨K970_chk, List.forall_mem_cons.2 ⟨K978_chk, List.forall_mem_cons.2 ⟨K986_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K999_chk, List.forall_mem_cons.2 ⟨K1002_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V317 : UnitD := ⟨992000000001, 249999999, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K961, K979, K988, K991], [K1001, K1005, K1011, K1028, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 556, 563, false, false⟩

theorem V317_ok : V317.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V317_fin : V317.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V317_V : V317.V where
  ok := V317_ok
  fin := V317_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K979_chk, List.forall_mem_cons.2 ⟨K988_chk, List.forall_mem_cons.2 ⟨K991_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1001_chk, List.forall_mem_cons.2 ⟨K1005_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V318 : UnitD := ⟨992375000001, 125000001, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K946, K961, K979, K988, K992], [K1003, K1005, K1011, K1028, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 558, 564, false, false⟩

theorem V318_ok : V318.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V318_fin : V318.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V318_V : V318.V where
  ok := V318_ok
  fin := V318_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K979_chk, List.forall_mem_cons.2 ⟨K988_chk, List.forall_mem_cons.2 ⟨K992_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1003_chk, List.forall_mem_cons.2 ⟨K1005_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V319 : UnitD := ⟨992750000001, 249999999, [K7, K276, K425, K571, K648, K713, K847, K881, K913, K947, K979, K989, K994], [K1007, K1010, K1021, K1028, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 559, 567, false, false⟩

theorem V319_ok : V319.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V319_fin : V319.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V319_V : V319.V where
  ok := V319_ok
  fin := V319_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K979_chk, List.forall_mem_cons.2 ⟨K989_chk, List.forall_mem_cons.2 ⟨K994_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1007_chk, List.forall_mem_cons.2 ⟨K1010_chk, List.forall_mem_cons.2 ⟨K1021_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V320 : UnitD := ⟨993125000001, 125000001, [K7, K276, K425, K571, K648, K713, K848, K913, K947, K980, K995, K998, K1000], [K1009, K1015, K1021, K1028, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 562, 568, false, false⟩

theorem V320_ok : V320.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V320_fin : V320.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V320_V : V320.V where
  ok := V320_ok
  fin := V320_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K995_chk, List.forall_mem_cons.2 ⟨K998_chk, List.forall_mem_cons.2 ⟨K1000_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1009_chk, List.forall_mem_cons.2 ⟨K1015_chk, List.forall_mem_cons.2 ⟨K1021_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V321 : UnitD := ⟨993500000001, 249999999, [K7, K276, K425, K571, K648, K713, K848, K913, K947, K980, K995, K999], [K1017, K1021, K1028, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 563, 571, false, false⟩

theorem V321_ok : V321.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V321_fin : V321.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V321_V : V321.V where
  ok := V321_ok
  fin := V321_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K995_chk, List.forall_mem_cons.2 ⟨K999_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1017_chk, List.forall_mem_cons.2 ⟨K1021_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V322 : UnitD := ⟨993875000001, 125000001, [K7, K276, K425, K571, K648, K713, K848, K913, K947, K980, K996, K1001, K1004], [K1018, K1021, K1028, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 566, 572, false, false⟩

theorem V322_ok : V322.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V322_fin : V322.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V322_V : V322.V where
  ok := V322_ok
  fin := V322_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K996_chk, List.forall_mem_cons.2 ⟨K1001_chk, List.forall_mem_cons.2 ⟨K1004_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1018_chk, List.forall_mem_cons.2 ⟨K1021_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V323 : UnitD := ⟨994125000001, 124999999, [K7, K276, K425, K571, K648, K713, K848, K913, K947, K980, K996, K1001, K1004, K1006, K1007], [K1018, K1020, K1024, K1028, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 568, 572, false, false⟩

theorem V323_ok : V323.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V323_fin : V323.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V323_V : V323.V where
  ok := V323_ok
  fin := V323_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K996_chk, List.forall_mem_cons.2 ⟨K1001_chk, List.forall_mem_cons.2 ⟨K1004_chk, List.forall_mem_cons.2 ⟨K1006_chk, List.forall_mem_cons.2 ⟨K1007_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1018_chk, List.forall_mem_cons.2 ⟨K1020_chk, List.forall_mem_cons.2 ⟨K1024_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V324 : UnitD := ⟨994375000001, 125000001, [K7, K276, K425, K571, K648, K713, K848, K913, K947, K980, K996, K1001, K1005, K1008, K1013], [K1024, K1028, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 570, 575, false, false⟩

theorem V324_ok : V324.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V324_fin : V324.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V324_V : V324.V where
  ok := V324_ok
  fin := V324_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K996_chk, List.forall_mem_cons.2 ⟨K1001_chk, List.forall_mem_cons.2 ⟨K1005_chk, List.forall_mem_cons.2 ⟨K1008_chk, List.forall_mem_cons.2 ⟨K1013_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1024_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V325 : UnitD := ⟨994625000001, 124999999, [K7, K276, K425, K571, K648, K713, K848, K914, K980, K996, K1002, K1009, K1014], [K1023, K1025, K1027, K1036, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 571, 575, false, false⟩

theorem V325_ok : V325.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V325_fin : V325.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V325_V : V325.V where
  ok := V325_ok
  fin := V325_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K996_chk, List.forall_mem_cons.2 ⟨K1002_chk, List.forall_mem_cons.2 ⟨K1009_chk, List.forall_mem_cons.2 ⟨K1014_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1023_chk, List.forall_mem_cons.2 ⟨K1025_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V326 : UnitD := ⟨994812499999, 62499999, [K7, K276, K425, K571, K648, K713, K848, K914, K980, K996, K1002, K1009, K1014, K1016], [K1025, K1027, K1036, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 572, 576, false, false⟩

theorem V326_ok : V326.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V326_fin : V326.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V326_V : V326.V where
  ok := V326_ok
  fin := V326_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K996_chk, List.forall_mem_cons.2 ⟨K1002_chk, List.forall_mem_cons.2 ⟨K1009_chk, List.forall_mem_cons.2 ⟨K1014_chk, List.forall_mem_cons.2 ⟨K1016_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1025_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V327 : UnitD := ⟨994937499999, 62500001, [K7, K276, K425, K571, K648, K713, K848, K914, K980, K997, K1009, K1014, K1016, K1018, K1019], [K1025, K1027, K1036, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 574, 576, false, false⟩

theorem V327_ok : V327.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V327_fin : V327.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V327_V : V327.V where
  ok := V327_ok
  fin := V327_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1009_chk, List.forall_mem_cons.2 ⟨K1014_chk, List.forall_mem_cons.2 ⟨K1016_chk, List.forall_mem_cons.2 ⟨K1018_chk, List.forall_mem_cons.2 ⟨K1019_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1025_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V328 : UnitD := ⟨995125000001, 125000001, [K7, K276, K425, K571, K648, K713, K848, K914, K980, K997, K1009, K1014, K1016, K1018, K1019], [K1029, K1031, K1036, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 574, 579, false, false⟩

theorem V328_ok : V328.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V328_fin : V328.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V328_V : V328.V where
  ok := V328_ok
  fin := V328_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1009_chk, List.forall_mem_cons.2 ⟨K1014_chk, List.forall_mem_cons.2 ⟨K1016_chk, List.forall_mem_cons.2 ⟨K1018_chk, List.forall_mem_cons.2 ⟨K1019_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1029_chk, List.forall_mem_cons.2 ⟨K1031_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V329 : UnitD := ⟨995375000001, 124999999, [K7, K276, K425, K571, K648, K713, K848, K914, K980, K997, K1009, K1015, K1019, K1022], [K1029, K1030, K1032, K1036, K1046], [K1117, K1119, K1124, K1135, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 575, 579, false, false⟩

theorem V329_ok : V329.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V329_fin : V329.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V329_V : V329.V where
  ok := V329_ok
  fin := V329_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1009_chk, List.forall_mem_cons.2 ⟨K1015_chk, List.forall_mem_cons.2 ⟨K1019_chk, List.forall_mem_cons.2 ⟨K1022_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1029_chk, List.forall_mem_cons.2 ⟨K1030_chk, List.forall_mem_cons.2 ⟨K1032_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1135_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V330 : UnitD := ⟨995667389443, 167389443, [K7, K276, K425, K571, K648, K713, K848, K914, K980, K997, K1010, K1020], [K1033, K1035, K1039, K1045, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 575, 582, false, false⟩

theorem V330_ok : V330.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V330_fin : V330.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V330_V : V330.V where
  ok := V330_ok
  fin := V330_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K980_chk, List.forall_mem_cons.2 ⟨K997_chk, List.forall_mem_cons.2 ⟨K1010_chk, List.forall_mem_cons.2 ⟨K1020_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1033_chk, List.forall_mem_cons.2 ⟨K1035_chk, List.forall_mem_cons.2 ⟨K1039_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def L10 : List UnitD := [V301, V302, V303, V304, V305, V306, V307, V308, V309, V310, V311, V312, V313, V314, V315, V316, V317, V318, V319, V320, V321, V322, V323, V324, V325, V326, V327, V328, V329, V330]

theorem L10_V : ∀ u ∈ L10, u.V :=
  List.forall_mem_cons.2 ⟨V301_V, List.forall_mem_cons.2 ⟨V302_V, List.forall_mem_cons.2 ⟨V303_V, List.forall_mem_cons.2 ⟨V304_V, List.forall_mem_cons.2 ⟨V305_V, List.forall_mem_cons.2 ⟨V306_V, List.forall_mem_cons.2 ⟨V307_V, List.forall_mem_cons.2 ⟨V308_V, List.forall_mem_cons.2 ⟨V309_V, List.forall_mem_cons.2 ⟨V310_V, List.forall_mem_cons.2 ⟨V311_V, List.forall_mem_cons.2 ⟨V312_V, List.forall_mem_cons.2 ⟨V313_V, List.forall_mem_cons.2 ⟨V314_V, List.forall_mem_cons.2 ⟨V315_V, List.forall_mem_cons.2 ⟨V316_V, List.forall_mem_cons.2 ⟨V317_V, List.forall_mem_cons.2 ⟨V318_V, List.forall_mem_cons.2 ⟨V319_V, List.forall_mem_cons.2 ⟨V320_V, List.forall_mem_cons.2 ⟨V321_V, List.forall_mem_cons.2 ⟨V322_V, List.forall_mem_cons.2 ⟨V323_V, List.forall_mem_cons.2 ⟨V324_V, List.forall_mem_cons.2 ⟨V325_V, List.forall_mem_cons.2 ⟨V326_V, List.forall_mem_cons.2 ⟨V327_V, List.forall_mem_cons.2 ⟨V328_V, List.forall_mem_cons.2 ⟨V329_V, List.forall_mem_cons.2 ⟨V330_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
