module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V331 : UnitD := ⟨995917389443, 82610557, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1010, K1020, K1024], [K1033, K1035, K1039, K1045, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 578, 582, false, false⟩

theorem V331_ok : V331.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V331_fin : V331.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V331_V : V331.V where
  ok := V331_ok
  fin := V331_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1010_chk, List.forall_mem_cons.2 ⟨K1020_chk, List.forall_mem_cons.2 ⟨K1024_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1033_chk, List.forall_mem_cons.2 ⟨K1035_chk, List.forall_mem_cons.2 ⟨K1039_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V332 : UnitD := ⟨996125000001, 125000001, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1010, K1020, K1024], [K1037, K1039, K1044, K1053, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 578, 584, false, false⟩

theorem V332_ok : V332.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V332_fin : V332.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V332_V : V332.V where
  ok := V332_ok
  fin := V332_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1010_chk, List.forall_mem_cons.2 ⟨K1020_chk, List.forall_mem_cons.2 ⟨K1024_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1037_chk, List.forall_mem_cons.2 ⟨K1039_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V333 : UnitD := ⟨996375000001, 124999999, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1010, K1021, K1026, K1030], [K1038, K1040, K1041, K1044, K1053, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 581, 585, false, false⟩

theorem V333_ok : V333.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V333_fin : V333.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V333_V : V333.V where
  ok := V333_ok
  fin := V333_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1010_chk, List.forall_mem_cons.2 ⟨K1021_chk, List.forall_mem_cons.2 ⟨K1026_chk, List.forall_mem_cons.2 ⟨K1030_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1038_chk, List.forall_mem_cons.2 ⟨K1040_chk, List.forall_mem_cons.2 ⟨K1041_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V334 : UnitD := ⟨996625000001, 125000001, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1010, K1021, K1026, K1030], [K1041, K1043, K1049, K1053, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 581, 587, false, false⟩

theorem V334_ok : V334.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V334_fin : V334.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V334_V : V334.V where
  ok := V334_ok
  fin := V334_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1010_chk, List.forall_mem_cons.2 ⟨K1021_chk, List.forall_mem_cons.2 ⟨K1026_chk, List.forall_mem_cons.2 ⟨K1030_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1041_chk, List.forall_mem_cons.2 ⟨K1043_chk, List.forall_mem_cons.2 ⟨K1049_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V335 : UnitD := ⟨996875000001, 124999999, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1026, K1031, K1034], [K1047, K1049, K1053, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 584, 589, false, false⟩

theorem V335_ok : V335.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V335_fin : V335.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V335_V : V335.V where
  ok := V335_ok
  fin := V335_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1026_chk, List.forall_mem_cons.2 ⟨K1031_chk, List.forall_mem_cons.2 ⟨K1034_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1047_chk, List.forall_mem_cons.2 ⟨K1049_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V336 : UnitD := ⟨997059691473, 59691473, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1034, K1037, K1038], [K1049, K1053, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 586, 590, false, false⟩

theorem V336_ok : V336.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V336_fin : V336.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V336_V : V336.V where
  ok := V336_ok
  fin := V336_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1034_chk, List.forall_mem_cons.2 ⟨K1037_chk, List.forall_mem_cons.2 ⟨K1038_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1049_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V337 : UnitD := ⟨997184691473, 65308527, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1035, K1038], [K1048, K1050, K1052, K1056, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 586, 590, false, false⟩

theorem V337_ok : V337.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V337_fin : V337.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V337_V : V337.V where
  ok := V337_ok
  fin := V337_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1035_chk, List.forall_mem_cons.2 ⟨K1038_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1048_chk, List.forall_mem_cons.2 ⟨K1050_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_cons.2 ⟨K1056_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V338 : UnitD := ⟨997351287667, 101287667, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1035, K1038, K1040], [K1051, K1052, K1056, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 587, 592, false, false⟩

theorem V338_ok : V338.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V338_fin : V338.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V338_V : V338.V where
  ok := V338_ok
  fin := V338_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1035_chk, List.forall_mem_cons.2 ⟨K1038_chk, List.forall_mem_cons.2 ⟨K1040_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1051_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_cons.2 ⟨K1056_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V339 : UnitD := ⟨997476287667, 23712333, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1035, K1039, K1042], [K1051, K1052, K1056, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 589, 592, false, false⟩

theorem V339_ok : V339.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V339_fin : V339.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V339_V : V339.V where
  ok := V339_ok
  fin := V339_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1035_chk, List.forall_mem_cons.2 ⟨K1039_chk, List.forall_mem_cons.2 ⟨K1042_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1051_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_cons.2 ⟨K1056_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V340 : UnitD := ⟨997623614177, 123614177, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1035, K1039, K1042], [K1054, K1055, K1058, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 589, 594, false, false⟩

theorem V340_ok : V340.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V340_fin : V340.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V340_V : V340.V where
  ok := V340_ok
  fin := V340_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1035_chk, List.forall_mem_cons.2 ⟨K1039_chk, List.forall_mem_cons.2 ⟨K1042_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1054_chk, List.forall_mem_cons.2 ⟨K1055_chk, List.forall_mem_cons.2 ⟨K1058_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V341 : UnitD := ⟨997748614177, 1385823, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1036, K1043, K1048], [K1054, K1055, K1058, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 591, 594, false, false⟩

theorem V341_ok : V341.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V341_fin : V341.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V341_V : V341.V where
  ok := V341_ok
  fin := V341_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1043_chk, List.forall_mem_cons.2 ⟨K1048_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1054_chk, List.forall_mem_cons.2 ⟨K1055_chk, List.forall_mem_cons.2 ⟨K1058_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V342 : UnitD := ⟨997812499999, 62499999, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1036, K1043, K1048], [K1058, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 591, 596, false, false⟩

theorem V342_ok : V342.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V342_fin : V342.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V342_V : V342.V where
  ok := V342_ok
  fin := V342_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1043_chk, List.forall_mem_cons.2 ⟨K1048_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1058_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V343 : UnitD := ⟨997937499999, 62500001, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1027, K1036, K1043, K1048], [K1057, K1059, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 591, 596, false, false⟩

theorem V343_ok : V343.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V343_fin : V343.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V343_V : V343.V where
  ok := V343_ok
  fin := V343_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1027_chk, List.forall_mem_cons.2 ⟨K1036_chk, List.forall_mem_cons.2 ⟨K1043_chk, List.forall_mem_cons.2 ⟨K1048_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1057_chk, List.forall_mem_cons.2 ⟨K1059_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V344 : UnitD := ⟨998003899867, 3899867, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1043, K1049], [K1058, K1063, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 593, 596, false, false⟩

theorem V344_ok : V344.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V344_fin : V344.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V344_V : V344.V where
  ok := V344_ok
  fin := V344_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1043_chk, List.forall_mem_cons.2 ⟨K1049_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1058_chk, List.forall_mem_cons.2 ⟨K1063_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V345 : UnitD := ⟨998065407699, 57607965, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1043, K1049], [K1059, K1062, K1072, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 593, 597, false, false⟩

theorem V345_ok : V345.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V345_fin : V345.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V345_V : V345.V where
  ok := V345_ok
  fin := V345_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1043_chk, List.forall_mem_cons.2 ⟨K1049_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1059_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V346 : UnitD := ⟨998180623633, 57607969, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1044], [K1059, K1062, K1072, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 593, 597, false, false⟩

theorem V346_ok : V346.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V346_fin : V346.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V346_V : V346.V where
  ok := V346_ok
  fin := V346_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1059_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V347 : UnitD := ⟨998289176225, 50944623, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1044, K1052], [K1061, K1066, K1072, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 595, 598, false, false⟩

theorem V347_ok : V347.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V347_fin : V347.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V347_V : V347.V where
  ok := V347_ok
  fin := V347_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1061_chk, List.forall_mem_cons.2 ⟨K1066_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V348 : UnitD := ⟨998391065475, 50944627, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1044, K1052], [K1060, K1064, K1066, K1072, K1082], [K1117, K1119, K1124, K1134, K1137, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 595, 598, false, false⟩

theorem V348_ok : V348.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V348_fin : V348.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V348_V : V348.V where
  ok := V348_ok
  fin := V348_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1060_chk, List.forall_mem_cons.2 ⟨K1064_chk, List.forall_mem_cons.2 ⟨K1066_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1137_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V349 : UnitD := ⟨998532114125, 90104023, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1044, K1052], [K1066, K1072, K1082], [K1117, K1119, K1124, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 595, 600, false, false⟩

theorem V349_ok : V349.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V349_fin : V349.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V349_V : V349.V where
  ok := V349_ok
  fin := V349_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1066_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V350 : UnitD := ⟨998701900109, 79681961, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1044, K1052, K1055], [K1068, K1072, K1082], [K1117, K1119, K1124, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 596, 601, false, false⟩

theorem V350_ok : V350.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V350_fin : V350.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V350_V : V350.V where
  ok := V350_ok
  fin := V350_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_cons.2 ⟨K1055_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1068_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V351 : UnitD := ⟨998852047455, 70465385, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1011, K1028, K1044, K1052, K1055, K1057], [K1069, K1072, K1082], [K1117, K1119, K1124, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 597, 602, false, false⟩

theorem V351_ok : V351.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V351_fin : V351.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V351_V : V351.V where
  ok := V351_ok
  fin := V351_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1011_chk, List.forall_mem_cons.2 ⟨K1028_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_cons.2 ⟨K1055_chk, List.forall_mem_cons.2 ⟨K1057_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1069_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V352 : UnitD := ⟨998984827703, 62314863, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1044, K1052, K1055, K1058], [K1071, K1075, K1082], [K1117, K1119, K1124, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 598, 603, false, false⟩

theorem V352_ok : V352.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V352_fin : V352.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V352_V : V352.V where
  ok := V352_ok
  fin := V352_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_cons.2 ⟨K1055_chk, List.forall_mem_cons.2 ⟨K1058_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1071_chk, List.forall_mem_cons.2 ⟨K1075_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V353 : UnitD := ⟨999102249657, 55107091, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1044, K1052, K1056, K1060], [K1073, K1075, K1082], [K1117, K1119, K1124, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 599, 604, false, false⟩

theorem V353_ok : V353.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V353_fin : V353.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V353_V : V353.V where
  ok := V353_ok
  fin := V353_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1052_chk, List.forall_mem_cons.2 ⟨K1056_chk, List.forall_mem_cons.2 ⟨K1060_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1073_chk, List.forall_mem_cons.2 ⟨K1075_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1124_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V354 : UnitD := ⟨999206089765, 48733017, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1044, K1053, K1061], [K1075, K1082], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 600, 605, false, false⟩

theorem V354_ok : V354.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V354_fin : V354.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V354_V : V354.V where
  ok := V354_ok
  fin := V354_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1061_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1075_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V355 : UnitD := ⟨999297918995, 43096213, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1044, K1053, K1061, K1065], [K1077, K1082], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 601, 606, false, false⟩

theorem V355_ok : V355.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V355_fin : V355.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V355_V : V355.V where
  ok := V355_ok
  fin := V355_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1061_chk, List.forall_mem_cons.2 ⟨K1065_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1077_chk, List.forall_mem_cons.2 ⟨K1082_chk, List.forall_mem_nil _⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V356 : UnitD := ⟨999379126611, 38111403, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1044, K1053, K1061, K1065, K1067], [K1078, K1081, K1091, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 602, 607, false, false⟩

theorem V356_ok : V356.ok = true := by
  -- kcost: 0.2 s measured mean, 34 pairs, 6 Nov
  decide +kernel

theorem V356_fin : V356.fin = true := by
  -- kcost: 1.4 s measured mean, 34 pair polynomials, 6 Nov
  decide +kernel

theorem V356_V : V356.V where
  ok := V356_ok
  fin := V356_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1044_chk, List.forall_mem_cons.2 ⟨K1053_chk, List.forall_mem_cons.2 ⟨K1061_chk, List.forall_mem_cons.2 ⟨K1065_chk, List.forall_mem_cons.2 ⟨K1067_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1078_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V357 : UnitD := ⟨999450941185, 33703171, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1061, K1065, K1068], [K1080, K1085, K1091, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 603, 608, false, false⟩

theorem V357_ok : V357.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V357_fin : V357.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V357_V : V357.V where
  ok := V357_ok
  fin := V357_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1061_chk, List.forall_mem_cons.2 ⟨K1065_chk, List.forall_mem_cons.2 ⟨K1068_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_cons.2 ⟨K1085_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V358 : UnitD := ⟨999514449183, 29804827, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1061, K1066, K1070], [K1083, K1085, K1091, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 604, 609, false, false⟩

theorem V358_ok : V358.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V358_fin : V358.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V358_V : V358.V where
  ok := V358_ok
  fin := V358_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1061_chk, List.forall_mem_cons.2 ⟨K1066_chk, List.forall_mem_cons.2 ⟨K1070_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1083_chk, List.forall_mem_cons.2 ⟨K1085_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V359 : UnitD := ⟨999570611399, 26357389, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1061, K1066, K1071], [K1085, K1091, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 605, 610, false, false⟩

theorem V359_ok : V359.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V359_fin : V359.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V359_V : V359.V where
  ok := V359_ok
  fin := V359_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1061_chk, List.forall_mem_cons.2 ⟨K1066_chk, List.forall_mem_cons.2 ⟨K1071_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1085_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V360 : UnitD := ⟨999620277499, 23308711, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1071, K1074], [K1087, K1091, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 606, 611, false, false⟩

theorem V360_ok : V360.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V360_fin : V360.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V360_V : V360.V where
  ok := V360_ok
  fin := V360_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1071_chk, List.forall_mem_cons.2 ⟨K1074_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1087_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def L11 : List UnitD := [V331, V332, V333, V334, V335, V336, V337, V338, V339, V340, V341, V342, V343, V344, V345, V346, V347, V348, V349, V350, V351, V352, V353, V354, V355, V356, V357, V358, V359, V360]

theorem L11_V : ∀ u ∈ L11, u.V :=
  List.forall_mem_cons.2 ⟨V331_V, List.forall_mem_cons.2 ⟨V332_V, List.forall_mem_cons.2 ⟨V333_V, List.forall_mem_cons.2 ⟨V334_V, List.forall_mem_cons.2 ⟨V335_V, List.forall_mem_cons.2 ⟨V336_V, List.forall_mem_cons.2 ⟨V337_V, List.forall_mem_cons.2 ⟨V338_V, List.forall_mem_cons.2 ⟨V339_V, List.forall_mem_cons.2 ⟨V340_V, List.forall_mem_cons.2 ⟨V341_V, List.forall_mem_cons.2 ⟨V342_V, List.forall_mem_cons.2 ⟨V343_V, List.forall_mem_cons.2 ⟨V344_V, List.forall_mem_cons.2 ⟨V345_V, List.forall_mem_cons.2 ⟨V346_V, List.forall_mem_cons.2 ⟨V347_V, List.forall_mem_cons.2 ⟨V348_V, List.forall_mem_cons.2 ⟨V349_V, List.forall_mem_cons.2 ⟨V350_V, List.forall_mem_cons.2 ⟨V351_V, List.forall_mem_cons.2 ⟨V352_V, List.forall_mem_cons.2 ⟨V353_V, List.forall_mem_cons.2 ⟨V354_V, List.forall_mem_cons.2 ⟨V355_V, List.forall_mem_cons.2 ⟨V356_V, List.forall_mem_cons.2 ⟨V357_V, List.forall_mem_cons.2 ⟨V358_V, List.forall_mem_cons.2 ⟨V359_V, List.forall_mem_cons.2 ⟨V360_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
