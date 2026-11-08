module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V361 : UnitD := ⟨999664198869, 20612659, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1071, K1074, K1076], [K1088, K1091, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 607, 612, false, false⟩

theorem V361_ok : V361.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V361_fin : V361.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V361_V : V361.V where
  ok := V361_ok
  fin := V361_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1071_chk, List.forall_mem_cons.2 ⟨K1074_chk, List.forall_mem_cons.2 ⟨K1076_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1088_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V362 : UnitD := ⟨999703039985, 18228457, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1071, K1074, K1077], [K1090, K1094, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 608, 613, false, false⟩

theorem V362_ok : V362.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V362_fin : V362.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V362_V : V362.V where
  ok := V362_ok
  fin := V362_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1071_chk, List.forall_mem_cons.2 ⟨K1074_chk, List.forall_mem_cons.2 ⟨K1077_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1090_chk, List.forall_mem_cons.2 ⟨K1094_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V363 : UnitD := ⟨999737388465, 16120023, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1071, K1075, K1079], [K1092, K1094, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 609, 614, false, false⟩

theorem V363_ok : V363.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V363_fin : V363.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V363_V : V363.V where
  ok := V363_ok
  fin := V363_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1071_chk, List.forall_mem_cons.2 ⟨K1075_chk, List.forall_mem_cons.2 ⟨K1079_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1092_chk, List.forall_mem_cons.2 ⟨K1094_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V364 : UnitD := ⟨999767763957, 14255469, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1071, K1075, K1080], [K1094, K1100], [K1117, K1119, K1123, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 610, 615, false, false⟩

theorem V364_ok : V364.ok = true := by
  -- kcost: 0.2 s measured mean, 32 pairs, 6 Nov
  decide +kernel

theorem V364_fin : V364.fin = true := by
  -- kcost: 1.4 s measured mean, 32 pair polynomials, 6 Nov
  decide +kernel

theorem V364_V : V364.V where
  ok := V364_ok
  fin := V364_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1071_chk, List.forall_mem_cons.2 ⟨K1075_chk, List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1094_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1123_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V365 : UnitD := ⟨999794626009, 12606583, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1080, K1084], [K1096, K1100], [K1117, K1119, K1122, K1129, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 611, 616, false, false⟩

theorem V365_ok : V365.ok = true := by
  -- kcost: 0.2 s measured mean, 33 pairs, 6 Nov
  decide +kernel

theorem V365_fin : V365.fin = true := by
  -- kcost: 1.4 s measured mean, 33 pair polynomials, 6 Nov
  decide +kernel

theorem V365_V : V365.V where
  ok := V365_ok
  fin := V365_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_cons.2 ⟨K1084_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1096_chk, List.forall_mem_cons.2 ⟨K1100_chk, List.forall_mem_nil _⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V366 : UnitD := ⟨999818381007, 11148415, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1080, K1084, K1086], [K1097, K1099, K1109], [K1117, K1119, K1122, K1129, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 612, 617, false, false⟩

theorem V366_ok : V366.ok = true := by
  -- kcost: 0.2 s measured mean, 35 pairs, 6 Nov
  decide +kernel

theorem V366_fin : V366.fin = true := by
  -- kcost: 1.4 s measured mean, 35 pair polynomials, 6 Nov
  decide +kernel

theorem V366_V : V366.V where
  ok := V366_ok
  fin := V366_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_cons.2 ⟨K1084_chk, List.forall_mem_cons.2 ⟨K1086_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1097_chk, List.forall_mem_cons.2 ⟨K1099_chk, List.forall_mem_cons.2 ⟨K1109_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V367 : UnitD := ⟨999839388335, 9858913, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1080, K1084, K1087], [K1098, K1103, K1109], [K1117, K1119, K1122, K1129, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 613, 618, false, false⟩

theorem V367_ok : V367.ok = true := by
  -- kcost: 0.2 s measured mean, 35 pairs, 6 Nov
  decide +kernel

theorem V367_fin : V367.fin = true := by
  -- kcost: 1.4 s measured mean, 35 pair polynomials, 6 Nov
  decide +kernel

theorem V367_V : V367.V where
  ok := V367_ok
  fin := V367_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_cons.2 ⟨K1084_chk, List.forall_mem_cons.2 ⟨K1087_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1109_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V368 : UnitD := ⟨999857965809, 8718561, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1080, K1085, K1089], [K1101, K1103, K1109], [K1117, K1119, K1122, K1129, K1132, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 614, 619, false, false⟩

theorem V368_ok : V368.ok = true := by
  -- kcost: 0.2 s measured mean, 35 pairs, 6 Nov
  decide +kernel

theorem V368_fin : V368.fin = true := by
  -- kcost: 1.4 s measured mean, 35 pair polynomials, 6 Nov
  decide +kernel

theorem V368_V : V368.V where
  ok := V368_ok
  fin := V368_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_cons.2 ⟨K1085_chk, List.forall_mem_cons.2 ⟨K1089_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1101_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1109_chk, List.forall_mem_nil _⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1132_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V369 : UnitD := ⟨999874394481, 7710111, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1080, K1085, K1090], [K1103, K1109], [K1117, K1119, K1122, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 615, 620, false, false⟩

theorem V369_ok : V369.ok = true := by
  -- kcost: 0.2 s measured mean, 35 pairs, 6 Nov
  decide +kernel

theorem V369_fin : V369.fin = true := by
  -- kcost: 1.4 s measured mean, 35 pair polynomials, 6 Nov
  decide +kernel

theorem V369_V : V369.V where
  ok := V369_ok
  fin := V369_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_cons.2 ⟨K1085_chk, List.forall_mem_cons.2 ⟨K1090_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1109_chk, List.forall_mem_nil _⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V370 : UnitD := ⟨999894952549, 12847957, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1080, K1085, K1090, K1093], [K1106, K1109], [K1117, K1119, K1122, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 616, 622, false, false⟩

theorem V370_ok : V370.ok = true := by
  -- kcost: 0.2 s measured mean, 36 pairs, 6 Nov
  decide +kernel

theorem V370_fin : V370.fin = true := by
  -- kcost: 1.4 s measured mean, 36 pair polynomials, 6 Nov
  decide +kernel

theorem V370_V : V370.V where
  ok := V370_ok
  fin := V370_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1080_chk, List.forall_mem_cons.2 ⟨K1085_chk, List.forall_mem_cons.2 ⟨K1090_chk, List.forall_mem_cons.2 ⟨K1093_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1106_chk, List.forall_mem_cons.2 ⟨K1109_chk, List.forall_mem_nil _⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V371 : UnitD := ⟨999917848183, 10047677, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1090, K1093, K1095, K1097], [K1110, K1112], [K1117, K1119, K1122, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 618, 624, false, false⟩

theorem V371_ok : V371.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V371_fin : V371.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V371_V : V371.V where
  ok := V371_ok
  fin := V371_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1090_chk, List.forall_mem_cons.2 ⟨K1093_chk, List.forall_mem_cons.2 ⟨K1095_chk, List.forall_mem_cons.2 ⟨K1097_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1110_chk, List.forall_mem_cons.2 ⟨K1112_chk, List.forall_mem_nil _⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V372 : UnitD := ⟨999932065895, 4170035, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1090, K1094, K1098], [K1112], [K1117, K1119, K1122, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 620, 625, false, false⟩

theorem V372_ok : V372.ok = true := by
  -- kcost: 0.2 s measured mean, 35 pairs, 6 Nov
  decide +kernel

theorem V372_fin : V372.fin = true := by
  -- kcost: 1.4 s measured mean, 35 pair polynomials, 6 Nov
  decide +kernel

theorem V372_V : V372.V where
  ok := V372_ok
  fin := V372_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1090_chk, List.forall_mem_cons.2 ⟨K1094_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1112_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V373 : UnitD := ⟨999939923631, 3687701, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1102], [K1114], [K1117, K1119, K1122, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 621, 626, false, false⟩

theorem V373_ok : V373.ok = true := by
  -- kcost: 0.2 s measured mean, 35 pairs, 6 Nov
  decide +kernel

theorem V373_fin : V373.fin = true := by
  -- kcost: 1.4 s measured mean, 35 pair polynomials, 6 Nov
  decide +kernel

theorem V373_V : V373.V where
  ok := V373_ok
  fin := V373_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1102_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1114_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1122_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V374 : UnitD := ⟨999946872485, 3261153, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1102, K1104], [K1115], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 622, 627, false, false⟩

theorem V374_ok : V374.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V374_fin : V374.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V374_V : V374.V where
  ok := V374_ok
  fin := V374_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1102_chk, List.forall_mem_cons.2 ⟨K1104_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1115_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V375 : UnitD := ⟨999951575613, 1441975, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1102, K1105, K1107], [K1115], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 624, 627, false, false⟩

theorem V375_ok : V375.ok = true := by
  -- kcost: 0.2 s measured mean, 38 pairs, 6 Nov
  decide +kernel

theorem V375_fin : V375.fin = true := by
  -- kcost: 1.4 s measured mean, 38 pair polynomials, 6 Nov
  decide +kernel

theorem V375_V : V375.V where
  ok := V375_ok
  fin := V375_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1102_chk, List.forall_mem_cons.2 ⟨K1105_chk, List.forall_mem_cons.2 ⟨K1107_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1115_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V376 : UnitD := ⟨999954459561, 1441973, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1107], [K1115], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 624, 627, false, false⟩

theorem V376_ok : V376.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V376_fin : V376.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V376_V : V376.V where
  ok := V376_ok
  fin := V376_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1107_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1115_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V377 : UnitD := ⟨999956220329, 318795, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1107, K1110], [K1115], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 625, 627, false, false⟩

theorem V377_ok : V377.ok = true := by
  -- kcost: 0.2 s measured mean, 38 pairs, 6 Nov
  decide +kernel

theorem V377_fin : V377.fin = true := by
  -- kcost: 1.4 s measured mean, 38 pair polynomials, 6 Nov
  decide +kernel

theorem V377_V : V377.V where
  ok := V377_ok
  fin := V377_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1107_chk, List.forall_mem_cons.2 ⟨K1110_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1115_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V378 : UnitD := ⟨999956857921, 318797, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1107, K1110], [K1115], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 625, 627, false, false⟩

theorem V378_ok : V378.ok = true := by
  -- kcost: 0.2 s measured mean, 38 pairs, 6 Nov
  decide +kernel

theorem V378_fin : V378.fin = true := by
  -- kcost: 1.4 s measured mean, 38 pair polynomials, 6 Nov
  decide +kernel

theorem V378_V : V378.V where
  ok := V378_ok
  fin := V378_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1107_chk, List.forall_mem_cons.2 ⟨K1110_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K1115_chk, List.forall_mem_nil _⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V379 : UnitD := ⟨999957814309, 637591, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1107, K1110], [], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 625, 628, false, false⟩

theorem V379_ok : V379.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V379_fin : V379.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V379_V : V379.V where
  ok := V379_ok
  fin := V379_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1107_chk, List.forall_mem_cons.2 ⟨K1110_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V380 : UnitD := ⟨999959727085, 1275185, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1108], [], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 625, 628, false, false⟩

theorem V380_ok : V380.ok = true := by
  -- kcost: 0.2 s measured mean, 36 pairs, 6 Nov
  decide +kernel

theorem V380_fin : V380.fin = true := by
  -- kcost: 1.4 s measured mean, 36 pair polynomials, 6 Nov
  decide +kernel

theorem V380_V : V380.V where
  ok := V380_ok
  fin := V380_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1108_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V381 : UnitD := ⟨999962129957, 1127687, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1108, K1111], [], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 626, 628, false, false⟩

theorem V381_ok : V381.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V381_fin : V381.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V381_V : V381.V where
  ok := V381_ok
  fin := V381_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1108_chk, List.forall_mem_cons.2 ⟨K1111_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V382 : UnitD := ⟨999964385333, 1127689, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1108, K1111], [], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 626, 628, false, false⟩

theorem V382_ok : V382.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V382_fin : V382.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V382_V : V382.V where
  ok := V382_ok
  fin := V382_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1108_chk, List.forall_mem_cons.2 ⟨K1111_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V383 : UnitD := ⟨999969823893, 4310871, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1098, K1103, K1108, K1111], [], [K1117, K1119, K1121, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 626, 628, false, false⟩

theorem V383_ok : V383.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V383_fin : V383.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V383_V : V383.V where
  ok := V383_ok
  fin := V383_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1098_chk, List.forall_mem_cons.2 ⟨K1103_chk, List.forall_mem_cons.2 ⟨K1108_chk, List.forall_mem_cons.2 ⟨K1111_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1121_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V384 : UnitD := ⟨999980601073, 6466309, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1099, K1108, K1111, K1113], [], [K1117, K1119, K1120, K1126, K1127, K1129, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 627, 628, false, false⟩

theorem V384_ok : V384.ok = true := by
  -- kcost: 0.2 s measured mean, 38 pairs, 6 Nov
  decide +kernel

theorem V384_fin : V384.fin = true := by
  -- kcost: 1.4 s measured mean, 38 pair polynomials, 6 Nov
  decide +kernel

theorem V384_V : V384.V where
  ok := V384_ok
  fin := V384_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1099_chk, List.forall_mem_cons.2 ⟨K1108_chk, List.forall_mem_cons.2 ⟨K1111_chk, List.forall_mem_cons.2 ⟨K1113_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1120_chk, List.forall_mem_cons.2 ⟨K1126_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1129_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V385 : UnitD := ⟨999993533691, 6466309, [K7, K276, K425, K571, K648, K713, K848, K914, K981, K1012, K1045, K1062, K1072, K1081, K1091, K1099, K1109], [], [K1117, K1119, K1120, K1126, K1127, K1128, K1130, K1131, K1133, K1134, K1136, K1138, K1139, K1143, K1144, K1145, K1147, K1148, K1150, K1151], 628, 628, false, true⟩

theorem V385_ok : V385.ok = true := by
  -- kcost: 0.2 s measured mean, 37 pairs, 6 Nov
  decide +kernel

theorem V385_fin : V385.fin = true := by
  -- kcost: 1.4 s measured mean, 37 pair polynomials, 6 Nov
  decide +kernel

theorem V385_V : V385.V where
  ok := V385_ok
  fin := V385_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K981_chk, List.forall_mem_cons.2 ⟨K1012_chk, List.forall_mem_cons.2 ⟨K1045_chk, List.forall_mem_cons.2 ⟨K1062_chk, List.forall_mem_cons.2 ⟨K1072_chk, List.forall_mem_cons.2 ⟨K1081_chk, List.forall_mem_cons.2 ⟨K1091_chk, List.forall_mem_cons.2 ⟨K1099_chk, List.forall_mem_cons.2 ⟨K1109_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1120_chk, List.forall_mem_cons.2 ⟨K1126_chk, List.forall_mem_cons.2 ⟨K1127_chk, List.forall_mem_cons.2 ⟨K1128_chk, List.forall_mem_cons.2 ⟨K1130_chk, List.forall_mem_cons.2 ⟨K1131_chk, List.forall_mem_cons.2 ⟨K1133_chk, List.forall_mem_cons.2 ⟨K1134_chk, List.forall_mem_cons.2 ⟨K1136_chk, List.forall_mem_cons.2 ⟨K1138_chk, List.forall_mem_cons.2 ⟨K1139_chk, List.forall_mem_cons.2 ⟨K1143_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def L12 : List UnitD := [V361, V362, V363, V364, V365, V366, V367, V368, V369, V370, V371, V372, V373, V374, V375, V376, V377, V378, V379, V380, V381, V382, V383, V384]

theorem L12_V : ∀ u ∈ L12, u.V :=
  List.forall_mem_cons.2 ⟨V361_V, List.forall_mem_cons.2 ⟨V362_V, List.forall_mem_cons.2 ⟨V363_V, List.forall_mem_cons.2 ⟨V364_V, List.forall_mem_cons.2 ⟨V365_V, List.forall_mem_cons.2 ⟨V366_V, List.forall_mem_cons.2 ⟨V367_V, List.forall_mem_cons.2 ⟨V368_V, List.forall_mem_cons.2 ⟨V369_V, List.forall_mem_cons.2 ⟨V370_V, List.forall_mem_cons.2 ⟨V371_V, List.forall_mem_cons.2 ⟨V372_V, List.forall_mem_cons.2 ⟨V373_V, List.forall_mem_cons.2 ⟨V374_V, List.forall_mem_cons.2 ⟨V375_V, List.forall_mem_cons.2 ⟨V376_V, List.forall_mem_cons.2 ⟨V377_V, List.forall_mem_cons.2 ⟨V378_V, List.forall_mem_cons.2 ⟨V379_V, List.forall_mem_cons.2 ⟨V380_V, List.forall_mem_cons.2 ⟨V381_V, List.forall_mem_cons.2 ⟨V382_V, List.forall_mem_cons.2 ⟨V383_V, List.forall_mem_cons.2 ⟨V384_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
