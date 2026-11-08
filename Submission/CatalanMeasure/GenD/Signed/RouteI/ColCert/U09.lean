module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V271 : UnitD := ⟨961302118773, 630476979, [K7, K276, K425, K571, K648, K712, K777, K810, K826, K835, K838, K840], [K858, K861, K866, K881, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 470, 477, false, false⟩

theorem V271_ok : V271.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V271_fin : V271.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V271_V : V271.V where
  ok := V271_ok
  fin := V271_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K826_chk, List.forall_mem_cons.2 ⟨K835_chk, List.forall_mem_cons.2 ⟨K838_chk, List.forall_mem_cons.2 ⟨K840_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K858_chk, List.forall_mem_cons.2 ⟨K861_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V272 : UnitD := ⟨962287193399, 354597647, [K7, K276, K425, K571, K648, K712, K777, K810, K826, K836, K843], [K861, K865, K874, K881, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 472, 478, false, false⟩

theorem V272_ok : V272.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V272_fin : V272.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V272_V : V272.V where
  ok := V272_ok
  fin := V272_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K826_chk, List.forall_mem_cons.2 ⟨K836_chk, List.forall_mem_cons.2 ⟨K843_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K861_chk, List.forall_mem_cons.2 ⟨K865_chk, List.forall_mem_cons.2 ⟨K874_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V273 : UnitD := ⟨963298507465, 656716419, [K7, K276, K425, K571, K648, K712, K777, K810, K826, K836, K844], [K864, K869, K874, K881, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 473, 480, false, false⟩

theorem V273_ok : V273.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V273_fin : V273.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V273_V : V273.V where
  ok := V273_ok
  fin := V273_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K826_chk, List.forall_mem_cons.2 ⟨K836_chk, List.forall_mem_cons.2 ⟨K844_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K864_chk, List.forall_mem_cons.2 ⟨K869_chk, List.forall_mem_cons.2 ⟨K874_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V274 : UnitD := ⟨964611940301, 656716417, [K7, K276, K425, K571, K648, K712, K777, K810, K827, K845, K854], [K868, K870, K871, K874, K880, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 476, 482, false, false⟩

theorem V274_ok : V274.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V274_fin : V274.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V274_V : V274.V where
  ok := V274_ok
  fin := V274_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K845_chk, List.forall_mem_cons.2 ⟨K854_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K868_chk, List.forall_mem_cons.2 ⟨K870_chk, List.forall_mem_cons.2 ⟨K871_chk, List.forall_mem_cons.2 ⟨K874_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V275 : UnitD := ⟨965802197827, 533541109, [K7, K276, K425, K571, K648, K712, K777, K810, K827, K845, K855, K858], [K871, K873, K876, K880, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 478, 484, false, false⟩

theorem V275_ok : V275.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V275_fin : V275.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V275_V : V275.V where
  ok := V275_ok
  fin := V275_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K845_chk, List.forall_mem_cons.2 ⟨K855_chk, List.forall_mem_cons.2 ⟨K858_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K871_chk, List.forall_mem_cons.2 ⟨K873_chk, List.forall_mem_cons.2 ⟨K876_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V276 : UnitD := ⟨966787272453, 451533517, [K7, K276, K425, K571, K648, K712, K777, K810, K827, K845, K855, K858, K860, K862], [K875, K876, K879, K889, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 480, 486, false, false⟩

theorem V276_ok : V276.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V276_fin : V276.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V276_V : V276.V where
  ok := V276_ok
  fin := V276_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K845_chk, List.forall_mem_cons.2 ⟨K855_chk, List.forall_mem_cons.2 ⟨K858_chk, List.forall_mem_cons.2 ⟨K860_chk, List.forall_mem_cons.2 ⟨K862_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K875_chk, List.forall_mem_cons.2 ⟨K876_chk, List.forall_mem_cons.2 ⟨K879_chk, List.forall_mem_cons.2 ⟨K889_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V277 : UnitD := ⟨967895522389, 656716419, [K7, K276, K425, K571, K648, K712, K777, K811, K845, K855, K859, K863, K867], [K877, K878, K884, K889, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 482, 488, false, false⟩

theorem V277_ok : V277.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V277_fin : V277.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V277_V : V277.V where
  ok := V277_ok
  fin := V277_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K845_chk, List.forall_mem_cons.2 ⟨K855_chk, List.forall_mem_cons.2 ⟨K859_chk, List.forall_mem_cons.2 ⟨K863_chk, List.forall_mem_cons.2 ⟨K867_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K877_chk, List.forall_mem_cons.2 ⟨K878_chk, List.forall_mem_cons.2 ⟨K884_chk, List.forall_mem_cons.2 ⟨K889_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V278 : UnitD := ⟨969208955225, 656716417, [K7, K276, K425, K571, K648, K712, K777, K811, K846, K864, K868, K870], [K882, K884, K889, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 484, 491, false, false⟩

theorem V278_ok : V278.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V278_fin : V278.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V278_V : V278.V where
  ok := V278_ok
  fin := V278_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K864_chk, List.forall_mem_cons.2 ⟨K868_chk, List.forall_mem_cons.2 ⟨K870_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K882_chk, List.forall_mem_cons.2 ⟨K884_chk, List.forall_mem_cons.2 ⟨K889_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V279 : UnitD := ⟨970194029851, 328358209, [K7, K276, K425, K571, K648, K712, K777, K811, K846, K865, K872, K875], [K882, K884, K889, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 487, 491, false, false⟩

theorem V279_ok : V279.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V279_fin : V279.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V279_V : V279.V where
  ok := V279_ok
  fin := V279_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K865_chk, List.forall_mem_cons.2 ⟨K872_chk, List.forall_mem_cons.2 ⟨K875_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K882_chk, List.forall_mem_cons.2 ⟨K884_chk, List.forall_mem_cons.2 ⟨K889_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V280 : UnitD := ⟨971179104479, 656716419, [K7, K276, K425, K571, K648, K712, K777, K811, K846, K865, K872, K875], [K886, K888, K891, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 487, 494, false, false⟩

theorem V280_ok : V280.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V280_fin : V280.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V280_V : V280.V where
  ok := V280_ok
  fin := V280_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K865_chk, List.forall_mem_cons.2 ⟨K872_chk, List.forall_mem_cons.2 ⟨K875_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K886_chk, List.forall_mem_cons.2 ⟨K888_chk, List.forall_mem_cons.2 ⟨K891_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V281 : UnitD := ⟨972492537315, 656716417, [K7, K276, K425, K571, K648, K712, K777, K811, K846, K865, K873, K876], [K890, K893, K897, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 490, 497, false, false⟩

theorem V281_ok : V281.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V281_fin : V281.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V281_V : V281.V where
  ok := V281_ok
  fin := V281_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K865_chk, List.forall_mem_cons.2 ⟨K873_chk, List.forall_mem_cons.2 ⟨K876_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K890_chk, List.forall_mem_cons.2 ⟨K893_chk, List.forall_mem_cons.2 ⟨K897_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V282 : UnitD := ⟨973477611941, 328358209, [K7, K276, K425, K571, K648, K712, K778, K846, K865, K874, K878, K883], [K893, K896, K903, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 493, 498, false, false⟩

theorem V282_ok : V282.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V282_fin : V282.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V282_V : V282.V where
  ok := V282_ok
  fin := V282_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K865_chk, List.forall_mem_cons.2 ⟨K874_chk, List.forall_mem_cons.2 ⟨K878_chk, List.forall_mem_cons.2 ⟨K883_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K893_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V283 : UnitD := ⟨974462686569, 656716419, [K7, K276, K425, K571, K648, K712, K778, K846, K865, K874, K878, K883], [K895, K899, K903, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 493, 500, false, false⟩

theorem V283_ok : V283.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V283_fin : V283.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V283_V : V283.V where
  ok := V283_ok
  fin := V283_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K865_chk, List.forall_mem_cons.2 ⟨K874_chk, List.forall_mem_cons.2 ⟨K878_chk, List.forall_mem_cons.2 ⟨K883_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K895_chk, List.forall_mem_cons.2 ⟨K899_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V284 : UnitD := ⟨975776119405, 656716417, [K7, K276, K425, K571, K648, K712, K778, K846, K866, K878, K883, K885, K887], [K900, K901, K903, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 496, 503, false, false⟩

theorem V284_ok : V284.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V284_fin : V284.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V284_V : V284.V where
  ok := V284_ok
  fin := V284_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K878_chk, List.forall_mem_cons.2 ⟨K883_chk, List.forall_mem_cons.2 ⟨K885_chk, List.forall_mem_cons.2 ⟨K887_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K900_chk, List.forall_mem_cons.2 ⟨K901_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V285 : UnitD := ⟨976761194031, 328358209, [K7, K276, K425, K571, K648, K712, K778, K847, K879, K888, K890, K892], [K901, K903, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 499, 504, false, false⟩

theorem V285_ok : V285.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V285_fin : V285.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V285_V : V285.V where
  ok := V285_ok
  fin := V285_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K879_chk, List.forall_mem_cons.2 ⟨K888_chk, List.forall_mem_cons.2 ⟨K890_chk, List.forall_mem_cons.2 ⟨K892_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K901_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V286 : UnitD := ⟨977417910449, 328358209, [K7, K276, K425, K571, K648, K712, K778, K847, K879, K888, K890, K892, K894], [K902, K905, K913, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 500, 505, false, false⟩

theorem V286_ok : V286.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V286_fin : V286.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V286_V : V286.V where
  ok := V286_ok
  fin := V286_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K879_chk, List.forall_mem_cons.2 ⟨K888_chk, List.forall_mem_cons.2 ⟨K890_chk, List.forall_mem_cons.2 ⟨K892_chk, List.forall_mem_cons.2 ⟨K894_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K905_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V287 : UnitD := ⟨977910447763, 164179105, [K7, K276, K425, K571, K648, K712, K778, K847, K879, K888, K891, K895], [K902, K905, K913, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 502, 505, false, false⟩

theorem V287_ok : V287.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V287_fin : V287.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V287_V : V287.V where
  ok := V287_ok
  fin := V287_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K879_chk, List.forall_mem_cons.2 ⟨K888_chk, List.forall_mem_cons.2 ⟨K891_chk, List.forall_mem_cons.2 ⟨K895_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K905_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V288 : UnitD := ⟨978238805973, 164179105, [K7, K276, K425, K571, K648, K712, K778, K847, K879, K889, K895], [K902, K905, K913, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 502, 505, false, false⟩

theorem V288_ok : V288.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V288_fin : V288.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V288_V : V288.V where
  ok := V288_ok
  fin := V288_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K879_chk, List.forall_mem_cons.2 ⟨K889_chk, List.forall_mem_cons.2 ⟨K895_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K905_chk, List.forall_mem_cons.2 ⟨K913_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V289 : UnitD := ⟨978907060787, 504075709, [K7, K276, K425, K571, K648, K712, K778, K847, K879, K889, K895], [K906, K908, K912, K930, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 502, 508, false, false⟩

theorem V289_ok : V289.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V289_fin : V289.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V289_V : V289.V where
  ok := V289_ok
  fin := V289_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K879_chk, List.forall_mem_cons.2 ⟨K889_chk, List.forall_mem_cons.2 ⟨K895_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K906_chk, List.forall_mem_cons.2 ⟨K908_chk, List.forall_mem_cons.2 ⟨K912_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V290 : UnitD := ⟨979892135413, 480998917, [K7, K276, K425, K571, K648, K712, K778, K847, K879, K889, K895, K898, K900], [K911, K921, K930, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 504, 510, false, false⟩

theorem V290_ok : V290.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V290_fin : V290.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V290_V : V290.V where
  ok := V290_ok
  fin := V290_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K879_chk, List.forall_mem_cons.2 ⟨K889_chk, List.forall_mem_cons.2 ⟨K895_chk, List.forall_mem_cons.2 ⟨K898_chk, List.forall_mem_cons.2 ⟨K900_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K911_chk, List.forall_mem_cons.2 ⟨K921_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V291 : UnitD := ⟨980701492539, 328358209, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K895, K899, K902], [K910, K917, K921, K930, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 507, 510, false, false⟩

theorem V291_ok : V291.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V291_fin : V291.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V291_V : V291.V where
  ok := V291_ok
  fin := V291_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K895_chk, List.forall_mem_cons.2 ⟨K899_chk, List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K910_chk, List.forall_mem_cons.2 ⟨K917_chk, List.forall_mem_cons.2 ⟨K921_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V292 : UnitD := ⟨981358208957, 328358209, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K902, K904], [K918, K920, K924, K930, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 508, 513, false, false⟩

theorem V292_ok : V292.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V292_fin : V292.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V292_V : V292.V where
  ok := V292_ok
  fin := V292_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K904_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K918_chk, List.forall_mem_cons.2 ⟨K920_chk, List.forall_mem_cons.2 ⟨K924_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V293 : UnitD := ⟨981843283583, 156716417, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K902, K904, K906], [K918, K919, K922, K924, K930, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 509, 513, false, false⟩

theorem V293_ok : V293.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V293_fin : V293.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V293_V : V293.V where
  ok := V293_ok
  fin := V293_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K904_chk, List.forall_mem_cons.2 ⟨K906_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K918_chk, List.forall_mem_cons.2 ⟨K919_chk, List.forall_mem_cons.2 ⟨K922_chk, List.forall_mem_cons.2 ⟨K924_chk, List.forall_mem_cons.2 ⟨K930_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V294 : UnitD := ⟨982171641791, 171641791, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K902, K904, K906], [K923, K926, K929, K937, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 509, 516, false, false⟩

theorem V294_ok : V294.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V294_fin : V294.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V294_V : V294.V where
  ok := V294_ok
  fin := V294_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K904_chk, List.forall_mem_cons.2 ⟨K906_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K923_chk, List.forall_mem_cons.2 ⟨K926_chk, List.forall_mem_cons.2 ⟨K929_chk, List.forall_mem_cons.2 ⟨K937_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V295 : UnitD := ⟨982546641791, 203358209, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K902, K904, K906, K908, K909, K915], [K927, K929, K937, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 512, 518, false, false⟩

theorem V295_ok : V295.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V295_fin : V295.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V295_V : V295.V where
  ok := V295_ok
  fin := V295_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K904_chk, List.forall_mem_cons.2 ⟨K906_chk, List.forall_mem_cons.2 ⟨K908_chk, List.forall_mem_cons.2 ⟨K909_chk, List.forall_mem_cons.2 ⟨K915_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K927_chk, List.forall_mem_cons.2 ⟨K929_chk, List.forall_mem_cons.2 ⟨K937_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V296 : UnitD := ⟨983000000001, 250000001, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K902, K904, K907, K910, K916, K918], [K931, K933, K937, K947, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 514, 520, false, false⟩

theorem V296_ok : V296.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V296_fin : V296.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V296_V : V296.V where
  ok := V296_ok
  fin := V296_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K902_chk, List.forall_mem_cons.2 ⟨K904_chk, List.forall_mem_cons.2 ⟨K907_chk, List.forall_mem_cons.2 ⟨K910_chk, List.forall_mem_cons.2 ⟨K916_chk, List.forall_mem_cons.2 ⟨K918_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K931_chk, List.forall_mem_cons.2 ⟨K933_chk, List.forall_mem_cons.2 ⟨K937_chk, List.forall_mem_cons.2 ⟨K947_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V297 : UnitD := ⟨983500000001, 249999999, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K903, K911, K920], [K935, K936, K939, K946, K961, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 516, 523, false, false⟩

theorem V297_ok : V297.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V297_fin : V297.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V297_V : V297.V where
  ok := V297_ok
  fin := V297_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K911_chk, List.forall_mem_cons.2 ⟨K920_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K935_chk, List.forall_mem_cons.2 ⟨K936_chk, List.forall_mem_cons.2 ⟨K939_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V298 : UnitD := ⟨983875000001, 125000001, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K903, K911, K920, K923, K925], [K936, K939, K946, K961, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 518, 524, false, false⟩

theorem V298_ok : V298.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V298_fin : V298.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V298_V : V298.V where
  ok := V298_ok
  fin := V298_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K911_chk, List.forall_mem_cons.2 ⟨K920_chk, List.forall_mem_cons.2 ⟨K923_chk, List.forall_mem_cons.2 ⟨K925_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K936_chk, List.forall_mem_cons.2 ⟨K939_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V299 : UnitD := ⟨984250000001, 249999999, [K7, K276, K425, K571, K648, K712, K778, K847, K880, K896, K903, K911, K920, K923, K926], [K938, K941, K946, K961, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 519, 526, false, false⟩

theorem V299_ok : V299.ok = true := by
  -- kcost: 0.2 s measured mean, 30 pairs, 6 Nov
  decide +kernel

theorem V299_fin : V299.fin = true := by
  -- kcost: 1.4 s measured mean, 30 pair polynomials, 6 Nov
  decide +kernel

theorem V299_V : V299.V where
  ok := V299_ok
  fin := V299_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K911_chk, List.forall_mem_cons.2 ⟨K920_chk, List.forall_mem_cons.2 ⟨K923_chk, List.forall_mem_cons.2 ⟨K926_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K938_chk, List.forall_mem_cons.2 ⟨K941_chk, List.forall_mem_cons.2 ⟨K946_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V300 : UnitD := ⟨984750000001, 250000001, [K7, K276, K425, K571, K648, K713, K847, K880, K896, K903, K911, K921, K928, K932], [K942, K944, K949, K953, K961, K982, K1046], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 522, 528, false, false⟩

theorem V300_ok : V300.ok = true := by
  -- kcost: 0.2 s measured mean, 31 pairs, 6 Nov
  decide +kernel

theorem V300_fin : V300.fin = true := by
  -- kcost: 1.4 s measured mean, 31 pair polynomials, 6 Nov
  decide +kernel

theorem V300_V : V300.V where
  ok := V300_ok
  fin := V300_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K880_chk, List.forall_mem_cons.2 ⟨K896_chk, List.forall_mem_cons.2 ⟨K903_chk, List.forall_mem_cons.2 ⟨K911_chk, List.forall_mem_cons.2 ⟨K921_chk, List.forall_mem_cons.2 ⟨K928_chk, List.forall_mem_cons.2 ⟨K932_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K942_chk, List.forall_mem_cons.2 ⟨K944_chk, List.forall_mem_cons.2 ⟨K949_chk, List.forall_mem_cons.2 ⟨K953_chk, List.forall_mem_cons.2 ⟨K961_chk, List.forall_mem_cons.2 ⟨K982_chk, List.forall_mem_cons.2 ⟨K1046_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def L9 : List UnitD := [V271, V272, V273, V274, V275, V276, V277, V278, V279, V280, V281, V282, V283, V284, V285, V286, V287, V288, V289, V290, V291, V292, V293, V294, V295, V296, V297, V298, V299, V300]

theorem L9_V : ∀ u ∈ L9, u.V :=
  List.forall_mem_cons.2 ⟨V271_V, List.forall_mem_cons.2 ⟨V272_V, List.forall_mem_cons.2 ⟨V273_V, List.forall_mem_cons.2 ⟨V274_V, List.forall_mem_cons.2 ⟨V275_V, List.forall_mem_cons.2 ⟨V276_V, List.forall_mem_cons.2 ⟨V277_V, List.forall_mem_cons.2 ⟨V278_V, List.forall_mem_cons.2 ⟨V279_V, List.forall_mem_cons.2 ⟨V280_V, List.forall_mem_cons.2 ⟨V281_V, List.forall_mem_cons.2 ⟨V282_V, List.forall_mem_cons.2 ⟨V283_V, List.forall_mem_cons.2 ⟨V284_V, List.forall_mem_cons.2 ⟨V285_V, List.forall_mem_cons.2 ⟨V286_V, List.forall_mem_cons.2 ⟨V287_V, List.forall_mem_cons.2 ⟨V288_V, List.forall_mem_cons.2 ⟨V289_V, List.forall_mem_cons.2 ⟨V290_V, List.forall_mem_cons.2 ⟨V291_V, List.forall_mem_cons.2 ⟨V292_V, List.forall_mem_cons.2 ⟨V293_V, List.forall_mem_cons.2 ⟨V294_V, List.forall_mem_cons.2 ⟨V295_V, List.forall_mem_cons.2 ⟨V296_V, List.forall_mem_cons.2 ⟨V297_V, List.forall_mem_cons.2 ⟨V298_V, List.forall_mem_cons.2 ⟨V299_V, List.forall_mem_cons.2 ⟨V300_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
