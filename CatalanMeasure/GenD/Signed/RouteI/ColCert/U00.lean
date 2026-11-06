module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V1 : UnitD := ⟨3387763791, 1129254597, [K2, K14, K24, K41, K73, K105, K121, K140, K204, K275, K350, K425, K574], [], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 628, 628, false, false⟩

theorem V1_ok : V1.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V1_fin : V1.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V1_V : V1.V where
  ok := V1_ok
  fin := V1_fin
  h0 := List.forall_mem_cons.2 ⟨K2_chk, List.forall_mem_cons.2 ⟨K14_chk, List.forall_mem_cons.2 ⟨K24_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K121_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V2 : UnitD := ⟨5269854787, 752836399, [], [K16, K19, K23, K32, K41, K73, K105, K121, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 0, 6, false, false⟩

theorem V2_ok : V2.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V2_fin : V2.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V2_V : V2.V where
  ok := V2_ok
  fin := V2_fin
  h0 := List.forall_mem_nil _
  h1 := List.forall_mem_cons.2 ⟨K16_chk, List.forall_mem_cons.2 ⟨K19_chk, List.forall_mem_cons.2 ⟨K23_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K121_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V3 : UnitD := ⟨6201821785, 179130599, [], [K13, K17, K24, K41, K73, K105, K121, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 0, 4, false, false⟩

theorem V3_ok : V3.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V3_fin : V3.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V3_V : V3.V where
  ok := V3_ok
  fin := V3_fin
  h0 := List.forall_mem_nil _
  h1 := List.forall_mem_cons.2 ⟨K13_chk, List.forall_mem_cons.2 ⟨K17_chk, List.forall_mem_cons.2 ⟨K24_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K121_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V4 : UnitD := ⟨6476190479, 95238095, [K0], [K12, K15, K16, K19, K24, K41, K73, K105, K121, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 1, 4, false, false⟩

theorem V4_ok : V4.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V4_fin : V4.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V4_V : V4.V where
  ok := V4_ok
  fin := V4_fin
  h0 := List.forall_mem_cons.2 ⟨K0_chk, List.forall_mem_nil _⟩
  h1 := List.forall_mem_cons.2 ⟨K12_chk, List.forall_mem_cons.2 ⟨K15_chk, List.forall_mem_cons.2 ⟨K16_chk, List.forall_mem_cons.2 ⟨K19_chk, List.forall_mem_cons.2 ⟨K24_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K121_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V5 : UnitD := ⟨6666666669, 95238095, [K0, K8], [K19, K23, K32, K41, K73, K105, K121, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 2, 7, false, false⟩

theorem V5_ok : V5.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V5_fin : V5.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V5_V : V5.V where
  ok := V5_ok
  fin := V5_fin
  h0 := List.forall_mem_cons.2 ⟨K0_chk, List.forall_mem_cons.2 ⟨K8_chk, List.forall_mem_nil _⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K19_chk, List.forall_mem_cons.2 ⟨K23_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K121_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V6 : UnitD := ⟨6857142859, 95238095, [K1, K9], [K20, K23, K32, K41, K73, K105, K121, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 3, 8, false, false⟩

theorem V6_ok : V6.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V6_fin : V6.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V6_V : V6.V where
  ok := V6_ok
  fin := V6_fin
  h0 := List.forall_mem_cons.2 ⟨K1_chk, List.forall_mem_cons.2 ⟨K9_chk, List.forall_mem_nil _⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K20_chk, List.forall_mem_cons.2 ⟨K23_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K121_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V7 : UnitD := ⟨7047619049, 95238095, [K1, K9, K11, K12], [K22, K27, K32, K41, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 5, 9, false, false⟩

theorem V7_ok : V7.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V7_fin : V7.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V7_V : V7.V where
  ok := V7_ok
  fin := V7_fin
  h0 := List.forall_mem_cons.2 ⟨K1_chk, List.forall_mem_cons.2 ⟨K9_chk, List.forall_mem_cons.2 ⟨K11_chk, List.forall_mem_cons.2 ⟨K12_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K22_chk, List.forall_mem_cons.2 ⟨K27_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V8 : UnitD := ⟨7238095239, 95238095, [K1, K10, K13], [K21, K25, K26, K28, K32, K40, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 6, 9, false, false⟩

theorem V8_ok : V8.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V8_fin : V8.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V8_V : V8.V where
  ok := V8_ok
  fin := V8_fin
  h0 := List.forall_mem_cons.2 ⟨K1_chk, List.forall_mem_cons.2 ⟨K10_chk, List.forall_mem_cons.2 ⟨K13_chk, List.forall_mem_nil _⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K21_chk, List.forall_mem_cons.2 ⟨K25_chk, List.forall_mem_cons.2 ⟨K26_chk, List.forall_mem_cons.2 ⟨K28_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V9 : UnitD := ⟨7517271535, 183938201, [K2, K13], [K29, K32, K40, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 6, 13, false, false⟩

theorem V9_ok : V9.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V9_fin : V9.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V9_V : V9.V where
  ok := V9_ok
  fin := V9_fin
  h0 := List.forall_mem_cons.2 ⟨K2_chk, List.forall_mem_cons.2 ⟨K13_chk, List.forall_mem_nil _⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K29_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V10 : UnitD := ⟨7802985821, 101776085, [K2, K13, K16, K18], [K31, K34, K40, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 8, 14, false, false⟩

theorem V10_ok : V10.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V10_fin : V10.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V10_V : V10.V where
  ok := V10_ok
  fin := V10_fin
  h0 := List.forall_mem_cons.2 ⟨K2_chk, List.forall_mem_cons.2 ⟨K13_chk, List.forall_mem_cons.2 ⟨K16_chk, List.forall_mem_cons.2 ⟨K18_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K31_chk, List.forall_mem_cons.2 ⟨K34_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V11 : UnitD := ⟨8095238097, 190476191, [K2, K13, K16, K19], [K33, K36, K39, K47, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 9, 16, false, false⟩

theorem V11_ok : V11.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V11_fin : V11.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V11_V : V11.V where
  ok := V11_ok
  fin := V11_fin
  h0 := List.forall_mem_cons.2 ⟨K2_chk, List.forall_mem_cons.2 ⟨K13_chk, List.forall_mem_cons.2 ⟨K16_chk, List.forall_mem_cons.2 ⟨K19_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K33_chk, List.forall_mem_cons.2 ⟨K36_chk, List.forall_mem_cons.2 ⟨K39_chk, List.forall_mem_cons.2 ⟨K47_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V12 : UnitD := ⟨8476190479, 190476191, [K2, K14, K22, K26], [K37, K42, K44, K47, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 12, 19, false, false⟩

theorem V12_ok : V12.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V12_fin : V12.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V12_V : V12.V where
  ok := V12_ok
  fin := V12_fin
  h0 := List.forall_mem_cons.2 ⟨K2_chk, List.forall_mem_cons.2 ⟨K14_chk, List.forall_mem_cons.2 ⟨K22_chk, List.forall_mem_cons.2 ⟨K26_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K37_chk, List.forall_mem_cons.2 ⟨K42_chk, List.forall_mem_cons.2 ⟨K44_chk, List.forall_mem_cons.2 ⟨K47_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V13 : UnitD := ⟨8761904765, 95238095, [K3, K22, K27, K30], [K42, K44, K47, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 15, 20, false, false⟩

theorem V13_ok : V13.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V13_fin : V13.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V13_V : V13.V where
  ok := V13_ok
  fin := V13_fin
  h0 := List.forall_mem_cons.2 ⟨K3_chk, List.forall_mem_cons.2 ⟨K22_chk, List.forall_mem_cons.2 ⟨K27_chk, List.forall_mem_cons.2 ⟨K30_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K42_chk, List.forall_mem_cons.2 ⟨K44_chk, List.forall_mem_cons.2 ⟨K47_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V14 : UnitD := ⟨9047619049, 190476189, [K3, K23, K30], [K45, K46, K50, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 15, 22, false, false⟩

theorem V14_ok : V14.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V14_fin : V14.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V14_V : V14.V where
  ok := V14_ok
  fin := V14_fin
  h0 := List.forall_mem_cons.2 ⟨K3_chk, List.forall_mem_cons.2 ⟨K23_chk, List.forall_mem_cons.2 ⟨K30_chk, List.forall_mem_nil _⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K45_chk, List.forall_mem_cons.2 ⟨K46_chk, List.forall_mem_cons.2 ⟨K50_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V15 : UnitD := ⟨9428571429, 190476191, [K3, K23, K31, K33, K35], [K48, K50, K56, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 18, 25, false, false⟩

theorem V15_ok : V15.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V15_fin : V15.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V15_V : V15.V where
  ok := V15_ok
  fin := V15_fin
  h0 := List.forall_mem_cons.2 ⟨K3_chk, List.forall_mem_cons.2 ⟨K23_chk, List.forall_mem_cons.2 ⟨K31_chk, List.forall_mem_cons.2 ⟨K33_chk, List.forall_mem_cons.2 ⟨K35_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K48_chk, List.forall_mem_cons.2 ⟨K50_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V16 : UnitD := ⟨9733288747, 114241127, [K3, K23, K32, K37], [K49, K52, K55, K63, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 20, 26, false, false⟩

theorem V16_ok : V16.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V16_fin : V16.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V16_V : V16.V where
  ok := V16_ok
  fin := V16_fin
  h0 := List.forall_mem_cons.2 ⟨K3_chk, List.forall_mem_cons.2 ⟨K23_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K37_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K49_chk, List.forall_mem_cons.2 ⟨K52_chk, List.forall_mem_cons.2 ⟨K55_chk, List.forall_mem_cons.2 ⟨K63_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V17 : UnitD := ⟨10019003033, 171473159, [K3, K23, K32, K38], [K53, K55, K63, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 21, 28, false, false⟩

theorem V17_ok : V17.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V17_fin : V17.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V17_V : V17.V where
  ok := V17_ok
  fin := V17_fin
  h0 := List.forall_mem_cons.2 ⟨K3_chk, List.forall_mem_cons.2 ⟨K23_chk, List.forall_mem_cons.2 ⟨K32_chk, List.forall_mem_cons.2 ⟨K38_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K53_chk, List.forall_mem_cons.2 ⟨K55_chk, List.forall_mem_cons.2 ⟨K63_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V18 : UnitD := ⟨10380952383, 190476191, [K3, K24, K38, K43, K45], [K57, K59, K63, K73, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 24, 30, false, false⟩

theorem V18_ok : V18.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V18_fin : V18.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V18_V : V18.V where
  ok := V18_ok
  fin := V18_fin
  h0 := List.forall_mem_cons.2 ⟨K3_chk, List.forall_mem_cons.2 ⟨K24_chk, List.forall_mem_cons.2 ⟨K38_chk, List.forall_mem_cons.2 ⟨K43_chk, List.forall_mem_cons.2 ⟨K45_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K57_chk, List.forall_mem_cons.2 ⟨K59_chk, List.forall_mem_cons.2 ⟨K63_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V19 : UnitD := ⟨10761904763, 190476189, [K3, K24, K39, K46], [K61, K62, K65, K72, K88, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 26, 33, false, false⟩

theorem V19_ok : V19.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V19_fin : V19.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V19_V : V19.V where
  ok := V19_ok
  fin := V19_fin
  h0 := List.forall_mem_cons.2 ⟨K3_chk, List.forall_mem_cons.2 ⟨K24_chk, List.forall_mem_cons.2 ⟨K39_chk, List.forall_mem_cons.2 ⟨K46_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K61_chk, List.forall_mem_cons.2 ⟨K62_chk, List.forall_mem_cons.2 ⟨K65_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V20 : UnitD := ⟨11047619047, 95238095, [K4, K39, K46, K49, K51], [K61, K62, K65, K72, K88, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 28, 33, false, false⟩

theorem V20_ok : V20.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V20_fin : V20.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V20_V : V20.V where
  ok := V20_ok
  fin := V20_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K39_chk, List.forall_mem_cons.2 ⟨K46_chk, List.forall_mem_cons.2 ⟨K49_chk, List.forall_mem_cons.2 ⟨K51_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K61_chk, List.forall_mem_cons.2 ⟨K62_chk, List.forall_mem_cons.2 ⟨K65_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V21 : UnitD := ⟨11333333333, 190476191, [K4, K39, K46, K49, K51, K53], [K64, K67, K71, K80, K88, K105, K120, K128, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 29, 36, false, false⟩

theorem V21_ok : V21.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V21_fin : V21.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V21_V : V21.V where
  ok := V21_ok
  fin := V21_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K39_chk, List.forall_mem_cons.2 ⟨K46_chk, List.forall_mem_cons.2 ⟨K49_chk, List.forall_mem_cons.2 ⟨K51_chk, List.forall_mem_cons.2 ⟨K53_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K64_chk, List.forall_mem_cons.2 ⟨K67_chk, List.forall_mem_cons.2 ⟨K71_chk, List.forall_mem_cons.2 ⟨K80_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V22 : UnitD := ⟨11714285715, 190476191, [K4, K39, K47, K54, K58], [K68, K71, K80, K88, K105, K120, K127, K131, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 32, 38, false, false⟩

theorem V22_ok : V22.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V22_fin : V22.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V22_V : V22.V where
  ok := V22_ok
  fin := V22_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K39_chk, List.forall_mem_cons.2 ⟨K47_chk, List.forall_mem_cons.2 ⟨K54_chk, List.forall_mem_cons.2 ⟨K58_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K68_chk, List.forall_mem_cons.2 ⟨K71_chk, List.forall_mem_cons.2 ⟨K80_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V23 : UnitD := ⟨12095238097, 190476191, [K4, K40, K54, K58, K60], [K75, K76, K77, K80, K88, K105, K120, K127, K131, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 34, 40, false, false⟩

theorem V23_ok : V23.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V23_fin : V23.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V23_V : V23.V where
  ok := V23_ok
  fin := V23_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K54_chk, List.forall_mem_cons.2 ⟨K58_chk, List.forall_mem_cons.2 ⟨K60_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K75_chk, List.forall_mem_cons.2 ⟨K76_chk, List.forall_mem_cons.2 ⟨K77_chk, List.forall_mem_cons.2 ⟨K80_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V24 : UnitD := ⟨12438870885, 153156597, [K4, K40, K55, K62], [K77, K79, K83, K88, K105, K120, K127, K131, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 36, 42, false, false⟩

theorem V24_ok : V24.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V24_fin : V24.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V24_V : V24.V where
  ok := V24_ok
  fin := V24_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K55_chk, List.forall_mem_cons.2 ⟨K62_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K77_chk, List.forall_mem_cons.2 ⟨K79_chk, List.forall_mem_cons.2 ⟨K83_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V25 : UnitD := ⟨12724585171, 132557689, [K4, K40, K55, K62, K64, K66], [K81, K83, K88, K105, K120, K127, K131, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 38, 44, false, false⟩

theorem V25_ok : V25.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V25_fin : V25.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V25_V : V25.V where
  ok := V25_ok
  fin := V25_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K55_chk, List.forall_mem_cons.2 ⟨K62_chk, List.forall_mem_cons.2 ⟨K64_chk, List.forall_mem_cons.2 ⟨K66_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K81_chk, List.forall_mem_cons.2 ⟨K83_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V26 : UnitD := ⟨13047619049, 190476189, [K4, K40, K55, K62, K64, K67, K69], [K85, K87, K96, K105, K120, K127, K131, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 40, 46, false, false⟩

theorem V26_ok : V26.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V26_fin : V26.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V26_V : V26.V where
  ok := V26_ok
  fin := V26_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K55_chk, List.forall_mem_cons.2 ⟨K62_chk, List.forall_mem_cons.2 ⟨K64_chk, List.forall_mem_cons.2 ⟨K67_chk, List.forall_mem_cons.2 ⟨K69_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K85_chk, List.forall_mem_cons.2 ⟨K87_chk, List.forall_mem_cons.2 ⟨K96_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V27 : UnitD := ⟨13428571427, 190476189, [K4, K40, K55, K63, K70, K76], [K86, K90, K96, K105, K120, K127, K131, K140, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 42, 48, false, false⟩

theorem V27_ok : V27.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V27_fin : V27.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V27_V : V27.V where
  ok := V27_ok
  fin := V27_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K55_chk, List.forall_mem_cons.2 ⟨K63_chk, List.forall_mem_cons.2 ⟨K70_chk, List.forall_mem_cons.2 ⟨K76_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K86_chk, List.forall_mem_cons.2 ⟨K90_chk, List.forall_mem_cons.2 ⟨K96_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V28 : UnitD := ⟨13809523807, 190476191, [K4, K40, K56, K71, K78], [K92, K96, K105, K120, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 44, 51, false, false⟩

theorem V28_ok : V28.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V28_fin : V28.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V28_V : V28.V where
  ok := V28_ok
  fin := V28_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K71_chk, List.forall_mem_cons.2 ⟨K78_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K92_chk, List.forall_mem_cons.2 ⟨K96_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V29 : UnitD := ⟨14119505747, 119505749, [K4, K40, K56, K71, K79, K82], [K93, K95, K99, K105, K120, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 46, 52, false, false⟩

theorem V29_ok : V29.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V29_fin : V29.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V29_V : V29.V where
  ok := V29_ok
  fin := V29_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K71_chk, List.forall_mem_cons.2 ⟨K79_chk, List.forall_mem_cons.2 ⟨K82_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K93_chk, List.forall_mem_cons.2 ⟨K95_chk, List.forall_mem_cons.2 ⟨K99_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V30 : UnitD := ⟨14405220033, 166208537, [K4, K40, K56, K71, K79, K82, K84], [K97, K99, K105, K120, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 47, 54, false, false⟩

theorem V30_ok : V30.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V30_fin : V30.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V30_V : V30.V where
  ok := V30_ok
  fin := V30_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K40_chk, List.forall_mem_cons.2 ⟨K56_chk, List.forall_mem_cons.2 ⟨K71_chk, List.forall_mem_cons.2 ⟨K79_chk, List.forall_mem_cons.2 ⟨K82_chk, List.forall_mem_cons.2 ⟨K84_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K97_chk, List.forall_mem_cons.2 ⟨K99_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V0 : UnitD := ⟨1129254597, 1129254597, [K4, K41, K73, K106, K140, K204, K275, K350, K425, K574], [], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 628, 628, true, false⟩

theorem V0_ok : V0.ok = true := by
  -- kcost: 0.2 s measured mean, 17 pairs, 6 Nov
  decide +kernel

theorem V0_fin : V0.fin = true := by
  -- kcost: 1.4 s measured mean, 17 pair polynomials, 6 Nov
  decide +kernel

theorem V0_V : V0.V where
  ok := V0_ok
  fin := V0_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K106_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_nil _
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def L0 : List UnitD := [V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30]

theorem L0_V : ∀ u ∈ L0, u.V :=
  List.forall_mem_cons.2 ⟨V1_V, List.forall_mem_cons.2 ⟨V2_V, List.forall_mem_cons.2 ⟨V3_V, List.forall_mem_cons.2 ⟨V4_V, List.forall_mem_cons.2 ⟨V5_V, List.forall_mem_cons.2 ⟨V6_V, List.forall_mem_cons.2 ⟨V7_V, List.forall_mem_cons.2 ⟨V8_V, List.forall_mem_cons.2 ⟨V9_V, List.forall_mem_cons.2 ⟨V10_V, List.forall_mem_cons.2 ⟨V11_V, List.forall_mem_cons.2 ⟨V12_V, List.forall_mem_cons.2 ⟨V13_V, List.forall_mem_cons.2 ⟨V14_V, List.forall_mem_cons.2 ⟨V15_V, List.forall_mem_cons.2 ⟨V16_V, List.forall_mem_cons.2 ⟨V17_V, List.forall_mem_cons.2 ⟨V18_V, List.forall_mem_cons.2 ⟨V19_V, List.forall_mem_cons.2 ⟨V20_V, List.forall_mem_cons.2 ⟨V21_V, List.forall_mem_cons.2 ⟨V22_V, List.forall_mem_cons.2 ⟨V23_V, List.forall_mem_cons.2 ⟨V24_V, List.forall_mem_cons.2 ⟨V25_V, List.forall_mem_cons.2 ⟨V26_V, List.forall_mem_cons.2 ⟨V27_V, List.forall_mem_cons.2 ⟨V28_V, List.forall_mem_cons.2 ⟨V29_V, List.forall_mem_cons.2 ⟨V30_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
