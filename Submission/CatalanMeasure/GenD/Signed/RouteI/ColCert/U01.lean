module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V31 : UnitD := ⟨14761904761, 190476191, [K4, K41, K71, K79, K83, K86], [K100, K101, K104, K112, K120, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 50, 56, false, false⟩

theorem V31_ok : V31.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V31_fin : V31.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V31_V : V31.V where
  ok := V31_ok
  fin := V31_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K71_chk, List.forall_mem_cons.2 ⟨K79_chk, List.forall_mem_cons.2 ⟨K83_chk, List.forall_mem_cons.2 ⟨K86_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K100_chk, List.forall_mem_cons.2 ⟨K101_chk, List.forall_mem_cons.2 ⟨K104_chk, List.forall_mem_cons.2 ⟨K112_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V32 : UnitD := ⟨15142857141, 190476189, [K4, K41, K72, K86, K89, K91], [K103, K108, K112, K120, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 52, 58, false, false⟩

theorem V32_ok : V32.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V32_fin : V32.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V32_V : V32.V where
  ok := V32_ok
  fin := V32_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K86_chk, List.forall_mem_cons.2 ⟨K89_chk, List.forall_mem_cons.2 ⟨K91_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K103_chk, List.forall_mem_cons.2 ⟨K108_chk, List.forall_mem_cons.2 ⟨K112_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V33 : UnitD := ⟨15523809521, 190476191, [K4, K41, K72, K86, K90, K94], [K108, K112, K119, K123, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 54, 60, false, false⟩

theorem V33_ok : V33.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V33_fin : V33.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V33_V : V33.V where
  ok := V33_ok
  fin := V33_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K86_chk, List.forall_mem_cons.2 ⟨K90_chk, List.forall_mem_cons.2 ⟨K94_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K108_chk, List.forall_mem_cons.2 ⟨K112_chk, List.forall_mem_cons.2 ⟨K119_chk, List.forall_mem_cons.2 ⟨K123_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V34 : UnitD := ⟨15904761905, 190476193, [K4, K41, K72, K87, K95, K98], [K110, K113, K115, K119, K123, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 56, 63, false, false⟩

theorem V34_ok : V34.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V34_fin : V34.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V34_V : V34.V where
  ok := V34_ok
  fin := V34_fin
  h0 := List.forall_mem_cons.2 ⟨K4_chk, List.forall_mem_cons.2 ⟨K41_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K87_chk, List.forall_mem_cons.2 ⟨K95_chk, List.forall_mem_cons.2 ⟨K98_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K110_chk, List.forall_mem_cons.2 ⟨K113_chk, List.forall_mem_cons.2 ⟨K115_chk, List.forall_mem_cons.2 ⟨K119_chk, List.forall_mem_cons.2 ⟨K123_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V35 : UnitD := ⟨16190476191, 95238093, [K5, K72, K87, K95, K99, K102], [K110, K113, K115, K119, K123, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 59, 63, false, false⟩

theorem V35_ok : V35.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V35_fin : V35.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V35_V : V35.V where
  ok := V35_ok
  fin := V35_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K87_chk, List.forall_mem_cons.2 ⟨K95_chk, List.forall_mem_cons.2 ⟨K99_chk, List.forall_mem_cons.2 ⟨K102_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K110_chk, List.forall_mem_cons.2 ⟨K113_chk, List.forall_mem_cons.2 ⟨K115_chk, List.forall_mem_cons.2 ⟨K119_chk, List.forall_mem_cons.2 ⟨K123_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V36 : UnitD := ⟨16476190475, 190476191, [K5, K72, K87, K95, K99, K102], [K117, K119, K122, K124, K125, K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 59, 66, false, false⟩

theorem V36_ok : V36.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V36_fin : V36.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V36_V : V36.V where
  ok := V36_ok
  fin := V36_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K87_chk, List.forall_mem_cons.2 ⟨K95_chk, List.forall_mem_cons.2 ⟨K99_chk, List.forall_mem_cons.2 ⟨K102_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K117_chk, List.forall_mem_cons.2 ⟨K119_chk, List.forall_mem_cons.2 ⟨K122_chk, List.forall_mem_cons.2 ⟨K124_chk, List.forall_mem_cons.2 ⟨K125_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V37 : UnitD := ⟨16857142857, 190476191, [K5, K72, K87, K96, K103, K107, K109], [K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 62, 73, false, false⟩

theorem V37_ok : V37.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V37_fin : V37.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V37_V : V37.V where
  ok := V37_ok
  fin := V37_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K87_chk, List.forall_mem_cons.2 ⟨K96_chk, List.forall_mem_cons.2 ⟨K103_chk, List.forall_mem_cons.2 ⟨K107_chk, List.forall_mem_cons.2 ⟨K109_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V38 : UnitD := ⟨17238095237, 190476189, [K5, K72, K88, K104, K110], [K127, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 64, 73, false, false⟩

theorem V38_ok : V38.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V38_fin : V38.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V38_V : V38.V where
  ok := V38_ok
  fin := V38_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K104_chk, List.forall_mem_cons.2 ⟨K110_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V39 : UnitD := ⟨17619047617, 190476191, [K5, K72, K88, K104, K111, K114], [K126, K129, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 66, 73, false, false⟩

theorem V39_ok : V39.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V39_fin : V39.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V39_V : V39.V where
  ok := V39_ok
  fin := V39_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K72_chk, List.forall_mem_cons.2 ⟨K88_chk, List.forall_mem_cons.2 ⟨K104_chk, List.forall_mem_cons.2 ⟨K111_chk, List.forall_mem_cons.2 ⟨K114_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K126_chk, List.forall_mem_cons.2 ⟨K129_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V40 : UnitD := ⟨18008467419, 198943611, [K5, K73, K104, K111, K114, K116, K118], [K126, K129, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 68, 73, false, false⟩

theorem V40_ok : V40.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V40_fin : V40.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V40_V : V40.V where
  ok := V40_ok
  fin := V40_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K104_chk, List.forall_mem_cons.2 ⟨K111_chk, List.forall_mem_cons.2 ⟨K114_chk, List.forall_mem_cons.2 ⟨K116_chk, List.forall_mem_cons.2 ⟨K118_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K126_chk, List.forall_mem_cons.2 ⟨K129_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V41 : UnitD := ⟨18802774149, 595363119, [K5, K73, K104, K111, K114, K116, K118], [K129, K131, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 68, 74, false, false⟩

theorem V41_ok : V41.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V41_fin : V41.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V41_V : V41.V where
  ok := V41_ok
  fin := V41_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K104_chk, List.forall_mem_cons.2 ⟨K111_chk, List.forall_mem_cons.2 ⟨K114_chk, List.forall_mem_cons.2 ⟨K116_chk, List.forall_mem_cons.2 ⟨K118_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K129_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V42 : UnitD := ⟨19993500385, 595363117, [K5, K73, K105, K119, K122, K124], [K129, K130, K133, K139, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 72, 74, false, false⟩

theorem V42_ok : V42.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V42_fin : V42.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V42_V : V42.V where
  ok := V42_ok
  fin := V42_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K119_chk, List.forall_mem_cons.2 ⟨K122_chk, List.forall_mem_cons.2 ⟨K124_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K129_chk, List.forall_mem_cons.2 ⟨K130_chk, List.forall_mem_cons.2 ⟨K133_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V43 : UnitD := ⟨21935331703, 1346468201, [K5, K73, K105, K119, K122, K124], [K133, K138, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 72, 76, false, false⟩

theorem V43_ok : V43.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V43_fin : V43.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V43_V : V43.V where
  ok := V43_ok
  fin := V43_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K119_chk, List.forall_mem_cons.2 ⟨K122_chk, List.forall_mem_cons.2 ⟨K124_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K133_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V44 : UnitD := ⟨24804380457, 1522580553, [K5, K73, K105, K119, K122, K124], [K134, K137, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 72, 77, false, false⟩

theorem V44_ok : V44.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V44_fin : V44.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V44_V : V44.V where
  ok := V44_ok
  fin := V44_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K119_chk, List.forall_mem_cons.2 ⟨K122_chk, List.forall_mem_cons.2 ⟨K124_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K134_chk, List.forall_mem_cons.2 ⟨K137_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V45 : UnitD := ⟨28048688671, 1721727661, [K5, K73, K105, K120], [K136, K144, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 73, 78, false, false⟩

theorem V45_ok : V45.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V45_fin : V45.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V45_V : V45.V where
  ok := V45_ok
  fin := V45_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V46 : UnitD := ⟨31717338699, 1946922367, [K5, K73, K105, K120, K126], [K142, K144, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 74, 79, false, false⟩

theorem V46_ok : V46.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V46_fin : V46.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V46_V : V46.V where
  ok := V46_ok
  fin := V46_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K126_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K142_chk, List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V47 : UnitD := ⟨34765046861, 1100785795, [K5, K73, K105, K120, K127, K130], [K142, K144, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 76, 79, false, false⟩

theorem V47_ok : V47.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V47_fin : V47.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V47_V : V47.V where
  ok := V47_ok
  fin := V47_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K130_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K142_chk, List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V48 : UnitD := ⟨36966618451, 1100785795, [K5, K73, K105, K120, K127, K130], [K142, K144, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 76, 79, false, false⟩

theorem V48_ok : V48.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V48_fin : V48.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V48_V : V48.V where
  ok := V48_ok
  fin := V48_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K130_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K142_chk, List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V49 : UnitD := ⟨39312168175, 1244763929, [K5, K73, K105, K120, K127, K130, K132], [K144, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 77, 80, false, false⟩

theorem V49_ok : V49.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V49_fin : V49.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V49_V : V49.V where
  ok := V49_ok
  fin := V49_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K130_chk, List.forall_mem_cons.2 ⟨K132_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V50 : UnitD := ⟨41801696033, 1244763929, [K5, K73, K105, K120, K127, K130, K132], [K143, K145, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 77, 80, false, false⟩

theorem V50_ok : V50.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V50_fin : V50.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V50_V : V50.V where
  ok := V50_ok
  fin := V50_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K130_chk, List.forall_mem_cons.2 ⟨K132_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K143_chk, List.forall_mem_cons.2 ⟨K145_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V51 : UnitD := ⟨44454033757, 1407573795, [K5, K73, K105, K120, K127, K130, K132, K134], [K145, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 78, 81, false, false⟩

theorem V51_ok : V51.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V51_fin : V51.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V51_V : V51.V where
  ok := V51_ok
  fin := V51_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K130_chk, List.forall_mem_cons.2 ⟨K132_chk, List.forall_mem_cons.2 ⟨K134_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K145_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V52 : UnitD := ⟨47269181345, 1407573793, [K5, K73, K105, K120, K127, K131], [K145, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 78, 81, false, false⟩

theorem V52_ok : V52.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V52_fin : V52.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V52_V : V52.V where
  ok := V52_ok
  fin := V52_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K127_chk, List.forall_mem_cons.2 ⟨K131_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K145_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V53 : UnitD := ⟨50268433641, 1591678503, [K5, K73, K105, K120, K128, K135], [K145, K147, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 79, 81, false, false⟩

theorem V53_ok : V53.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V53_fin : V53.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V53_V : V53.V where
  ok := V53_ok
  fin := V53_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K105_chk, List.forall_mem_cons.2 ⟨K120_chk, List.forall_mem_cons.2 ⟨K128_chk, List.forall_mem_cons.2 ⟨K135_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K145_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V54 : UnitD := ⟨53451790647, 1591678503, [K5, K73, K106, K135], [K146, K149, K155, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 79, 82, false, false⟩

theorem V54_ok : V54.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V54_fin : V54.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V54_V : V54.V where
  ok := V54_ok
  fin := V54_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K73_chk, List.forall_mem_cons.2 ⟨K106_chk, List.forall_mem_cons.2 ⟨K135_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K146_chk, List.forall_mem_cons.2 ⟨K149_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V55 : UnitD := ⟨56521734575, 1478265425, [K5, K74, K135, K142], [K150, K154, K162, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 80, 85, false, false⟩

theorem V55_ok : V55.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V55_fin : V55.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V55_V : V55.V where
  ok := V55_ok
  fin := V55_fin
  h0 := List.forall_mem_cons.2 ⟨K5_chk, List.forall_mem_cons.2 ⟨K74_chk, List.forall_mem_cons.2 ⟨K135_chk, List.forall_mem_cons.2 ⟨K142_chk, List.forall_mem_nil _⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K150_chk, List.forall_mem_cons.2 ⟨K154_chk, List.forall_mem_cons.2 ⟨K162_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V56 : UnitD := ⟨58881355931, 881355931, [K6, K136], [K151, K153, K157, K162, K172, K204, K275, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 80, 86, false, false⟩

theorem V56_ok : V56.ok = true := by
  -- kcost: 0.2 s measured mean, 19 pairs, 6 Nov
  decide +kernel

theorem V56_fin : V56.fin = true := by
  -- kcost: 1.4 s measured mean, 19 pair polynomials, 6 Nov
  decide +kernel

theorem V56_V : V56.V where
  ok := V56_ok
  fin := V56_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_nil _⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K151_chk, List.forall_mem_cons.2 ⟨K153_chk, List.forall_mem_cons.2 ⟨K157_chk, List.forall_mem_cons.2 ⟨K162_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V57 : UnitD := ⟨60644067795, 881355933, [K6, K136, K143], [K156, K159, K162, K172, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 81, 89, false, false⟩

theorem V57_ok : V57.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V57_fin : V57.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V57_V : V57.V where
  ok := V57_ok
  fin := V57_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_cons.2 ⟨K143_chk, List.forall_mem_nil _⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K156_chk, List.forall_mem_cons.2 ⟨K159_chk, List.forall_mem_cons.2 ⟨K162_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V58 : UnitD := ⟨61966101693, 440677965, [K6, K136, K143, K145, K146], [K156, K159, K162, K171, K186, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 84, 89, false, false⟩

theorem V58_ok : V58.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V58_fin : V58.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V58_V : V58.V where
  ok := V58_ok
  fin := V58_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_cons.2 ⟨K143_chk, List.forall_mem_cons.2 ⟨K145_chk, List.forall_mem_cons.2 ⟨K146_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K156_chk, List.forall_mem_cons.2 ⟨K159_chk, List.forall_mem_cons.2 ⟨K162_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V59 : UnitD := ⟨63288135591, 881355933, [K6, K136, K143, K145, K146, K148], [K161, K164, K171, K186, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 85, 92, false, false⟩

theorem V59_ok : V59.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V59_fin : V59.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V59_V : V59.V where
  ok := V59_ok
  fin := V59_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_cons.2 ⟨K143_chk, List.forall_mem_cons.2 ⟨K145_chk, List.forall_mem_cons.2 ⟨K146_chk, List.forall_mem_cons.2 ⟨K148_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K161_chk, List.forall_mem_cons.2 ⟨K164_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V60 : UnitD := ⟨65050847457, 881355933, [K6, K136, K144, K146, K148, K150, K152], [K163, K166, K170, K178, K186, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 88, 94, false, false⟩

theorem V60_ok : V60.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V60_fin : V60.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V60_V : V60.V where
  ok := V60_ok
  fin := V60_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K146_chk, List.forall_mem_cons.2 ⟨K148_chk, List.forall_mem_cons.2 ⟨K150_chk, List.forall_mem_cons.2 ⟨K152_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K163_chk, List.forall_mem_cons.2 ⟨K166_chk, List.forall_mem_cons.2 ⟨K170_chk, List.forall_mem_cons.2 ⟨K178_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def L1 : List UnitD := [V31, V32, V33, V34, V35, V36, V37, V38, V39, V40, V41, V42, V43, V44, V45, V46, V47, V48, V49, V50, V51, V52, V53, V54, V55, V56, V57, V58, V59, V60]

theorem L1_V : ∀ u ∈ L1, u.V :=
  List.forall_mem_cons.2 ⟨V31_V, List.forall_mem_cons.2 ⟨V32_V, List.forall_mem_cons.2 ⟨V33_V, List.forall_mem_cons.2 ⟨V34_V, List.forall_mem_cons.2 ⟨V35_V, List.forall_mem_cons.2 ⟨V36_V, List.forall_mem_cons.2 ⟨V37_V, List.forall_mem_cons.2 ⟨V38_V, List.forall_mem_cons.2 ⟨V39_V, List.forall_mem_cons.2 ⟨V40_V, List.forall_mem_cons.2 ⟨V41_V, List.forall_mem_cons.2 ⟨V42_V, List.forall_mem_cons.2 ⟨V43_V, List.forall_mem_cons.2 ⟨V44_V, List.forall_mem_cons.2 ⟨V45_V, List.forall_mem_cons.2 ⟨V46_V, List.forall_mem_cons.2 ⟨V47_V, List.forall_mem_cons.2 ⟨V48_V, List.forall_mem_cons.2 ⟨V49_V, List.forall_mem_cons.2 ⟨V50_V, List.forall_mem_cons.2 ⟨V51_V, List.forall_mem_cons.2 ⟨V52_V, List.forall_mem_cons.2 ⟨V53_V, List.forall_mem_cons.2 ⟨V54_V, List.forall_mem_cons.2 ⟨V55_V, List.forall_mem_cons.2 ⟨V56_V, List.forall_mem_cons.2 ⟨V57_V, List.forall_mem_cons.2 ⟨V58_V, List.forall_mem_cons.2 ⟨V59_V, List.forall_mem_cons.2 ⟨V60_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
