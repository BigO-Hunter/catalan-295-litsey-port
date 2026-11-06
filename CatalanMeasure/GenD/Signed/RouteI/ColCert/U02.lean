module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V61 : UnitD := ⟨66813559321, 881355931, [K6, K136, K144, K147, K153, K156], [K167, K170, K178, K186, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 90, 96, false, false⟩

theorem V61_ok : V61.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V61_fin : V61.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V61_V : V61.V where
  ok := V61_ok
  fin := V61_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K153_chk, List.forall_mem_cons.2 ⟨K156_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K167_chk, List.forall_mem_cons.2 ⟨K170_chk, List.forall_mem_cons.2 ⟨K178_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V62 : UnitD := ⟨68576271185, 881355933, [K6, K136, K144, K147, K153, K156, K158, K160], [K173, K175, K178, K186, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 92, 99, false, false⟩

theorem V62_ok : V62.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V62_fin : V62.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V62_V : V62.V where
  ok := V62_ok
  fin := V62_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K136_chk, List.forall_mem_cons.2 ⟨K144_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K153_chk, List.forall_mem_cons.2 ⟨K156_chk, List.forall_mem_cons.2 ⟨K158_chk, List.forall_mem_cons.2 ⟨K160_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K173_chk, List.forall_mem_cons.2 ⟨K175_chk, List.forall_mem_cons.2 ⟨K178_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V63 : UnitD := ⟨69920830493, 463203375, [K6, K137, K147, K154, K161], [K175, K178, K186, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 94, 100, false, false⟩

theorem V63_ok : V63.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V63_fin : V63.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V63_V : V63.V where
  ok := V63_ok
  fin := V63_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K137_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K154_chk, List.forall_mem_cons.2 ⟨K161_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K175_chk, List.forall_mem_cons.2 ⟨K178_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V64 : UnitD := ⟨71242864391, 858830523, [K6, K137, K147, K154, K161, K163], [K177, K180, K186, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 95, 102, false, false⟩

theorem V64_ok : V64.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V64_fin : V64.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V64_V : V64.V where
  ok := V64_ok
  fin := V64_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K137_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K154_chk, List.forall_mem_cons.2 ⟨K161_chk, List.forall_mem_cons.2 ⟨K163_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K177_chk, List.forall_mem_cons.2 ⟨K180_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V65 : UnitD := ⟨72983050847, 881355933, [K6, K137, K147, K154, K161, K163, K165, K167, K168], [K179, K182, K185, K193, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 98, 104, false, false⟩

theorem V65_ok : V65.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V65_fin : V65.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V65_V : V65.V where
  ok := V65_ok
  fin := V65_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K137_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K154_chk, List.forall_mem_cons.2 ⟨K161_chk, List.forall_mem_cons.2 ⟨K163_chk, List.forall_mem_cons.2 ⟨K165_chk, List.forall_mem_cons.2 ⟨K167_chk, List.forall_mem_cons.2 ⟨K168_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K179_chk, List.forall_mem_cons.2 ⟨K182_chk, List.forall_mem_cons.2 ⟨K185_chk, List.forall_mem_cons.2 ⟨K193_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V66 : UnitD := ⟨74745762711, 881355931, [K6, K137, K147, K154, K162, K169, K173], [K183, K185, K193, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 100, 106, false, false⟩

theorem V66_ok : V66.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V66_fin : V66.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V66_V : V66.V where
  ok := V66_ok
  fin := V66_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K137_chk, List.forall_mem_cons.2 ⟨K147_chk, List.forall_mem_cons.2 ⟨K154_chk, List.forall_mem_cons.2 ⟨K162_chk, List.forall_mem_cons.2 ⟨K169_chk, List.forall_mem_cons.2 ⟨K173_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K183_chk, List.forall_mem_cons.2 ⟨K185_chk, List.forall_mem_cons.2 ⟨K193_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V67 : UnitD := ⟨76508474575, 881355933, [K6, K138, K155, K169, K173, K174, K176], [K187, K189, K193, K203, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 102, 108, false, false⟩

theorem V67_ok : V67.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V67_fin : V67.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V67_V : V67.V where
  ok := V67_ok
  fin := V67_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K169_chk, List.forall_mem_cons.2 ⟨K173_chk, List.forall_mem_cons.2 ⟨K174_chk, List.forall_mem_cons.2 ⟨K176_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K187_chk, List.forall_mem_cons.2 ⟨K189_chk, List.forall_mem_cons.2 ⟨K193_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V68 : UnitD := ⟨78271186439, 881355931, [K6, K138, K155, K170, K177], [K191, K192, K195, K202, K219, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 104, 111, false, false⟩

theorem V68_ok : V68.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V68_fin : V68.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V68_V : V68.V where
  ok := V68_ok
  fin := V68_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K170_chk, List.forall_mem_cons.2 ⟨K177_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K191_chk, List.forall_mem_cons.2 ⟨K192_chk, List.forall_mem_cons.2 ⟨K195_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V69 : UnitD := ⟨79593220337, 440677967, [K6, K138, K155, K170, K177, K179, K181], [K192, K195, K202, K219, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 106, 112, false, false⟩

theorem V69_ok : V69.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V69_fin : V69.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V69_V : V69.V where
  ok := V69_ok
  fin := V69_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K170_chk, List.forall_mem_cons.2 ⟨K177_chk, List.forall_mem_cons.2 ⟨K179_chk, List.forall_mem_cons.2 ⟨K181_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K192_chk, List.forall_mem_cons.2 ⟨K195_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V70 : UnitD := ⟨80915254235, 881355931, [K6, K138, K155, K170, K177, K179, K181, K183], [K194, K197, K201, K210, K219, K238, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 107, 114, false, false⟩

theorem V70_ok : V70.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V70_fin : V70.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V70_V : V70.V where
  ok := V70_ok
  fin := V70_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K170_chk, List.forall_mem_cons.2 ⟨K177_chk, List.forall_mem_cons.2 ⟨K179_chk, List.forall_mem_cons.2 ⟨K181_chk, List.forall_mem_cons.2 ⟨K183_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K194_chk, List.forall_mem_cons.2 ⟨K197_chk, List.forall_mem_cons.2 ⟨K201_chk, List.forall_mem_cons.2 ⟨K210_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V71 : UnitD := ⟨82677966099, 881355933, [K6, K138, K155, K170, K178, K184, K188], [K198, K200, K207, K210, K219, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 110, 116, false, false⟩

theorem V71_ok : V71.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V71_fin : V71.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V71_V : V71.V where
  ok := V71_ok
  fin := V71_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K170_chk, List.forall_mem_cons.2 ⟨K178_chk, List.forall_mem_cons.2 ⟨K184_chk, List.forall_mem_cons.2 ⟨K188_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K198_chk, List.forall_mem_cons.2 ⟨K200_chk, List.forall_mem_cons.2 ⟨K207_chk, List.forall_mem_cons.2 ⟨K210_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V72 : UnitD := ⟨84440677965, 881355933, [K6, K138, K155, K171, K184, K188, K190, K191], [K205, K207, K210, K219, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 112, 118, false, false⟩

theorem V72_ok : V72.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V72_fin : V72.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V72_V : V72.V where
  ok := V72_ok
  fin := V72_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K184_chk, List.forall_mem_cons.2 ⟨K188_chk, List.forall_mem_cons.2 ⟨K190_chk, List.forall_mem_cons.2 ⟨K191_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K205_chk, List.forall_mem_cons.2 ⟨K207_chk, List.forall_mem_cons.2 ⟨K210_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V73 : UnitD := ⟨86203389829, 881355931, [K6, K138, K155, K171, K185, K192], [K208, K210, K219, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 114, 120, false, false⟩

theorem V73_ok : V73.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V73_fin : V73.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V73_V : V73.V where
  ok := V73_ok
  fin := V73_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K185_chk, List.forall_mem_cons.2 ⟨K192_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K208_chk, List.forall_mem_cons.2 ⟨K210_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V74 : UnitD := ⟨87966101693, 881355933, [K6, K138, K155, K171, K185, K192, K194, K196], [K211, K213, K219, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 116, 123, false, false⟩

theorem V74_ok : V74.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V74_fin : V74.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V74_V : V74.V where
  ok := V74_ok
  fin := V74_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K138_chk, List.forall_mem_cons.2 ⟨K155_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K185_chk, List.forall_mem_cons.2 ⟨K192_chk, List.forall_mem_cons.2 ⟨K194_chk, List.forall_mem_cons.2 ⟨K196_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K211_chk, List.forall_mem_cons.2 ⟨K213_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V75 : UnitD := ⟨89423728813, 576271187, [K6, K139, K171, K185, K192, K195, K199], [K212, K214, K218, K227, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 118, 124, false, false⟩

theorem V75_ok : V75.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V75_fin : V75.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V75_V : V75.V where
  ok := V75_ok
  fin := V75_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K185_chk, List.forall_mem_cons.2 ⟨K192_chk, List.forall_mem_cons.2 ⟨K195_chk, List.forall_mem_cons.2 ⟨K199_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K212_chk, List.forall_mem_cons.2 ⟨K214_chk, List.forall_mem_cons.2 ⟨K218_chk, List.forall_mem_cons.2 ⟨K227_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V76 : UnitD := ⟨90745762711, 745762711, [K6, K139, K171, K185, K193, K200], [K215, K217, K221, K227, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 119, 126, false, false⟩

theorem V76_ok : V76.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V76_fin : V76.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V76_V : V76.V where
  ok := V76_ok
  fin := V76_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K185_chk, List.forall_mem_cons.2 ⟨K193_chk, List.forall_mem_cons.2 ⟨K200_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K215_chk, List.forall_mem_cons.2 ⟨K217_chk, List.forall_mem_cons.2 ⟨K221_chk, List.forall_mem_cons.2 ⟨K227_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V77 : UnitD := ⟨92372881355, 881355933, [K6, K139, K171, K186, K200, K206, K208], [K220, K223, K227, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 122, 129, false, false⟩

theorem V77_ok : V77.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V77_fin : V77.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V77_V : V77.V where
  ok := V77_ok
  fin := V77_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K200_chk, List.forall_mem_cons.2 ⟨K206_chk, List.forall_mem_cons.2 ⟨K208_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K220_chk, List.forall_mem_cons.2 ⟨K223_chk, List.forall_mem_cons.2 ⟨K227_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V78 : UnitD := ⟨93694915253, 440677965, [K6, K139, K171, K186, K201, K209, K212], [K220, K223, K227, K237, K254, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 125, 129, false, false⟩

theorem V78_ok : V78.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V78_fin : V78.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V78_V : V78.V where
  ok := V78_ok
  fin := V78_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K201_chk, List.forall_mem_cons.2 ⟨K209_chk, List.forall_mem_cons.2 ⟨K212_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K220_chk, List.forall_mem_cons.2 ⟨K223_chk, List.forall_mem_cons.2 ⟨K227_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V79 : UnitD := ⟨95016949151, 881355933, [K6, K139, K171, K186, K201, K209, K212], [K226, K230, K237, K253, K263, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 125, 132, false, false⟩

theorem V79_ok : V79.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V79_fin : V79.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V79_V : V79.V where
  ok := V79_ok
  fin := V79_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K171_chk, List.forall_mem_cons.2 ⟨K186_chk, List.forall_mem_cons.2 ⟨K201_chk, List.forall_mem_cons.2 ⟨K209_chk, List.forall_mem_cons.2 ⟨K212_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K226_chk, List.forall_mem_cons.2 ⟨K230_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V80 : UnitD := ⟨96676425269, 778120185, [K6, K139, K172, K201, K209, K213, K216], [K232, K236, K246, K253, K263, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 128, 135, false, false⟩

theorem V80_ok : V80.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V80_fin : V80.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V80_V : V80.V where
  ok := V80_ok
  fin := V80_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K201_chk, List.forall_mem_cons.2 ⟨K209_chk, List.forall_mem_cons.2 ⟨K213_chk, List.forall_mem_cons.2 ⟨K216_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K232_chk, List.forall_mem_cons.2 ⟨K236_chk, List.forall_mem_cons.2 ⟨K246_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V81 : UnitD := ⟨97998459167, 543913713, [K6, K139, K172, K201, K210, K217, K220], [K233, K236, K246, K253, K263, K274, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 130, 136, false, false⟩

theorem V81_ok : V81.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V81_fin : V81.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V81_V : V81.V where
  ok := V81_ok
  fin := V81_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K201_chk, List.forall_mem_cons.2 ⟨K210_chk, List.forall_mem_cons.2 ⟨K217_chk, List.forall_mem_cons.2 ⟨K220_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K233_chk, List.forall_mem_cons.2 ⟨K236_chk, List.forall_mem_cons.2 ⟨K246_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V82 : UnitD := ⟨98983050847, 440677967, [K6, K139, K172, K202, K217, K220, K222, K224, K225], [K233, K235, K241, K246, K253, K263, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 133, 136, false, false⟩

theorem V82_ok : V82.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V82_fin : V82.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V82_V : V82.V where
  ok := V82_ok
  fin := V82_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K217_chk, List.forall_mem_cons.2 ⟨K220_chk, List.forall_mem_cons.2 ⟨K222_chk, List.forall_mem_cons.2 ⟨K224_chk, List.forall_mem_cons.2 ⟨K225_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K233_chk, List.forall_mem_cons.2 ⟨K235_chk, List.forall_mem_cons.2 ⟨K241_chk, List.forall_mem_cons.2 ⟨K246_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V83 : UnitD := ⟨99864406779, 440677965, [K6, K139, K172, K202, K217, K221, K225, K228], [K234, K239, K241, K246, K253, K263, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 134, 137, false, false⟩

theorem V83_ok : V83.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V83_fin : V83.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V83_V : V83.V where
  ok := V83_ok
  fin := V83_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K217_chk, List.forall_mem_cons.2 ⟨K221_chk, List.forall_mem_cons.2 ⟨K225_chk, List.forall_mem_cons.2 ⟨K228_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K234_chk, List.forall_mem_cons.2 ⟨K239_chk, List.forall_mem_cons.2 ⟨K241_chk, List.forall_mem_cons.2 ⟨K246_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V84 : UnitD := ⟨100745762711, 440677967, [K6, K139, K172, K202, K218, K226], [K243, K246, K253, K263, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 134, 140, false, false⟩

theorem V84_ok : V84.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V84_fin : V84.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V84_V : V84.V where
  ok := V84_ok
  fin := V84_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K218_chk, List.forall_mem_cons.2 ⟨K226_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K243_chk, List.forall_mem_cons.2 ⟨K246_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V85 : UnitD := ⟨101627118643, 440677965, [K6, K139, K172, K202, K218, K226, K229, K231], [K242, K244, K246, K253, K263, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 136, 140, false, false⟩

theorem V85_ok : V85.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V85_fin : V85.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V85_V : V85.V where
  ok := V85_ok
  fin := V85_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K218_chk, List.forall_mem_cons.2 ⟨K226_chk, List.forall_mem_cons.2 ⟨K229_chk, List.forall_mem_cons.2 ⟨K231_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K242_chk, List.forall_mem_cons.2 ⟨K244_chk, List.forall_mem_cons.2 ⟨K246_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V86 : UnitD := ⟨102508474575, 440677967, [K6, K139, K172, K202, K218, K226, K229, K231, K233, K234], [K244, K245, K248, K253, K263, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 138, 141, false, false⟩

theorem V86_ok : V86.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V86_fin : V86.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V86_V : V86.V where
  ok := V86_ok
  fin := V86_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K218_chk, List.forall_mem_cons.2 ⟨K226_chk, List.forall_mem_cons.2 ⟨K229_chk, List.forall_mem_cons.2 ⟨K231_chk, List.forall_mem_cons.2 ⟨K233_chk, List.forall_mem_cons.2 ⟨K234_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K244_chk, List.forall_mem_cons.2 ⟨K245_chk, List.forall_mem_cons.2 ⟨K248_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V87 : UnitD := ⟨103830508473, 881355931, [K6, K139, K172, K202, K218, K226, K229, K232, K234], [K250, K252, K257, K263, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 138, 145, false, false⟩

theorem V87_ok : V87.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V87_fin : V87.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V87_V : V87.V where
  ok := V87_ok
  fin := V87_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K218_chk, List.forall_mem_cons.2 ⟨K226_chk, List.forall_mem_cons.2 ⟨K229_chk, List.forall_mem_cons.2 ⟨K232_chk, List.forall_mem_cons.2 ⟨K234_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K250_chk, List.forall_mem_cons.2 ⟨K252_chk, List.forall_mem_cons.2 ⟨K257_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V88 : UnitD := ⟨105152542371, 440677967, [K6, K139, K172, K202, K218, K227, K235, K240], [K249, K251, K252, K256, K259, K263, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 140, 145, false, false⟩

theorem V88_ok : V88.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V88_fin : V88.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V88_V : V88.V where
  ok := V88_ok
  fin := V88_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K218_chk, List.forall_mem_cons.2 ⟨K227_chk, List.forall_mem_cons.2 ⟨K235_chk, List.forall_mem_cons.2 ⟨K240_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K249_chk, List.forall_mem_cons.2 ⟨K251_chk, List.forall_mem_cons.2 ⟨K252_chk, List.forall_mem_cons.2 ⟨K256_chk, List.forall_mem_cons.2 ⟨K259_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V89 : UnitD := ⟨106474576269, 881355931, [K6, K139, K172, K202, K218, K227, K235, K240, K242], [K255, K256, K258, K260, K262, K266, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 141, 148, false, false⟩

theorem V89_ok : V89.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V89_fin : V89.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V89_V : V89.V where
  ok := V89_ok
  fin := V89_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K218_chk, List.forall_mem_cons.2 ⟨K227_chk, List.forall_mem_cons.2 ⟨K235_chk, List.forall_mem_cons.2 ⟨K240_chk, List.forall_mem_cons.2 ⟨K242_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K255_chk, List.forall_mem_cons.2 ⟨K256_chk, List.forall_mem_cons.2 ⟨K258_chk, List.forall_mem_cons.2 ⟨K260_chk, List.forall_mem_cons.2 ⟨K262_chk, List.forall_mem_cons.2 ⟨K266_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V90 : UnitD := ⟨107996147917, 640215717, [K6, K139, K172, K202, K219, K236, K245], [K260, K262, K266, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 144, 151, false, false⟩

theorem V90_ok : V90.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V90_fin : V90.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V90_V : V90.V where
  ok := V90_ok
  fin := V90_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K236_chk, List.forall_mem_cons.2 ⟨K245_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K260_chk, List.forall_mem_cons.2 ⟨K262_chk, List.forall_mem_cons.2 ⟨K266_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def L2 : List UnitD := [V61, V62, V63, V64, V65, V66, V67, V68, V69, V70, V71, V72, V73, V74, V75, V76, V77, V78, V79, V80, V81, V82, V83, V84, V85, V86, V87, V88, V89, V90]

theorem L2_V : ∀ u ∈ L2, u.V :=
  List.forall_mem_cons.2 ⟨V61_V, List.forall_mem_cons.2 ⟨V62_V, List.forall_mem_cons.2 ⟨V63_V, List.forall_mem_cons.2 ⟨V64_V, List.forall_mem_cons.2 ⟨V65_V, List.forall_mem_cons.2 ⟨V66_V, List.forall_mem_cons.2 ⟨V67_V, List.forall_mem_cons.2 ⟨V68_V, List.forall_mem_cons.2 ⟨V69_V, List.forall_mem_cons.2 ⟨V70_V, List.forall_mem_cons.2 ⟨V71_V, List.forall_mem_cons.2 ⟨V72_V, List.forall_mem_cons.2 ⟨V73_V, List.forall_mem_cons.2 ⟨V74_V, List.forall_mem_cons.2 ⟨V75_V, List.forall_mem_cons.2 ⟨V76_V, List.forall_mem_cons.2 ⟨V77_V, List.forall_mem_cons.2 ⟨V78_V, List.forall_mem_cons.2 ⟨V79_V, List.forall_mem_cons.2 ⟨V80_V, List.forall_mem_cons.2 ⟨V81_V, List.forall_mem_cons.2 ⟨V82_V, List.forall_mem_cons.2 ⟨V83_V, List.forall_mem_cons.2 ⟨V84_V, List.forall_mem_cons.2 ⟨V85_V, List.forall_mem_cons.2 ⟨V86_V, List.forall_mem_cons.2 ⟨V87_V, List.forall_mem_cons.2 ⟨V88_V, List.forall_mem_cons.2 ⟨V89_V, List.forall_mem_cons.2 ⟨V90_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
