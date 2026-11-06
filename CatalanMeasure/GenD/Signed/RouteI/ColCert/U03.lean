module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V91 : UnitD := ⟨109318181817, 681818183, [K6, K139, K172, K202, K219, K236, K245, K247, K249], [K262, K266, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 146, 152, false, false⟩

theorem V91_ok : V91.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V91_fin : V91.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V91_V : V91.V where
  ok := V91_ok
  fin := V91_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K202_chk, List.forall_mem_cons.2 ⟨K219_chk, List.forall_mem_cons.2 ⟨K236_chk, List.forall_mem_cons.2 ⟨K245_chk, List.forall_mem_cons.2 ⟨K247_chk, List.forall_mem_cons.2 ⟨K249_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K262_chk, List.forall_mem_cons.2 ⟨K266_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V92 : UnitD := ⟨111181818181, 1181818181, [K6, K139, K172, K203, K236, K245, K247, K249, K251], [K261, K264, K266, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 147, 152, false, false⟩

theorem V92_ok : V92.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V92_fin : V92.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V92_V : V92.V where
  ok := V92_ok
  fin := V92_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K139_chk, List.forall_mem_cons.2 ⟨K172_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K236_chk, List.forall_mem_cons.2 ⟨K245_chk, List.forall_mem_cons.2 ⟨K247_chk, List.forall_mem_cons.2 ⟨K249_chk, List.forall_mem_cons.2 ⟨K251_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K261_chk, List.forall_mem_cons.2 ⟨K264_chk, List.forall_mem_cons.2 ⟨K266_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V93 : UnitD := ⟨114227272725, 1863636363, [K6, K140, K203, K236, K246, K252, K256], [K264, K266, K273, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 150, 153, false, false⟩

theorem V93_ok : V93.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V93_fin : V93.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V93_V : V93.V where
  ok := V93_ok
  fin := V93_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K236_chk, List.forall_mem_cons.2 ⟨K246_chk, List.forall_mem_cons.2 ⟨K252_chk, List.forall_mem_cons.2 ⟨K256_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K264_chk, List.forall_mem_cons.2 ⟨K266_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V94 : UnitD := ⟨117022727269, 931818181, [K6, K140, K203, K237, K252, K256, K258], [K265, K268, K272, K283, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 151, 154, false, false⟩

theorem V94_ok : V94.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V94_fin : V94.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V94_V : V94.V where
  ok := V94_ok
  fin := V94_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K252_chk, List.forall_mem_cons.2 ⟨K256_chk, List.forall_mem_cons.2 ⟨K258_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K265_chk, List.forall_mem_cons.2 ⟨K268_chk, List.forall_mem_cons.2 ⟨K272_chk, List.forall_mem_cons.2 ⟨K283_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V95 : UnitD := ⟨118886363633, 931818183, [K6, K140, K203, K237, K252, K256, K258], [K265, K268, K272, K283, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 151, 154, false, false⟩

theorem V95_ok : V95.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V95_fin : V95.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V95_V : V95.V where
  ok := V95_ok
  fin := V95_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K252_chk, List.forall_mem_cons.2 ⟨K256_chk, List.forall_mem_cons.2 ⟨K258_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K265_chk, List.forall_mem_cons.2 ⟨K268_chk, List.forall_mem_cons.2 ⟨K272_chk, List.forall_mem_cons.2 ⟨K283_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V96 : UnitD := ⟨121681818179, 1863636363, [K6, K140, K203, K237, K252, K256, K258], [K267, K269, K272, K283, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 151, 155, false, false⟩

theorem V96_ok : V96.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V96_fin : V96.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V96_V : V96.V where
  ok := V96_ok
  fin := V96_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K252_chk, List.forall_mem_cons.2 ⟨K256_chk, List.forall_mem_cons.2 ⟨K258_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K267_chk, List.forall_mem_cons.2 ⟨K269_chk, List.forall_mem_cons.2 ⟨K272_chk, List.forall_mem_cons.2 ⟨K283_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V97 : UnitD := ⟨125409090907, 1863636365, [K6, K140, K203, K237, K253], [K271, K279, K283, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 152, 157, false, false⟩

theorem V97_ok : V97.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V97_fin : V97.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V97_V : V97.V where
  ok := V97_ok
  fin := V97_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K271_chk, List.forall_mem_cons.2 ⟨K279_chk, List.forall_mem_cons.2 ⟨K283_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V98 : UnitD := ⟨129136363635, 1863636363, [K6, K140, K203, K237, K253, K261, K264], [K270, K277, K279, K283, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 154, 157, false, false⟩

theorem V98_ok : V98.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V98_fin : V98.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V98_V : V98.V where
  ok := V98_ok
  fin := V98_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K261_chk, List.forall_mem_cons.2 ⟨K264_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K270_chk, List.forall_mem_cons.2 ⟨K277_chk, List.forall_mem_cons.2 ⟨K279_chk, List.forall_mem_cons.2 ⟨K283_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V99 : UnitD := ⟨132863636361, 1863636363, [K6, K140, K203, K237, K253, K262], [K277, K279, K283, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 154, 158, false, false⟩

theorem V99_ok : V99.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V99_fin : V99.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V99_V : V99.V where
  ok := V99_ok
  fin := V99_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K262_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K277_chk, List.forall_mem_cons.2 ⟨K279_chk, List.forall_mem_cons.2 ⟨K283_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V100 : UnitD := ⟨136590909089, 1863636365, [K6, K140, K203, K237, K253, K262, K265], [K280, K282, K286, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 155, 160, false, false⟩

theorem V100_ok : V100.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V100_fin : V100.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V100_V : V100.V where
  ok := V100_ok
  fin := V100_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K262_chk, List.forall_mem_cons.2 ⟨K265_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K280_chk, List.forall_mem_cons.2 ⟨K282_chk, List.forall_mem_cons.2 ⟨K286_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V101 : UnitD := ⟨142181818181, 3727272727, [K6, K140, K203, K237, K253, K262, K265, K267], [K284, K286, K293, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 156, 162, false, false⟩

theorem V101_ok : V101.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V101_fin : V101.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V101_V : V101.V where
  ok := V101_ok
  fin := V101_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K262_chk, List.forall_mem_cons.2 ⟨K265_chk, List.forall_mem_cons.2 ⟨K267_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K284_chk, List.forall_mem_cons.2 ⟨K286_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V102 : UnitD := ⟨147772727271, 1863636363, [K6, K140, K203, K237, K253, K263, K270], [K284, K286, K292, K302, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 158, 162, false, false⟩

theorem V102_ok : V102.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V102_fin : V102.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V102_V : V102.V where
  ok := V102_ok
  fin := V102_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K270_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K284_chk, List.forall_mem_cons.2 ⟨K286_chk, List.forall_mem_cons.2 ⟨K292_chk, List.forall_mem_cons.2 ⟨K302_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V103 : UnitD := ⟨151499999999, 1863636365, [K6, K140, K203, K237, K253, K263, K271], [K288, K292, K302, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 159, 164, false, false⟩

theorem V103_ok : V103.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V103_fin : V103.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V103_V : V103.V where
  ok := V103_ok
  fin := V103_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K253_chk, List.forall_mem_cons.2 ⟨K263_chk, List.forall_mem_cons.2 ⟨K271_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K288_chk, List.forall_mem_cons.2 ⟨K292_chk, List.forall_mem_cons.2 ⟨K302_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V104 : UnitD := ⟨157090909091, 3727272727, [K6, K140, K203, K237, K254, K271, K278], [K291, K296, K302, K311, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 160, 166, false, false⟩

theorem V104_ok : V104.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V104_fin : V104.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V104_V : V104.V where
  ok := V104_ok
  fin := V104_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K237_chk, List.forall_mem_cons.2 ⟨K254_chk, List.forall_mem_cons.2 ⟨K271_chk, List.forall_mem_cons.2 ⟨K278_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K291_chk, List.forall_mem_cons.2 ⟨K296_chk, List.forall_mem_cons.2 ⟨K302_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V105 : UnitD := ⟨164545454545, 3727272727, [K6, K140, K203, K238, K272, K281], [K295, K298, K302, K310, K330, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 162, 168, false, false⟩

theorem V105_ok : V105.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V105_fin : V105.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V105_V : V105.V where
  ok := V105_ok
  fin := V105_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K203_chk, List.forall_mem_cons.2 ⟨K238_chk, List.forall_mem_cons.2 ⟨K272_chk, List.forall_mem_cons.2 ⟨K281_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K295_chk, List.forall_mem_cons.2 ⟨K298_chk, List.forall_mem_cons.2 ⟨K302_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V106 : UnitD := ⟨171999999999, 3727272727, [K6, K140, K204, K272, K282, K285], [K299, K301, K305, K310, K330, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 164, 170, false, false⟩

theorem V106_ok : V106.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V106_fin : V106.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V106_V : V106.V where
  ok := V106_ok
  fin := V106_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K272_chk, List.forall_mem_cons.2 ⟨K282_chk, List.forall_mem_cons.2 ⟨K285_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K299_chk, List.forall_mem_cons.2 ⟨K301_chk, List.forall_mem_cons.2 ⟨K305_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V107 : UnitD := ⟨179454545453, 3727272727, [K6, K140, K204, K272, K282, K285, K287, K289], [K303, K305, K310, K330, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 166, 172, false, false⟩

theorem V107_ok : V107.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V107_fin : V107.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V107_V : V107.V where
  ok := V107_ok
  fin := V107_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K272_chk, List.forall_mem_cons.2 ⟨K282_chk, List.forall_mem_cons.2 ⟨K285_chk, List.forall_mem_cons.2 ⟨K287_chk, List.forall_mem_cons.2 ⟨K289_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K303_chk, List.forall_mem_cons.2 ⟨K305_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V108 : UnitD := ⟨186909090907, 3727272727, [K6, K140, K204, K272, K283, K290, K294], [K306, K309, K320, K330, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 168, 174, false, false⟩

theorem V108_ok : V108.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V108_fin : V108.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V108_V : V108.V where
  ok := V108_ok
  fin := V108_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K140_chk, List.forall_mem_cons.2 ⟨K204_chk, List.forall_mem_cons.2 ⟨K272_chk, List.forall_mem_cons.2 ⟨K283_chk, List.forall_mem_cons.2 ⟨K290_chk, List.forall_mem_cons.2 ⟨K294_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K306_chk, List.forall_mem_cons.2 ⟨K309_chk, List.forall_mem_cons.2 ⟨K320_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V109 : UnitD := ⟨194363636361, 3727272727, [K6, K141, K273, K291, K295, K297], [K308, K314, K320, K330, K350, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 170, 176, false, false⟩

theorem V109_ok : V109.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V109_fin : V109.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V109_V : V109.V where
  ok := V109_ok
  fin := V109_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K141_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K291_chk, List.forall_mem_cons.2 ⟨K295_chk, List.forall_mem_cons.2 ⟨K297_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K308_chk, List.forall_mem_cons.2 ⟨K314_chk, List.forall_mem_cons.2 ⟨K320_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V110 : UnitD := ⟨201818181815, 3727272727, [K6, K141, K273, K291, K296, K300], [K313, K316, K320, K330, K349, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 172, 178, false, false⟩

theorem V110_ok : V110.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V110_fin : V110.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V110_V : V110.V where
  ok := V110_ok
  fin := V110_fin
  h0 := List.forall_mem_cons.2 ⟨K6_chk, List.forall_mem_cons.2 ⟨K141_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K291_chk, List.forall_mem_cons.2 ⟨K296_chk, List.forall_mem_cons.2 ⟨K300_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K313_chk, List.forall_mem_cons.2 ⟨K316_chk, List.forall_mem_cons.2 ⟨K320_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V111 : UnitD := ⟨209272727271, 3727272729, [K7, K273, K292, K301, K304], [K317, K319, K323, K330, K349, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 174, 180, false, false⟩

theorem V111_ok : V111.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V111_fin : V111.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V111_V : V111.V where
  ok := V111_ok
  fin := V111_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K292_chk, List.forall_mem_cons.2 ⟨K301_chk, List.forall_mem_cons.2 ⟨K304_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K317_chk, List.forall_mem_cons.2 ⟨K319_chk, List.forall_mem_cons.2 ⟨K323_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V112 : UnitD := ⟨216727272727, 3727272727, [K7, K273, K292, K301, K304, K306], [K321, K323, K330, K349, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 176, 182, false, false⟩

theorem V112_ok : V112.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V112_fin : V112.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V112_V : V112.V where
  ok := V112_ok
  fin := V112_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K292_chk, List.forall_mem_cons.2 ⟨K301_chk, List.forall_mem_cons.2 ⟨K304_chk, List.forall_mem_cons.2 ⟨K306_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K321_chk, List.forall_mem_cons.2 ⟨K323_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V113 : UnitD := ⟨224181818181, 3727272727, [K7, K273, K292, K302, K307, K312], [K325, K329, K339, K349, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 178, 184, false, false⟩

theorem V113_ok : V113.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V113_fin : V113.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V113_V : V113.V where
  ok := V113_ok
  fin := V113_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K292_chk, List.forall_mem_cons.2 ⟨K302_chk, List.forall_mem_cons.2 ⟨K307_chk, List.forall_mem_cons.2 ⟨K312_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K325_chk, List.forall_mem_cons.2 ⟨K329_chk, List.forall_mem_cons.2 ⟨K339_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V114 : UnitD := ⟨231636363635, 3727272727, [K7, K273, K293, K308, K313, K315], [K328, K333, K339, K349, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 180, 186, false, false⟩

theorem V114_ok : V114.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V114_fin : V114.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V114_V : V114.V where
  ok := V114_ok
  fin := V114_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K308_chk, List.forall_mem_cons.2 ⟨K313_chk, List.forall_mem_cons.2 ⟨K315_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K328_chk, List.forall_mem_cons.2 ⟨K333_chk, List.forall_mem_cons.2 ⟨K339_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V115 : UnitD := ⟨239090909089, 3727272727, [K7, K273, K293, K308, K314, K318], [K332, K335, K339, K348, K367, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 182, 188, false, false⟩

theorem V115_ok : V115.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V115_fin : V115.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V115_V : V115.V where
  ok := V115_ok
  fin := V115_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K308_chk, List.forall_mem_cons.2 ⟨K314_chk, List.forall_mem_cons.2 ⟨K318_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K332_chk, List.forall_mem_cons.2 ⟨K335_chk, List.forall_mem_cons.2 ⟨K339_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V116 : UnitD := ⟨246545454543, 3727272727, [K7, K273, K293, K309, K319, K322], [K336, K338, K342, K348, K367, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 184, 190, false, false⟩

theorem V116_ok : V116.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V116_fin : V116.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V116_V : V116.V where
  ok := V116_ok
  fin := V116_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K273_chk, List.forall_mem_cons.2 ⟨K293_chk, List.forall_mem_cons.2 ⟨K309_chk, List.forall_mem_cons.2 ⟨K319_chk, List.forall_mem_cons.2 ⟨K322_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K336_chk, List.forall_mem_cons.2 ⟨K338_chk, List.forall_mem_cons.2 ⟨K342_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V117 : UnitD := ⟨253999999997, 3727272727, [K7, K274, K309, K319, K322, K324, K326], [K340, K342, K348, K367, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 186, 192, false, false⟩

theorem V117_ok : V117.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V117_fin : V117.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V117_V : V117.V where
  ok := V117_ok
  fin := V117_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K309_chk, List.forall_mem_cons.2 ⟨K319_chk, List.forall_mem_cons.2 ⟨K322_chk, List.forall_mem_cons.2 ⟨K324_chk, List.forall_mem_cons.2 ⟨K326_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K340_chk, List.forall_mem_cons.2 ⟨K342_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V118 : UnitD := ⟨261454545453, 3727272729, [K7, K274, K309, K320, K327, K331], [K343, K344, K347, K357, K367, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 188, 194, false, false⟩

theorem V118_ok : V118.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V118_fin : V118.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V118_V : V118.V where
  ok := V118_ok
  fin := V118_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K309_chk, List.forall_mem_cons.2 ⟨K320_chk, List.forall_mem_cons.2 ⟨K327_chk, List.forall_mem_cons.2 ⟨K331_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K343_chk, List.forall_mem_cons.2 ⟨K344_chk, List.forall_mem_cons.2 ⟨K347_chk, List.forall_mem_cons.2 ⟨K357_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V119 : UnitD := ⟨268909090909, 3727272727, [K7, K274, K310, K328, K332, K334], [K346, K353, K357, K367, K386, K425, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 190, 196, false, false⟩

theorem V119_ok : V119.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V119_fin : V119.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V119_V : V119.V where
  ok := V119_ok
  fin := V119_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K328_chk, List.forall_mem_cons.2 ⟨K332_chk, List.forall_mem_cons.2 ⟨K334_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K346_chk, List.forall_mem_cons.2 ⟨K353_chk, List.forall_mem_cons.2 ⟨K357_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V120 : UnitD := ⟨276363636363, 3727272727, [K7, K274, K310, K328, K333, K337], [K353, K357, K367, K386, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 192, 198, false, false⟩

theorem V120_ok : V120.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V120_fin : V120.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V120_V : V120.V where
  ok := V120_ok
  fin := V120_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K328_chk, List.forall_mem_cons.2 ⟨K333_chk, List.forall_mem_cons.2 ⟨K337_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K353_chk, List.forall_mem_cons.2 ⟨K357_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def L3 : List UnitD := [V91, V92, V93, V94, V95, V96, V97, V98, V99, V100, V101, V102, V103, V104, V105, V106, V107, V108, V109, V110, V111, V112, V113, V114, V115, V116, V117, V118, V119, V120]

theorem L3_V : ∀ u ∈ L3, u.V :=
  List.forall_mem_cons.2 ⟨V91_V, List.forall_mem_cons.2 ⟨V92_V, List.forall_mem_cons.2 ⟨V93_V, List.forall_mem_cons.2 ⟨V94_V, List.forall_mem_cons.2 ⟨V95_V, List.forall_mem_cons.2 ⟨V96_V, List.forall_mem_cons.2 ⟨V97_V, List.forall_mem_cons.2 ⟨V98_V, List.forall_mem_cons.2 ⟨V99_V, List.forall_mem_cons.2 ⟨V100_V, List.forall_mem_cons.2 ⟨V101_V, List.forall_mem_cons.2 ⟨V102_V, List.forall_mem_cons.2 ⟨V103_V, List.forall_mem_cons.2 ⟨V104_V, List.forall_mem_cons.2 ⟨V105_V, List.forall_mem_cons.2 ⟨V106_V, List.forall_mem_cons.2 ⟨V107_V, List.forall_mem_cons.2 ⟨V108_V, List.forall_mem_cons.2 ⟨V109_V, List.forall_mem_cons.2 ⟨V110_V, List.forall_mem_cons.2 ⟨V111_V, List.forall_mem_cons.2 ⟨V112_V, List.forall_mem_cons.2 ⟨V113_V, List.forall_mem_cons.2 ⟨V114_V, List.forall_mem_cons.2 ⟨V115_V, List.forall_mem_cons.2 ⟨V116_V, List.forall_mem_cons.2 ⟨V117_V, List.forall_mem_cons.2 ⟨V118_V, List.forall_mem_cons.2 ⟨V119_V, List.forall_mem_cons.2 ⟨V120_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
