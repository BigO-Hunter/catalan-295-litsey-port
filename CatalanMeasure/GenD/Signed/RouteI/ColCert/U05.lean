module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V151 : UnitD := ⟨507454545457, 3727272727, [K7, K275, K350, K422, K440, K448, K451, K454], [K468, K470, K475, K485, K496, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 254, 260, false, false⟩

theorem V151_ok : V151.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V151_fin : V151.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V151_V : V151.V where
  ok := V151_ok
  fin := V151_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K440_chk, List.forall_mem_cons.2 ⟨K448_chk, List.forall_mem_cons.2 ⟨K451_chk, List.forall_mem_cons.2 ⟨K454_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K468_chk, List.forall_mem_cons.2 ⟨K470_chk, List.forall_mem_cons.2 ⟨K475_chk, List.forall_mem_cons.2 ⟨K485_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V152 : UnitD := ⟨514909090911, 3727272727, [K7, K275, K350, K422, K440, K449, K456], [K471, K472, K475, K485, K496, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 256, 262, false, false⟩

theorem V152_ok : V152.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V152_fin : V152.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V152_V : V152.V where
  ok := V152_ok
  fin := V152_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K440_chk, List.forall_mem_cons.2 ⟨K449_chk, List.forall_mem_cons.2 ⟨K456_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K471_chk, List.forall_mem_cons.2 ⟨K472_chk, List.forall_mem_cons.2 ⟨K475_chk, List.forall_mem_cons.2 ⟨K485_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V153 : UnitD := ⟨522363636365, 3727272727, [K7, K275, K350, K422, K441, K456, K460, K462], [K473, K477, K479, K485, K496, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 258, 264, false, false⟩

theorem V153_ok : V153.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V153_fin : V153.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V153_V : V153.V where
  ok := V153_ok
  fin := V153_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K456_chk, List.forall_mem_cons.2 ⟨K460_chk, List.forall_mem_cons.2 ⟨K462_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K473_chk, List.forall_mem_cons.2 ⟨K477_chk, List.forall_mem_cons.2 ⟨K479_chk, List.forall_mem_cons.2 ⟨K485_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V154 : UnitD := ⟨529818181819, 3727272727, [K7, K275, K350, K422, K441, K456, K461, K465], [K478, K481, K485, K495, K515, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 260, 266, false, false⟩

theorem V154_ok : V154.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V154_fin : V154.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V154_V : V154.V where
  ok := V154_ok
  fin := V154_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K456_chk, List.forall_mem_cons.2 ⟨K461_chk, List.forall_mem_cons.2 ⟨K465_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K478_chk, List.forall_mem_cons.2 ⟨K481_chk, List.forall_mem_cons.2 ⟨K485_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V155 : UnitD := ⟨537272727273, 3727272727, [K7, K275, K350, K422, K441, K457, K466, K469], [K482, K484, K488, K495, K515, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 262, 268, false, false⟩

theorem V155_ok : V155.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V155_fin : V155.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V155_V : V155.V where
  ok := V155_ok
  fin := V155_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K457_chk, List.forall_mem_cons.2 ⟨K466_chk, List.forall_mem_cons.2 ⟨K469_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K482_chk, List.forall_mem_cons.2 ⟨K484_chk, List.forall_mem_cons.2 ⟨K488_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V156 : UnitD := ⟨544727272729, 3727272729, [K7, K275, K350, K423, K457, K466, K469, K471, K472], [K486, K488, K494, K506, K515, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 264, 270, false, false⟩

theorem V156_ok : V156.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V156_fin : V156.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V156_V : V156.V where
  ok := V156_ok
  fin := V156_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K457_chk, List.forall_mem_cons.2 ⟨K466_chk, List.forall_mem_cons.2 ⟨K469_chk, List.forall_mem_cons.2 ⟨K471_chk, List.forall_mem_cons.2 ⟨K472_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K486_chk, List.forall_mem_cons.2 ⟨K488_chk, List.forall_mem_cons.2 ⟨K494_chk, List.forall_mem_cons.2 ⟨K506_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V157 : UnitD := ⟨552181818185, 3727272727, [K7, K275, K350, K423, K457, K467, K474], [K489, K491, K494, K506, K515, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 266, 272, false, false⟩

theorem V157_ok : V157.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V157_fin : V157.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V157_V : V157.V where
  ok := V157_ok
  fin := V157_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K457_chk, List.forall_mem_cons.2 ⟨K467_chk, List.forall_mem_cons.2 ⟨K474_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K489_chk, List.forall_mem_cons.2 ⟨K491_chk, List.forall_mem_cons.2 ⟨K494_chk, List.forall_mem_cons.2 ⟨K506_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V158 : UnitD := ⟨559636363639, 3727272727, [K7, K275, K350, K423, K458, K474, K478, K480], [K492, K498, K500, K506, K515, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 268, 274, false, false⟩

theorem V158_ok : V158.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V158_fin : V158.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V158_V : V158.V where
  ok := V158_ok
  fin := V158_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K474_chk, List.forall_mem_cons.2 ⟨K478_chk, List.forall_mem_cons.2 ⟨K480_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K492_chk, List.forall_mem_cons.2 ⟨K498_chk, List.forall_mem_cons.2 ⟨K500_chk, List.forall_mem_cons.2 ⟨K506_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V159 : UnitD := ⟨567090909093, 3727272727, [K7, K275, K350, K423, K458, K474, K479, K483], [K499, K502, K506, K515, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 270, 276, false, false⟩

theorem V159_ok : V159.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V159_fin : V159.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V159_V : V159.V where
  ok := V159_ok
  fin := V159_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K474_chk, List.forall_mem_cons.2 ⟨K479_chk, List.forall_mem_cons.2 ⟨K483_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K499_chk, List.forall_mem_cons.2 ⟨K502_chk, List.forall_mem_cons.2 ⟨K506_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V160 : UnitD := ⟨574545454547, 3727272727, [K7, K275, K350, K423, K458, K475, K484, K487], [K503, K505, K509, K515, K533, K573, K850], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 272, 278, false, false⟩

theorem V160_ok : V160.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V160_fin : V160.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V160_V : V160.V where
  ok := V160_ok
  fin := V160_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K350_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K475_chk, List.forall_mem_cons.2 ⟨K484_chk, List.forall_mem_cons.2 ⟨K487_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K503_chk, List.forall_mem_cons.2 ⟨K505_chk, List.forall_mem_cons.2 ⟨K509_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K573_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V161 : UnitD := ⟨582000000001, 3727272727, [K7, K276, K423, K458, K475, K484, K487, K490], [K507, K509, K514, K523, K533, K573, K850], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 274, 280, false, false⟩

theorem V161_ok : V161.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V161_fin : V161.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V161_V : V161.V where
  ok := V161_ok
  fin := V161_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K475_chk, List.forall_mem_cons.2 ⟨K484_chk, List.forall_mem_cons.2 ⟨K487_chk, List.forall_mem_cons.2 ⟨K490_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K507_chk, List.forall_mem_cons.2 ⟨K509_chk, List.forall_mem_cons.2 ⟨K514_chk, List.forall_mem_cons.2 ⟨K523_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K573_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V162 : UnitD := ⟨589454545455, 3727272727, [K7, K276, K423, K458, K475, K485, K493], [K510, K512, K514, K523, K533, K573, K850], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 276, 282, false, false⟩

theorem V162_ok : V162.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V162_fin : V162.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V162_V : V162.V where
  ok := V162_ok
  fin := V162_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K475_chk, List.forall_mem_cons.2 ⟨K485_chk, List.forall_mem_cons.2 ⟨K493_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K510_chk, List.forall_mem_cons.2 ⟨K512_chk, List.forall_mem_cons.2 ⟨K514_chk, List.forall_mem_cons.2 ⟨K523_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K573_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V163 : UnitD := ⟨596909090909, 3727272727, [K7, K276, K423, K458, K476, K493, K499, K501], [K513, K517, K523, K533, K572, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 278, 284, false, false⟩

theorem V163_ok : V163.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V163_fin : V163.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V163_V : V163.V where
  ok := V163_ok
  fin := V163_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K493_chk, List.forall_mem_cons.2 ⟨K499_chk, List.forall_mem_cons.2 ⟨K501_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K513_chk, List.forall_mem_cons.2 ⟨K517_chk, List.forall_mem_cons.2 ⟨K523_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K572_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V164 : UnitD := ⟨604363636365, 3727272729, [K7, K276, K423, K458, K476, K493, K500, K504], [K516, K519, K523, K532, K552, K572, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 280, 286, false, false⟩

theorem V164_ok : V164.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V164_fin : V164.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V164_V : V164.V where
  ok := V164_ok
  fin := V164_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K493_chk, List.forall_mem_cons.2 ⟨K500_chk, List.forall_mem_cons.2 ⟨K504_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K516_chk, List.forall_mem_cons.2 ⟨K519_chk, List.forall_mem_cons.2 ⟨K523_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K572_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V165 : UnitD := ⟨611818181821, 3727272727, [K7, K276, K423, K458, K476, K494, K505, K508], [K520, K522, K526, K532, K552, K572, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 282, 288, false, false⟩

theorem V165_ok : V165.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V165_fin : V165.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V165_V : V165.V where
  ok := V165_ok
  fin := V165_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K494_chk, List.forall_mem_cons.2 ⟨K505_chk, List.forall_mem_cons.2 ⟨K508_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K520_chk, List.forall_mem_cons.2 ⟨K522_chk, List.forall_mem_cons.2 ⟨K526_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K572_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V166 : UnitD := ⟨619272727275, 3727272727, [K7, K276, K423, K459, K494, K505, K508, K511], [K524, K526, K531, K542, K552, K571, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 284, 290, false, false⟩

theorem V166_ok : V166.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V166_fin : V166.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V166_V : V166.V where
  ok := V166_ok
  fin := V166_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K494_chk, List.forall_mem_cons.2 ⟨K505_chk, List.forall_mem_cons.2 ⟨K508_chk, List.forall_mem_cons.2 ⟨K511_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K524_chk, List.forall_mem_cons.2 ⟨K526_chk, List.forall_mem_cons.2 ⟨K531_chk, List.forall_mem_cons.2 ⟨K542_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V167 : UnitD := ⟨626727272729, 3727272727, [K7, K276, K423, K459, K494, K506, K513], [K527, K528, K531, K542, K552, K571, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 286, 292, false, false⟩

theorem V167_ok : V167.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V167_fin : V167.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V167_V : V167.V where
  ok := V167_ok
  fin := V167_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K494_chk, List.forall_mem_cons.2 ⟨K506_chk, List.forall_mem_cons.2 ⟨K513_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K527_chk, List.forall_mem_cons.2 ⟨K528_chk, List.forall_mem_cons.2 ⟨K531_chk, List.forall_mem_cons.2 ⟨K542_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V168 : UnitD := ⟨634181818183, 3727272727, [K7, K276, K423, K459, K495, K513, K516, K518], [K529, K534, K536, K542, K552, K571, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 288, 294, false, false⟩

theorem V168_ok : V168.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V168_fin : V168.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V168_V : V168.V where
  ok := V168_ok
  fin := V168_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K513_chk, List.forall_mem_cons.2 ⟨K516_chk, List.forall_mem_cons.2 ⟨K518_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K529_chk, List.forall_mem_cons.2 ⟨K534_chk, List.forall_mem_cons.2 ⟨K536_chk, List.forall_mem_cons.2 ⟨K542_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V169 : UnitD := ⟨641636363637, 3727272727, [K7, K276, K423, K459, K495, K513, K517, K521], [K535, K538, K542, K552, K570, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 290, 296, false, false⟩

theorem V169_ok : V169.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V169_fin : V169.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V169_V : V169.V where
  ok := V169_ok
  fin := V169_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K513_chk, List.forall_mem_cons.2 ⟨K517_chk, List.forall_mem_cons.2 ⟨K521_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K535_chk, List.forall_mem_cons.2 ⟨K538_chk, List.forall_mem_cons.2 ⟨K542_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V170 : UnitD := ⟨649090909091, 3727272727, [K7, K276, K423, K459, K495, K514, K522, K525], [K539, K541, K545, K552, K570, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 292, 298, false, false⟩

theorem V170_ok : V170.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V170_fin : V170.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V170_V : V170.V where
  ok := V170_ok
  fin := V170_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K514_chk, List.forall_mem_cons.2 ⟨K522_chk, List.forall_mem_cons.2 ⟨K525_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K539_chk, List.forall_mem_cons.2 ⟨K541_chk, List.forall_mem_cons.2 ⟨K545_chk, List.forall_mem_cons.2 ⟨K552_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V171 : UnitD := ⟨656545454547, 3727272729, [K7, K276, K424, K495, K514, K522, K525, K527, K528], [K543, K545, K551, K561, K570, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 294, 300, false, false⟩

theorem V171_ok : V171.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V171_fin : V171.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V171_V : V171.V where
  ok := V171_ok
  fin := V171_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K514_chk, List.forall_mem_cons.2 ⟨K522_chk, List.forall_mem_cons.2 ⟨K525_chk, List.forall_mem_cons.2 ⟨K527_chk, List.forall_mem_cons.2 ⟨K528_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K543_chk, List.forall_mem_cons.2 ⟨K545_chk, List.forall_mem_cons.2 ⟨K551_chk, List.forall_mem_cons.2 ⟨K561_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V172 : UnitD := ⟨664000000003, 3727272727, [K7, K276, K424, K495, K514, K523, K530], [K546, K548, K551, K561, K570, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 296, 302, false, false⟩

theorem V172_ok : V172.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V172_fin : V172.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V172_V : V172.V where
  ok := V172_ok
  fin := V172_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K514_chk, List.forall_mem_cons.2 ⟨K523_chk, List.forall_mem_cons.2 ⟨K530_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K546_chk, List.forall_mem_cons.2 ⟨K548_chk, List.forall_mem_cons.2 ⟨K551_chk, List.forall_mem_cons.2 ⟨K561_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V173 : UnitD := ⟨671454545457, 3727272727, [K7, K276, K424, K495, K515, K530, K535, K537], [K549, K553, K555, K561, K570, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 298, 304, false, false⟩

theorem V173_ok : V173.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V173_fin : V173.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V173_V : V173.V where
  ok := V173_ok
  fin := V173_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K530_chk, List.forall_mem_cons.2 ⟨K535_chk, List.forall_mem_cons.2 ⟨K537_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K549_chk, List.forall_mem_cons.2 ⟨K553_chk, List.forall_mem_cons.2 ⟨K555_chk, List.forall_mem_cons.2 ⟨K561_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V174 : UnitD := ⟨678909090911, 3727272727, [K7, K276, K424, K495, K515, K530, K536, K540], [K554, K557, K561, K569, K591, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 300, 306, false, false⟩

theorem V174_ok : V174.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V174_fin : V174.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V174_V : V174.V where
  ok := V174_ok
  fin := V174_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K530_chk, List.forall_mem_cons.2 ⟨K536_chk, List.forall_mem_cons.2 ⟨K540_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K554_chk, List.forall_mem_cons.2 ⟨K557_chk, List.forall_mem_cons.2 ⟨K561_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V175 : UnitD := ⟨686363636365, 3727272727, [K7, K276, K424, K495, K515, K531, K541, K544], [K558, K560, K564, K569, K591, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 302, 308, false, false⟩

theorem V175_ok : V175.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V175_fin : V175.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V175_V : V175.V where
  ok := V175_ok
  fin := V175_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K495_chk, List.forall_mem_cons.2 ⟨K515_chk, List.forall_mem_cons.2 ⟨K531_chk, List.forall_mem_cons.2 ⟨K541_chk, List.forall_mem_cons.2 ⟨K544_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K558_chk, List.forall_mem_cons.2 ⟨K560_chk, List.forall_mem_cons.2 ⟨K564_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V176 : UnitD := ⟨693818181819, 3727272727, [K7, K276, K424, K496, K531, K541, K544, K547], [K562, K564, K569, K591, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 304, 310, false, false⟩

theorem V176_ok : V176.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V176_fin : V176.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V176_V : V176.V where
  ok := V176_ok
  fin := V176_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K531_chk, List.forall_mem_cons.2 ⟨K541_chk, List.forall_mem_cons.2 ⟨K544_chk, List.forall_mem_cons.2 ⟨K547_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K562_chk, List.forall_mem_cons.2 ⟨K564_chk, List.forall_mem_cons.2 ⟨K569_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V177 : UnitD := ⟨701272727273, 3727272727, [K7, K276, K424, K496, K531, K542, K550], [K565, K568, K581, K591, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 306, 312, false, false⟩

theorem V177_ok : V177.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V177_fin : V177.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V177_V : V177.V where
  ok := V177_ok
  fin := V177_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K531_chk, List.forall_mem_cons.2 ⟨K542_chk, List.forall_mem_cons.2 ⟨K550_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K565_chk, List.forall_mem_cons.2 ⟨K568_chk, List.forall_mem_cons.2 ⟨K581_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V178 : UnitD := ⟨708727272729, 3727272729, [K7, K276, K424, K496, K531, K542, K550, K554, K556], [K566, K575, K577, K581, K591, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 308, 314, false, false⟩

theorem V178_ok : V178.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V178_fin : V178.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V178_V : V178.V where
  ok := V178_ok
  fin := V178_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K531_chk, List.forall_mem_cons.2 ⟨K542_chk, List.forall_mem_cons.2 ⟨K550_chk, List.forall_mem_cons.2 ⟨K554_chk, List.forall_mem_cons.2 ⟨K556_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K566_chk, List.forall_mem_cons.2 ⟨K575_chk, List.forall_mem_cons.2 ⟨K577_chk, List.forall_mem_cons.2 ⟨K581_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V179 : UnitD := ⟨716181818185, 3727272727, [K7, K276, K424, K496, K532, K550, K555, K559], [K576, K578, K581, K591, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 310, 316, false, false⟩

theorem V179_ok : V179.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V179_fin : V179.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V179_V : V179.V where
  ok := V179_ok
  fin := V179_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K550_chk, List.forall_mem_cons.2 ⟨K555_chk, List.forall_mem_cons.2 ⟨K559_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K576_chk, List.forall_mem_cons.2 ⟨K578_chk, List.forall_mem_cons.2 ⟨K581_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V180 : UnitD := ⟨723636363639, 3727272727, [K7, K276, K424, K496, K532, K551, K560, K563], [K579, K582, K584, K591, K609, K648, K713, K850], [K1116, K1118, K1119, K1125, K1142, K1148, K1150, K1151], 312, 318, false, false⟩

theorem V180_ok : V180.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V180_fin : V180.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V180_V : V180.V where
  ok := V180_ok
  fin := V180_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K532_chk, List.forall_mem_cons.2 ⟨K551_chk, List.forall_mem_cons.2 ⟨K560_chk, List.forall_mem_cons.2 ⟨K563_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K579_chk, List.forall_mem_cons.2 ⟨K582_chk, List.forall_mem_cons.2 ⟨K584_chk, List.forall_mem_cons.2 ⟨K591_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K713_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def L5 : List UnitD := [V151, V152, V153, V154, V155, V156, V157, V158, V159, V160, V161, V162, V163, V164, V165, V166, V167, V168, V169, V170, V171, V172, V173, V174, V175, V176, V177, V178, V179, V180]

theorem L5_V : ∀ u ∈ L5, u.V :=
  List.forall_mem_cons.2 ⟨V151_V, List.forall_mem_cons.2 ⟨V152_V, List.forall_mem_cons.2 ⟨V153_V, List.forall_mem_cons.2 ⟨V154_V, List.forall_mem_cons.2 ⟨V155_V, List.forall_mem_cons.2 ⟨V156_V, List.forall_mem_cons.2 ⟨V157_V, List.forall_mem_cons.2 ⟨V158_V, List.forall_mem_cons.2 ⟨V159_V, List.forall_mem_cons.2 ⟨V160_V, List.forall_mem_cons.2 ⟨V161_V, List.forall_mem_cons.2 ⟨V162_V, List.forall_mem_cons.2 ⟨V163_V, List.forall_mem_cons.2 ⟨V164_V, List.forall_mem_cons.2 ⟨V165_V, List.forall_mem_cons.2 ⟨V166_V, List.forall_mem_cons.2 ⟨V167_V, List.forall_mem_cons.2 ⟨V168_V, List.forall_mem_cons.2 ⟨V169_V, List.forall_mem_cons.2 ⟨V170_V, List.forall_mem_cons.2 ⟨V171_V, List.forall_mem_cons.2 ⟨V172_V, List.forall_mem_cons.2 ⟨V173_V, List.forall_mem_cons.2 ⟨V174_V, List.forall_mem_cons.2 ⟨V175_V, List.forall_mem_cons.2 ⟨V176_V, List.forall_mem_cons.2 ⟨V177_V, List.forall_mem_cons.2 ⟨V178_V, List.forall_mem_cons.2 ⟨V179_V, List.forall_mem_cons.2 ⟨V180_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
