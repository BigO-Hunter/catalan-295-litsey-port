module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V121 : UnitD := ⟨283818181817, 3727272727, [K7, K274, K310, K329, K338, K341], [K356, K360, K367, K386, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 194, 200, false, false⟩

theorem V121_ok : V121.ok = true := by
  -- kcost: 0.2 s measured mean, 20 pairs, 6 Nov
  decide +kernel

theorem V121_fin : V121.fin = true := by
  -- kcost: 1.4 s measured mean, 20 pair polynomials, 6 Nov
  decide +kernel

theorem V121_V : V121.V where
  ok := V121_ok
  fin := V121_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K329_chk, List.forall_mem_cons.2 ⟨K338_chk, List.forall_mem_cons.2 ⟨K341_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K356_chk, List.forall_mem_cons.2 ⟨K360_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V122 : UnitD := ⟨291272727271, 3727272727, [K7, K274, K310, K329, K338, K341, K343, K344], [K359, K362, K366, K375, K386, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 196, 202, false, false⟩

theorem V122_ok : V122.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V122_fin : V122.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V122_V : V122.V where
  ok := V122_ok
  fin := V122_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K329_chk, List.forall_mem_cons.2 ⟨K338_chk, List.forall_mem_cons.2 ⟨K341_chk, List.forall_mem_cons.2 ⟨K343_chk, List.forall_mem_cons.2 ⟨K344_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K359_chk, List.forall_mem_cons.2 ⟨K362_chk, List.forall_mem_cons.2 ⟨K366_chk, List.forall_mem_cons.2 ⟨K375_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V123 : UnitD := ⟨298727272725, 3727272727, [K7, K274, K310, K329, K339, K345, K351], [K363, K365, K370, K375, K386, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 198, 204, false, false⟩

theorem V123_ok : V123.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V123_fin : V123.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V123_V : V123.V where
  ok := V123_ok
  fin := V123_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K329_chk, List.forall_mem_cons.2 ⟨K339_chk, List.forall_mem_cons.2 ⟨K345_chk, List.forall_mem_cons.2 ⟨K351_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K363_chk, List.forall_mem_cons.2 ⟨K365_chk, List.forall_mem_cons.2 ⟨K370_chk, List.forall_mem_cons.2 ⟨K375_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V124 : UnitD := ⟨306181818179, 3727272727, [K7, K274, K310, K329, K339, K346, K352, K354], [K368, K370, K375, K386, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 200, 206, false, false⟩

theorem V124_ok : V124.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V124_fin : V124.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V124_V : V124.V where
  ok := V124_ok
  fin := V124_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K329_chk, List.forall_mem_cons.2 ⟨K339_chk, List.forall_mem_cons.2 ⟨K346_chk, List.forall_mem_cons.2 ⟨K352_chk, List.forall_mem_cons.2 ⟨K354_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K368_chk, List.forall_mem_cons.2 ⟨K370_chk, List.forall_mem_cons.2 ⟨K375_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V125 : UnitD := ⟨313636363635, 3727272729, [K7, K274, K310, K330, K347, K355, K358], [K371, K372, K375, K385, K403, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 202, 208, false, false⟩

theorem V125_ok : V125.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V125_fin : V125.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V125_V : V125.V where
  ok := V125_ok
  fin := V125_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K347_chk, List.forall_mem_cons.2 ⟨K355_chk, List.forall_mem_cons.2 ⟨K358_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K371_chk, List.forall_mem_cons.2 ⟨K372_chk, List.forall_mem_cons.2 ⟨K375_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V126 : UnitD := ⟨321090909091, 3727272727, [K7, K274, K310, K330, K347, K356, K359, K361], [K374, K378, K385, K403, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 204, 210, false, false⟩

theorem V126_ok : V126.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V126_fin : V126.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V126_V : V126.V where
  ok := V126_ok
  fin := V126_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K310_chk, List.forall_mem_cons.2 ⟨K330_chk, List.forall_mem_cons.2 ⟨K347_chk, List.forall_mem_cons.2 ⟨K356_chk, List.forall_mem_cons.2 ⟨K359_chk, List.forall_mem_cons.2 ⟨K361_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K374_chk, List.forall_mem_cons.2 ⟨K378_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V127 : UnitD := ⟨328545454545, 3727272727, [K7, K274, K311, K347, K356, K360, K364], [K377, K380, K384, K393, K403, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 206, 212, false, false⟩

theorem V127_ok : V127.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V127_fin : V127.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V127_V : V127.V where
  ok := V127_ok
  fin := V127_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K347_chk, List.forall_mem_cons.2 ⟨K356_chk, List.forall_mem_cons.2 ⟨K360_chk, List.forall_mem_cons.2 ⟨K364_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K377_chk, List.forall_mem_cons.2 ⟨K380_chk, List.forall_mem_cons.2 ⟨K384_chk, List.forall_mem_cons.2 ⟨K393_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V128 : UnitD := ⟨335999999999, 3727272727, [K7, K274, K311, K347, K357, K365, K369], [K381, K383, K389, K393, K403, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 208, 214, false, false⟩

theorem V128_ok : V128.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V128_fin : V128.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V128_V : V128.V where
  ok := V128_ok
  fin := V128_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K347_chk, List.forall_mem_cons.2 ⟨K357_chk, List.forall_mem_cons.2 ⟨K365_chk, List.forall_mem_cons.2 ⟨K369_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K381_chk, List.forall_mem_cons.2 ⟨K383_chk, List.forall_mem_cons.2 ⟨K389_chk, List.forall_mem_cons.2 ⟨K393_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V129 : UnitD := ⟨343454545453, 3727272727, [K7, K274, K311, K348, K365, K369, K371, K372], [K387, K389, K393, K403, K424, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 210, 216, false, false⟩

theorem V129_ok : V129.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V129_fin : V129.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V129_V : V129.V where
  ok := V129_ok
  fin := V129_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K365_chk, List.forall_mem_cons.2 ⟨K369_chk, List.forall_mem_cons.2 ⟨K371_chk, List.forall_mem_cons.2 ⟨K372_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K387_chk, List.forall_mem_cons.2 ⟨K389_chk, List.forall_mem_cons.2 ⟨K393_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K424_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V130 : UnitD := ⟨350909090907, 3727272727, [K7, K274, K311, K348, K366, K373, K376], [K390, K393, K403, K423, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 212, 218, false, false⟩

theorem V130_ok : V130.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V130_fin : V130.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V130_V : V130.V where
  ok := V130_ok
  fin := V130_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K366_chk, List.forall_mem_cons.2 ⟨K373_chk, List.forall_mem_cons.2 ⟨K376_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K390_chk, List.forall_mem_cons.2 ⟨K393_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V131 : UnitD := ⟨358363636361, 3727272727, [K7, K274, K311, K348, K366, K374, K377, K379], [K392, K396, K403, K423, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 214, 220, false, false⟩

theorem V131_ok : V131.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V131_fin : V131.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V131_V : V131.V where
  ok := V131_ok
  fin := V131_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K274_chk, List.forall_mem_cons.2 ⟨K311_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K366_chk, List.forall_mem_cons.2 ⟨K374_chk, List.forall_mem_cons.2 ⟨K377_chk, List.forall_mem_cons.2 ⟨K379_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K392_chk, List.forall_mem_cons.2 ⟨K396_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V132 : UnitD := ⟨365818181815, 3727272727, [K7, K275, K348, K366, K374, K378, K382], [K395, K398, K402, K412, K423, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 216, 222, false, false⟩

theorem V132_ok : V132.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V132_fin : V132.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V132_V : V132.V where
  ok := V132_ok
  fin := V132_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K366_chk, List.forall_mem_cons.2 ⟨K374_chk, List.forall_mem_cons.2 ⟨K378_chk, List.forall_mem_cons.2 ⟨K382_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K395_chk, List.forall_mem_cons.2 ⟨K398_chk, List.forall_mem_cons.2 ⟨K402_chk, List.forall_mem_cons.2 ⟨K412_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V133 : UnitD := ⟨373272727271, 3727272729, [K7, K275, K348, K366, K375, K383, K388], [K399, K401, K406, K412, K423, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 218, 224, false, false⟩

theorem V133_ok : V133.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V133_fin : V133.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V133_V : V133.V where
  ok := V133_ok
  fin := V133_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K366_chk, List.forall_mem_cons.2 ⟨K375_chk, List.forall_mem_cons.2 ⟨K383_chk, List.forall_mem_cons.2 ⟨K388_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K399_chk, List.forall_mem_cons.2 ⟨K401_chk, List.forall_mem_cons.2 ⟨K406_chk, List.forall_mem_cons.2 ⟨K412_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V134 : UnitD := ⟨380727272727, 3727272727, [K7, K275, K348, K367, K383, K388, K390], [K404, K406, K412, K423, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 220, 226, false, false⟩

theorem V134_ok : V134.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V134_fin : V134.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V134_V : V134.V where
  ok := V134_ok
  fin := V134_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K383_chk, List.forall_mem_cons.2 ⟨K388_chk, List.forall_mem_cons.2 ⟨K390_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K404_chk, List.forall_mem_cons.2 ⟨K406_chk, List.forall_mem_cons.2 ⟨K412_chk, List.forall_mem_cons.2 ⟨K423_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V135 : UnitD := ⟨388181818181, 3727272727, [K7, K275, K348, K367, K384, K391, K394], [K408, K412, K422, K441, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 222, 228, false, false⟩

theorem V135_ok : V135.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V135_fin : V135.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V135_V : V135.V where
  ok := V135_ok
  fin := V135_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K348_chk, List.forall_mem_cons.2 ⟨K367_chk, List.forall_mem_cons.2 ⟨K384_chk, List.forall_mem_cons.2 ⟨K391_chk, List.forall_mem_cons.2 ⟨K394_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K408_chk, List.forall_mem_cons.2 ⟨K412_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V136 : UnitD := ⟨395636363635, 3727272727, [K7, K275, K349, K384, K392, K395, K397], [K411, K415, K422, K441, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 224, 230, false, false⟩

theorem V136_ok : V136.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V136_fin : V136.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V136_V : V136.V where
  ok := V136_ok
  fin := V136_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K384_chk, List.forall_mem_cons.2 ⟨K392_chk, List.forall_mem_cons.2 ⟨K395_chk, List.forall_mem_cons.2 ⟨K397_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K411_chk, List.forall_mem_cons.2 ⟨K415_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V137 : UnitD := ⟨403090909089, 3727272727, [K7, K275, K349, K384, K392, K396, K400], [K414, K417, K421, K432, K441, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 226, 232, false, false⟩

theorem V137_ok : V137.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V137_fin : V137.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V137_V : V137.V where
  ok := V137_ok
  fin := V137_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K384_chk, List.forall_mem_cons.2 ⟨K392_chk, List.forall_mem_cons.2 ⟨K396_chk, List.forall_mem_cons.2 ⟨K400_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K414_chk, List.forall_mem_cons.2 ⟨K417_chk, List.forall_mem_cons.2 ⟨K421_chk, List.forall_mem_cons.2 ⟨K432_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V138 : UnitD := ⟨410545454543, 3727272727, [K7, K275, K349, K384, K393, K401, K405], [K418, K421, K432, K441, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 228, 234, false, false⟩

theorem V138_ok : V138.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V138_fin : V138.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V138_V : V138.V where
  ok := V138_ok
  fin := V138_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K384_chk, List.forall_mem_cons.2 ⟨K393_chk, List.forall_mem_cons.2 ⟨K401_chk, List.forall_mem_cons.2 ⟨K405_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K418_chk, List.forall_mem_cons.2 ⟨K421_chk, List.forall_mem_cons.2 ⟨K432_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V139 : UnitD := ⟨417999999997, 3727272727, [K7, K275, K349, K385, K401, K405, K407, K409], [K426, K428, K432, K441, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 230, 236, false, false⟩

theorem V139_ok : V139.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V139_fin : V139.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V139_V : V139.V where
  ok := V139_ok
  fin := V139_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K401_chk, List.forall_mem_cons.2 ⟨K405_chk, List.forall_mem_cons.2 ⟨K407_chk, List.forall_mem_cons.2 ⟨K409_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K426_chk, List.forall_mem_cons.2 ⟨K428_chk, List.forall_mem_cons.2 ⟨K432_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V140 : UnitD := ⟨425454545453, 3727272729, [K7, K275, K349, K385, K402, K410, K413], [K429, K431, K435, K441, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 232, 238, false, false⟩

theorem V140_ok : V140.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V140_fin : V140.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V140_V : V140.V where
  ok := V140_ok
  fin := V140_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K402_chk, List.forall_mem_cons.2 ⟨K410_chk, List.forall_mem_cons.2 ⟨K413_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K429_chk, List.forall_mem_cons.2 ⟨K431_chk, List.forall_mem_cons.2 ⟨K435_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V141 : UnitD := ⟨432909090909, 3727272727, [K7, K275, K349, K385, K402, K411, K414, K416], [K433, K435, K441, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 234, 240, false, false⟩

theorem V141_ok : V141.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V141_fin : V141.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V141_V : V141.V where
  ok := V141_ok
  fin := V141_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K402_chk, List.forall_mem_cons.2 ⟨K411_chk, List.forall_mem_cons.2 ⟨K414_chk, List.forall_mem_cons.2 ⟨K416_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K433_chk, List.forall_mem_cons.2 ⟨K435_chk, List.forall_mem_cons.2 ⟨K441_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V142 : UnitD := ⟨440363636363, 3727272727, [K7, K275, K349, K385, K402, K411, K415, K419], [K437, K440, K449, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 236, 242, false, false⟩

theorem V142_ok : V142.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V142_fin : V142.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V142_V : V142.V where
  ok := V142_ok
  fin := V142_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K402_chk, List.forall_mem_cons.2 ⟨K411_chk, List.forall_mem_cons.2 ⟨K415_chk, List.forall_mem_cons.2 ⟨K419_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K437_chk, List.forall_mem_cons.2 ⟨K440_chk, List.forall_mem_cons.2 ⟨K449_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V143 : UnitD := ⟨447818181817, 3727272727, [K7, K275, K349, K385, K402, K412, K420, K427], [K439, K443, K449, K459, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 238, 244, false, false⟩

theorem V143_ok : V143.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V143_fin : V143.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V143_V : V143.V where
  ok := V143_ok
  fin := V143_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K402_chk, List.forall_mem_cons.2 ⟨K412_chk, List.forall_mem_cons.2 ⟨K420_chk, List.forall_mem_cons.2 ⟨K427_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K439_chk, List.forall_mem_cons.2 ⟨K443_chk, List.forall_mem_cons.2 ⟨K449_chk, List.forall_mem_cons.2 ⟨K459_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V144 : UnitD := ⟨455272727271, 3727272727, [K7, K275, K349, K385, K403, K420, K428, K430], [K442, K445, K449, K458, K476, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 240, 246, false, false⟩

theorem V144_ok : V144.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V144_fin : V144.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V144_V : V144.V where
  ok := V144_ok
  fin := V144_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K420_chk, List.forall_mem_cons.2 ⟨K428_chk, List.forall_mem_cons.2 ⟨K430_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K442_chk, List.forall_mem_cons.2 ⟨K445_chk, List.forall_mem_cons.2 ⟨K449_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V145 : UnitD := ⟨462727272725, 3727272727, [K7, K275, K349, K385, K403, K421, K431, K434], [K446, K448, K452, K458, K476, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 242, 248, false, false⟩

theorem V145_ok : V145.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V145_fin : V145.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V145_V : V145.V where
  ok := V145_ok
  fin := V145_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K421_chk, List.forall_mem_cons.2 ⟨K431_chk, List.forall_mem_cons.2 ⟨K434_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K446_chk, List.forall_mem_cons.2 ⟨K448_chk, List.forall_mem_cons.2 ⟨K452_chk, List.forall_mem_cons.2 ⟨K458_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V146 : UnitD := ⟨470181818181, 3727272729, [K7, K275, K349, K385, K403, K421, K431, K434, K436, K438], [K450, K452, K457, K467, K476, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 244, 250, false, false⟩

theorem V146_ok : V146.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V146_fin : V146.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V146_V : V146.V where
  ok := V146_ok
  fin := V146_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K385_chk, List.forall_mem_cons.2 ⟨K403_chk, List.forall_mem_cons.2 ⟨K421_chk, List.forall_mem_cons.2 ⟨K431_chk, List.forall_mem_cons.2 ⟨K434_chk, List.forall_mem_cons.2 ⟨K436_chk, List.forall_mem_cons.2 ⟨K438_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K450_chk, List.forall_mem_cons.2 ⟨K452_chk, List.forall_mem_cons.2 ⟨K457_chk, List.forall_mem_cons.2 ⟨K467_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V147 : UnitD := ⟨477636363637, 3727272727, [K7, K275, K349, K386, K421, K432, K439], [K453, K455, K457, K467, K476, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 246, 252, false, false⟩

theorem V147_ok : V147.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V147_fin : V147.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V147_V : V147.V where
  ok := V147_ok
  fin := V147_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K421_chk, List.forall_mem_cons.2 ⟨K432_chk, List.forall_mem_cons.2 ⟨K439_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K453_chk, List.forall_mem_cons.2 ⟨K455_chk, List.forall_mem_cons.2 ⟨K457_chk, List.forall_mem_cons.2 ⟨K467_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V148 : UnitD := ⟨485090909091, 3727272727, [K7, K275, K349, K386, K422, K439, K442, K444], [K456, K461, K467, K476, K497, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 248, 254, false, false⟩

theorem V148_ok : V148.ok = true := by
  -- kcost: 0.2 s measured mean, 21 pairs, 6 Nov
  decide +kernel

theorem V148_fin : V148.fin = true := by
  -- kcost: 1.4 s measured mean, 21 pair polynomials, 6 Nov
  decide +kernel

theorem V148_V : V148.V where
  ok := V148_ok
  fin := V148_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K439_chk, List.forall_mem_cons.2 ⟨K442_chk, List.forall_mem_cons.2 ⟨K444_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K456_chk, List.forall_mem_cons.2 ⟨K461_chk, List.forall_mem_cons.2 ⟨K467_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K497_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V149 : UnitD := ⟨492545454547, 3727272729, [K7, K275, K349, K386, K422, K439, K443, K447], [K460, K463, K467, K476, K496, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 250, 256, false, false⟩

theorem V149_ok : V149.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V149_fin : V149.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V149_V : V149.V where
  ok := V149_ok
  fin := V149_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K439_chk, List.forall_mem_cons.2 ⟨K443_chk, List.forall_mem_cons.2 ⟨K447_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K460_chk, List.forall_mem_cons.2 ⟨K463_chk, List.forall_mem_cons.2 ⟨K467_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def V150 : UnitD := ⟨500000000003, 3727272727, [K7, K275, K349, K386, K422, K440, K448, K451], [K464, K466, K470, K476, K496, K533, K574], [K1116, K1118, K1119, K1125, K1142, K1149, K1151], 252, 258, false, false⟩

theorem V150_ok : V150.ok = true := by
  -- kcost: 0.2 s measured mean, 22 pairs, 6 Nov
  decide +kernel

theorem V150_fin : V150.fin = true := by
  -- kcost: 1.4 s measured mean, 22 pair polynomials, 6 Nov
  decide +kernel

theorem V150_V : V150.V where
  ok := V150_ok
  fin := V150_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K275_chk, List.forall_mem_cons.2 ⟨K349_chk, List.forall_mem_cons.2 ⟨K386_chk, List.forall_mem_cons.2 ⟨K422_chk, List.forall_mem_cons.2 ⟨K440_chk, List.forall_mem_cons.2 ⟨K448_chk, List.forall_mem_cons.2 ⟨K451_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K464_chk, List.forall_mem_cons.2 ⟨K466_chk, List.forall_mem_cons.2 ⟨K470_chk, List.forall_mem_cons.2 ⟨K476_chk, List.forall_mem_cons.2 ⟨K496_chk, List.forall_mem_cons.2 ⟨K533_chk, List.forall_mem_cons.2 ⟨K574_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1116_chk, List.forall_mem_cons.2 ⟨K1118_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1142_chk, List.forall_mem_cons.2 ⟨K1149_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩

def L4 : List UnitD := [V121, V122, V123, V124, V125, V126, V127, V128, V129, V130, V131, V132, V133, V134, V135, V136, V137, V138, V139, V140, V141, V142, V143, V144, V145, V146, V147, V148, V149, V150]

theorem L4_V : ∀ u ∈ L4, u.V :=
  List.forall_mem_cons.2 ⟨V121_V, List.forall_mem_cons.2 ⟨V122_V, List.forall_mem_cons.2 ⟨V123_V, List.forall_mem_cons.2 ⟨V124_V, List.forall_mem_cons.2 ⟨V125_V, List.forall_mem_cons.2 ⟨V126_V, List.forall_mem_cons.2 ⟨V127_V, List.forall_mem_cons.2 ⟨V128_V, List.forall_mem_cons.2 ⟨V129_V, List.forall_mem_cons.2 ⟨V130_V, List.forall_mem_cons.2 ⟨V131_V, List.forall_mem_cons.2 ⟨V132_V, List.forall_mem_cons.2 ⟨V133_V, List.forall_mem_cons.2 ⟨V134_V, List.forall_mem_cons.2 ⟨V135_V, List.forall_mem_cons.2 ⟨V136_V, List.forall_mem_cons.2 ⟨V137_V, List.forall_mem_cons.2 ⟨V138_V, List.forall_mem_cons.2 ⟨V139_V, List.forall_mem_cons.2 ⟨V140_V, List.forall_mem_cons.2 ⟨V141_V, List.forall_mem_cons.2 ⟨V142_V, List.forall_mem_cons.2 ⟨V143_V, List.forall_mem_cons.2 ⟨V144_V, List.forall_mem_cons.2 ⟨V145_V, List.forall_mem_cons.2 ⟨V146_V, List.forall_mem_cons.2 ⟨V147_V, List.forall_mem_cons.2 ⟨V148_V, List.forall_mem_cons.2 ⟨V149_V, List.forall_mem_cons.2 ⟨V150_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
