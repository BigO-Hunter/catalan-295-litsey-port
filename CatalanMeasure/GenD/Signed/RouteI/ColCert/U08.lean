module

public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V241 : UnitD := ⟨925208955225, 656716419, [K7, K276, K425, K570, K609, K647, K681, K710, K726, K732, K735, K737], [K749, K752, K754, K759, K767, K777, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 410, 416, false, false⟩

theorem V241_ok : V241.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V241_fin : V241.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V241_V : V241.V where
  ok := V241_ok
  fin := V241_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K726_chk, List.forall_mem_cons.2 ⟨K732_chk, List.forall_mem_cons.2 ⟨K735_chk, List.forall_mem_cons.2 ⟨K737_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K749_chk, List.forall_mem_cons.2 ⟨K752_chk, List.forall_mem_cons.2 ⟨K754_chk, List.forall_mem_cons.2 ⟨K759_chk, List.forall_mem_cons.2 ⟨K767_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V242 : UnitD := ⟨926522388061, 656716417, [K7, K276, K425, K570, K609, K647, K681, K710, K726, K732, K736, K740], [K753, K755, K759, K767, K777, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 412, 418, false, false⟩

theorem V242_ok : V242.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V242_fin : V242.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V242_V : V242.V where
  ok := V242_ok
  fin := V242_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K726_chk, List.forall_mem_cons.2 ⟨K732_chk, List.forall_mem_cons.2 ⟨K736_chk, List.forall_mem_cons.2 ⟨K740_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K753_chk, List.forall_mem_cons.2 ⟨K755_chk, List.forall_mem_cons.2 ⟨K759_chk, List.forall_mem_cons.2 ⟨K767_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V243 : UnitD := ⟨927835820897, 656716419, [K7, K276, K425, K570, K609, K647, K681, K710, K726, K733, K741, K746], [K756, K757, K761, K763, K767, K777, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 414, 420, false, false⟩

theorem V243_ok : V243.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V243_fin : V243.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V243_V : V243.V where
  ok := V243_ok
  fin := V243_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K726_chk, List.forall_mem_cons.2 ⟨K733_chk, List.forall_mem_cons.2 ⟨K741_chk, List.forall_mem_cons.2 ⟨K746_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K756_chk, List.forall_mem_cons.2 ⟨K757_chk, List.forall_mem_cons.2 ⟨K761_chk, List.forall_mem_cons.2 ⟨K763_chk, List.forall_mem_cons.2 ⟨K767_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V244 : UnitD := ⟨929054251725, 561714409, [K7, K276, K425, K570, K609, K647, K681, K710, K727, K741, K746, K748], [K762, K764, K767, K777, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 416, 423, false, false⟩

theorem V244_ok : V244.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V244_fin : V244.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V244_V : V244.V where
  ok := V244_ok
  fin := V244_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K741_chk, List.forall_mem_cons.2 ⟨K746_chk, List.forall_mem_cons.2 ⟨K748_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K762_chk, List.forall_mem_cons.2 ⟨K764_chk, List.forall_mem_cons.2 ⟨K767_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V245 : UnitD := ⟨930039326351, 423360217, [K7, K276, K425, K570, K609, K647, K681, K710, K727, K742, K750], [K764, K767, K776, K794, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 418, 424, false, false⟩

theorem V245_ok : V245.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V245_fin : V245.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V245_V : V245.V where
  ok := V245_ok
  fin := V245_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K742_chk, List.forall_mem_cons.2 ⟨K750_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K764_chk, List.forall_mem_cons.2 ⟨K767_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V246 : UnitD := ⟨931119402987, 656716419, [K7, K276, K425, K570, K609, K647, K681, K711, K742, K750, K753], [K765, K768, K770, K776, K794, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 419, 426, false, false⟩

theorem V246_ok : V246.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V246_fin : V246.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V246_V : V246.V where
  ok := V246_ok
  fin := V246_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K742_chk, List.forall_mem_cons.2 ⟨K750_chk, List.forall_mem_cons.2 ⟨K753_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K765_chk, List.forall_mem_cons.2 ⟨K768_chk, List.forall_mem_cons.2 ⟨K770_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V247 : UnitD := ⟨932432835823, 656716417, [K7, K276, K425, K570, K609, K647, K681, K711, K742, K751, K757], [K769, K772, K775, K785, K794, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 422, 428, false, false⟩

theorem V247_ok : V247.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V247_fin : V247.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V247_V : V247.V where
  ok := V247_ok
  fin := V247_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K742_chk, List.forall_mem_cons.2 ⟨K751_chk, List.forall_mem_cons.2 ⟨K757_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K769_chk, List.forall_mem_cons.2 ⟨K772_chk, List.forall_mem_cons.2 ⟨K775_chk, List.forall_mem_cons.2 ⟨K785_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V248 : UnitD := ⟨933746268659, 656716419, [K7, K276, K425, K570, K609, K647, K681, K711, K742, K751, K758, K762], [K773, K774, K781, K785, K794, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 424, 430, false, false⟩

theorem V248_ok : V248.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V248_fin : V248.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V248_V : V248.V where
  ok := V248_ok
  fin := V248_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K742_chk, List.forall_mem_cons.2 ⟨K751_chk, List.forall_mem_cons.2 ⟨K758_chk, List.forall_mem_cons.2 ⟨K762_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K773_chk, List.forall_mem_cons.2 ⟨K774_chk, List.forall_mem_cons.2 ⟨K781_chk, List.forall_mem_cons.2 ⟨K785_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V249 : UnitD := ⟨935059701495, 656716417, [K7, K276, K425, K570, K609, K647, K681, K711, K743, K758, K762, K764], [K779, K781, K785, K794, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 426, 432, false, false⟩

theorem V249_ok : V249.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V249_fin : V249.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V249_V : V249.V where
  ok := V249_ok
  fin := V249_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K758_chk, List.forall_mem_cons.2 ⟨K762_chk, List.forall_mem_cons.2 ⟨K764_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K779_chk, List.forall_mem_cons.2 ⟨K781_chk, List.forall_mem_cons.2 ⟨K785_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V250 : UnitD := ⟨936373134329, 656716417, [K7, K276, K425, K570, K609, K647, K681, K711, K743, K759, K766], [K783, K784, K787, K794, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 428, 435, false, false⟩

theorem V250_ok : V250.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V250_fin : V250.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V250_V : V250.V where
  ok := V250_ok
  fin := V250_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K759_chk, List.forall_mem_cons.2 ⟨K766_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K783_chk, List.forall_mem_cons.2 ⟨K784_chk, List.forall_mem_cons.2 ⟨K787_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V251 : UnitD := ⟨937393464141, 363613395, [K7, K276, K425, K570, K609, K648, K711, K743, K759, K766, K769, K771], [K784, K787, K794, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 430, 436, false, false⟩

theorem V251_ok : V251.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V251_fin : V251.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V251_V : V251.V where
  ok := V251_ok
  fin := V251_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K759_chk, List.forall_mem_cons.2 ⟨K766_chk, List.forall_mem_cons.2 ⟨K769_chk, List.forall_mem_cons.2 ⟨K771_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K784_chk, List.forall_mem_cons.2 ⟨K787_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V252 : UnitD := ⟨938378538769, 621461233, [K7, K276, K425, K570, K609, K648, K711, K743, K759, K766, K769, K772], [K786, K789, K793, K800, K811, K850], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 431, 438, false, false⟩

theorem V252_ok : V252.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V252_fin : V252.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V252_V : V252.V where
  ok := V252_ok
  fin := V252_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K759_chk, List.forall_mem_cons.2 ⟨K766_chk, List.forall_mem_cons.2 ⟨K769_chk, List.forall_mem_cons.2 ⟨K772_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K786_chk, List.forall_mem_cons.2 ⟨K789_chk, List.forall_mem_cons.2 ⟨K793_chk, List.forall_mem_cons.2 ⟨K800_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V253 : UnitD := ⟨939656716419, 656716417, [K7, K276, K425, K571, K648, K711, K743, K759, K767, K774, K780], [K790, K792, K797, K800, K811, K849, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 434, 440, false, false⟩

theorem V253_ok : V253.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V253_fin : V253.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V253_V : V253.V where
  ok := V253_ok
  fin := V253_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K759_chk, List.forall_mem_cons.2 ⟨K767_chk, List.forall_mem_cons.2 ⟨K774_chk, List.forall_mem_cons.2 ⟨K780_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K790_chk, List.forall_mem_cons.2 ⟨K792_chk, List.forall_mem_cons.2 ⟨K797_chk, List.forall_mem_cons.2 ⟨K800_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K849_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V254 : UnitD := ⟨940970149255, 656716419, [K7, K276, K425, K571, K648, K711, K743, K759, K767, K774, K780, K782], [K795, K797, K800, K810, K827, K849, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 436, 442, false, false⟩

theorem V254_ok : V254.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V254_fin : V254.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V254_V : V254.V where
  ok := V254_ok
  fin := V254_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K759_chk, List.forall_mem_cons.2 ⟨K767_chk, List.forall_mem_cons.2 ⟨K774_chk, List.forall_mem_cons.2 ⟨K780_chk, List.forall_mem_cons.2 ⟨K782_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K795_chk, List.forall_mem_cons.2 ⟨K797_chk, List.forall_mem_cons.2 ⟨K800_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K849_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V255 : UnitD := ⟨942283582091, 656716417, [K7, K276, K425, K571, K648, K711, K743, K760, K775, K784], [K798, K799, K803, K810, K827, K849, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 438, 444, false, false⟩

theorem V255_ok : V255.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V255_fin : V255.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V255_V : V255.V where
  ok := V255_ok
  fin := V255_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K775_chk, List.forall_mem_cons.2 ⟨K784_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K798_chk, List.forall_mem_cons.2 ⟨K799_chk, List.forall_mem_cons.2 ⟨K803_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K849_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V256 : UnitD := ⟨943597014927, 656716419, [K7, K276, K425, K571, K648, K711, K743, K760, K775, K784, K786, K788], [K801, K803, K810, K827, K849, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 440, 447, false, false⟩

theorem V256_ok : V256.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V256_fin : V256.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V256_V : V256.V where
  ok := V256_ok
  fin := V256_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K775_chk, List.forall_mem_cons.2 ⟨K784_chk, List.forall_mem_cons.2 ⟨K786_chk, List.forall_mem_cons.2 ⟨K788_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K801_chk, List.forall_mem_cons.2 ⟨K803_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K849_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V257 : UnitD := ⟨944605131099, 351399753, [K7, K276, K425, K571, K648, K711, K744, K775, K784, K787, K791], [K802, K805, K809, K818, K827, K848, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 442, 448, false, false⟩

theorem V257_ok : V257.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V257_fin : V257.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V257_V : V257.V where
  ok := V257_ok
  fin := V257_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K775_chk, List.forall_mem_cons.2 ⟨K784_chk, List.forall_mem_cons.2 ⟨K787_chk, List.forall_mem_cons.2 ⟨K791_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K802_chk, List.forall_mem_cons.2 ⟨K805_chk, List.forall_mem_cons.2 ⟨K809_chk, List.forall_mem_cons.2 ⟨K818_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V258 : UnitD := ⟨945590205725, 633674873, [K7, K276, K425, K571, K648, K711, K744, K775, K785, K792], [K806, K808, K814, K818, K827, K848, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 443, 450, false, false⟩

theorem V258_ok : V258.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V258_fin : V258.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V258_V : V258.V where
  ok := V258_ok
  fin := V258_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K775_chk, List.forall_mem_cons.2 ⟨K785_chk, List.forall_mem_cons.2 ⟨K792_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K806_chk, List.forall_mem_cons.2 ⟨K808_chk, List.forall_mem_cons.2 ⟨K814_chk, List.forall_mem_cons.2 ⟨K818_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V259 : UnitD := ⟨946880597017, 656716419, [K7, K276, K425, K571, K648, K711, K744, K776, K792, K796, K798], [K812, K814, K818, K827, K848, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 446, 452, false, false⟩

theorem V259_ok : V259.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V259_fin : V259.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V259_V : V259.V where
  ok := V259_ok
  fin := V259_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K792_chk, List.forall_mem_cons.2 ⟨K796_chk, List.forall_mem_cons.2 ⟨K798_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K812_chk, List.forall_mem_cons.2 ⟨K814_chk, List.forall_mem_cons.2 ⟨K818_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K848_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V260 : UnitD := ⟨948194029853, 656716417, [K7, K276, K425, K571, K648, K711, K744, K776, K793, K799], [K816, K818, K827, K847, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 448, 454, false, false⟩

theorem V260_ok : V260.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V260_fin : V260.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V260_V : V260.V where
  ok := V260_ok
  fin := V260_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K793_chk, List.forall_mem_cons.2 ⟨K799_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K816_chk, List.forall_mem_cons.2 ⟨K818_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V261 : UnitD := ⟨949507462687, 656716417, [K7, K276, K425, K571, K648, K711, K744, K776, K793, K799, K802, K804], [K817, K820, K827, K847, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 450, 456, false, false⟩

theorem V261_ok : V261.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V261_fin : V261.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V261_V : V261.V where
  ok := V261_ok
  fin := V261_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K793_chk, List.forall_mem_cons.2 ⟨K799_chk, List.forall_mem_cons.2 ⟨K802_chk, List.forall_mem_cons.2 ⟨K804_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K817_chk, List.forall_mem_cons.2 ⟨K820_chk, List.forall_mem_cons.2 ⟨K827_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V262 : UnitD := ⟨950743711983, 579532879, [K7, K276, K425, K571, K648, K712, K776, K793, K799, K803, K807], [K822, K826, K836, K847, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 452, 459, false, false⟩

theorem V262_ok : V262.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V262_fin : V262.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V262_V : V262.V where
  ok := V262_ok
  fin := V262_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K793_chk, List.forall_mem_cons.2 ⟨K799_chk, List.forall_mem_cons.2 ⟨K803_chk, List.forall_mem_cons.2 ⟨K807_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K822_chk, List.forall_mem_cons.2 ⟨K826_chk, List.forall_mem_cons.2 ⟨K836_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V263 : UnitD := ⟨951728786611, 405541749, [K7, K276, K425, K571, K648, K712, K776, K793, K800, K808, K813], [K823, K826, K836, K847, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 454, 460, false, false⟩

theorem V263_ok : V263.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V263_fin : V263.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V263_V : V263.V where
  ok := V263_ok
  fin := V263_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K793_chk, List.forall_mem_cons.2 ⟨K800_chk, List.forall_mem_cons.2 ⟨K808_chk, List.forall_mem_cons.2 ⟨K813_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K823_chk, List.forall_mem_cons.2 ⟨K826_chk, List.forall_mem_cons.2 ⟨K836_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V264 : UnitD := ⟨952791044777, 656716417, [K7, K276, K425, K571, K648, K712, K776, K794, K808, K813, K815], [K828, K830, K836, K847, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 455, 462, false, false⟩

theorem V264_ok : V264.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V264_fin : V264.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V264_V : V264.V where
  ok := V264_ok
  fin := V264_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K808_chk, List.forall_mem_cons.2 ⟨K813_chk, List.forall_mem_cons.2 ⟨K815_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K828_chk, List.forall_mem_cons.2 ⟨K830_chk, List.forall_mem_cons.2 ⟨K836_chk, List.forall_mem_cons.2 ⟨K847_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V265 : UnitD := ⟨954104477613, 656716419, [K7, K276, K425, K571, K648, K712, K776, K794, K808, K814, K817], [K832, K836, K846, K866, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 458, 464, false, false⟩

theorem V265_ok : V265.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V265_fin : V265.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V265_V : V265.V where
  ok := V265_ok
  fin := V265_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K776_chk, List.forall_mem_cons.2 ⟨K794_chk, List.forall_mem_cons.2 ⟨K808_chk, List.forall_mem_cons.2 ⟨K814_chk, List.forall_mem_cons.2 ⟨K817_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K832_chk, List.forall_mem_cons.2 ⟨K836_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V266 : UnitD := ⟨955417910449, 656716417, [K7, K276, K425, K571, K648, K712, K777, K809, K817, K819, K821], [K834, K837, K839, K846, K866, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 460, 466, false, false⟩

theorem V266_ok : V266.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V266_fin : V266.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V266_V : V266.V where
  ok := V266_ok
  fin := V266_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K809_chk, List.forall_mem_cons.2 ⟨K817_chk, List.forall_mem_cons.2 ⟨K819_chk, List.forall_mem_cons.2 ⟨K821_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K834_chk, List.forall_mem_cons.2 ⟨K837_chk, List.forall_mem_cons.2 ⟨K839_chk, List.forall_mem_cons.2 ⟨K846_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V267 : UnitD := ⟨956514083451, 439456585, [K7, K276, K425, K571, K648, K712, K777, K809, K818, K824], [K838, K841, K845, K856, K866, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 462, 468, false, false⟩

theorem V267_ok : V267.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V267_fin : V267.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V267_V : V267.V where
  ok := V267_ok
  fin := V267_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K809_chk, List.forall_mem_cons.2 ⟨K818_chk, List.forall_mem_cons.2 ⟨K824_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K838_chk, List.forall_mem_cons.2 ⟨K841_chk, List.forall_mem_cons.2 ⟨K845_chk, List.forall_mem_cons.2 ⟨K856_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V268 : UnitD := ⟨957499158079, 545618043, [K7, K276, K425, K571, K648, K712, K777, K809, K818, K825, K829], [K842, K845, K856, K866, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 464, 470, false, false⟩

theorem V268_ok : V268.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V268_fin : V268.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V268_V : V268.V where
  ok := V268_ok
  fin := V268_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K809_chk, List.forall_mem_cons.2 ⟨K818_chk, List.forall_mem_cons.2 ⟨K825_chk, List.forall_mem_cons.2 ⟨K829_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K842_chk, List.forall_mem_cons.2 ⟨K845_chk, List.forall_mem_cons.2 ⟨K856_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V269 : UnitD := ⟨958701492539, 656716417, [K7, K276, K425, K571, K648, K712, K777, K810, K825, K829, K831, K833], [K851, K852, K856, K866, K881, K914, K983], [K1117, K1119, K1125, K1141, K1145, K1147, K1148, K1150, K1151], 466, 472, false, false⟩

theorem V269_ok : V269.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V269_fin : V269.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V269_V : V269.V where
  ok := V269_ok
  fin := V269_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K825_chk, List.forall_mem_cons.2 ⟨K829_chk, List.forall_mem_cons.2 ⟨K831_chk, List.forall_mem_cons.2 ⟨K833_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K851_chk, List.forall_mem_cons.2 ⟨K852_chk, List.forall_mem_cons.2 ⟨K856_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩

def V270 : UnitD := ⟨960014925375, 656716419, [K7, K276, K425, K571, K648, K712, K777, K810, K826, K835], [K853, K854, K857, K859, K866, K881, K914, K983], [K1117, K1119, K1125, K1140, K1144, K1145, K1147, K1148, K1150, K1151], 468, 474, false, false⟩

theorem V270_ok : V270.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V270_fin : V270.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V270_V : V270.V where
  ok := V270_ok
  fin := V270_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K571_chk, List.forall_mem_cons.2 ⟨K648_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K810_chk, List.forall_mem_cons.2 ⟨K826_chk, List.forall_mem_cons.2 ⟨K835_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K853_chk, List.forall_mem_cons.2 ⟨K854_chk, List.forall_mem_cons.2 ⟨K857_chk, List.forall_mem_cons.2 ⟨K859_chk, List.forall_mem_cons.2 ⟨K866_chk, List.forall_mem_cons.2 ⟨K881_chk, List.forall_mem_cons.2 ⟨K914_chk, List.forall_mem_cons.2 ⟨K983_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1140_chk, List.forall_mem_cons.2 ⟨K1144_chk, List.forall_mem_cons.2 ⟨K1145_chk, List.forall_mem_cons.2 ⟨K1147_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def L8 : List UnitD := [V241, V242, V243, V244, V245, V246, V247, V248, V249, V250, V251, V252, V253, V254, V255, V256, V257, V258, V259, V260, V261, V262, V263, V264, V265, V266, V267, V268, V269, V270]

theorem L8_V : ∀ u ∈ L8, u.V :=
  List.forall_mem_cons.2 ⟨V241_V, List.forall_mem_cons.2 ⟨V242_V, List.forall_mem_cons.2 ⟨V243_V, List.forall_mem_cons.2 ⟨V244_V, List.forall_mem_cons.2 ⟨V245_V, List.forall_mem_cons.2 ⟨V246_V, List.forall_mem_cons.2 ⟨V247_V, List.forall_mem_cons.2 ⟨V248_V, List.forall_mem_cons.2 ⟨V249_V, List.forall_mem_cons.2 ⟨V250_V, List.forall_mem_cons.2 ⟨V251_V, List.forall_mem_cons.2 ⟨V252_V, List.forall_mem_cons.2 ⟨V253_V, List.forall_mem_cons.2 ⟨V254_V, List.forall_mem_cons.2 ⟨V255_V, List.forall_mem_cons.2 ⟨V256_V, List.forall_mem_cons.2 ⟨V257_V, List.forall_mem_cons.2 ⟨V258_V, List.forall_mem_cons.2 ⟨V259_V, List.forall_mem_cons.2 ⟨V260_V, List.forall_mem_cons.2 ⟨V261_V, List.forall_mem_cons.2 ⟨V262_V, List.forall_mem_cons.2 ⟨V263_V, List.forall_mem_cons.2 ⟨V264_V, List.forall_mem_cons.2 ⟨V265_V, List.forall_mem_cons.2 ⟨V266_V, List.forall_mem_cons.2 ⟨V267_V, List.forall_mem_cons.2 ⟨V268_V, List.forall_mem_cons.2 ⟨V269_V, List.forall_mem_cons.2 ⟨V270_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
