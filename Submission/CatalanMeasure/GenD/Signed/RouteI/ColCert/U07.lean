module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.T1

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

def V211 : UnitD := ⟨885772727273, 1863636363, [K7, K276, K425, K570, K608, K627, K636, K644, K650, K652], [K659, K663, K681, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 357, 360, false, false⟩

theorem V211_ok : V211.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V211_fin : V211.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V211_V : V211.V where
  ok := V211_ok
  fin := V211_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K627_chk, List.forall_mem_cons.2 ⟨K636_chk, List.forall_mem_cons.2 ⟨K644_chk, List.forall_mem_cons.2 ⟨K650_chk, List.forall_mem_cons.2 ⟨K652_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K659_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V212 : UnitD := ⟨889500000001, 1863636365, [K7, K276, K425, K570, K608, K628, K644, K651], [K660, K662, K671, K681, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 357, 361, false, false⟩

theorem V212_ok : V212.ok = true := by
  -- kcost: 0.2 s measured mean, 23 pairs, 6 Nov
  decide +kernel

theorem V212_fin : V212.fin = true := by
  -- kcost: 1.4 s measured mean, 23 pair polynomials, 6 Nov
  decide +kernel

theorem V212_V : V212.V where
  ok := V212_ok
  fin := V212_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K644_chk, List.forall_mem_cons.2 ⟨K651_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K660_chk, List.forall_mem_cons.2 ⟨K662_chk, List.forall_mem_cons.2 ⟨K671_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V213 : UnitD := ⟨892272727273, 909090907, [K7, K276, K425, K570, K608, K628, K645, K653, K656], [K660, K661, K666, K671, K681, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 359, 361, false, false⟩

theorem V213_ok : V213.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V213_fin : V213.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V213_V : V213.V where
  ok := V213_ok
  fin := V213_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K653_chk, List.forall_mem_cons.2 ⟨K656_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K660_chk, List.forall_mem_cons.2 ⟨K661_chk, List.forall_mem_cons.2 ⟨K666_chk, List.forall_mem_cons.2 ⟨K671_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V214 : UnitD := ⟨894090909091, 909090911, [K7, K276, K425, K570, K608, K628, K645, K654], [K665, K668, K671, K680, K695, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 359, 364, false, false⟩

theorem V214_ok : V214.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V214_fin : V214.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V214_V : V214.V where
  ok := V214_ok
  fin := V214_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K665_chk, List.forall_mem_cons.2 ⟨K668_chk, List.forall_mem_cons.2 ⟨K671_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V215 : UnitD := ⟨895045454545, 45454543, [K7, K276, K425, K570, K608, K628, K645, K654, K657], [K664, K666, K671, K681, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 360, 363, false, false⟩

theorem V215_ok : V215.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V215_fin : V215.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V215_V : V215.V where
  ok := V215_ok
  fin := V215_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K657_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K664_chk, List.forall_mem_cons.2 ⟨K666_chk, List.forall_mem_cons.2 ⟨K671_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V216 : UnitD := ⟨895702170963, 611261875, [K7, K276, K425, K570, K608, K628, K645, K654, K657], [K669, K671, K680, K695, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 360, 366, false, false⟩

theorem V216_ok : V216.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V216_fin : V216.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V216_V : V216.V where
  ok := V216_ok
  fin := V216_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K657_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K669_chk, List.forall_mem_cons.2 ⟨K671_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V217 : UnitD := ⟨896970149255, 656716417, [K7, K276, K425, K570, K608, K628, K645, K654, K657], [K672, K673, K675, K679, K688, K695, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 360, 368, false, false⟩

theorem V217_ok : V217.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V217_fin : V217.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V217_V : V217.V where
  ok := V217_ok
  fin := V217_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K657_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K672_chk, List.forall_mem_cons.2 ⟨K673_chk, List.forall_mem_cons.2 ⟨K675_chk, List.forall_mem_cons.2 ⟨K679_chk, List.forall_mem_cons.2 ⟨K688_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V218 : UnitD := ⟨898222523745, 595658073, [K7, K276, K425, K570, K608, K628, K645, K654, K657, K659, K661], [K676, K679, K688, K695, K712, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 364, 371, false, false⟩

theorem V218_ok : V218.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V218_fin : V218.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V218_V : V218.V where
  ok := V218_ok
  fin := V218_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K657_chk, List.forall_mem_cons.2 ⟨K659_chk, List.forall_mem_cons.2 ⟨K661_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K676_chk, List.forall_mem_cons.2 ⟨K679_chk, List.forall_mem_cons.2 ⟨K688_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K712_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V219 : UnitD := ⟨899207598373, 389416555, [K7, K276, K425, K570, K608, K628, K645, K654, K657, K659, K661, K665, K667], [K678, K683, K688, K695, K711, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 366, 372, false, false⟩

theorem V219_ok : V219.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V219_fin : V219.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V219_V : V219.V where
  ok := V219_ok
  fin := V219_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K657_chk, List.forall_mem_cons.2 ⟨K659_chk, List.forall_mem_cons.2 ⟨K661_chk, List.forall_mem_cons.2 ⟨K665_chk, List.forall_mem_cons.2 ⟨K667_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K678_chk, List.forall_mem_cons.2 ⟨K683_chk, List.forall_mem_cons.2 ⟨K688_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V220 : UnitD := ⟨900253731345, 656716417, [K7, K276, K425, K570, K608, K628, K645, K654, K658, K661, K665, K668], [K682, K685, K688, K695, K711, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 367, 374, false, false⟩

theorem V220_ok : V220.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V220_fin : V220.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V220_V : V220.V where
  ok := V220_ok
  fin := V220_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K658_chk, List.forall_mem_cons.2 ⟨K661_chk, List.forall_mem_cons.2 ⟨K665_chk, List.forall_mem_cons.2 ⟨K668_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K682_chk, List.forall_mem_cons.2 ⟨K685_chk, List.forall_mem_cons.2 ⟨K688_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V221 : UnitD := ⟨901567164181, 656716419, [K7, K276, K425, K570, K608, K628, K645, K654, K658, K662, K670, K673], [K686, K689, K691, K695, K711, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 370, 377, false, false⟩

theorem V221_ok : V221.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V221_fin : V221.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V221_V : V221.V where
  ok := V221_ok
  fin := V221_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K658_chk, List.forall_mem_cons.2 ⟨K662_chk, List.forall_mem_cons.2 ⟨K670_chk, List.forall_mem_cons.2 ⟨K673_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K686_chk, List.forall_mem_cons.2 ⟨K689_chk, List.forall_mem_cons.2 ⟨K691_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V222 : UnitD := ⟨902552238809, 328358209, [K7, K276, K425, K570, K608, K628, K645, K654, K658, K662, K670, K674, K677], [K689, K691, K695, K711, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 373, 378, false, false⟩

theorem V222_ok : V222.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V222_fin : V222.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V222_V : V222.V where
  ok := V222_ok
  fin := V222_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K658_chk, List.forall_mem_cons.2 ⟨K662_chk, List.forall_mem_cons.2 ⟨K670_chk, List.forall_mem_cons.2 ⟨K674_chk, List.forall_mem_cons.2 ⟨K677_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K689_chk, List.forall_mem_cons.2 ⟨K691_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V223 : UnitD := ⟨903537313435, 656716417, [K7, K276, K425, K570, K608, K628, K645, K654, K658, K662, K671, K677], [K692, K693, K698, K703, K711, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 373, 380, false, false⟩

theorem V223_ok : V223.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V223_fin : V223.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V223_V : V223.V where
  ok := V223_ok
  fin := V223_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K608_chk, List.forall_mem_cons.2 ⟨K628_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K654_chk, List.forall_mem_cons.2 ⟨K658_chk, List.forall_mem_cons.2 ⟨K662_chk, List.forall_mem_cons.2 ⟨K671_chk, List.forall_mem_cons.2 ⟨K677_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K692_chk, List.forall_mem_cons.2 ⟨K693_chk, List.forall_mem_cons.2 ⟨K698_chk, List.forall_mem_cons.2 ⟨K703_chk, List.forall_mem_cons.2 ⟨K711_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V224 : UnitD := ⟨904850746271, 656716419, [K7, K276, K425, K570, K609, K645, K655, K662, K671, K678, K682, K684], [K696, K698, K703, K710, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 376, 383, false, false⟩

theorem V224_ok : V224.ok = true := by
  -- kcost: 0.2 s measured mean, 28 pairs, 6 Nov
  decide +kernel

theorem V224_fin : V224.fin = true := by
  -- kcost: 1.4 s measured mean, 28 pair polynomials, 6 Nov
  decide +kernel

theorem V224_V : V224.V where
  ok := V224_ok
  fin := V224_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K662_chk, List.forall_mem_cons.2 ⟨K671_chk, List.forall_mem_cons.2 ⟨K678_chk, List.forall_mem_cons.2 ⟨K682_chk, List.forall_mem_cons.2 ⟨K684_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K696_chk, List.forall_mem_cons.2 ⟨K698_chk, List.forall_mem_cons.2 ⟨K703_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V225 : UnitD := ⟨905890094983, 382632293, [K7, K276, K425, K570, K609, K645, K655, K663, K679, K686], [K697, K700, K703, K710, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 378, 384, false, false⟩

theorem V225_ok : V225.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V225_fin : V225.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V225_V : V225.V where
  ok := V225_ok
  fin := V225_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K679_chk, List.forall_mem_cons.2 ⟨K686_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K697_chk, List.forall_mem_cons.2 ⟨K700_chk, List.forall_mem_cons.2 ⟨K703_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V226 : UnitD := ⟨906875169609, 602442333, [K7, K276, K425, K570, K609, K645, K655, K663, K679, K687], [K701, K703, K710, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 379, 386, false, false⟩

theorem V226_ok : V226.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V226_fin : V226.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V226_V : V226.V where
  ok := V226_ok
  fin := V226_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K679_chk, List.forall_mem_cons.2 ⟨K687_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K701_chk, List.forall_mem_cons.2 ⟨K703_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V227 : UnitD := ⟨908134328359, 656716417, [K7, K276, K425, K570, K609, K645, K655, K663, K679, K687, K690, K692], [K704, K705, K706, K709, K717, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 382, 388, false, false⟩

theorem V227_ok : V227.ok = true := by
  -- kcost: 0.2 s measured mean, 29 pairs, 6 Nov
  decide +kernel

theorem V227_fin : V227.fin = true := by
  -- kcost: 1.4 s measured mean, 29 pair polynomials, 6 Nov
  decide +kernel

theorem V227_V : V227.V where
  ok := V227_ok
  fin := V227_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K679_chk, List.forall_mem_cons.2 ⟨K687_chk, List.forall_mem_cons.2 ⟨K690_chk, List.forall_mem_cons.2 ⟨K692_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K704_chk, List.forall_mem_cons.2 ⟨K705_chk, List.forall_mem_cons.2 ⟨K706_chk, List.forall_mem_cons.2 ⟨K709_chk, List.forall_mem_cons.2 ⟨K717_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V228 : UnitD := ⟨909395522389, 604477613, [K7, K276, K425, K570, K609, K645, K655, K663, K679, K688, K693], [K707, K709, K717, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 384, 391, false, false⟩

theorem V228_ok : V228.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V228_fin : V228.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V228_V : V228.V where
  ok := V228_ok
  fin := V228_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K679_chk, List.forall_mem_cons.2 ⟨K688_chk, List.forall_mem_cons.2 ⟨K693_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K707_chk, List.forall_mem_cons.2 ⟨K709_chk, List.forall_mem_cons.2 ⟨K717_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V229 : UnitD := ⟨910380597017, 380597015, [K7, K276, K425, K570, K609, K645, K655, K663, K680, K693, K697, K699], [K708, K714, K717, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 386, 392, false, false⟩

theorem V229_ok : V229.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V229_fin : V229.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V229_V : V229.V where
  ok := V229_ok
  fin := V229_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K645_chk, List.forall_mem_cons.2 ⟨K655_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K693_chk, List.forall_mem_cons.2 ⟨K697_chk, List.forall_mem_cons.2 ⟨K699_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K708_chk, List.forall_mem_cons.2 ⟨K714_chk, List.forall_mem_cons.2 ⟨K717_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V230 : UnitD := ⟨911417910449, 656716417, [K7, K276, K425, K570, K609, K646, K663, K680, K693, K697, K700], [K714, K717, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 387, 394, false, false⟩

theorem V230_ok : V230.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V230_fin : V230.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V230_V : V230.V where
  ok := V230_ok
  fin := V230_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K693_chk, List.forall_mem_cons.2 ⟨K697_chk, List.forall_mem_cons.2 ⟨K700_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K714_chk, List.forall_mem_cons.2 ⟨K717_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V231 : UnitD := ⟨912731343285, 656716419, [K7, K276, K425, K570, K609, K646, K663, K680, K694, K702, K705], [K715, K718, K720, K727, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 390, 396, false, false⟩

theorem V231_ok : V231.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V231_fin : V231.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V231_V : V231.V where
  ok := V231_ok
  fin := V231_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K694_chk, List.forall_mem_cons.2 ⟨K702_chk, List.forall_mem_cons.2 ⟨K705_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K715_chk, List.forall_mem_cons.2 ⟨K718_chk, List.forall_mem_cons.2 ⟨K720_chk, List.forall_mem_cons.2 ⟨K727_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V232 : UnitD := ⟨914044776121, 656716417, [K7, K276, K425, K570, K609, K646, K663, K680, K694, K702, K705, K706], [K719, K722, K726, K733, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 392, 398, false, false⟩

theorem V232_ok : V232.ok = true := by
  -- kcost: 0.2 s measured mean, 27 pairs, 6 Nov
  decide +kernel

theorem V232_fin : V232.fin = true := by
  -- kcost: 1.4 s measured mean, 27 pair polynomials, 6 Nov
  decide +kernel

theorem V232_V : V232.V where
  ok := V232_ok
  fin := V232_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K694_chk, List.forall_mem_cons.2 ⟨K702_chk, List.forall_mem_cons.2 ⟨K705_chk, List.forall_mem_cons.2 ⟨K706_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K719_chk, List.forall_mem_cons.2 ⟨K722_chk, List.forall_mem_cons.2 ⟨K726_chk, List.forall_mem_cons.2 ⟨K733_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V233 : UnitD := ⟨915358208957, 656716419, [K7, K276, K425, K570, K609, K646, K663, K680, K694, K703, K708], [K723, K725, K730, K733, K744, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 394, 400, false, false⟩

theorem V233_ok : V233.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V233_fin : V233.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V233_V : V233.V where
  ok := V233_ok
  fin := V233_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K694_chk, List.forall_mem_cons.2 ⟨K703_chk, List.forall_mem_cons.2 ⟨K708_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K723_chk, List.forall_mem_cons.2 ⟨K725_chk, List.forall_mem_cons.2 ⟨K730_chk, List.forall_mem_cons.2 ⟨K733_chk, List.forall_mem_cons.2 ⟨K744_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V234 : UnitD := ⟨916671641793, 656716417, [K7, K276, K425, K570, K609, K646, K663, K680, K695, K708, K714], [K728, K730, K733, K743, K760, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 396, 402, false, false⟩

theorem V234_ok : V234.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V234_fin : V234.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V234_V : V234.V where
  ok := V234_ok
  fin := V234_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K708_chk, List.forall_mem_cons.2 ⟨K714_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K728_chk, List.forall_mem_cons.2 ⟨K730_chk, List.forall_mem_cons.2 ⟨K733_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V235 : UnitD := ⟨917985074629, 656716419, [K7, K276, K425, K570, K609, K646, K663, K680, K695, K709, K716], [K731, K732, K736, K743, K760, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 398, 404, false, false⟩

theorem V235_ok : V235.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V235_fin : V235.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V235_V : V235.V where
  ok := V235_ok
  fin := V235_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K680_chk, List.forall_mem_cons.2 ⟨K695_chk, List.forall_mem_cons.2 ⟨K709_chk, List.forall_mem_cons.2 ⟨K716_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K731_chk, List.forall_mem_cons.2 ⟨K732_chk, List.forall_mem_cons.2 ⟨K736_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V236 : UnitD := ⟨919298507465, 656716417, [K7, K276, K425, K570, K609, K646, K663, K681, K709, K716, K719, K721], [K734, K736, K743, K760, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 400, 407, false, false⟩

theorem V236_ok : V236.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V236_fin : V236.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V236_V : V236.V where
  ok := V236_ok
  fin := V236_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K646_chk, List.forall_mem_cons.2 ⟨K663_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K709_chk, List.forall_mem_cons.2 ⟨K716_chk, List.forall_mem_cons.2 ⟨K719_chk, List.forall_mem_cons.2 ⟨K721_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K734_chk, List.forall_mem_cons.2 ⟨K736_chk, List.forall_mem_cons.2 ⟨K743_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V237 : UnitD := ⟨920283582091, 328358209, [K7, K276, K425, K570, K609, K647, K681, K709, K717, K724, K728], [K735, K738, K742, K751, K760, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 403, 408, false, false⟩

theorem V237_ok : V237.ok = true := by
  -- kcost: 0.2 s measured mean, 26 pairs, 6 Nov
  decide +kernel

theorem V237_fin : V237.fin = true := by
  -- kcost: 1.4 s measured mean, 26 pair polynomials, 6 Nov
  decide +kernel

theorem V237_V : V237.V where
  ok := V237_ok
  fin := V237_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K709_chk, List.forall_mem_cons.2 ⟨K717_chk, List.forall_mem_cons.2 ⟨K724_chk, List.forall_mem_cons.2 ⟨K728_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K735_chk, List.forall_mem_cons.2 ⟨K738_chk, List.forall_mem_cons.2 ⟨K742_chk, List.forall_mem_cons.2 ⟨K751_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V238 : UnitD := ⟨921268656717, 656716417, [K7, K276, K425, K570, K609, K647, K681, K709, K717, K725], [K739, K741, K747, K751, K760, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 403, 410, false, false⟩

theorem V238_ok : V238.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V238_fin : V238.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V238_V : V238.V where
  ok := V238_ok
  fin := V238_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K709_chk, List.forall_mem_cons.2 ⟨K717_chk, List.forall_mem_cons.2 ⟨K725_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K739_chk, List.forall_mem_cons.2 ⟨K741_chk, List.forall_mem_cons.2 ⟨K747_chk, List.forall_mem_cons.2 ⟨K751_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V239 : UnitD := ⟨922582089553, 656716419, [K7, K276, K425, K570, K609, K647, K681, K710, K725, K729, K731], [K745, K747, K751, K760, K778, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 406, 412, false, false⟩

theorem V239_ok : V239.ok = true := by
  -- kcost: 0.2 s measured mean, 25 pairs, 6 Nov
  decide +kernel

theorem V239_fin : V239.fin = true := by
  -- kcost: 1.4 s measured mean, 25 pair polynomials, 6 Nov
  decide +kernel

theorem V239_V : V239.V where
  ok := V239_ok
  fin := V239_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K725_chk, List.forall_mem_cons.2 ⟨K729_chk, List.forall_mem_cons.2 ⟨K731_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K745_chk, List.forall_mem_cons.2 ⟨K747_chk, List.forall_mem_cons.2 ⟨K751_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K778_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def V240 : UnitD := ⟨923895522389, 656716417, [K7, K276, K425, K570, K609, K647, K681, K710, K726, K732], [K748, K751, K760, K777, K811, K850], [K1117, K1119, K1125, K1141, K1146, K1148, K1150, K1151], 408, 414, false, false⟩

theorem V240_ok : V240.ok = true := by
  -- kcost: 0.2 s measured mean, 24 pairs, 6 Nov
  decide +kernel

theorem V240_fin : V240.fin = true := by
  -- kcost: 1.4 s measured mean, 24 pair polynomials, 6 Nov
  decide +kernel

theorem V240_V : V240.V where
  ok := V240_ok
  fin := V240_fin
  h0 := List.forall_mem_cons.2 ⟨K7_chk, List.forall_mem_cons.2 ⟨K276_chk, List.forall_mem_cons.2 ⟨K425_chk, List.forall_mem_cons.2 ⟨K570_chk, List.forall_mem_cons.2 ⟨K609_chk, List.forall_mem_cons.2 ⟨K647_chk, List.forall_mem_cons.2 ⟨K681_chk, List.forall_mem_cons.2 ⟨K710_chk, List.forall_mem_cons.2 ⟨K726_chk, List.forall_mem_cons.2 ⟨K732_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  h1 := List.forall_mem_cons.2 ⟨K748_chk, List.forall_mem_cons.2 ⟨K751_chk, List.forall_mem_cons.2 ⟨K760_chk, List.forall_mem_cons.2 ⟨K777_chk, List.forall_mem_cons.2 ⟨K811_chk, List.forall_mem_cons.2 ⟨K850_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  hr := List.forall_mem_cons.2 ⟨K1117_chk, List.forall_mem_cons.2 ⟨K1119_chk, List.forall_mem_cons.2 ⟨K1125_chk, List.forall_mem_cons.2 ⟨K1141_chk, List.forall_mem_cons.2 ⟨K1146_chk, List.forall_mem_cons.2 ⟨K1148_chk, List.forall_mem_cons.2 ⟨K1150_chk, List.forall_mem_cons.2 ⟨K1151_chk, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

def L7 : List UnitD := [V211, V212, V213, V214, V215, V216, V217, V218, V219, V220, V221, V222, V223, V224, V225, V226, V227, V228, V229, V230, V231, V232, V233, V234, V235, V236, V237, V238, V239, V240]

theorem L7_V : ∀ u ∈ L7, u.V :=
  List.forall_mem_cons.2 ⟨V211_V, List.forall_mem_cons.2 ⟨V212_V, List.forall_mem_cons.2 ⟨V213_V, List.forall_mem_cons.2 ⟨V214_V, List.forall_mem_cons.2 ⟨V215_V, List.forall_mem_cons.2 ⟨V216_V, List.forall_mem_cons.2 ⟨V217_V, List.forall_mem_cons.2 ⟨V218_V, List.forall_mem_cons.2 ⟨V219_V, List.forall_mem_cons.2 ⟨V220_V, List.forall_mem_cons.2 ⟨V221_V, List.forall_mem_cons.2 ⟨V222_V, List.forall_mem_cons.2 ⟨V223_V, List.forall_mem_cons.2 ⟨V224_V, List.forall_mem_cons.2 ⟨V225_V, List.forall_mem_cons.2 ⟨V226_V, List.forall_mem_cons.2 ⟨V227_V, List.forall_mem_cons.2 ⟨V228_V, List.forall_mem_cons.2 ⟨V229_V, List.forall_mem_cons.2 ⟨V230_V, List.forall_mem_cons.2 ⟨V231_V, List.forall_mem_cons.2 ⟨V232_V, List.forall_mem_cons.2 ⟨V233_V, List.forall_mem_cons.2 ⟨V234_V, List.forall_mem_cons.2 ⟨V235_V, List.forall_mem_cons.2 ⟨V236_V, List.forall_mem_cons.2 ⟨V237_V, List.forall_mem_cons.2 ⟨V238_V, List.forall_mem_cons.2 ⟨V239_V, List.forall_mem_cons.2 ⟨V240_V, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CatalanMeasure.GenD.Signed.RouteI.ColCert
