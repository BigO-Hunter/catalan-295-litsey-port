module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import CatalanMeasure.GenD.Cert.WLogSpec
public import CatalanMeasure.CellCert.CellW
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 4 evLe goals, one declaration each, about 3.1 s each (YMCriticalValueProbe mean)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal6
open CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
theorem yv0 : evLe (colSpecW C Vc V 0).ev (midQ (0xff3d7cbf05d4a0f0a5b0 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv1 : evLe (colSpecW C Vc V 0).ev (midQ (0xffb0b260400df312b5e1 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv2 : evLe (colSpecW C Vc V 0).ev (midQ (0xffe6bcc2161638d35fb4 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv3 : evLe (colSpecW C Vc V 0).ev (midQ (0xfff96098ffc040c519fa : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem valsC6 : ∀ l ∈ KeepC6, evLe (colSpecW C Vc V 0).ev (midQ l) (MY - 1/2^28) = true := by
  simp only [KeepC6, List.forall_mem_cons]
  exact ⟨yv0, yv1, yv2, yv3, fun x hx => absurd hx (by simp)⟩
#print axioms yv0
#print axioms yv1
#print axioms yv2
#print axioms yv3
#print axioms valsC6
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal6
