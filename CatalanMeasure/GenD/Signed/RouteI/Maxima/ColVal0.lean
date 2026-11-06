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
-- kcost: 10 evLe goals, one declaration each, about 3.1 s each (YMCriticalValueProbe mean)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal0
open CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
theorem yv0 : evLe (colSpecW C Vc V 0).ev (midQ (0x24d55cb424220305298 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv1 : evLe (colSpecW C Vc V 0).ev (midQ (0x3ac8eea49df9554f949 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv2 : evLe (colSpecW C Vc V 0).ev (midQ (0x534e058d350678b9523 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv3 : evLe (colSpecW C Vc V 0).ev (midQ (0x6d1109a57d68ca53f1a : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv4 : evLe (colSpecW C Vc V 0).ev (midQ (0x8769bf3ac891cf735be : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv5 : evLe (colSpecW C Vc V 0).ev (midQ (0xa21bc2a2d19ad564104 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv6 : evLe (colSpecW C Vc V 0).ev (midQ (0xbd1110e3f4e6129cad5 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv7 : evLe (colSpecW C Vc V 0).ev (midQ (0xd8429ec02e587bbd3dd : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv8 : evLe (colSpecW C Vc V 0).ev (midQ (0xf3a5f1607ea9b8db9e0 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv9 : evLe (colSpecW C Vc V 0).ev (midQ (0x10f1e4fb08d1aab02884 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem valsC0 : ∀ l ∈ KeepC0, evLe (colSpecW C Vc V 0).ev (midQ l) (MY - 1/2^28) = true := by
  simp only [KeepC0, List.forall_mem_cons]
  exact ⟨yv0, yv1, yv2, yv3, yv4, yv5, yv6, yv7, yv8, yv9, fun x hx => absurd hx (by simp)⟩
#print axioms yv0
#print axioms yv1
#print axioms yv2
#print axioms yv3
#print axioms yv4
#print axioms yv5
#print axioms yv6
#print axioms yv7
#print axioms yv8
#print axioms yv9
#print axioms valsC0
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal0
