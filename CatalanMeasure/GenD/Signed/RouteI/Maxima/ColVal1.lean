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
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal1
open CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
theorem yv0 : evLe (colSpecW C Vc V 0).ev (midQ (0x12adba1e3147a76e5e92 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv1 : evLe (colSpecW C Vc V 0).ev (midQ (0x1465ae29c62a6105528e : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv2 : evLe (colSpecW C Vc V 0).ev (midQ (0x162802b803d9cc3f124d : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv3 : evLe (colSpecW C Vc V 0).ev (midQ (0x17e7a761eaf8e9e7decc : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv4 : evLe (colSpecW C Vc V 0).ev (midQ (0x19a891afb4dbe750b08a : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv5 : evLe (colSpecW C Vc V 0).ev (midQ (0x1b712d6d3418dba7ba50 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv6 : evLe (colSpecW C Vc V 0).ev (midQ (0x1d387ee28ab0ade6eb8a : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv7 : evLe (colSpecW C Vc V 0).ev (midQ (0x1f08db35e4f351a4e7c3 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv8 : evLe (colSpecW C Vc V 0).ev (midQ (0x20dae40d2fa8e1699901 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv9 : evLe (colSpecW C Vc V 0).ev (midQ (0x22b833962a23113d17ac : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem valsC1 : ∀ l ∈ KeepC1, evLe (colSpecW C Vc V 0).ev (midQ l) (MY - 1/2^28) = true := by
  simp only [KeepC1, List.forall_mem_cons]
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
#print axioms valsC1
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal1
