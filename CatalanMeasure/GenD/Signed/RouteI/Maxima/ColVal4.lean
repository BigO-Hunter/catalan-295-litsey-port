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
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal4
open CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
theorem yv0 : evLe (colSpecW C Vc V 0).ev (midQ (0xaf6f4aade5946a427b35 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv1 : evLe (colSpecW C Vc V 0).ev (midQ (0xb64f02df1ead0050d27a : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv2 : evLe (colSpecW C Vc V 0).ev (midQ (0xbcf0d82973c3632f48af : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv3 : evLe (colSpecW C Vc V 0).ev (midQ (0xc34840eb8ea229c16d70 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv4 : evLe (colSpecW C Vc V 0).ev (midQ (0xc95ec53697346dc3dc28 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv5 : evLe (colSpecW C Vc V 0).ev (midQ (0xcf2e4c41c2a7583bcfbc : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv6 : evLe (colSpecW C Vc V 0).ev (midQ (0xd4af8543f30309757248 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv7 : evLe (colSpecW C Vc V 0).ev (midQ (0xd9ee99a591cdf0e74432 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv8 : evLe (colSpecW C Vc V 0).ev (midQ (0xded5c23425eb1b1763e3 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv9 : evLe (colSpecW C Vc V 0).ev (midQ (0xe36a657f08be9541955c : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem valsC4 : ∀ l ∈ KeepC4, evLe (colSpecW C Vc V 0).ev (midQ l) (MY - 1/2^28) = true := by
  simp only [KeepC4, List.forall_mem_cons]
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
#print axioms valsC4
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal4
