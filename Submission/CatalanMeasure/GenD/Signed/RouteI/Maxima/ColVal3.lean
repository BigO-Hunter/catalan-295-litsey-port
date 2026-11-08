module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Submission.CatalanMeasure.GenD.Cert.WLogSpec
public import Submission.CatalanMeasure.CellCert.CellW
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 10 evLe goals, one declaration each, about 3.1 s each (YMCriticalValueProbe mean)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal3
open CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
theorem yv0 : evLe (colSpecW C Vc V 0).ev (midQ (0x608232c6397f19752411 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv1 : evLe (colSpecW C Vc V 0).ev (midQ (0x68dff732d09dda3b10c6 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv2 : evLe (colSpecW C Vc V 0).ev (midQ (0x713c1b4f243ba00d70a6 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv3 : evLe (colSpecW C Vc V 0).ev (midQ (0x79a102e53a96ad86b345 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv4 : evLe (colSpecW C Vc V 0).ev (midQ (0x81c4ef84762bdde7f2c1 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv5 : evLe (colSpecW C Vc V 0).ev (midQ (0x89d27f3bba8ce9019dde : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv6 : evLe (colSpecW C Vc V 0).ev (midQ (0x91b2684e83594709c0be : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv7 : evLe (colSpecW C Vc V 0).ev (midQ (0x9971d4bd1fe31dcbf13e : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv8 : evLe (colSpecW C Vc V 0).ev (midQ (0xa0f85f694e2c29592590 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv9 : evLe (colSpecW C Vc V 0).ev (midQ (0xa84a276f77e8ec207a3a : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem valsC3 : ∀ l ∈ KeepC3, evLe (colSpecW C Vc V 0).ev (midQ l) (MY - 1/2^28) = true := by
  simp only [KeepC3, List.forall_mem_cons]
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
#print axioms valsC3
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal3
