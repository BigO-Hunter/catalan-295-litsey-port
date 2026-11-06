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
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal5
open CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
theorem yv0 : evLe (colSpecW C Vc V 0).ev (midQ (0xe7af1c283b807650b1fd : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv1 : evLe (colSpecW C Vc V 0).ev (midQ (0xeb9d1b5d24813c83fa54 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv2 : evLe (colSpecW C Vc V 0).ev (midQ (0xef36f6702baa03db4a17 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv3 : evLe (colSpecW C Vc V 0).ev (midQ (0xf27988d54de3954e2aa9 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv4 : evLe (colSpecW C Vc V 0).ev (midQ (0xf55c4a98f13897d9a76b : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv5 : evLe (colSpecW C Vc V 0).ev (midQ (0xf7e84c2393429f8e6efe : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv6 : evLe (colSpecW C Vc V 0).ev (midQ (0xfa172d66d6d8383697b1 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv7 : evLe (colSpecW C Vc V 0).ev (midQ (0xfbe9d3e04aaf1d1770e8 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv8 : evLe (colSpecW C Vc V 0).ev (midQ (0xfd60046a580ef90a714f : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem yv9 : evLe (colSpecW C Vc V 0).ev (midQ (0xfe7aef954fcbd0acbab3 : ℤ)) (MY - 1/2^28) = true := by decide +kernel -- kcost: 2.3 s each (standalone 6 Nov)
theorem valsC5 : ∀ l ∈ KeepC5, evLe (colSpecW C Vc V 0).ev (midQ l) (MY - 1/2^28) = true := by
  simp only [KeepC5, List.forall_mem_cons]
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
#print axioms valsC5
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal5
