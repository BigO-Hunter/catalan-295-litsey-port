module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 10 evLe goals, one declaration each, about 5.6 s each (RealValueChunk row mean)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal4
open CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem xv0 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x3d48402ea295910b4b7f : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv1 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x35e5d5470a7ec08a24a5 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv2 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x2fcd95eb42c05f69d6ea : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv3 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x2b7dea862d6d1a2f0173 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv4 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x2889fe4cb5a4e0b11d61 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv5 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x2663f29616208458d8c0 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv6 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x24755b3e6533b4615d73 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv7 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x229f8a56acc5400df8d6 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv8 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x20d772b7e581661cb543 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv9 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x1f2063c99c03c3d7bdd1 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem valsC4 : ∀ l ∈ KeepC4, evLe (rowSpecW R Pc Vc P V 0).ev (midQ l) (MX - 1/2^28) = true := by
  simp only [KeepC4, List.forall_mem_cons]
  exact ⟨xv0, xv1, xv2, xv3, xv4, xv5, xv6, xv7, xv8, xv9, fun x hx => absurd hx (by simp)⟩
#print axioms xv0
#print axioms xv1
#print axioms xv2
#print axioms xv3
#print axioms xv4
#print axioms xv5
#print axioms xv6
#print axioms xv7
#print axioms xv8
#print axioms xv9
#print axioms valsC4
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal4
