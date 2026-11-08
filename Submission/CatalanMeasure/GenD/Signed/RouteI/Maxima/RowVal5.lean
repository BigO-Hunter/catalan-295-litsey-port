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
-- kcost: 11 evLe goals, one declaration each, about 5.6 s each (RealValueChunk row mean)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal5
open CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem xv0 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x1d73844eac950fb4ba76 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv1 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x1bddd1945c1402b9c301 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv2 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x1a67e6f665e5cc5acc31 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv3 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x19a3ec31b035481b3b60 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv4 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x1b18405949205f93577f : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv5 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x1caf8f19a5338d424926 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv6 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x1e57a37120274f748018 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv7 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x2010c7fd162ad0ff5d12 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv8 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x21d0dd3a978ae4601111 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv9 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x23a21b65f3bbfe8b122b : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv10 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (0x2582fb7de734274e1ab9 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem valsC5 : ∀ l ∈ KeepC5, evLe (rowSpecW R Pc Vc P V 0).ev (midQ l) (MX - 1/2^28) = true := by
  simp only [KeepC5, List.forall_mem_cons]
  exact ⟨xv0, xv1, xv2, xv3, xv4, xv5, xv6, xv7, xv8, xv9, xv10, fun x hx => absurd hx (by simp)⟩
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
#print axioms xv10
#print axioms valsC5
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal5
