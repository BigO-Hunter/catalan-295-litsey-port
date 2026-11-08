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
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal0
open CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem xv0 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xfffffffff920a2bf95cf : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv1 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xfffffffeb7b3cb0f1a6f : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv2 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xffffffde7d0f856f7f90 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv3 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xfffffcea0e526787ac2a : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv4 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xffe3d449cf8c58b6b4d7 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv5 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xffa4d53f8a758829d311 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv6 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xff22e1da4684c56a93ac : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv7 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xfe4d661284409ab0abb6 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv8 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xfd1c931999ca524060c4 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv9 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xfb8fa2ef57bb3ec45611 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem valsC0 : ∀ l ∈ KeepC0, evLe (rowSpecW R Pc Vc P V 0).ev (midQ l) (MX - 1/2^28) = true := by
  simp only [KeepC0, List.forall_mem_cons]
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
#print axioms valsC0
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal0
