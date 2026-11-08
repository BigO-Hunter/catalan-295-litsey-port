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
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal3
open CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem xv0 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x8f0905eca23d967ded3c : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv1 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x876c8a43b1ff18090873 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv2 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x7efc2393c425d8698581 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv3 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x76f30478c4e08d836678 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv4 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x6e8d39f13450d098a9d2 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv5 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x663ad7b156b7fc043a7d : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv6 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x5da21c86b7d7699ba384 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv7 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x556744ba5f62bf06aaee : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv8 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x4cf89d4a2a5a6bc831a5 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv9 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x44fc58f49f2cf3f130a0 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem valsC3 : ∀ l ∈ KeepC3, evLe (rowSpecW R Pc Vc P V 0).ev (midQ l) (MX - 1/2^28) = true := by
  simp only [KeepC3, List.forall_mem_cons]
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
#print axioms valsC3
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal3
