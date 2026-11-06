module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 10 evLe goals, one declaration each, about 5.6 s each (RealValueChunk row mean)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal2
open CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem xv0 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xd2f854b963c4fb15f69e : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv1 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xcda563b2b766594bfbac : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv2 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xc7707bad6b739e0d70ac : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv3 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xc1525d88c0b1f533a683 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv4 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xbafee2f566d9f3383545 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv5 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xb41d5290bd1a7b96e614 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv6 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xad0c3b60f28254926b0b : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv7 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0xa633b3295d5f0517f680 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv8 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x9e7531204755c7faff25 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem xv9 : evLe (rowSpecW R Pc Vc P V 0).ev (midQ (-0x96fc7f0c637e0043e024 : ℤ)) (MX - 1/2^28) = true := by decide +kernel -- kcost: 4.6 s each (standalone 5 Nov)
theorem valsC2 : ∀ l ∈ KeepC2, evLe (rowSpecW R Pc Vc P V 0).ev (midQ l) (MX - 1/2^28) = true := by
  simp only [KeepC2, List.forall_mem_cons]
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
#print axioms valsC2
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal2
