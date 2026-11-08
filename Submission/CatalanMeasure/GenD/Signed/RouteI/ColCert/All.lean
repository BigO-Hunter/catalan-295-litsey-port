module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U00
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U01
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U02
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U03
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U04
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U05
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U06
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U07
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U08
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U09
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U10
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U11
public import Submission.CatalanMeasure.GenD.Signed.RouteI.ColCert.U12

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Signed.RouteI.ColCert.All
open CatalanMeasure.GenD.Signed.RouteI.FreeColCert CatalanMeasure.GenD.Signed.RouteI.CapSourceData CatalanMeasure.GenD.Signed.RouteI.FreeColCap0
open CatalanMeasure.GenD.Signed.RouteI.ColCert

/-! All units of the anchor-0 free column cover: `freeColCap_of_units` on the finite data. -/

def Lall : List UnitD := L0 ++ (L1 ++ (L2 ++ (L3 ++ (L4 ++ (L5 ++ (L6 ++ (L7 ++ (L8 ++ (L9 ++ (L10 ++ (L11 ++ (L12))))))))))))

theorem Lall_V : ∀ u ∈ Lall, u.V :=
  List.forall_mem_append.2 ⟨L0_V, List.forall_mem_append.2 ⟨L1_V, List.forall_mem_append.2 ⟨L2_V, List.forall_mem_append.2 ⟨L3_V, List.forall_mem_append.2 ⟨L4_V, List.forall_mem_append.2 ⟨L5_V, List.forall_mem_append.2 ⟨L6_V, List.forall_mem_append.2 ⟨L7_V, List.forall_mem_append.2 ⟨L8_V, List.forall_mem_append.2 ⟨L9_V, List.forall_mem_append.2 ⟨L10_V, List.forall_mem_append.2 ⟨L11_V, L12_V⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

def inOK : Bool := Lall.all fun u => decide (0 < u.M - u.δ) && decide (u.M + u.δ < lamZ)

theorem inOK_true : inOK = true := by
  -- kcost: 0.1 s estimated, 384 units, two comparisons each
  decide +kernel

theorem chain_true : chain 2258509194 (Lall.map rng) 999987067382 = true := by
  -- kcost: 0.1 s estimated, 384 units, one comparison each
  decide +kernel

/-- The anchor-0 free column cap, input `hC` of T4. -/
theorem freeColCap0_cert : capSource.FreeColCap 0 (-2946610 / 1000000) := by
  have hin : ∀ u ∈ Lall, 0 < u.M - u.δ ∧ u.M + u.δ < lamZ := by
    intro u hu
    have h := (List.all_eq_true.1 inOK_true) u hu
    simpa [Bool.and_eq_true, decide_eq_true_eq] using h
  exact freeColCap_of_units V0 V385 Lall 2258509194 999987067382 V0_V V385_V Lall_V hin chain_true
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

#print axioms freeColCap0_cert

end CatalanMeasure.GenD.Signed.RouteI.ColCert.All
