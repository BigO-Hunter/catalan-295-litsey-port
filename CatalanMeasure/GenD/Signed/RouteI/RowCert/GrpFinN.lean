module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpN0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpN1
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpN2
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpN3

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The atoms of sign N together

kcost: one addition of lists, one length.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open Set

theorem cFN_eq : (addZ (addZ (addZ (addZ (addZ (addZ (addZ (addZ GcN0L GcN1L) GcN2L) GcN3L) GcN4L) GcN5L) GcN6L) GcN7L) GcN8L) = cFN := by
  decide +kernel -- kcost: 9 list additions, 8192 terms at most
theorem lenN : ALN.length ≤ 3110 := by
  decide +kernel -- kcost: one list spine of 3110
theorem hFN : Close dPc (avQ false ALN) cFN (9 / 10 ^ 10) := by
  have h0 : Close dPc (avQ false (ALN.take 16)) GcN0L (1 / 10 ^ 10) := grp_chunk gN0
  have h1 : Close dPc (avQ false (ALN.take 216)) (addZ GcN0L GcN1L) ((1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 16) (n := 200) false h0 (grp_chunk gN1)
  have h2 : Close dPc (avQ false (ALN.take 816)) (addZ (addZ GcN0L GcN1L) GcN2L) (((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 216) (n := 600) false h1 (grp_chunk gN2)
  have h3 : Close dPc (avQ false (ALN.take 1416)) (addZ (addZ (addZ GcN0L GcN1L) GcN2L) GcN3L) ((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 816) (n := 600) false h2 (grp_chunk gN3)
  have h4 : Close dPc (avQ false (ALN.take 1625)) (addZ (addZ (addZ (addZ GcN0L GcN1L) GcN2L) GcN3L) GcN4L) (((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 1416) (n := 209) false h3 (grp_chunk gN4)
  have h5 : Close dPc (avQ false (ALN.take 1628)) (addZ (addZ (addZ (addZ (addZ GcN0L GcN1L) GcN2L) GcN3L) GcN4L) GcN5L) ((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 1625) (n := 3) false h4 (grp_chunk gN5)
  have h6 : Close dPc (avQ false (ALN.take 2228)) (addZ (addZ (addZ (addZ (addZ (addZ GcN0L GcN1L) GcN2L) GcN3L) GcN4L) GcN5L) GcN6L) (((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 1628) (n := 600) false h5 (grp_chunk gN6)
  have h7 : Close dPc (avQ false (ALN.take 2828)) (addZ (addZ (addZ (addZ (addZ (addZ (addZ GcN0L GcN1L) GcN2L) GcN3L) GcN4L) GcN5L) GcN6L) GcN7L) ((((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 2228) (n := 600) false h6 (grp_chunk gN7)
  have h8 : Close dPc (avQ false (ALN.take 3110)) (addZ (addZ (addZ (addZ (addZ (addZ (addZ (addZ GcN0L GcN1L) GcN2L) GcN3L) GcN4L) GcN5L) GcN6L) GcN7L) GcN8L) (((((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 2828) (n := 282) false h7 (grp_chunk gN8)
  rw [List.take_of_length_le lenN, cFN_eq] at h8
  exact Close.mono h8 (by norm_num)
theorem hTN : Close dPc (avQ true LTN) cTN (1 / 10 ^ 10) := grp_chunk gNT

end CatalanMeasure.GenD.Signed.RouteI.RowCert
