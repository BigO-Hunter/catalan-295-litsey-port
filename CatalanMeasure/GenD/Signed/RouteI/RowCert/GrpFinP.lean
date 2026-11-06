module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpP0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpP1
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpP2
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.GrpP3

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The atoms of sign P together

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

theorem cFP_eq : (addZ (addZ (addZ (addZ (addZ (addZ (addZ (addZ GcP0L GcP1L) GcP2L) GcP3L) GcP4L) GcP5L) GcP6L) GcP7L) GcP8L) = cFP := by
  decide +kernel -- kcost: 9 list additions, 8192 terms at most
theorem lenP : ALP.length ≤ 2660 := by
  decide +kernel -- kcost: one list spine of 2660
theorem hFP : Close dPc (avQ false ALP) cFP (9 / 10 ^ 10) := by
  have h0 : Close dPc (avQ false (ALP.take 31)) GcP0L (1 / 10 ^ 10) := grp_chunk gP0
  have h1 : Close dPc (avQ false (ALP.take 531)) (addZ GcP0L GcP1L) ((1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 31) (n := 500) false h0 (grp_chunk gP1)
  have h2 : Close dPc (avQ false (ALP.take 1131)) (addZ (addZ GcP0L GcP1L) GcP2L) (((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 531) (n := 600) false h1 (grp_chunk gP2)
  have h3 : Close dPc (avQ false (ALP.take 1731)) (addZ (addZ (addZ GcP0L GcP1L) GcP2L) GcP3L) ((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 1131) (n := 600) false h2 (grp_chunk gP3)
  have h4 : Close dPc (avQ false (ALP.take 2331)) (addZ (addZ (addZ (addZ GcP0L GcP1L) GcP2L) GcP3L) GcP4L) (((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 1731) (n := 600) false h3 (grp_chunk gP4)
  have h5 : Close dPc (avQ false (ALP.take 2531)) (addZ (addZ (addZ (addZ (addZ GcP0L GcP1L) GcP2L) GcP3L) GcP4L) GcP5L) ((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 2331) (n := 200) false h4 (grp_chunk gP5)
  have h6 : Close dPc (avQ false (ALP.take 2624)) (addZ (addZ (addZ (addZ (addZ (addZ GcP0L GcP1L) GcP2L) GcP3L) GcP4L) GcP5L) GcP6L) (((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 2531) (n := 93) false h5 (grp_chunk gP6)
  have h7 : Close dPc (avQ false (ALP.take 2659)) (addZ (addZ (addZ (addZ (addZ (addZ (addZ GcP0L GcP1L) GcP2L) GcP3L) GcP4L) GcP5L) GcP6L) GcP7L) ((((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 2624) (n := 35) false h6 (grp_chunk gP7)
  have h8 : Close dPc (avQ false (ALP.take 2660)) (addZ (addZ (addZ (addZ (addZ (addZ (addZ (addZ GcP0L GcP1L) GcP2L) GcP3L) GcP4L) GcP5L) GcP6L) GcP7L) GcP8L) (((((((((1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) + 1 / 10 ^ 10) := close_step (a := 2659) (n := 1) false h7 (grp_chunk gP8)
  rw [List.take_of_length_le lenP, cFP_eq] at h8
  exact Close.mono h8 (by norm_num)
theorem hTP : Close dPc (avQ true LTP) cTP (1 / 10 ^ 10) := grp_chunk gPT

end CatalanMeasure.GenD.Signed.RouteI.RowCert
