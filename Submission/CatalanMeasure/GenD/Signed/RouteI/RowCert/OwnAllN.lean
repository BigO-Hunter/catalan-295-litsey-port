module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnFinN
public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.DirVN
public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnN0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnN1
public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnN2
public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnN3

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The direct stream of sign N assembled

kcost: one sum of 277 weights, one list spine.
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

def EAllN : List Ent := (((((((((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) ++ EN4) ++ EN5) ++ EN6) ++ EN7) ++ EN8) ++ EN9)
theorem esumN : (EAllN.map fun e => |e.1|).sum ≤ 3900838476838327919823493073245331380935 := by
  decide +kernel -- kcost: 277 absolute values
theorem alenN : AoN.length ≤ 277 := by
  decide +kernel -- kcost: one filter of 1626
theorem preN : OwnPre pOwN qLN DzoN e1N e2N dlN ggN AoN EAllN accN9 := by
  have h0 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 0) [] 0 := OwnPre.base _ _ _ _ _ _ _ _
  have h1 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 28) ([] ++ EN0) accN0 := OwnPre.step (a := 0) (n := 28) h0 ownN0
  have h2 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 56) (([] ++ EN0) ++ EN1) accN1 := OwnPre.step (a := 28) (n := 28) h1 ownN1
  have h3 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 84) ((([] ++ EN0) ++ EN1) ++ EN2) accN2 := OwnPre.step (a := 56) (n := 28) h2 ownN2
  have h4 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 112) (((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) accN3 := OwnPre.step (a := 84) (n := 28) h3 ownN3
  have h5 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 140) ((((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) ++ EN4) accN4 := OwnPre.step (a := 112) (n := 28) h4 ownN4
  have h6 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 168) (((((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) ++ EN4) ++ EN5) accN5 := OwnPre.step (a := 140) (n := 28) h5 ownN5
  have h7 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 196) ((((((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) ++ EN4) ++ EN5) ++ EN6) accN6 := OwnPre.step (a := 168) (n := 28) h6 ownN6
  have h8 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 224) (((((((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) ++ EN4) ++ EN5) ++ EN6) ++ EN7) accN7 := OwnPre.step (a := 196) (n := 28) h7 ownN7
  have h9 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 252) ((((((((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) ++ EN4) ++ EN5) ++ EN6) ++ EN7) ++ EN8) accN8 := OwnPre.step (a := 224) (n := 28) h8 ownN8
  have h10 : OwnPre (pO DoN BoN CoN 64 128 6 7) qLN DzoN e1N e2N dlN ggN (AoN.take 277) (((((((((([] ++ EN0) ++ EN1) ++ EN2) ++ EN3) ++ EN4) ++ EN5) ++ EN6) ++ EN7) ++ EN8) ++ EN9) accN9 := OwnPre.step (a := 252) (n := 25) h9 ownN9
  rw [List.take_of_length_le alenN] at h10
  exact h10
theorem hDirFN : Close dPc (fun t => pint (GoN.map segR) fun y => Real.log |t - YCell.physX y|) cDN (12903603511 / 1125899906842624) :=
  hDirN preN esumN hVN

end CatalanMeasure.GenD.Signed.RouteI.RowCert
