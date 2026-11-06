module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnFinP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.DirVP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP1
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP2
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP3
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP4
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP5
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP6
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP7
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP8
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP9
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.OwnP10

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The direct stream of sign P assembled

kcost: one sum of 428 weights, one list spine.
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

def EAllP : List Ent := ((((((((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) ++ EP25) ++ EP26) ++ EP27) ++ EP28) ++ EP29) ++ EP30)
theorem esumP : (EAllP.map fun e => |e.1|).sum ≤ 13738551238933200232784319445618147403 := by
  decide +kernel -- kcost: 428 absolute values
theorem alenP : AoP.length ≤ 428 := by
  decide +kernel -- kcost: one filter of 596
theorem preP : OwnPre pOwP qLP DzoP e1P e2P dlP ggP AoP EAllP accP30 := by
  have h0 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 0) [] 0 := OwnPre.base _ _ _ _ _ _ _ _
  have h1 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 14) ([] ++ EP0) accP0 := OwnPre.step (a := 0) (n := 14) h0 ownP0
  have h2 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 28) (([] ++ EP0) ++ EP1) accP1 := OwnPre.step (a := 14) (n := 14) h1 ownP1
  have h3 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 42) ((([] ++ EP0) ++ EP1) ++ EP2) accP2 := OwnPre.step (a := 28) (n := 14) h2 ownP2
  have h4 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 56) (((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) accP3 := OwnPre.step (a := 42) (n := 14) h3 ownP3
  have h5 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 70) ((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) accP4 := OwnPre.step (a := 56) (n := 14) h4 ownP4
  have h6 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 84) (((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) accP5 := OwnPre.step (a := 70) (n := 14) h5 ownP5
  have h7 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 98) ((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) accP6 := OwnPre.step (a := 84) (n := 14) h6 ownP6
  have h8 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 112) (((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) accP7 := OwnPre.step (a := 98) (n := 14) h7 ownP7
  have h9 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 126) ((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) accP8 := OwnPre.step (a := 112) (n := 14) h8 ownP8
  have h10 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 140) (((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) accP9 := OwnPre.step (a := 126) (n := 14) h9 ownP9
  have h11 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 154) ((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) accP10 := OwnPre.step (a := 140) (n := 14) h10 ownP10
  have h12 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 168) (((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) accP11 := OwnPre.step (a := 154) (n := 14) h11 ownP11
  have h13 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 182) ((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) accP12 := OwnPre.step (a := 168) (n := 14) h12 ownP12
  have h14 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 196) (((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) accP13 := OwnPre.step (a := 182) (n := 14) h13 ownP13
  have h15 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 210) ((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) accP14 := OwnPre.step (a := 196) (n := 14) h14 ownP14
  have h16 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 224) (((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) accP15 := OwnPre.step (a := 210) (n := 14) h15 ownP15
  have h17 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 238) ((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) accP16 := OwnPre.step (a := 224) (n := 14) h16 ownP16
  have h18 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 252) (((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) accP17 := OwnPre.step (a := 238) (n := 14) h17 ownP17
  have h19 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 266) ((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) accP18 := OwnPre.step (a := 252) (n := 14) h18 ownP18
  have h20 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 280) (((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) accP19 := OwnPre.step (a := 266) (n := 14) h19 ownP19
  have h21 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 294) ((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) accP20 := OwnPre.step (a := 280) (n := 14) h20 ownP20
  have h22 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 308) (((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) accP21 := OwnPre.step (a := 294) (n := 14) h21 ownP21
  have h23 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 322) ((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) accP22 := OwnPre.step (a := 308) (n := 14) h22 ownP22
  have h24 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 336) (((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) accP23 := OwnPre.step (a := 322) (n := 14) h23 ownP23
  have h25 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 350) ((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) accP24 := OwnPre.step (a := 336) (n := 14) h24 ownP24
  have h26 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 364) (((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) ++ EP25) accP25 := OwnPre.step (a := 350) (n := 14) h25 ownP25
  have h27 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 378) ((((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) ++ EP25) ++ EP26) accP26 := OwnPre.step (a := 364) (n := 14) h26 ownP26
  have h28 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 392) (((((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) ++ EP25) ++ EP26) ++ EP27) accP27 := OwnPre.step (a := 378) (n := 14) h27 ownP27
  have h29 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 406) ((((((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) ++ EP25) ++ EP26) ++ EP27) ++ EP28) accP28 := OwnPre.step (a := 392) (n := 14) h28 ownP28
  have h30 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 420) (((((((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) ++ EP25) ++ EP26) ++ EP27) ++ EP28) ++ EP29) accP29 := OwnPre.step (a := 406) (n := 14) h29 ownP29
  have h31 : OwnPre (pO DoP BoP CoP 64 256 6 8) qLP DzoP e1P e2P dlP ggP (AoP.take 428) ((((((((((((((((((((((((((((((([] ++ EP0) ++ EP1) ++ EP2) ++ EP3) ++ EP4) ++ EP5) ++ EP6) ++ EP7) ++ EP8) ++ EP9) ++ EP10) ++ EP11) ++ EP12) ++ EP13) ++ EP14) ++ EP15) ++ EP16) ++ EP17) ++ EP18) ++ EP19) ++ EP20) ++ EP21) ++ EP22) ++ EP23) ++ EP24) ++ EP25) ++ EP26) ++ EP27) ++ EP28) ++ EP29) ++ EP30) accP30 := OwnPre.step (a := 420) (n := 8) h30 ownP30
  rw [List.take_of_length_le alenP] at h31
  exact h31
theorem hDirFP : Close dPc (fun t => pint (GoP.map segR) fun y => Real.log |t - YCell.physX y|) cDP (12441036745 / 1125899906842624) :=
  hDirP preP esumP hVP

end CatalanMeasure.GenD.Signed.RouteI.RowCert
