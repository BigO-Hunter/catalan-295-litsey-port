module
public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeP
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.PolyPos

/-! Measurement probe: the four heaviest LinkSlope blocks (S0..S3), with the upstream helper
defs `zMul`/`chebGen`/`slopeN` copied VERBATIM from LinkP, so each decision class can be
peak-measured without waiting for the full Submission closure. Not part of any build. -/

open CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed
open CatalanMeasure.Signed.Consts

namespace W4Probe.Blocks

set_option maxRecDepth 1000000
set_option Elab.async false

def zMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => zAdd (zSmul a q) (0 :: zMul p q)


def chebGen (c0 : ℚ) (g : List ℚ) : List ℚ := chebGo (g.map (fun x => x / 2)) [1] [0, 1] [c0]

def slopeN (Pn : List ℤ) (T : ℤ) : List ℤ :=
  zAdd (zSmul (2 ^ 40) [0, 0, 2 ^ 44 + T ^ 4, 0, 2 * 2 ^ 22 * T ^ 2])
    (zSmul (-1) (zMul (zAdd Pn [3 * 2 ^ 36]) [2 ^ 22 * T ^ 2, 0, 2 ^ 44 + T ^ 4, 0, 2 ^ 22 * T ^ 2]))

