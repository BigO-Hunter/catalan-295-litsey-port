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

def gS0N : List ℤ := raw_ints% [0, 214875342195, 0, -162752782224, 0, 127922979274, 0, -100564326715, 0, 79056881821, 0, -62149181426, 0, 48857489229, 0, -38408458470, 0, 30194136157, 0, -23736590703, 0, 18660104574, 0, -14669314017, 0, 11532023997, 0, -9065698458, 0, 7126839881, 0, -5602640208, 0, 4404417360, 0, -3462455479, 0, 2721948663, 0, -2139812213, 0, 1682175851, 0, -1322413049, 0, 1039591831, 0, -817256889, 0, 642472173, 0, -505068234, 0, 397050536, 0, -312134317, 0, 245378920, 0, -192900335]
def gS0 : List ℚ := gS0N.map (fun n : ℤ => (n : ℚ) / 2 ^ 40)
def c0S0 : ℚ := (768498781808 : ℤ) / 2 ^ 40
def PnS0 : List ℤ := raw_ints% [-206561083391, 0, 73876711208124, 0, -4444599862150304, 0, 213324850951074176, 0, -7661961419699225344, 0, 203608697024565094400, 0, -4056074084229528514560, 0, 61808332622689626849280, 0, -735237479415212547932160, 0, 6951776549970588868018176, 0, -53055253453954299210498048, 0, 331040372087211806347493376, 0, -1706506676565657076117798912, 0, 7329696786849390104810618880, 0, -26406916489136317284636164096, 0, 80206832894709670116384047104, 0, -206127282088825982725673451520, 0, 449209062510192516674602663936, 0, -830814462842512643300224139264, 0, 1303252731354216982179452289024, 0, -1730084393658379297325141983232, 0, 1935916633381347854395184775168, 0, -1814757426345137986913704083456, 0, 1412579059989673448626832015360, 0, -901656746653564812363709808640, 0, 463706523650262056628842921984, 0, -187315766314805612934068174848, 0, 57200995897487731524418666496, 0, -12408450442406584471452123136, 0, 1703354912710886579178045440, 0, -111199472233682412482068480]
theorem monoS0 : chebGen c0S0 gS0 = PnS0.map (fun n : ℤ => (n : ℚ) / 2 ^ 40) := by decide +kernel
def cutsS0 : List ℤ := raw_ints% [-14, -12, -8, -4, 0, 4, 8, 12, 14]
