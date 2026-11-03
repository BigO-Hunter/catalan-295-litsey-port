module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsStandaloneDelta011
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta011
namespace StandaloneDelta011
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta011.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta011.q2listC (raw_ints% []))⟩
def d2Delta88Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta88Ts : List LTerm := laurentClean []
def d2Delta88Lo : ℚ := (d2LitsStandaloneDelta011.q2 (41116633) 1 (-28))
def d2Delta88Hi : ℚ := (d2LitsStandaloneDelta011.q2 (5270523) 1 (-25))
def d2Delta88Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta88Qd : List (ℚ × ℚ) := []
def d2Delta88Ld : List LaurentPieceData := []
def d2Delta88Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-2229695088076271192027823358720693907165145355, 1, -158, -1130607398286155626302222081115298585661, 1, -157, 12665588474239067056004462367332627577, 1, -160, 31849788848924222261894225416645822649, 1, -160, -11136967876994541421988901504900283, 1, -159, -17215659579376187723821596087170571, 1, -159, -7460196894953188563504063941025, 1, -159, 16311218147643723839578254507313, 1, -160, 6232248210879773821279009625, 1, -159, -2117907762462398585097577131, 1, -159, -2805390407221785287396653, 1, -160, 687722076162078434627605, 1, -160, 264340784140371710337, 1, -160, -18957566299946885451, 1, -158, -1205409121939063, 1, -158, 187740486158031, 1, -155, -704515210513, 1, -159, -44841720647, 1, -157, -1799279581, 1, -160, -1376266575, 1, -160, -314790099, 1, -158, -428234937, 1, -159, -391115899, 1, -159, -511378457, 1, -160, -472033741, 1, -160, -37038015, 1, -157, -34560939, 1, -157, -166538393, 1, -160, -157087987, 1, -160, -45379509, 1, -159, -10813941, 1, -157, -47937079, 1, -160])
def d2Delta88S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-2076565372988798712669698891891565871, 1, -128, -1064103658270145344808675458735, 1, -127, 2969650024131133036024059275, 1, -127, 29822973468233224483760361023, 1, -128, -5165153173968180153116385, 1, -125, -128692433632066315889188895, 1, -128, -55954635067106376251471, 1, -127, 243624609097415557217261, 1, -128, 372307437695435398453, 1, -128, -252925479315654538417, 1, -128, -20925424005106553, 1, -124, 41050220159300441, 1, -126, 63039813202561, 1, -127, -36201678808789, 1, -127, -1144197571, 1, -125, 22940683381, 1, -128, -10750669, 1, -128, -2722515, 1, -127, 5227, 1, -128, 125, 1, -125, -1, 1, -127, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta88Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta88Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta88Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta88Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta88Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta88Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta88El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta88Shift : polyRoundApx 128 d2Delta88Lo d2Delta88Hi d2Delta88Fq.poly = (d2Delta88S,d2Delta88Es) := by decide +kernel
theorem d2Delta88Sites : mergeSites d2Delta88Fq.plogs = [] := by decide +kernel
theorem d2Delta88PData : d2Delta88Pd = [] := by decide +kernel
theorem d2Delta88Plogs : plogsRoundM 16 24 20 128 d2Delta88Lo d2Delta88Hi (mergeSites d2Delta88Fq.plogs) d2Delta88Pd = some (d2Delta88Ap,d2Delta88Ep) := by
  rw [d2Delta88Sites,d2Delta88PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta88Poles : polesRoundM 16 24 12 128 d2Delta88Lo d2Delta88Hi d2Delta88Fq.poles d2Delta88Qd = some (d2Delta88Aq,d2Delta88Eq) := by decide +kernel
theorem d2Delta88Laurent : laurentRoundM 16 30 128 d2Delta88Lo d2Delta88Hi d2Delta88Ts d2Delta88Ld = some (d2Delta88Al,d2Delta88El) := by decide +kernel
theorem d2Delta88Small : chebPolyUB (vecAdd d2Delta88S (vecAdd d2Delta88Ap (vecAdd d2Delta88Aq d2Delta88Al))) d2Delta88Gam+d2Delta88Es+d2Delta88Ep+d2Delta88Eq+d2Delta88El ≤ (d2LitsStandaloneDelta011.q2 (-7377434676444277401807) 1 (-80)) := by decide +kernel
theorem d2Delta88Check : chebRoundPieceL d2Delta88Fq d2Delta88Ts 16 24 12 20 30 128 d2Delta88Lo d2Delta88Hi d2Delta88Pd d2Delta88Qd d2Delta88Ld d2Delta88Gam (d2LitsStandaloneDelta011.q2 (-7377434676444277401807) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta88Fq d2Delta88Ts 16 24 12 20 30 128 d2Delta88Lo d2Delta88Hi d2Delta88Pd d2Delta88Qd d2Delta88Ld d2Delta88Gam d2Delta88S d2Delta88Ap d2Delta88Aq d2Delta88Al d2Delta88Es d2Delta88Ep d2Delta88Eq d2Delta88El (by decide +kernel) d2Delta88Shift d2Delta88Plogs d2Delta88Poles d2Delta88Laurent]
  exact decide_eq_true d2Delta88Small
theorem d2Delta88Bound : ∀ x ∈ Icc ((d2Delta88Lo : ℚ) : ℝ) ((d2Delta88Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-7377434676444277401807) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta88Fq d2Delta88Ts 16 24 12 20 30 128 d2Delta88Lo d2Delta88Hi d2Delta88Pd d2Delta88Qd d2Delta88Ld d2Delta88Gam (d2LitsStandaloneDelta011.q2 (-7377434676444277401807) 1 (-80)) d2Delta88Check
  simpa only [d2Delta88Fq, d2Delta88Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta88Shift
#print axioms d2Delta88Sites
#print axioms d2Delta88PData
#print axioms d2Delta88Plogs
#print axioms d2Delta88Poles
#print axioms d2Delta88Laurent
#print axioms d2Delta88Small
#print axioms d2Delta88Check
#print axioms d2Delta88Bound

def d2Delta89Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta89Ts : List LTerm := laurentClean []
def d2Delta89Lo : ℚ := (d2LitsStandaloneDelta011.q2 (5270523) 1 (-25))
def d2Delta89Hi : ℚ := (d2LitsStandaloneDelta011.q2 (43211735) 1 (-28))
def d2Delta89Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta89Qd : List (ℚ × ℚ) := []
def d2Delta89Ld : List LaurentPieceData := []
def d2Delta89Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-8918797168794870839831173417972569480247709669, 1, -160, -7472497170897219908405895544258943976131, 1, -160, 185179685231139326542104096808954641683, 1, -159, 408112997484958653612111386291439367, 1, -154, -677850453638856822690320864564432563, 1, -160, -29403980813735998075344683193161631, 1, -160, 212320308265956962811540479503773, 1, -159, 14307434153208317609141851555697, 1, -160, -33705227685138681928209492915, 1, -158, -3753035890624986036688884981, 1, -160, 13179545445029488834721751, 1, -159, 151938681045453560238631, 1, -158, -878370283725618075961, 1, -158, -66273132130137347479, 1, -160, 337729700727719705, 1, -160, 2583432741579017, 1, -159, -24243554110249, 1, -160, -151731994355, 1, -159, -327082473, 1, -159, -186811859, 1, -157, -628302217, 1, -159, -58359765, 1, -156, -772169913, 1, -160, -560946165, 1, -160, -230485591, 1, -159, -163370025, 1, -159, -133596835, 1, -159, -92211419, 1, -159, -75142903, 1, -159, -100811835, 1, -160, -20493845, 1, -158, -53340301, 1, -160])
def d2Delta89S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-2076569371817753773930596323697916833, 1, -128, -3433798149901223828932070327, 1, -119, 43431599182097304521978176907, 1, -126, 24462539851487323640060059445, 1, -128, -316836403251898774674113193, 1, -126, -109911837546477767074741341, 1, -128, 3171861967292641933578235, 1, -128, 106850551275705848067847, 1, -127, -4025837524186844860389, 1, -128, -112048551492862246707, 1, -127, 3147277674364974055, 1, -128, 18138192297541243, 1, -125, -1677614151244093, 1, -128, -63276930809905, 1, -128, 644908396331, 1, -128, 19729575487, 1, -128, -185123489, 1, -128, -4598347, 1, -128, 40723, 1, -128, 829, 1, -128, -1, 1, -125, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta89Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta89Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta89Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta89Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta89Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta89Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta89El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta89Shift : polyRoundApx 128 d2Delta89Lo d2Delta89Hi d2Delta89Fq.poly = (d2Delta89S,d2Delta89Es) := by decide +kernel
theorem d2Delta89Sites : mergeSites d2Delta89Fq.plogs = [] := by decide +kernel
theorem d2Delta89PData : d2Delta89Pd = [] := by decide +kernel
theorem d2Delta89Plogs : plogsRoundM 16 24 20 128 d2Delta89Lo d2Delta89Hi (mergeSites d2Delta89Fq.plogs) d2Delta89Pd = some (d2Delta89Ap,d2Delta89Ep) := by
  rw [d2Delta89Sites,d2Delta89PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta89Poles : polesRoundM 16 24 12 128 d2Delta89Lo d2Delta89Hi d2Delta89Fq.poles d2Delta89Qd = some (d2Delta89Aq,d2Delta89Eq) := by decide +kernel
theorem d2Delta89Laurent : laurentRoundM 16 30 128 d2Delta89Lo d2Delta89Hi d2Delta89Ts d2Delta89Ld = some (d2Delta89Al,d2Delta89El) := by decide +kernel
theorem d2Delta89Small : chebPolyUB (vecAdd d2Delta89S (vecAdd d2Delta89Ap (vecAdd d2Delta89Aq d2Delta89Al))) d2Delta89Gam+d2Delta89Es+d2Delta89Ep+d2Delta89Eq+d2Delta89El ≤ (d2LitsStandaloneDelta011.q2 (-3688724797835179812537) 1 (-79)) := by decide +kernel
theorem d2Delta89Check : chebRoundPieceL d2Delta89Fq d2Delta89Ts 16 24 12 20 30 128 d2Delta89Lo d2Delta89Hi d2Delta89Pd d2Delta89Qd d2Delta89Ld d2Delta89Gam (d2LitsStandaloneDelta011.q2 (-3688724797835179812537) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta89Fq d2Delta89Ts 16 24 12 20 30 128 d2Delta89Lo d2Delta89Hi d2Delta89Pd d2Delta89Qd d2Delta89Ld d2Delta89Gam d2Delta89S d2Delta89Ap d2Delta89Aq d2Delta89Al d2Delta89Es d2Delta89Ep d2Delta89Eq d2Delta89El (by decide +kernel) d2Delta89Shift d2Delta89Plogs d2Delta89Poles d2Delta89Laurent]
  exact decide_eq_true d2Delta89Small
theorem d2Delta89Bound : ∀ x ∈ Icc ((d2Delta89Lo : ℚ) : ℝ) ((d2Delta89Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-3688724797835179812537) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta89Fq d2Delta89Ts 16 24 12 20 30 128 d2Delta89Lo d2Delta89Hi d2Delta89Pd d2Delta89Qd d2Delta89Ld d2Delta89Gam (d2LitsStandaloneDelta011.q2 (-3688724797835179812537) 1 (-79)) d2Delta89Check
  simpa only [d2Delta89Fq, d2Delta89Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta89Shift
#print axioms d2Delta89Sites
#print axioms d2Delta89PData
#print axioms d2Delta89Plogs
#print axioms d2Delta89Poles
#print axioms d2Delta89Laurent
#print axioms d2Delta89Small
#print axioms d2Delta89Check
#print axioms d2Delta89Bound

def d2Delta90Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta90Ts : List LTerm := laurentClean []
def d2Delta90Lo : ℚ := (d2LitsStandaloneDelta011.q2 (43211735) 1 (-28))
def d2Delta90Hi : ℚ := (d2LitsStandaloneDelta011.q2 (45306837) 1 (-28))
def d2Delta90Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta90Qd : List (ℚ × ℚ) := []
def d2Delta90Ld : List LaurentPieceData := []
def d2Delta90Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-2229702165331768037362318204951162110843169099, 1, -158, -486139779447786312745577457342604301303, 1, -158, 78236769036702998422513381064773241709, 1, -155, 6493280514372497689776184648648369521, 1, -159, -9783850123457950970679589291862935773, 1, -159, -173175737410143582597207097558966025, 1, -160, 26369643130198178748535765407878665, 1, -159, 494056548803691508467973582133697, 1, -160, -1097338919337108154553762208197, 1, -154, -606175799794769060946566106277, 1, -160, 55622149738261276535984262053, 1, -160, 414909058251172110399965649, 1, -160, -29126913286313483969639455, 1, -160, -180706994208109608709873, 1, -160, 5390530384196541698197, 1, -159, 54276610572619891457, 1, -160, -2953569722086041369, 1, -160, -11895339462422247, 1, -160, 619880938284367, 1, -160, 993225463043, 1, -159, -103580191669, 1, -160, -1122290757, 1, -160, -689608809, 1, -160, -256581935, 1, -159, -210837701, 1, -159, -18579265, 1, -156, -61415147, 1, -158, -166955653, 1, -160, -69472081, 1, -159, -90874323, 1, -160, -76235539, 1, -160, -47916131, 1, -160])
def d2Delta90S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-2076572548720098832264460076013005383, 1, -128, -462026368691684009664103578041, 1, -128, 601243970171818362199232063303, 1, -127, 12907548542683393655502129997, 1, -128, -4629963855832572671014590093, 1, -125, -658074513000512738756158221, 1, -128, 397138847617236536802200327, 1, -128, 3721791619175198706748971, 1, -127, -2109631522126442731424739, 1, -128, -18201814899663654940993, 1, -127, 3336221210946497051091, 1, -127, 49741642395497188735, 1, -127, -6980456268074746851, 1, -127, -173113403544016045, 1, -128, 20653537082822433, 1, -128, 51955350601795, 1, -126, -22619209584597, 1, -128, -182085511543, 1, -128, 296561425, 1, -122, 121665919, 1, -128, -12541523, 1, -128, -64333, 1, -128, 6675, 1, -128, 27, 1, -128, -3, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta90Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta90Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta90Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta90Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta90Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta90Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta90El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta90Shift : polyRoundApx 128 d2Delta90Lo d2Delta90Hi d2Delta90Fq.poly = (d2Delta90S,d2Delta90Es) := by decide +kernel
theorem d2Delta90Sites : mergeSites d2Delta90Fq.plogs = [] := by decide +kernel
theorem d2Delta90PData : d2Delta90Pd = [] := by decide +kernel
theorem d2Delta90Plogs : plogsRoundM 16 24 20 128 d2Delta90Lo d2Delta90Hi (mergeSites d2Delta90Fq.plogs) d2Delta90Pd = some (d2Delta90Ap,d2Delta90Ep) := by
  rw [d2Delta90Sites,d2Delta90PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta90Poles : polesRoundM 16 24 12 128 d2Delta90Lo d2Delta90Hi d2Delta90Fq.poles d2Delta90Qd = some (d2Delta90Aq,d2Delta90Eq) := by decide +kernel
theorem d2Delta90Laurent : laurentRoundM 16 30 128 d2Delta90Lo d2Delta90Hi d2Delta90Ts d2Delta90Ld = some (d2Delta90Al,d2Delta90El) := by decide +kernel
theorem d2Delta90Small : chebPolyUB (vecAdd d2Delta90S (vecAdd d2Delta90Ap (vecAdd d2Delta90Aq d2Delta90Al))) d2Delta90Gam+d2Delta90Es+d2Delta90Ep+d2Delta90Eq+d2Delta90El ≤ (d2LitsStandaloneDelta011.q2 (-7377461905192547313591) 1 (-80)) := by decide +kernel
theorem d2Delta90Check : chebRoundPieceL d2Delta90Fq d2Delta90Ts 16 24 12 20 30 128 d2Delta90Lo d2Delta90Hi d2Delta90Pd d2Delta90Qd d2Delta90Ld d2Delta90Gam (d2LitsStandaloneDelta011.q2 (-7377461905192547313591) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta90Fq d2Delta90Ts 16 24 12 20 30 128 d2Delta90Lo d2Delta90Hi d2Delta90Pd d2Delta90Qd d2Delta90Ld d2Delta90Gam d2Delta90S d2Delta90Ap d2Delta90Aq d2Delta90Al d2Delta90Es d2Delta90Ep d2Delta90Eq d2Delta90El (by decide +kernel) d2Delta90Shift d2Delta90Plogs d2Delta90Poles d2Delta90Laurent]
  exact decide_eq_true d2Delta90Small
theorem d2Delta90Bound : ∀ x ∈ Icc ((d2Delta90Lo : ℚ) : ℝ) ((d2Delta90Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-7377461905192547313591) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta90Fq d2Delta90Ts 16 24 12 20 30 128 d2Delta90Lo d2Delta90Hi d2Delta90Pd d2Delta90Qd d2Delta90Ld d2Delta90Gam (d2LitsStandaloneDelta011.q2 (-7377461905192547313591) 1 (-80)) d2Delta90Check
  simpa only [d2Delta90Fq, d2Delta90Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta90Shift
#print axioms d2Delta90Sites
#print axioms d2Delta90PData
#print axioms d2Delta90Plogs
#print axioms d2Delta90Poles
#print axioms d2Delta90Laurent
#print axioms d2Delta90Small
#print axioms d2Delta90Check
#print axioms d2Delta90Bound

def d2Delta91Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta91Ts : List LTerm := laurentClean []
def d2Delta91Lo : ℚ := (d2LitsStandaloneDelta011.q2 (45306837) 1 (-28))
def d2Delta91Hi : ℚ := (d2LitsStandaloneDelta011.q2 (11588597) 1 (-26))
def d2Delta91Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta91Qd : List (ℚ × ℚ) := []
def d2Delta91Ld : List LaurentPieceData := []
def d2Delta91Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-1114850343831540346054761643304398758114683431, 1, -157, 5656964828106628172034511706735570995, 1, -150, 409035700086007895300908402380270700125, 1, -160, -26311722601232582701036525110899526173, 1, -160, -237662679743070757350104182851795299, 1, -158, 11958630145176882974685181631797969, 1, -159, 88712041273730283999535827699051, 1, -157, -4718999088107287718285773454843, 1, -159, -249324050023866940699385440913, 1, -160, 2136982640512761843434940621, 1, -160, 50554299260477363395434747, 1, -160, -19959682766533905614367, 1, -156, -6648246906371342462459, 1, -160, 17005045075864562707, 1, -159, 38165939372643713, 1, -156, -674496235885595, 1, -158, -5156211144105, 1, -157, 161778541459, 1, -160, 16418723, 1, -157, -711343949, 1, -159, -9860235, 1, -153, -868759673, 1, -160, -773856523, 1, -160, -517950757, 1, -160, -460295587, 1, -160, -299691837, 1, -160, -132704803, 1, -159, -168200461, 1, -160, -74130895, 1, -159, -91517163, 1, -160, -80187597, 1, -160, -48245429, 1, -160])
def d2Delta91S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-1038285340256917234408095512888513759, 1, -127, 85445743813347658662084401031, 1, -124, 96122895884168714571081657675, 1, -127, -3077024721864828067639941465, 1, -125, -1778665717621959203896097799, 1, -128, 89345067742150581802160339, 1, -128, 1325630941866506893268831, 1, -126, -70461966670324253089565, 1, -127, -3722756388039431600645, 1, -127, 63791804196763939441, 1, -127, 1509014524767189005, 1, -126, -76245617467741619, 1, -128, -793552442510047, 1, -126, 32473163035023, 1, -128, 291497835127, 1, -126, -2575655915, 1, -126, -314979221, 1, -128, 1252481, 1, -127, 16257, 1, -126, -477, 1, -128, -11, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta91Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta91Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta91Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta91Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta91Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta91Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta91El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta91Shift : polyRoundApx 128 d2Delta91Lo d2Delta91Hi d2Delta91Fq.poly = (d2Delta91S,d2Delta91Es) := by decide +kernel
theorem d2Delta91Sites : mergeSites d2Delta91Fq.plogs = [] := by decide +kernel
theorem d2Delta91PData : d2Delta91Pd = [] := by decide +kernel
theorem d2Delta91Plogs : plogsRoundM 16 24 20 128 d2Delta91Lo d2Delta91Hi (mergeSites d2Delta91Fq.plogs) d2Delta91Pd = some (d2Delta91Ap,d2Delta91Ep) := by
  rw [d2Delta91Sites,d2Delta91PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta91Poles : polesRoundM 16 24 12 128 d2Delta91Lo d2Delta91Hi d2Delta91Fq.poles d2Delta91Qd = some (d2Delta91Aq,d2Delta91Eq) := by decide +kernel
theorem d2Delta91Laurent : laurentRoundM 16 30 128 d2Delta91Lo d2Delta91Hi d2Delta91Ts d2Delta91Ld = some (d2Delta91Al,d2Delta91El) := by decide +kernel
theorem d2Delta91Small : chebPolyUB (vecAdd d2Delta91S (vecAdd d2Delta91Ap (vecAdd d2Delta91Aq d2Delta91Al))) d2Delta91Gam+d2Delta91Es+d2Delta91Ep+d2Delta91Eq+d2Delta91El ≤ (d2LitsStandaloneDelta011.q2 (-7377455569970939057679) 1 (-80)) := by decide +kernel
theorem d2Delta91Check : chebRoundPieceL d2Delta91Fq d2Delta91Ts 16 24 12 20 30 128 d2Delta91Lo d2Delta91Hi d2Delta91Pd d2Delta91Qd d2Delta91Ld d2Delta91Gam (d2LitsStandaloneDelta011.q2 (-7377455569970939057679) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta91Fq d2Delta91Ts 16 24 12 20 30 128 d2Delta91Lo d2Delta91Hi d2Delta91Pd d2Delta91Qd d2Delta91Ld d2Delta91Gam d2Delta91S d2Delta91Ap d2Delta91Aq d2Delta91Al d2Delta91Es d2Delta91Ep d2Delta91Eq d2Delta91El (by decide +kernel) d2Delta91Shift d2Delta91Plogs d2Delta91Poles d2Delta91Laurent]
  exact decide_eq_true d2Delta91Small
theorem d2Delta91Bound : ∀ x ∈ Icc ((d2Delta91Lo : ℚ) : ℝ) ((d2Delta91Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-7377455569970939057679) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta91Fq d2Delta91Ts 16 24 12 20 30 128 d2Delta91Lo d2Delta91Hi d2Delta91Pd d2Delta91Qd d2Delta91Ld d2Delta91Gam (d2LitsStandaloneDelta011.q2 (-7377455569970939057679) 1 (-80)) d2Delta91Check
  simpa only [d2Delta91Fq, d2Delta91Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta91Shift
#print axioms d2Delta91Sites
#print axioms d2Delta91PData
#print axioms d2Delta91Plogs
#print axioms d2Delta91Poles
#print axioms d2Delta91Laurent
#print axioms d2Delta91Small
#print axioms d2Delta91Check
#print axioms d2Delta91Bound

def d2Delta92Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta92Ts : List LTerm := laurentClean []
def d2Delta92Lo : ℚ := (d2LitsStandaloneDelta011.q2 (11588597) 1 (-26))
def d2Delta92Hi : ℚ := (d2LitsStandaloneDelta011.q2 (3159037) 1 (-24))
def d2Delta92Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta92Qd : List (ℚ × ℚ) := []
def d2Delta92Ld : List LaurentPieceData := []
def d2Delta92Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-8918779139362692911454674137287914655030724807, 1, -160, 5061518371547095201439715958213033254317, 1, -159, -9278289505572179960902805591456978751635, 1, -160, -1795054964225061001781640828393590883397, 1, -160, 103161759890522165170798316151152039533, 1, -159, 8890630169580287102518374981667556415, 1, -158, -762664213346660032766085911657443083, 1, -159, -271208770671604485463895681131009925, 1, -160, 90906785568084231572863532866167, 1, -154, 275901521232089377567890026929059, 1, -158, -7045928507934505782435252026375, 1, -159, -1400063884910107703456952699369, 1, -159, 24513403733498323630336639449, 1, -160, 2424289827620091764385062315, 1, -159, -32830841064288082657859305, 1, -160, -1519347700023665063907605, 1, -158, 17439050777688140141503, 1, -159, 5750437024692414301683, 1, -160, -29625798102043675389, 1, -160, -2120244266418365581, 1, -159, 2521021154827515, 1, -157, 156234046728351, 1, -156, -2763282729567, 1, -158, -300826666961, 1, -158, 4444829445, 1, -160, 80223375, 1, -159, -270543111, 1, -160, -182273119, 1, -160, -75156189, 1, -159, -100557125, 1, -160, -40690061, 1, -159, -13466209, 1, -158])
def d2Delta92S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-1038281439479732301651665485139371189, 1, -127, 3652629131422139005533211427065, 1, -128, -1177820957063876297098549375451, 1, -126, -230117905074464757356697650171, 1, -125, 200786216370701942522461824967, 1, -127, 139664843424769430341731001115, 1, -128, -11715059511934960120266210891, 1, -128, -4191177937053837007477604307, 1, -128, 44407572506865413270203375, 1, -126, 67634840294399146953316669, 1, -128, -1715249794809099014505313, 1, -128, -682761387717644476860559, 1, -128, 1488726082600182032123, 1, -125, 2355779479281832044029, 1, -127, -63691914268230554437, 1, -128, -23558788944937797895, 1, -128, 270193534389469431, 1, -128, 88981328414419453, 1, -128, -229122001117163, 1, -126, -131019917835931, 1, -127, 2491767966325, 1, -128, 617075602253, 1, -128, -5454459107, 1, -128, -593177401, 1, -127, 9681451, 1, -128, 1894429, 1, -128, -3511, 1, -126, -1275, 1, -127, 1, 1, -124, 1, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta92Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta92Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta92Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta92Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta92Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta92Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta92El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta92Shift : polyRoundApx 128 d2Delta92Lo d2Delta92Hi d2Delta92Fq.poly = (d2Delta92S,d2Delta92Es) := by decide +kernel
theorem d2Delta92Sites : mergeSites d2Delta92Fq.plogs = [] := by decide +kernel
theorem d2Delta92PData : d2Delta92Pd = [] := by decide +kernel
theorem d2Delta92Plogs : plogsRoundM 16 24 20 128 d2Delta92Lo d2Delta92Hi (mergeSites d2Delta92Fq.plogs) d2Delta92Pd = some (d2Delta92Ap,d2Delta92Ep) := by
  rw [d2Delta92Sites,d2Delta92PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta92Poles : polesRoundM 16 24 12 128 d2Delta92Lo d2Delta92Hi d2Delta92Fq.poles d2Delta92Qd = some (d2Delta92Aq,d2Delta92Eq) := by decide +kernel
theorem d2Delta92Laurent : laurentRoundM 16 30 128 d2Delta92Lo d2Delta92Hi d2Delta92Ts d2Delta92Ld = some (d2Delta92Al,d2Delta92El) := by decide +kernel
theorem d2Delta92Small : chebPolyUB (vecAdd d2Delta92S (vecAdd d2Delta92Ap (vecAdd d2Delta92Aq d2Delta92Al))) d2Delta92Gam+d2Delta92Es+d2Delta92Ep+d2Delta92Eq+d2Delta92El ≤ (d2LitsStandaloneDelta011.q2 (-7377423456912358417225) 1 (-80)) := by decide +kernel
theorem d2Delta92Check : chebRoundPieceL d2Delta92Fq d2Delta92Ts 16 24 12 20 30 128 d2Delta92Lo d2Delta92Hi d2Delta92Pd d2Delta92Qd d2Delta92Ld d2Delta92Gam (d2LitsStandaloneDelta011.q2 (-7377423456912358417225) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta92Fq d2Delta92Ts 16 24 12 20 30 128 d2Delta92Lo d2Delta92Hi d2Delta92Pd d2Delta92Qd d2Delta92Ld d2Delta92Gam d2Delta92S d2Delta92Ap d2Delta92Aq d2Delta92Al d2Delta92Es d2Delta92Ep d2Delta92Eq d2Delta92El (by decide +kernel) d2Delta92Shift d2Delta92Plogs d2Delta92Poles d2Delta92Laurent]
  exact decide_eq_true d2Delta92Small
theorem d2Delta92Bound : ∀ x ∈ Icc ((d2Delta92Lo : ℚ) : ℝ) ((d2Delta92Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-7377423456912358417225) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta92Fq d2Delta92Ts 16 24 12 20 30 128 d2Delta92Lo d2Delta92Hi d2Delta92Pd d2Delta92Qd d2Delta92Ld d2Delta92Gam (d2LitsStandaloneDelta011.q2 (-7377423456912358417225) 1 (-80)) d2Delta92Check
  simpa only [d2Delta92Fq, d2Delta92Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta92Shift
#print axioms d2Delta92Sites
#print axioms d2Delta92PData
#print axioms d2Delta92Plogs
#print axioms d2Delta92Poles
#print axioms d2Delta92Laurent
#print axioms d2Delta92Small
#print axioms d2Delta92Check
#print axioms d2Delta92Bound

def d2Delta93Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta93Ts : List LTerm := laurentClean []
def d2Delta93Lo : ℚ := (d2LitsStandaloneDelta011.q2 (3159037) 1 (-24))
def d2Delta93Hi : ℚ := (d2LitsStandaloneDelta011.q2 (13683699) 1 (-26))
def d2Delta93Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta93Qd : List (ℚ × ℚ) := []
def d2Delta93Ld : List LaurentPieceData := []
def d2Delta93Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-4459420151959715393430101234134441402158303919, 1, -159, -31447863068212306265551176765740064471487, 1, -159, 741674617920868800874594091830316242143, 1, -160, 848422718436499442908296433646785599535, 1, -158, 169926409021645390971268468909945112019, 1, -160, -21708365443775995352598334525211493713, 1, -159, -1234665587953065919849061099251586117, 1, -159, 253496406571616657147363128572655469, 1, -160, 7205987241825893993816833601848525, 1, -159, -431623287841765863707666309511103, 1, -159, -47094561887066207222546442805255, 1, -160, 1942928624247069897926557633753, 1, -160, 24830742660841930898560410469, 1, -158, -388793196748886316150436571, 1, -157, -18330782142144573108251751, 1, -157, 3712162073738730835739125, 1, -160, 159933800458968976478899, 1, -160, -1705930634783944141945, 1, -159, -133932316943298484979, 1, -160, 2473344181519611337, 1, -160, 88717468943956081, 1, -160, -720479539913831, 1, -159, -5949913814551, 1, -157, 85566390683, 1, -157, 20658769639, 1, -160, -627565891, 1, -160, -126294311, 1, -159, -51244683, 1, -158, -135418245, 1, -160, -113861443, 1, -160, -18130929, 1, -158, -7659457, 1, -157])
def d2Delta93S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-2076579461149836271456946784019262095, 1, -128, -4266369195979685369388485379367, 1, -126, 18399780947958859050493285145, 1, -128, 420765658190667983674044822059, 1, -125, 344650821299400115731581256903, 1, -128, -21054718440440185642810708193, 1, -125, -19269335633782792798427314375, 1, -128, 243402646389279615579772119, 1, -124, 110926586720694210075707173, 1, -126, -52739500227805952226390933, 1, -128, -5757544728041956885103913, 1, -128, 236475315525884186973699, 1, -127, 12086954675649957099395, 1, -126, -3019748368841227412335, 1, -128, -284620952529129329183, 1, -128, 3595868147515457393, 1, -126, 1238706342027665857, 1, -128, -26391052629548619, 1, -127, -1035435841129729, 1, -126, 76408763333309, 1, -127, 2739562032229, 1, -126, -44457718923, 1, -125, -23489758635, 1, -128, 337842041, 1, -127, 41585565, 1, -128, -66339, 1, -124, -3861, 1, -124, 1393, 1, -128, 39, 1, -127, -1, 1, -127, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta93Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta93Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta93Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta93Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta93Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta93Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta93El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta93Shift : polyRoundApx 128 d2Delta93Lo d2Delta93Hi d2Delta93Fq.poly = (d2Delta93S,d2Delta93Es) := by decide +kernel
theorem d2Delta93Sites : mergeSites d2Delta93Fq.plogs = [] := by decide +kernel
theorem d2Delta93PData : d2Delta93Pd = [] := by decide +kernel
theorem d2Delta93Plogs : plogsRoundM 16 24 20 128 d2Delta93Lo d2Delta93Hi (mergeSites d2Delta93Fq.plogs) d2Delta93Pd = some (d2Delta93Ap,d2Delta93Ep) := by
  rw [d2Delta93Sites,d2Delta93PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta93Poles : polesRoundM 16 24 12 128 d2Delta93Lo d2Delta93Hi d2Delta93Fq.poles d2Delta93Qd = some (d2Delta93Aq,d2Delta93Eq) := by decide +kernel
theorem d2Delta93Laurent : laurentRoundM 16 30 128 d2Delta93Lo d2Delta93Hi d2Delta93Ts d2Delta93Ld = some (d2Delta93Al,d2Delta93El) := by decide +kernel
theorem d2Delta93Small : chebPolyUB (vecAdd d2Delta93S (vecAdd d2Delta93Ap (vecAdd d2Delta93Aq d2Delta93Al))) d2Delta93Gam+d2Delta93Es+d2Delta93Ep+d2Delta93Eq+d2Delta93El ≤ (d2LitsStandaloneDelta011.q2 (-7377436160301017893901) 1 (-80)) := by decide +kernel
theorem d2Delta93Check : chebRoundPieceL d2Delta93Fq d2Delta93Ts 16 24 12 20 30 128 d2Delta93Lo d2Delta93Hi d2Delta93Pd d2Delta93Qd d2Delta93Ld d2Delta93Gam (d2LitsStandaloneDelta011.q2 (-7377436160301017893901) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta93Fq d2Delta93Ts 16 24 12 20 30 128 d2Delta93Lo d2Delta93Hi d2Delta93Pd d2Delta93Qd d2Delta93Ld d2Delta93Gam d2Delta93S d2Delta93Ap d2Delta93Aq d2Delta93Al d2Delta93Es d2Delta93Ep d2Delta93Eq d2Delta93El (by decide +kernel) d2Delta93Shift d2Delta93Plogs d2Delta93Poles d2Delta93Laurent]
  exact decide_eq_true d2Delta93Small
theorem d2Delta93Bound : ∀ x ∈ Icc ((d2Delta93Lo : ℚ) : ℝ) ((d2Delta93Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-7377436160301017893901) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta93Fq d2Delta93Ts 16 24 12 20 30 128 d2Delta93Lo d2Delta93Hi d2Delta93Pd d2Delta93Qd d2Delta93Ld d2Delta93Gam (d2LitsStandaloneDelta011.q2 (-7377436160301017893901) 1 (-80)) d2Delta93Check
  simpa only [d2Delta93Fq, d2Delta93Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta93Shift
#print axioms d2Delta93Sites
#print axioms d2Delta93PData
#print axioms d2Delta93Plogs
#print axioms d2Delta93Poles
#print axioms d2Delta93Laurent
#print axioms d2Delta93Small
#print axioms d2Delta93Check
#print axioms d2Delta93Bound

def d2Delta94Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta94Ts : List LTerm := laurentClean []
def d2Delta94Lo : ℚ := (d2LitsStandaloneDelta011.q2 (13683699) 1 (-26))
def d2Delta94Hi : ℚ := (d2LitsStandaloneDelta011.q2 (28414949) 1 (-27))
def d2Delta94Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta94Qd : List (ℚ × ℚ) := []
def d2Delta94Ld : List LaurentPieceData := []
def d2Delta94Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-8918893372640960280071082199425641183356298055, 1, -160, 12440157253767924838171249570991453999477, 1, -160, 7056600629229401626888296218907255185019, 1, -160, 151193801383461899551905887436084863933, 1, -160, -33599658039816965975176735104809689761, 1, -160, -478345336501492353823686449013384199, 1, -159, 1986595300420046370475175232009707, 1, -155, 941158463226777619958636051814231, 1, -159, -8203780020331904591508292231155, 1, -157, -958533401763591861805339319505, 1, -159, 21542062222155305162233564653, 1, -159, 75700490755648812650033819, 1, -156, -19623438885245396180869007, 1, -160, -65347866551355629430509, 1, -157, 6553154822880296583473, 1, -160, 163861692724783961067, 1, -160, -1665808340881068707, 1, -160, -19465497350374561, 1, -159, 331118246544209, 1, -160, 452412371481, 1, -156, -13418727083, 1, -158, -1827187005, 1, -160, -350911583, 1, -159, -221956721, 1, -159, -422471217, 1, -160, -256423583, 1, -160, -122146615, 1, -159, -143629815, 1, -160, -8557189, 1, -156, -19493325, 1, -158, -74324649, 1, -160, -2562219, 1, -156])
def d2Delta94S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-519148333865734997219815480057578009, 1, -126, 1394862681949407295828715342031, 1, -127, 3348836885763724773538460347837, 1, -128, 145289734717565874326428968507, 1, -128, -15824287710044922428093677227, 1, -126, -3613228893466546760764355555, 1, -128, 477564347377800786257607791, 1, -128, 1769162623638949158368281, 1, -124, -1968805266918560346265731, 1, -128, -115062243693421499482757, 1, -128, 5164159642534949067105, 1, -128, 72599577604776029557, 1, -126, -2350253638952259047, 1, -126, -500913138778260527, 1, -128, 12550072669116365, 1, -128, 627611622186443, 1, -128, -12754649624475, 1, -128, -298070935971, 1, -127, 5068541155, 1, -127, 443270427, 1, -128, -6429481, 1, -128, -264591, 1, -128, 1653, 1, -127, 129, 1, -128, -1, 1, -127, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta94Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta94Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta94Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta94Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta94Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta94Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta94El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta94Shift : polyRoundApx 128 d2Delta94Lo d2Delta94Hi d2Delta94Fq.poly = (d2Delta94S,d2Delta94Es) := by decide +kernel
theorem d2Delta94Sites : mergeSites d2Delta94Fq.plogs = [] := by decide +kernel
theorem d2Delta94PData : d2Delta94Pd = [] := by decide +kernel
theorem d2Delta94Plogs : plogsRoundM 16 24 20 128 d2Delta94Lo d2Delta94Hi (mergeSites d2Delta94Fq.plogs) d2Delta94Pd = some (d2Delta94Ap,d2Delta94Ep) := by
  rw [d2Delta94Sites,d2Delta94PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta94Poles : polesRoundM 16 24 12 128 d2Delta94Lo d2Delta94Hi d2Delta94Fq.poles d2Delta94Qd = some (d2Delta94Aq,d2Delta94Eq) := by decide +kernel
theorem d2Delta94Laurent : laurentRoundM 16 30 128 d2Delta94Lo d2Delta94Hi d2Delta94Ts d2Delta94Ld = some (d2Delta94Al,d2Delta94El) := by decide +kernel
theorem d2Delta94Small : chebPolyUB (vecAdd d2Delta94S (vecAdd d2Delta94Ap (vecAdd d2Delta94Aq d2Delta94Al))) d2Delta94Gam+d2Delta94Es+d2Delta94Ep+d2Delta94Eq+d2Delta94El ≤ (d2LitsStandaloneDelta011.q2 (-7377519402233039384467) 1 (-80)) := by decide +kernel
theorem d2Delta94Check : chebRoundPieceL d2Delta94Fq d2Delta94Ts 16 24 12 20 30 128 d2Delta94Lo d2Delta94Hi d2Delta94Pd d2Delta94Qd d2Delta94Ld d2Delta94Gam (d2LitsStandaloneDelta011.q2 (-7377519402233039384467) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta94Fq d2Delta94Ts 16 24 12 20 30 128 d2Delta94Lo d2Delta94Hi d2Delta94Pd d2Delta94Qd d2Delta94Ld d2Delta94Gam d2Delta94S d2Delta94Ap d2Delta94Aq d2Delta94Al d2Delta94Es d2Delta94Ep d2Delta94Eq d2Delta94El (by decide +kernel) d2Delta94Shift d2Delta94Plogs d2Delta94Poles d2Delta94Laurent]
  exact decide_eq_true d2Delta94Small
theorem d2Delta94Bound : ∀ x ∈ Icc ((d2Delta94Lo : ℚ) : ℝ) ((d2Delta94Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-7377519402233039384467) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta94Fq d2Delta94Ts 16 24 12 20 30 128 d2Delta94Lo d2Delta94Hi d2Delta94Pd d2Delta94Qd d2Delta94Ld d2Delta94Gam (d2LitsStandaloneDelta011.q2 (-7377519402233039384467) 1 (-80)) d2Delta94Check
  simpa only [d2Delta94Fq, d2Delta94Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta94Shift
#print axioms d2Delta94Sites
#print axioms d2Delta94PData
#print axioms d2Delta94Plogs
#print axioms d2Delta94Poles
#print axioms d2Delta94Laurent
#print axioms d2Delta94Small
#print axioms d2Delta94Check
#print axioms d2Delta94Bound

def d2Delta95Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta95Ts : List LTerm := laurentClean []
def d2Delta95Lo : ℚ := (d2LitsStandaloneDelta011.q2 (28414949) 1 (-27))
def d2Delta95Hi : ℚ := (d2LitsStandaloneDelta011.q2 (7365625) 1 (-25))
def d2Delta95Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta95Qd : List (ℚ × ℚ) := []
def d2Delta95Ld : List LaurentPieceData := []
def d2Delta95Gam : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-8918813322180996449000686575522259169259742851, 1, -160, 33082378646111667480811133271829281177815, 1, -159, 5319639825765309417066593638390397437511, 1, -160, -55450796553643928500108209921707813743, 1, -157, -135366549820551212114028180779425343, 1, -152, 914499244658648711426573204340015569, 1, -160, 19844198129943577308488104275962005, 1, -158, -905296844224189014160940948485267, 1, -160, -93914722181063394011071168978923, 1, -160, 257496316959855197118526238055, 1, -159, 34101279774171739353481958549, 1, -159, -90893419778403020514228317, 1, -159, -33486723932999267240366785, 1, -160, 39488614577449569539565, 1, -160, 2956841919502222793491, 1, -158, -3992630537746639533, 1, -160, -3138599403843532983, 1, -160, -546600195360105, 1, -160, 323193320059007, 1, -159, 332033003191, 1, -160, -107227681219, 1, -160, -466899133, 1, -159, -770477357, 1, -160, -253777119, 1, -159, -469880357, 1, -160, -293365151, 1, -160, -273106173, 1, -160, -82184457, 1, -159, -153917677, 1, -160, -89221199, 1, -160, -42016757, 1, -159, -11722363, 1, -158])
def d2Delta95S : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [-2076574293094251710886421478055062985, 1, -128, 15716104592999658997270624073073, 1, -128, 2542031495019819966787883144787, 1, -128, -208705457983559322540609249775, 1, -127, -32719205335965175250170226029, 1, -127, 3430434470527279933009886985, 1, -128, 597018757021423019737160869, 1, -128, -13559159378892583413100631, 1, -128, -2819256739183039994981263, 1, -128, 15407647401459342733375, 1, -127, 8178390508707760875117, 1, -128, -43463838253232900305, 1, -128, -16046826290129895699, 1, -128, 37716330307333289, 1, -128, 1415928914035551, 1, -124, -7597518177653, 1, -127, -12017259310223, 1, -127, -4218662309, 1, -127, 19790975975, 1, -128, 20455679, 1, -128, -3242979, 1, -126, -10051, 1, -127, 3453, 1, -127, 13, 1, -128, -1, 1, -126, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta95Ap : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta95Aq : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta95Al : List ℚ := d2LitsStandaloneDelta011.q2listC (raw_ints% [])
def d2Delta95Es : ℚ := (d2LitsStandaloneDelta011.q2 (61) 1 (-127))
def d2Delta95Ep : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta95Eq : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
def d2Delta95El : ℚ := (d2LitsStandaloneDelta011.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta95Shift : polyRoundApx 128 d2Delta95Lo d2Delta95Hi d2Delta95Fq.poly = (d2Delta95S,d2Delta95Es) := by decide +kernel
theorem d2Delta95Sites : mergeSites d2Delta95Fq.plogs = [] := by decide +kernel
theorem d2Delta95PData : d2Delta95Pd = [] := by decide +kernel
theorem d2Delta95Plogs : plogsRoundM 16 24 20 128 d2Delta95Lo d2Delta95Hi (mergeSites d2Delta95Fq.plogs) d2Delta95Pd = some (d2Delta95Ap,d2Delta95Ep) := by
  rw [d2Delta95Sites,d2Delta95PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta95Poles : polesRoundM 16 24 12 128 d2Delta95Lo d2Delta95Hi d2Delta95Fq.poles d2Delta95Qd = some (d2Delta95Aq,d2Delta95Eq) := by decide +kernel
theorem d2Delta95Laurent : laurentRoundM 16 30 128 d2Delta95Lo d2Delta95Hi d2Delta95Ts d2Delta95Ld = some (d2Delta95Al,d2Delta95El) := by decide +kernel
theorem d2Delta95Small : chebPolyUB (vecAdd d2Delta95S (vecAdd d2Delta95Ap (vecAdd d2Delta95Aq d2Delta95Al))) d2Delta95Gam+d2Delta95Es+d2Delta95Ep+d2Delta95Eq+d2Delta95El ≤ (d2LitsStandaloneDelta011.q2 (-7377409940149869577733) 1 (-80)) := by decide +kernel
theorem d2Delta95Check : chebRoundPieceL d2Delta95Fq d2Delta95Ts 16 24 12 20 30 128 d2Delta95Lo d2Delta95Hi d2Delta95Pd d2Delta95Qd d2Delta95Ld d2Delta95Gam (d2LitsStandaloneDelta011.q2 (-7377409940149869577733) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta95Fq d2Delta95Ts 16 24 12 20 30 128 d2Delta95Lo d2Delta95Hi d2Delta95Pd d2Delta95Qd d2Delta95Ld d2Delta95Gam d2Delta95S d2Delta95Ap d2Delta95Aq d2Delta95Al d2Delta95Es d2Delta95Ep d2Delta95Eq d2Delta95El (by decide +kernel) d2Delta95Shift d2Delta95Plogs d2Delta95Poles d2Delta95Laurent]
  exact decide_eq_true d2Delta95Small
theorem d2Delta95Bound : ∀ x ∈ Icc ((d2Delta95Lo : ℚ) : ℝ) ((d2Delta95Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta011.q2 (-7377409940149869577733) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta95Fq d2Delta95Ts 16 24 12 20 30 128 d2Delta95Lo d2Delta95Hi d2Delta95Pd d2Delta95Qd d2Delta95Ld d2Delta95Gam (d2LitsStandaloneDelta011.q2 (-7377409940149869577733) 1 (-80)) d2Delta95Check
  simpa only [d2Delta95Fq, d2Delta95Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta95Shift
#print axioms d2Delta95Sites
#print axioms d2Delta95PData
#print axioms d2Delta95Plogs
#print axioms d2Delta95Poles
#print axioms d2Delta95Laurent
#print axioms d2Delta95Small
#print axioms d2Delta95Check
#print axioms d2Delta95Bound

end StandaloneDelta011
end CatalanMeasure.GenD.Signed.Data.Cells
