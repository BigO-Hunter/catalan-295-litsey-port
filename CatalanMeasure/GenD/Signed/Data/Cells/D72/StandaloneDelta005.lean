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
namespace d2LitsStandaloneDelta005
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta005
namespace StandaloneDelta005
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta005.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta005.q2listC (raw_ints% []))⟩
def d2Delta40Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta40Ts : List LTerm := laurentClean []
def d2Delta40Lo : ℚ := (d2LitsStandaloneDelta005.q2 (5368827) 1 (-27))
def d2Delta40Hi : ℚ := (d2LitsStandaloneDelta005.q2 (22522859) 1 (-29))
def d2Delta40Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta40Qd : List (ℚ × ℚ) := []
def d2Delta40Ld : List LaurentPieceData := []
def d2Delta40Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918807324172301572112100445180113295491320417, 1, -160, -53132252302908993557837963923874564717, 1, -154, 504509033893922661019319786325524252713, 1, -160, 303815666268657041985759918341889361, 1, -157, -89843872272387663187071152210914905, 1, -158, 485127422800828962031790410723653, 1, -158, 17181873339527813275497079065253, 1, -158, -105219216022294293008482042327, 1, -157, -69331332412453972533531827, 1, -160, 43025191157755881329453681, 1, -160, -120550989170377870963651, 1, -160, -137916813764814233127, 1, -157, 5065657275978213217, 1, -160, 548461671201233, 1, -155, -116354100253963, 1, -160, -92362469881, 1, -159, -151330445, 1, -157, -2403913833, 1, -160, -995868529, 1, -159, -1546484501, 1, -160, -1269602613, 1, -160, -967171661, 1, -160, -393424609, 1, -159, -73484153, 1, -157, -236868427, 1, -159, -347044705, 1, -160, -276863299, 1, -160, -99422715, 1, -159, -156951801, 1, -160, -1726659, 1, -154, -43125013, 1, -159, -7440875, 1, -157])
def d2Delta40S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-1038285883730368186101187137521197575, 1, -127, -793427698066342622978668498771, 1, -128, 235600003227045468051494789995, 1, -128, 2254555929312695600052129139, 1, -128, -20942409489670412564920121, 1, -123, 1812729173401077780438003, 1, -126, 512063829518247723185515, 1, -128, -12548878840330699010891, 1, -128, -126893723291945453, 1, -124, 2565224705828281355, 1, -128, -14378045322575657, 1, -128, -263109847672915, 1, -128, 1208135215511, 1, -127, 16740317579, 1, -128, -221975059, 1, -128, -690855, 1, -128, 6981, 1, -127, 1, 1, -124, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta40Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta40Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta40Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta40Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta40Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta40Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta40El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta40Shift : polyRoundApx 128 d2Delta40Lo d2Delta40Hi d2Delta40Fq.poly = (d2Delta40S,d2Delta40Es) := by decide +kernel
theorem d2Delta40Sites : mergeSites d2Delta40Fq.plogs = [] := by decide +kernel
theorem d2Delta40PData : d2Delta40Pd = [] := by decide +kernel
theorem d2Delta40Plogs : plogsRoundM 16 24 20 128 d2Delta40Lo d2Delta40Hi (mergeSites d2Delta40Fq.plogs) d2Delta40Pd = some (d2Delta40Ap,d2Delta40Ep) := by
  rw [d2Delta40Sites,d2Delta40PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta40Poles : polesRoundM 16 24 12 128 d2Delta40Lo d2Delta40Hi d2Delta40Fq.poles d2Delta40Qd = some (d2Delta40Aq,d2Delta40Eq) := by decide +kernel
theorem d2Delta40Laurent : laurentRoundM 16 30 128 d2Delta40Lo d2Delta40Hi d2Delta40Ts d2Delta40Ld = some (d2Delta40Al,d2Delta40El) := by decide +kernel
theorem d2Delta40Small : chebPolyUB (vecAdd d2Delta40S (vecAdd d2Delta40Ap (vecAdd d2Delta40Aq d2Delta40Al))) d2Delta40Gam+d2Delta40Es+d2Delta40Ep+d2Delta40Eq+d2Delta40El ≤ (d2LitsStandaloneDelta005.q2 (-7377461273223751423523) 1 (-80)) := by decide +kernel
theorem d2Delta40Check : chebRoundPieceL d2Delta40Fq d2Delta40Ts 16 24 12 20 30 128 d2Delta40Lo d2Delta40Hi d2Delta40Pd d2Delta40Qd d2Delta40Ld d2Delta40Gam (d2LitsStandaloneDelta005.q2 (-7377461273223751423523) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta40Fq d2Delta40Ts 16 24 12 20 30 128 d2Delta40Lo d2Delta40Hi d2Delta40Pd d2Delta40Qd d2Delta40Ld d2Delta40Gam d2Delta40S d2Delta40Ap d2Delta40Aq d2Delta40Al d2Delta40Es d2Delta40Ep d2Delta40Eq d2Delta40El (by decide +kernel) d2Delta40Shift d2Delta40Plogs d2Delta40Poles d2Delta40Laurent]
  exact decide_eq_true d2Delta40Small
theorem d2Delta40Bound : ∀ x ∈ Icc ((d2Delta40Lo : ℚ) : ℝ) ((d2Delta40Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-7377461273223751423523) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta40Fq d2Delta40Ts 16 24 12 20 30 128 d2Delta40Lo d2Delta40Hi d2Delta40Pd d2Delta40Qd d2Delta40Ld d2Delta40Gam (d2LitsStandaloneDelta005.q2 (-7377461273223751423523) 1 (-80)) d2Delta40Check
  simpa only [d2Delta40Fq, d2Delta40Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta40Shift
#print axioms d2Delta40Sites
#print axioms d2Delta40PData
#print axioms d2Delta40Plogs
#print axioms d2Delta40Poles
#print axioms d2Delta40Laurent
#print axioms d2Delta40Small
#print axioms d2Delta40Check
#print axioms d2Delta40Bound

def d2Delta41Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta41Ts : List LTerm := laurentClean []
def d2Delta41Lo : ℚ := (d2LitsStandaloneDelta005.q2 (22522859) 1 (-29))
def d2Delta41Hi : ℚ := (d2LitsStandaloneDelta005.q2 (48188371) 1 (-30))
def d2Delta41Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta41Qd : List (ℚ × ℚ) := []
def d2Delta41Ld : List LaurentPieceData := []
def d2Delta41Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918808880584228069990639787724682365994269289, 1, -160, 38272062628305971905239647900168661395, 1, -154, 274902229588894771875728276026073117289, 1, -158, -1727510249519523856330427105258472111, 1, -157, -182560206901211911332542501111839835, 1, -157, 6751238877462295282652249463320901, 1, -158, 451874483719572101035944374578859, 1, -160, -1724472619562306500444062400983, 1, -157, 43770606701560975181778635233, 1, -160, 1369226489751240862102514289, 1, -160, -9931837486752406313428367, 1, -160, -8330318076816780566055, 1, -157, 769574774505495644537, 1, -160, 55099141119524305, 1, -155, -36302788184746319, 1, -160, -7282813809145, 1, -159, 602510248885, 1, -159, -3221311593, 1, -160, -244818597, 1, -157, -1546451733, 1, -160, -1220171871, 1, -160, -967171661, 1, -160, -751482793, 1, -160, -73484153, 1, -157, -450220399, 1, -160, -347044705, 1, -160, -16389079, 1, -156, -99422715, 1, -159, -148377867, 1, -160, -1726659, 1, -154, -20376579, 1, -158, -7440875, 1, -157])
def d2Delta41S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-129785766790942287647086819120746169, 1, -124, 289991425299131135384174782641, 1, -127, 257383778492499448812065780755, 1, -127, -101538170971029379343717843, 1, -121, -1362703765000408520216454509, 1, -127, 12620148691717391096222493, 1, -125, 3364115738611255052126467, 1, -128, -25719603388483147464405, 1, -125, 653713444487612019829, 1, -127, 40827979813582251233, 1, -127, -1185068509553210663, 1, -128, -15894285957221991, 1, -128, 367204255643643, 1, -128, 1681700567093, 1, -128, -69278937593, 1, -128, -27748309, 1, -127, 9220379, 1, -128, -6233, 1, -127, -927, 1, -128, 1, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta41Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta41Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta41Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta41Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta41Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta41Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta41El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta41Shift : polyRoundApx 128 d2Delta41Lo d2Delta41Hi d2Delta41Fq.poly = (d2Delta41S,d2Delta41Es) := by decide +kernel
theorem d2Delta41Sites : mergeSites d2Delta41Fq.plogs = [] := by decide +kernel
theorem d2Delta41PData : d2Delta41Pd = [] := by decide +kernel
theorem d2Delta41Plogs : plogsRoundM 16 24 20 128 d2Delta41Lo d2Delta41Hi (mergeSites d2Delta41Fq.plogs) d2Delta41Pd = some (d2Delta41Ap,d2Delta41Ep) := by
  rw [d2Delta41Sites,d2Delta41PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta41Poles : polesRoundM 16 24 12 128 d2Delta41Lo d2Delta41Hi d2Delta41Fq.poles d2Delta41Qd = some (d2Delta41Aq,d2Delta41Eq) := by decide +kernel
theorem d2Delta41Laurent : laurentRoundM 16 30 128 d2Delta41Lo d2Delta41Hi d2Delta41Ts d2Delta41Ld = some (d2Delta41Al,d2Delta41El) := by decide +kernel
theorem d2Delta41Small : chebPolyUB (vecAdd d2Delta41S (vecAdd d2Delta41Ap (vecAdd d2Delta41Aq d2Delta41Al))) d2Delta41Gam+d2Delta41Es+d2Delta41Ep+d2Delta41Eq+d2Delta41El ≤ (d2LitsStandaloneDelta005.q2 (-7377462844741231621301) 1 (-80)) := by decide +kernel
theorem d2Delta41Check : chebRoundPieceL d2Delta41Fq d2Delta41Ts 16 24 12 20 30 128 d2Delta41Lo d2Delta41Hi d2Delta41Pd d2Delta41Qd d2Delta41Ld d2Delta41Gam (d2LitsStandaloneDelta005.q2 (-7377462844741231621301) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta41Fq d2Delta41Ts 16 24 12 20 30 128 d2Delta41Lo d2Delta41Hi d2Delta41Pd d2Delta41Qd d2Delta41Ld d2Delta41Gam d2Delta41S d2Delta41Ap d2Delta41Aq d2Delta41Al d2Delta41Es d2Delta41Ep d2Delta41Eq d2Delta41El (by decide +kernel) d2Delta41Shift d2Delta41Plogs d2Delta41Poles d2Delta41Laurent]
  exact decide_eq_true d2Delta41Small
theorem d2Delta41Bound : ∀ x ∈ Icc ((d2Delta41Lo : ℚ) : ℝ) ((d2Delta41Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-7377462844741231621301) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta41Fq d2Delta41Ts 16 24 12 20 30 128 d2Delta41Lo d2Delta41Hi d2Delta41Pd d2Delta41Qd d2Delta41Ld d2Delta41Gam (d2LitsStandaloneDelta005.q2 (-7377462844741231621301) 1 (-80)) d2Delta41Check
  simpa only [d2Delta41Fq, d2Delta41Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta41Shift
#print axioms d2Delta41Sites
#print axioms d2Delta41PData
#print axioms d2Delta41Plogs
#print axioms d2Delta41Poles
#print axioms d2Delta41Laurent
#print axioms d2Delta41Small
#print axioms d2Delta41Check
#print axioms d2Delta41Bound

def d2Delta42Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta42Ts : List LTerm := laurentClean []
def d2Delta42Lo : ℚ := (d2LitsStandaloneDelta005.q2 (48188371) 1 (-30))
def d2Delta42Hi : ℚ := (d2LitsStandaloneDelta005.q2 (97424293) 1 (-31))
def d2Delta42Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta42Qd : List (ℚ × ℚ) := []
def d2Delta42Ld : List LaurentPieceData := []
def d2Delta42Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918804148777825587130762483909398910821182943, 1, -160, 19139395343763696469591750913754672531, 1, -154, 13381527959180525922259934045014181127, 1, -159, -15064362634039433978152281558049455, 1, -157, -215302956226569732812684318599763, 1, -158, 1024879218533174561200223777093, 1, -158, 2508711270531683875698151181, 1, -159, -5687091351725344966836695, 1, -157, 10429779543929284230259, 1, -158, 111157314195922545265, 1, -160, -47009105337142219, 1, -158, -15340896804391, 1, -157, 363595811413, 1, -160, -166323759, 1, -155, -276681927, 1, -156, -1820193273, 1, -159, -1475640605, 1, -159, -2405027945, 1, -160, -958534889, 1, -159, -1546484501, 1, -160, -1212819507, 1, -160, -967171661, 1, -160, -186714541, 1, -158, -73484153, 1, -157, -447369117, 1, -160, -347044705, 1, -160, -260469725, 1, -160, -99422715, 1, -159, -147294699, 1, -160, -1726659, 1, -154, -5052683, 1, -156, -7440875, 1, -157])
def d2Delta42S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-2076570916814204007930611592977697259, 1, -128, 71320849657174919804613614355, 1, -126, 12464123224288603439565489809, 1, -128, -3508041825076905703051497, 1, -123, -1604188100634391505426289, 1, -128, 15273076870477392513393, 1, -128, 18690112164380572949, 1, -127, -677969027087543441, 1, -128, 621691324708385, 1, -127, 6625572688801, 1, -128, -11208108243, 1, -127, -29258739, 1, -128, 88231, 1, -127, 21, 1, -127, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta42Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta42Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta42Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta42Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta42Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta42Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta42El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta42Shift : polyRoundApx 128 d2Delta42Lo d2Delta42Hi d2Delta42Fq.poly = (d2Delta42S,d2Delta42Es) := by decide +kernel
theorem d2Delta42Sites : mergeSites d2Delta42Fq.plogs = [] := by decide +kernel
theorem d2Delta42PData : d2Delta42Pd = [] := by decide +kernel
theorem d2Delta42Plogs : plogsRoundM 16 24 20 128 d2Delta42Lo d2Delta42Hi (mergeSites d2Delta42Fq.plogs) d2Delta42Pd = some (d2Delta42Ap,d2Delta42Ep) := by
  rw [d2Delta42Sites,d2Delta42PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta42Poles : polesRoundM 16 24 12 128 d2Delta42Lo d2Delta42Hi d2Delta42Fq.poles d2Delta42Qd = some (d2Delta42Aq,d2Delta42Eq) := by decide +kernel
theorem d2Delta42Laurent : laurentRoundM 16 30 128 d2Delta42Lo d2Delta42Hi d2Delta42Ts d2Delta42Ld = some (d2Delta42Al,d2Delta42El) := by decide +kernel
theorem d2Delta42Small : chebPolyUB (vecAdd d2Delta42S (vecAdd d2Delta42Ap (vecAdd d2Delta42Aq d2Delta42Al))) d2Delta42Gam+d2Delta42Es+d2Delta42Ep+d2Delta42Eq+d2Delta42El ≤ (d2LitsStandaloneDelta005.q2 (-7377460843557089072901) 1 (-80)) := by decide +kernel
theorem d2Delta42Check : chebRoundPieceL d2Delta42Fq d2Delta42Ts 16 24 12 20 30 128 d2Delta42Lo d2Delta42Hi d2Delta42Pd d2Delta42Qd d2Delta42Ld d2Delta42Gam (d2LitsStandaloneDelta005.q2 (-7377460843557089072901) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta42Fq d2Delta42Ts 16 24 12 20 30 128 d2Delta42Lo d2Delta42Hi d2Delta42Pd d2Delta42Qd d2Delta42Ld d2Delta42Gam d2Delta42S d2Delta42Ap d2Delta42Aq d2Delta42Al d2Delta42Es d2Delta42Ep d2Delta42Eq d2Delta42El (by decide +kernel) d2Delta42Shift d2Delta42Plogs d2Delta42Poles d2Delta42Laurent]
  exact decide_eq_true d2Delta42Small
theorem d2Delta42Bound : ∀ x ∈ Icc ((d2Delta42Lo : ℚ) : ℝ) ((d2Delta42Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-7377460843557089072901) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta42Fq d2Delta42Ts 16 24 12 20 30 128 d2Delta42Lo d2Delta42Hi d2Delta42Pd d2Delta42Qd d2Delta42Ld d2Delta42Gam (d2LitsStandaloneDelta005.q2 (-7377460843557089072901) 1 (-80)) d2Delta42Check
  simpa only [d2Delta42Fq, d2Delta42Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta42Shift
#print axioms d2Delta42Sites
#print axioms d2Delta42PData
#print axioms d2Delta42Plogs
#print axioms d2Delta42Poles
#print axioms d2Delta42Laurent
#print axioms d2Delta42Small
#print axioms d2Delta42Check
#print axioms d2Delta42Bound

def d2Delta43Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta43Ts : List LTerm := laurentClean []
def d2Delta43Lo : ℚ := (d2LitsStandaloneDelta005.q2 (97424293) 1 (-31))
def d2Delta43Hi : ℚ := (d2LitsStandaloneDelta005.q2 (99519395) 1 (-31))
def d2Delta43Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta43Qd : List (ℚ × ℚ) := []
def d2Delta43Ld : List LaurentPieceData := []
def d2Delta43Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918799933812178984652739013514522538619653667, 1, -160, 47845934085897019901868401129272012179, 1, -154, 12204003941189546535443563373885535353, 1, -157, -139624719242291641611737116993872559, 1, -157, -11772833356174712511934654695125807, 1, -160, 33962902346311244867581073912133, 1, -158, 201710158724621144557787046831, 1, -160, -693638376817005782143730135, 1, -157, 758511909069036108787331, 1, -156, 51019071114242185947761, 1, -160, -49981722519648502459, 1, -158, -24572624934952487, 1, -157, 1523661109328363, 1, -160, 1325504977, 1, -155, -11833207223, 1, -160, -1818620409, 1, -159, -2945087231, 1, -160, -2405027945, 1, -160, -956766421, 1, -159, -1546484501, 1, -160, -151385173, 1, -157, -967171661, 1, -160, -746120493, 1, -160, -73484153, 1, -157, -447099053, 1, -160, -347044705, 1, -160, -130192425, 1, -159, -99422715, 1, -159, -73635997, 1, -159, -1726659, 1, -154, -80837823, 1, -160, -7440875, 1, -157])
def d2Delta43S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-2076569951944049342820259822467945147, 1, -128, 713740348363322067917024590601, 1, -128, 45485386940715050142369125571, 1, -128, -1040917904744193092213275385, 1, -128, -10965432389074240654912083, 1, -127, 253115695923337319165343, 1, -127, 751067184666724884787, 1, -127, -82694980425024712233, 1, -128, 45218281061518529, 1, -125, 760275624815635, 1, -126, -23835322219279, 1, -128, -23434354385, 1, -127, 363295409, 1, -127, 11381, 1, -126, -14145, 1, -128, 3, 1, -126, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta43Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta43Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta43Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta43Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta43Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta43Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta43El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta43Shift : polyRoundApx 128 d2Delta43Lo d2Delta43Hi d2Delta43Fq.poly = (d2Delta43S,d2Delta43Es) := by decide +kernel
theorem d2Delta43Sites : mergeSites d2Delta43Fq.plogs = [] := by decide +kernel
theorem d2Delta43PData : d2Delta43Pd = [] := by decide +kernel
theorem d2Delta43Plogs : plogsRoundM 16 24 20 128 d2Delta43Lo d2Delta43Hi (mergeSites d2Delta43Fq.plogs) d2Delta43Pd = some (d2Delta43Ap,d2Delta43Ep) := by
  rw [d2Delta43Sites,d2Delta43PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta43Poles : polesRoundM 16 24 12 128 d2Delta43Lo d2Delta43Hi d2Delta43Fq.poles d2Delta43Qd = some (d2Delta43Aq,d2Delta43Eq) := by decide +kernel
theorem d2Delta43Laurent : laurentRoundM 16 30 128 d2Delta43Lo d2Delta43Hi d2Delta43Ts d2Delta43Ld = some (d2Delta43Al,d2Delta43El) := by decide +kernel
theorem d2Delta43Small : chebPolyUB (vecAdd d2Delta43S (vecAdd d2Delta43Ap (vecAdd d2Delta43Aq d2Delta43Al))) d2Delta43Gam+d2Delta43Es+d2Delta43Ep+d2Delta43Eq+d2Delta43El ≤ (d2LitsStandaloneDelta005.q2 (-1844363944463216844279) 1 (-78)) := by decide +kernel
theorem d2Delta43Check : chebRoundPieceL d2Delta43Fq d2Delta43Ts 16 24 12 20 30 128 d2Delta43Lo d2Delta43Hi d2Delta43Pd d2Delta43Qd d2Delta43Ld d2Delta43Gam (d2LitsStandaloneDelta005.q2 (-1844363944463216844279) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta43Fq d2Delta43Ts 16 24 12 20 30 128 d2Delta43Lo d2Delta43Hi d2Delta43Pd d2Delta43Qd d2Delta43Ld d2Delta43Gam d2Delta43S d2Delta43Ap d2Delta43Aq d2Delta43Al d2Delta43Es d2Delta43Ep d2Delta43Eq d2Delta43El (by decide +kernel) d2Delta43Shift d2Delta43Plogs d2Delta43Poles d2Delta43Laurent]
  exact decide_eq_true d2Delta43Small
theorem d2Delta43Bound : ∀ x ∈ Icc ((d2Delta43Lo : ℚ) : ℝ) ((d2Delta43Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-1844363944463216844279) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta43Fq d2Delta43Ts 16 24 12 20 30 128 d2Delta43Lo d2Delta43Hi d2Delta43Pd d2Delta43Qd d2Delta43Ld d2Delta43Gam (d2LitsStandaloneDelta005.q2 (-1844363944463216844279) 1 (-78)) d2Delta43Check
  simpa only [d2Delta43Fq, d2Delta43Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta43Shift
#print axioms d2Delta43Sites
#print axioms d2Delta43PData
#print axioms d2Delta43Plogs
#print axioms d2Delta43Poles
#print axioms d2Delta43Laurent
#print axioms d2Delta43Small
#print axioms d2Delta43Check
#print axioms d2Delta43Bound

def d2Delta44Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta44Ts : List LTerm := laurentClean []
def d2Delta44Lo : ℚ := (d2LitsStandaloneDelta005.q2 (99519395) 1 (-31))
def d2Delta44Hi : ℚ := (d2LitsStandaloneDelta005.q2 (3208189) 1 (-26))
def d2Delta44Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta44Qd : List (ℚ × ℚ) := []
def d2Delta44Ld : List LaurentPieceData := []
def d2Delta44Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918791041716913020595548447189050857858808069, 1, -160, 92439911092293171278288741639110565267, 1, -154, 89149875049035015461309394433943835655, 1, -159, -555708945074953752986363878955737775, 1, -157, -42143706628325920000646141963082911, 1, -160, 263949399876498609148447121371461, 1, -158, 185095992522026127702555611, 1, -150, -10722129209593820239764095447, 1, -157, 90988632437263662903176101, 1, -158, 1568217854071485247711857, 1, -160, -12006153286682013908333, 1, -160, -1139712967294836263, 1, -157, 195916721624117103, 1, -160, -2801943316015, 1, -155, -2074320518429, 1, -160, -654569977, 1, -159, -3120852371, 1, -160, -2405027945, 1, -160, -2052765521, 1, -160, -1546484501, 1, -160, -1308418539, 1, -160, -967171661, 1, -160, -811401537, 1, -160, -73484153, 1, -157, -489079371, 1, -160, -347044705, 1, -160, -71568153, 1, -158, -99422715, 1, -159, -81292059, 1, -159, -1726659, 1, -154, -89525617, 1, -160, -7440875, 1, -157])
def d2Delta44S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-2076567900380773240343722304390971667, 1, -128, 690284255446984052151973512867, 1, -127, 41552895359835687337616463507, 1, -127, -4145271842854729395051894397, 1, -128, -2453152356809764874172733, 1, -123, 3935389522777184088998893, 1, -128, 1390473841631814851335, 1, -128, -1278387725928458303265, 1, -128, 10850268657858948697, 1, -128, 46739522903686727, 1, -127, -1431525283668257, 1, -128, -2173552032039, 1, -128, 93434193193, 1, -128, -85536755, 1, -128, -987005, 1, -126, 8893, 1, -128, 119, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta44Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta44Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta44Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta44Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta44Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta44Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta44El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta44Shift : polyRoundApx 128 d2Delta44Lo d2Delta44Hi d2Delta44Fq.poly = (d2Delta44S,d2Delta44Es) := by decide +kernel
theorem d2Delta44Sites : mergeSites d2Delta44Fq.plogs = [] := by decide +kernel
theorem d2Delta44PData : d2Delta44Pd = [] := by decide +kernel
theorem d2Delta44Plogs : plogsRoundM 16 24 20 128 d2Delta44Lo d2Delta44Hi (mergeSites d2Delta44Fq.plogs) d2Delta44Pd = some (d2Delta44Ap,d2Delta44Ep) := by
  rw [d2Delta44Sites,d2Delta44PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta44Poles : polesRoundM 16 24 12 128 d2Delta44Lo d2Delta44Hi d2Delta44Fq.poles d2Delta44Qd = some (d2Delta44Aq,d2Delta44Eq) := by decide +kernel
theorem d2Delta44Laurent : laurentRoundM 16 30 128 d2Delta44Lo d2Delta44Hi d2Delta44Ts d2Delta44Ld = some (d2Delta44Al,d2Delta44El) := by decide +kernel
theorem d2Delta44Small : chebPolyUB (vecAdd d2Delta44S (vecAdd d2Delta44Ap (vecAdd d2Delta44Aq d2Delta44Al))) d2Delta44Gam+d2Delta44Es+d2Delta44Ep+d2Delta44Eq+d2Delta44El ≤ (d2LitsStandaloneDelta005.q2 (-3688722996096251019697) 1 (-79)) := by decide +kernel
theorem d2Delta44Check : chebRoundPieceL d2Delta44Fq d2Delta44Ts 16 24 12 20 30 128 d2Delta44Lo d2Delta44Hi d2Delta44Pd d2Delta44Qd d2Delta44Ld d2Delta44Gam (d2LitsStandaloneDelta005.q2 (-3688722996096251019697) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta44Fq d2Delta44Ts 16 24 12 20 30 128 d2Delta44Lo d2Delta44Hi d2Delta44Pd d2Delta44Qd d2Delta44Ld d2Delta44Gam d2Delta44S d2Delta44Ap d2Delta44Aq d2Delta44Al d2Delta44Es d2Delta44Ep d2Delta44Eq d2Delta44El (by decide +kernel) d2Delta44Shift d2Delta44Plogs d2Delta44Poles d2Delta44Laurent]
  exact decide_eq_true d2Delta44Small
theorem d2Delta44Bound : ∀ x ∈ Icc ((d2Delta44Lo : ℚ) : ℝ) ((d2Delta44Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-3688722996096251019697) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta44Fq d2Delta44Ts 16 24 12 20 30 128 d2Delta44Lo d2Delta44Hi d2Delta44Pd d2Delta44Qd d2Delta44Ld d2Delta44Gam (d2LitsStandaloneDelta005.q2 (-3688722996096251019697) 1 (-79)) d2Delta44Check
  simpa only [d2Delta44Fq, d2Delta44Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta44Shift
#print axioms d2Delta44Sites
#print axioms d2Delta44PData
#print axioms d2Delta44Plogs
#print axioms d2Delta44Poles
#print axioms d2Delta44Laurent
#print axioms d2Delta44Small
#print axioms d2Delta44Check
#print axioms d2Delta44Bound

def d2Delta45Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta45Ts : List LTerm := laurentClean []
def d2Delta45Lo : ℚ := (d2LitsStandaloneDelta005.q2 (3208189) 1 (-26))
def d2Delta45Hi : ℚ := (d2LitsStandaloneDelta005.q2 (13880307) 1 (-28))
def d2Delta45Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta45Qd : List (ℚ × ℚ) := []
def d2Delta45Ld : List LaurentPieceData := []
def d2Delta45Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918765102363838662658638069138328826036963527, 1, -160, 319533891416524464500232437917258150803, 1, -154, 504599949753343980075775207610669187769, 1, -160, -12068047481093790869851902821848634031, 1, -157, -14286671341844065859172342050418701, 1, -156, 32808005447226991171091692137820485, 1, -158, -647197742669004232095959128205041, 1, -159, -7422762549705148501657989439959, 1, -157, 1118352163573291109152114742623, 1, -160, 4623544067678573323100088945, 1, -160, -219101747311156384472180987, 1, -160, 45081149501482765320665, 1, -157, 5741003283652901671225, 1, -158, -3074645364647663663, 1, -155, -789949816879300753, 1, -159, 4855568773656071, 1, -159, 19466776977191, 1, -158, -615739330665, 1, -160, -2461092589, 1, -159, -1518189333, 1, -160, -1309609223, 1, -160, -967171661, 1, -160, -813306989, 1, -160, -73484153, 1, -157, -490848449, 1, -160, -347044705, 1, -160, -287669335, 1, -160, -99422715, 1, -159, -5112361, 1, -155, -1726659, 1, -154, -45106923, 1, -159, -7440875, 1, -157])
def d2Delta45S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-2076561936920294455116497563198377457, 1, -128, 2414507182085545728960052656631, 1, -127, 58848251269750875720900360297, 1, -126, -353616529340022356804979801, 1, -120, -411268306070392281778111705, 1, -128, 122606587875255739151661763, 1, -126, -4855357012823912119266899, 1, -127, -13835657483509897787527, 1, -122, 16697413048668835519109, 1, -127, 275347860371407704137, 1, -128, -26151828425938755827, 1, -128, 43145313591640361, 1, -127, 5480322797178755, 1, -127, -23492429682439, 1, -126, -1507898273941, 1, -127, 37084854781, 1, -128, 297248539, 1, -127, -9366943, 1, -128, -43825, 1, -127, 1727, 1, -128, 9, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta45Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta45Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta45Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta45Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta45Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta45Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta45El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta45Shift : polyRoundApx 128 d2Delta45Lo d2Delta45Hi d2Delta45Fq.poly = (d2Delta45S,d2Delta45Es) := by decide +kernel
theorem d2Delta45Sites : mergeSites d2Delta45Fq.plogs = [] := by decide +kernel
theorem d2Delta45PData : d2Delta45Pd = [] := by decide +kernel
theorem d2Delta45Plogs : plogsRoundM 16 24 20 128 d2Delta45Lo d2Delta45Hi (mergeSites d2Delta45Fq.plogs) d2Delta45Pd = some (d2Delta45Ap,d2Delta45Ep) := by
  rw [d2Delta45Sites,d2Delta45PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta45Poles : polesRoundM 16 24 12 128 d2Delta45Lo d2Delta45Hi d2Delta45Fq.poles d2Delta45Qd = some (d2Delta45Aq,d2Delta45Eq) := by decide +kernel
theorem d2Delta45Laurent : laurentRoundM 16 30 128 d2Delta45Lo d2Delta45Hi d2Delta45Ts d2Delta45Ld = some (d2Delta45Al,d2Delta45El) := by decide +kernel
theorem d2Delta45Small : chebPolyUB (vecAdd d2Delta45S (vecAdd d2Delta45Ap (vecAdd d2Delta45Aq d2Delta45Al))) d2Delta45Gam+d2Delta45Es+d2Delta45Ep+d2Delta45Eq+d2Delta45El ≤ (d2LitsStandaloneDelta005.q2 (-1844353041763208464335) 1 (-78)) := by decide +kernel
theorem d2Delta45Check : chebRoundPieceL d2Delta45Fq d2Delta45Ts 16 24 12 20 30 128 d2Delta45Lo d2Delta45Hi d2Delta45Pd d2Delta45Qd d2Delta45Ld d2Delta45Gam (d2LitsStandaloneDelta005.q2 (-1844353041763208464335) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta45Fq d2Delta45Ts 16 24 12 20 30 128 d2Delta45Lo d2Delta45Hi d2Delta45Pd d2Delta45Qd d2Delta45Ld d2Delta45Gam d2Delta45S d2Delta45Ap d2Delta45Aq d2Delta45Al d2Delta45Es d2Delta45Ep d2Delta45Eq d2Delta45El (by decide +kernel) d2Delta45Shift d2Delta45Plogs d2Delta45Poles d2Delta45Laurent]
  exact decide_eq_true d2Delta45Small
theorem d2Delta45Bound : ∀ x ∈ Icc ((d2Delta45Lo : ℚ) : ℝ) ((d2Delta45Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-1844353041763208464335) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta45Fq d2Delta45Ts 16 24 12 20 30 128 d2Delta45Lo d2Delta45Hi d2Delta45Pd d2Delta45Qd d2Delta45Ld d2Delta45Gam (d2LitsStandaloneDelta005.q2 (-1844353041763208464335) 1 (-78)) d2Delta45Check
  simpa only [d2Delta45Fq, d2Delta45Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta45Shift
#print axioms d2Delta45Sites
#print axioms d2Delta45PData
#print axioms d2Delta45Plogs
#print axioms d2Delta45Poles
#print axioms d2Delta45Laurent
#print axioms d2Delta45Small
#print axioms d2Delta45Check
#print axioms d2Delta45Bound

def d2Delta46Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta46Ts : List LTerm := laurentClean []
def d2Delta46Lo : ℚ := (d2LitsStandaloneDelta005.q2 (13880307) 1 (-28))
def d2Delta46Hi : ℚ := (d2LitsStandaloneDelta005.q2 (28808165) 1 (-29))
def d2Delta46Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta46Qd : List (ℚ × ℚ) := []
def d2Delta46Ld : List LaurentPieceData := []
def d2Delta46Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918733614044742429711921828149079551675405395, 1, -160, 164919860046474249071853892469001588115, 1, -154, -21626586073035539524380018332864707467, 1, -158, -1386502036482366208351185007199216303, 1, -157, 23826285815997470681247387496574991, 1, -158, 770539439205842828032795441590597, 1, -158, -35308622037532951738643463313667, 1, -160, -30990647636087629093010932183, 1, -157, 4525149505211497539827830277, 1, -160, -3221597875780583064147343, 1, -160, -190046524979605033661333, 1, -160, 67466349193511543257, 1, -157, 274269841901600825, 1, -156, -589957409138223, 1, -155, -32694027623245, 1, -159, 191252925959, 1, -159, -2255944957, 1, -160, -2410532969, 1, -160, -949848743, 1, -159, -1546484501, 1, -160, -601458947, 1, -159, -967171661, 1, -160, -740642553, 1, -160, -73484153, 1, -157, -443146299, 1, -160, -347044705, 1, -160, -257506393, 1, -160, -99422715, 1, -159, -145235579, 1, -160, -1726659, 1, -154, -79460147, 1, -160, -7440875, 1, -157])
def d2Delta46S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-1038277233885957123846560339306879093, 1, -127, 1232624345502601949702759652979, 1, -127, -20230161658302787418821072899, 1, -127, -10344600818584583831950576943, 1, -128, 88957217995736721624157081, 1, -127, 44876551634898159916689, 1, -120, -263339503747929102074769, 1, -128, -3693940683554393810071, 1, -128, 134916609747534044715, 1, -128, -96188072613684643, 1, -127, -5665397340777363, 1, -126, 8046273149905, 1, -124, 2092949351011, 1, -128, -18009590697, 1, -128, -124729717, 1, -128, 368347, 1, -126, 5055, 1, -128, -85, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta46Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta46Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta46Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta46Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta46Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta46Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta46El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta46Shift : polyRoundApx 128 d2Delta46Lo d2Delta46Hi d2Delta46Fq.poly = (d2Delta46S,d2Delta46Es) := by decide +kernel
theorem d2Delta46Sites : mergeSites d2Delta46Fq.plogs = [] := by decide +kernel
theorem d2Delta46PData : d2Delta46Pd = [] := by decide +kernel
theorem d2Delta46Plogs : plogsRoundM 16 24 20 128 d2Delta46Lo d2Delta46Hi (mergeSites d2Delta46Fq.plogs) d2Delta46Pd = some (d2Delta46Ap,d2Delta46Ep) := by
  rw [d2Delta46Sites,d2Delta46PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta46Poles : polesRoundM 16 24 12 128 d2Delta46Lo d2Delta46Hi d2Delta46Fq.poles d2Delta46Qd = some (d2Delta46Aq,d2Delta46Eq) := by decide +kernel
theorem d2Delta46Laurent : laurentRoundM 16 30 128 d2Delta46Lo d2Delta46Hi d2Delta46Ts d2Delta46Ld = some (d2Delta46Al,d2Delta46El) := by decide +kernel
theorem d2Delta46Small : chebPolyUB (vecAdd d2Delta46S (vecAdd d2Delta46Ap (vecAdd d2Delta46Aq d2Delta46Al))) d2Delta46Gam+d2Delta46Es+d2Delta46Ep+d2Delta46Eq+d2Delta46El ≤ (d2LitsStandaloneDelta005.q2 (-3688697361232614215311) 1 (-79)) := by decide +kernel
theorem d2Delta46Check : chebRoundPieceL d2Delta46Fq d2Delta46Ts 16 24 12 20 30 128 d2Delta46Lo d2Delta46Hi d2Delta46Pd d2Delta46Qd d2Delta46Ld d2Delta46Gam (d2LitsStandaloneDelta005.q2 (-3688697361232614215311) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta46Fq d2Delta46Ts 16 24 12 20 30 128 d2Delta46Lo d2Delta46Hi d2Delta46Pd d2Delta46Qd d2Delta46Ld d2Delta46Gam d2Delta46S d2Delta46Ap d2Delta46Aq d2Delta46Al d2Delta46Es d2Delta46Ep d2Delta46Eq d2Delta46El (by decide +kernel) d2Delta46Shift d2Delta46Plogs d2Delta46Poles d2Delta46Laurent]
  exact decide_eq_true d2Delta46Small
theorem d2Delta46Bound : ∀ x ∈ Icc ((d2Delta46Lo : ℚ) : ℝ) ((d2Delta46Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-3688697361232614215311) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta46Fq d2Delta46Ts 16 24 12 20 30 128 d2Delta46Lo d2Delta46Hi d2Delta46Pd d2Delta46Qd d2Delta46Ld d2Delta46Gam (d2LitsStandaloneDelta005.q2 (-3688697361232614215311) 1 (-79)) d2Delta46Check
  simpa only [d2Delta46Fq, d2Delta46Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta46Shift
#print axioms d2Delta46Sites
#print axioms d2Delta46PData
#print axioms d2Delta46Plogs
#print axioms d2Delta46Poles
#print axioms d2Delta46Laurent
#print axioms d2Delta46Small
#print axioms d2Delta46Check
#print axioms d2Delta46Bound

def d2Delta47Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta47Ts : List LTerm := laurentClean []
def d2Delta47Lo : ℚ := (d2LitsStandaloneDelta005.q2 (28808165) 1 (-29))
def d2Delta47Hi : ℚ := (d2LitsStandaloneDelta005.q2 (30903267) 1 (-29))
def d2Delta47Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta47Qd : List (ℚ × ℚ) := []
def d2Delta47Ld : List LaurentPieceData := []
def d2Delta47Gam : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-8918705486499314930290768438470119240141227219, 1, -160, 261017582377261241241773299251091967379, 1, -154, -1030322713923491926519499712232362726455, 1, -160, -7833255234289884980728609546055033519, 1, -157, 2663838191423114329481225023084832279, 1, -160, 13414637178694793477873878338466117, 1, -158, -2634966494700017605849251976969439, 1, -160, -638918097707157845372925936087, 1, -157, 1039579542403122271133221324513, 1, -160, -6829607015352682991623673231, 1, -160, -37156506631522232410636487, 1, -158, 204120787257757698597337, 1, -157, 5610842403776692389039, 1, -159, -5844305855799619119, 1, -155, -468374211718331171, 1, -160, 6913522385882631, 1, -159, 2880278508997, 1, -159, -739889369193, 1, -160, -723823095, 1, -159, -1516403477, 1, -160, -1312030119, 1, -160, -967171661, 1, -160, -815516053, 1, -160, -73484153, 1, -157, -246347469, 1, -159, -347044705, 1, -160, -289102627, 1, -160, -99422715, 1, -159, -82322347, 1, -159, -1726659, 1, -154, -90941595, 1, -160, -7440875, 1, -157])
def d2Delta47S : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [-2076547698469396403327781688441006733, 1, -128, 1966649634557447817442296435565, 1, -127, -60594279669727281266392068587, 1, -125, -58612233001498392121434717905, 1, -128, 2495636036074387088952831975, 1, -127, 200026272248807969738402939, 1, -128, -19694032774918805073697709, 1, -128, -9405997467825144630781, 1, -125, 31026196740201865286595, 1, -128, -51018460129131923619, 1, -125, -8866830039657451147, 1, -127, 48738681496929805, 1, -125, 5354043314720017, 1, -128, -11159496360245, 1, -124, -223382160313, 1, -126, 52793846963, 1, -128, 21945113, 1, -127, -703865, 1, -124, 18503, 1, -128, 459, 1, -126, -7, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta47Ap : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta47Aq : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta47Al : List ℚ := d2LitsStandaloneDelta005.q2listC (raw_ints% [])
def d2Delta47Es : ℚ := (d2LitsStandaloneDelta005.q2 (61) 1 (-127))
def d2Delta47Ep : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta47Eq : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
def d2Delta47El : ℚ := (d2LitsStandaloneDelta005.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta47Shift : polyRoundApx 128 d2Delta47Lo d2Delta47Hi d2Delta47Fq.poly = (d2Delta47S,d2Delta47Es) := by decide +kernel
theorem d2Delta47Sites : mergeSites d2Delta47Fq.plogs = [] := by decide +kernel
theorem d2Delta47PData : d2Delta47Pd = [] := by decide +kernel
theorem d2Delta47Plogs : plogsRoundM 16 24 20 128 d2Delta47Lo d2Delta47Hi (mergeSites d2Delta47Fq.plogs) d2Delta47Pd = some (d2Delta47Ap,d2Delta47Ep) := by
  rw [d2Delta47Sites,d2Delta47PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta47Poles : polesRoundM 16 24 12 128 d2Delta47Lo d2Delta47Hi d2Delta47Fq.poles d2Delta47Qd = some (d2Delta47Aq,d2Delta47Eq) := by decide +kernel
theorem d2Delta47Laurent : laurentRoundM 16 30 128 d2Delta47Lo d2Delta47Hi d2Delta47Ts d2Delta47Ld = some (d2Delta47Al,d2Delta47El) := by decide +kernel
theorem d2Delta47Small : chebPolyUB (vecAdd d2Delta47S (vecAdd d2Delta47Ap (vecAdd d2Delta47Aq d2Delta47Al))) d2Delta47Gam+d2Delta47Es+d2Delta47Ep+d2Delta47Eq+d2Delta47El ≤ (d2LitsStandaloneDelta005.q2 (-3688682771498821396263) 1 (-79)) := by decide +kernel
theorem d2Delta47Check : chebRoundPieceL d2Delta47Fq d2Delta47Ts 16 24 12 20 30 128 d2Delta47Lo d2Delta47Hi d2Delta47Pd d2Delta47Qd d2Delta47Ld d2Delta47Gam (d2LitsStandaloneDelta005.q2 (-3688682771498821396263) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta47Fq d2Delta47Ts 16 24 12 20 30 128 d2Delta47Lo d2Delta47Hi d2Delta47Pd d2Delta47Qd d2Delta47Ld d2Delta47Gam d2Delta47S d2Delta47Ap d2Delta47Aq d2Delta47Al d2Delta47Es d2Delta47Ep d2Delta47Eq d2Delta47El (by decide +kernel) d2Delta47Shift d2Delta47Plogs d2Delta47Poles d2Delta47Laurent]
  exact decide_eq_true d2Delta47Small
theorem d2Delta47Bound : ∀ x ∈ Icc ((d2Delta47Lo : ℚ) : ℝ) ((d2Delta47Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta005.q2 (-3688682771498821396263) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta47Fq d2Delta47Ts 16 24 12 20 30 128 d2Delta47Lo d2Delta47Hi d2Delta47Pd d2Delta47Qd d2Delta47Ld d2Delta47Gam (d2LitsStandaloneDelta005.q2 (-3688682771498821396263) 1 (-79)) d2Delta47Check
  simpa only [d2Delta47Fq, d2Delta47Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta47Shift
#print axioms d2Delta47Sites
#print axioms d2Delta47PData
#print axioms d2Delta47Plogs
#print axioms d2Delta47Poles
#print axioms d2Delta47Laurent
#print axioms d2Delta47Small
#print axioms d2Delta47Check
#print axioms d2Delta47Bound

end StandaloneDelta005
end CatalanMeasure.GenD.Signed.Data.Cells
