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
namespace d2LitsStandaloneDelta024
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta024
namespace StandaloneDelta024
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta024.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta024.q2listC (raw_ints% []))⟩
def d2Delta192Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta192Ts : List LTerm := laurentClean []
def d2Delta192Lo : ℚ := (d2LitsStandaloneDelta024.q2 (17178805249) 1 (-34))
def d2Delta192Hi : ℚ := (d2LitsStandaloneDelta024.q2 (68716268547) 1 (-36))
def d2Delta192Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta192Qd : List (ℚ × ℚ) := []
def d2Delta192Ld : List LaurentPieceData := []
def d2Delta192Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-531590562854721702930121803204283757455, 1, -136, 141795989076379379566759650097255, 1, -134, 5293519627377397447178160037747, 1, -136, 11406684370435877608324031671, 1, -135, 13058293566345715178315925, 1, -134, 72036266796145992586507, 1, -136, 131675303515149442807, 1, -137, 21366172033207359, 1, -135, 20717979725627, 1, -136, 3896412823, 1, -135, 4682787, 1, -137, 575, 1, -136, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta192S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-2076525656828863660933951166255186987, 1, -128, 2215294986560452882249141756457, 1, -128, 41353989806819331641139550003, 1, -128, 356453258752125422966096861, 1, -128, 1632274351246458585699317, 1, -128, 562780997421468233841, 1, -125, 8229685751727358145, 1, -128, 10683068482752301, 1, -128, 5179489077923, 1, -127, 7792819321, 1, -128, 4682787, 1, -128, 575, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta192Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta192Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta192Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta192Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta192Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta192Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta192El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta192Shift : polyRoundApx 128 d2Delta192Lo d2Delta192Hi d2Delta192Fq.poly = (d2Delta192S,d2Delta192Es) := by decide +kernel
theorem d2Delta192Sites : mergeSites d2Delta192Fq.plogs = [] := by decide +kernel
theorem d2Delta192PData : d2Delta192Pd = [] := by decide +kernel
theorem d2Delta192Plogs : plogsRoundM 16 24 20 128 d2Delta192Lo d2Delta192Hi (mergeSites d2Delta192Fq.plogs) d2Delta192Pd = some (d2Delta192Ap,d2Delta192Ep) := by
  rw [d2Delta192Sites,d2Delta192PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta192Poles : polesRoundM 16 24 12 128 d2Delta192Lo d2Delta192Hi d2Delta192Fq.poles d2Delta192Qd = some (d2Delta192Aq,d2Delta192Eq) := by decide +kernel
theorem d2Delta192Laurent : laurentRoundM 16 30 128 d2Delta192Lo d2Delta192Hi d2Delta192Ts d2Delta192Ld = some (d2Delta192Al,d2Delta192El) := by decide +kernel
theorem d2Delta192Small : chebPolyUB (vecAdd d2Delta192S (vecAdd d2Delta192Ap (vecAdd d2Delta192Aq d2Delta192Al))) d2Delta192Gam+d2Delta192Es+d2Delta192Ep+d2Delta192Eq+d2Delta192El ≤ (d2LitsStandaloneDelta024.q2 (-1844323271724055191063) 1 (-78)) := by decide +kernel
theorem d2Delta192Check : chebRoundPieceL d2Delta192Fq d2Delta192Ts 16 24 12 20 30 128 d2Delta192Lo d2Delta192Hi d2Delta192Pd d2Delta192Qd d2Delta192Ld d2Delta192Gam (d2LitsStandaloneDelta024.q2 (-1844323271724055191063) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta192Fq d2Delta192Ts 16 24 12 20 30 128 d2Delta192Lo d2Delta192Hi d2Delta192Pd d2Delta192Qd d2Delta192Ld d2Delta192Gam d2Delta192S d2Delta192Ap d2Delta192Aq d2Delta192Al d2Delta192Es d2Delta192Ep d2Delta192Eq d2Delta192El (by decide +kernel) d2Delta192Shift d2Delta192Plogs d2Delta192Poles d2Delta192Laurent]
  exact decide_eq_true d2Delta192Small
theorem d2Delta192Bound : ∀ x ∈ Icc ((d2Delta192Lo : ℚ) : ℝ) ((d2Delta192Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-1844323271724055191063) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta192Fq d2Delta192Ts 16 24 12 20 30 128 d2Delta192Lo d2Delta192Hi d2Delta192Pd d2Delta192Qd d2Delta192Ld d2Delta192Gam (d2LitsStandaloneDelta024.q2 (-1844323271724055191063) 1 (-78)) d2Delta192Check
  simpa only [d2Delta192Fq, d2Delta192Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta192Shift
#print axioms d2Delta192Sites
#print axioms d2Delta192PData
#print axioms d2Delta192Plogs
#print axioms d2Delta192Poles
#print axioms d2Delta192Laurent
#print axioms d2Delta192Small
#print axioms d2Delta192Check
#print axioms d2Delta192Bound

def d2Delta193Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta193Ts : List LTerm := laurentClean []
def d2Delta193Lo : ℚ := (d2LitsStandaloneDelta024.q2 (68716268547) 1 (-36))
def d2Delta193Hi : ℚ := (d2LitsStandaloneDelta024.q2 (34358658049) 1 (-35))
def d2Delta193Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta193Qd : List (ℚ × ℚ) := []
def d2Delta193Ld : List LaurentPieceData := []
def d2Delta193Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-531589385261642758380232925307779230507, 1, -136, 610641472502426029320107275817363, 1, -136, 5572342260146467337794625689745, 1, -136, 23660711592266226723771380825, 1, -136, 13422449485740976965040645, 1, -134, 147261607364033625060757, 1, -137, 134086962700562692373, 1, -137, 86799652420737847, 1, -137, 21000213366423, 1, -136, 15773978323, 1, -137, 4733641, 1, -137, 1161, 1, -137, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta193S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-2076521057945044253108596716971152751, 1, -128, 2385040979436730254887920057189, 1, -128, 43532246105922550611815331741, 1, -128, 369692866232115843281941421, 1, -128, 209724201884749259066691, 1, -125, 4601906242715393038161, 1, -128, 4190207084291078345, 1, -127, 10849938806873003, 1, -128, 10500094849109, 1, -128, 985872847, 1, -125, 4733641, 1, -128, 1161, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta193Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta193Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta193Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta193Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta193Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta193Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta193El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta193Shift : polyRoundApx 128 d2Delta193Lo d2Delta193Hi d2Delta193Fq.poly = (d2Delta193S,d2Delta193Es) := by decide +kernel
theorem d2Delta193Sites : mergeSites d2Delta193Fq.plogs = [] := by decide +kernel
theorem d2Delta193PData : d2Delta193Pd = [] := by decide +kernel
theorem d2Delta193Plogs : plogsRoundM 16 24 20 128 d2Delta193Lo d2Delta193Hi (mergeSites d2Delta193Fq.plogs) d2Delta193Pd = some (d2Delta193Ap,d2Delta193Ep) := by
  rw [d2Delta193Sites,d2Delta193PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta193Poles : polesRoundM 16 24 12 128 d2Delta193Lo d2Delta193Hi d2Delta193Fq.poles d2Delta193Qd = some (d2Delta193Aq,d2Delta193Eq) := by decide +kernel
theorem d2Delta193Laurent : laurentRoundM 16 30 128 d2Delta193Lo d2Delta193Hi d2Delta193Ts d2Delta193Ld = some (d2Delta193Al,d2Delta193El) := by decide +kernel
theorem d2Delta193Small : chebPolyUB (vecAdd d2Delta193S (vecAdd d2Delta193Ap (vecAdd d2Delta193Aq d2Delta193Al))) d2Delta193Gam+d2Delta193Es+d2Delta193Ep+d2Delta193Eq+d2Delta193El ≤ (d2LitsStandaloneDelta024.q2 (-7377276137533937970797) 1 (-80)) := by decide +kernel
theorem d2Delta193Check : chebRoundPieceL d2Delta193Fq d2Delta193Ts 16 24 12 20 30 128 d2Delta193Lo d2Delta193Hi d2Delta193Pd d2Delta193Qd d2Delta193Ld d2Delta193Gam (d2LitsStandaloneDelta024.q2 (-7377276137533937970797) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta193Fq d2Delta193Ts 16 24 12 20 30 128 d2Delta193Lo d2Delta193Hi d2Delta193Pd d2Delta193Qd d2Delta193Ld d2Delta193Gam d2Delta193S d2Delta193Ap d2Delta193Aq d2Delta193Al d2Delta193Es d2Delta193Ep d2Delta193Eq d2Delta193El (by decide +kernel) d2Delta193Shift d2Delta193Plogs d2Delta193Poles d2Delta193Laurent]
  exact decide_eq_true d2Delta193Small
theorem d2Delta193Bound : ∀ x ∈ Icc ((d2Delta193Lo : ℚ) : ℝ) ((d2Delta193Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-7377276137533937970797) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta193Fq d2Delta193Ts 16 24 12 20 30 128 d2Delta193Lo d2Delta193Hi d2Delta193Pd d2Delta193Qd d2Delta193Ld d2Delta193Gam (d2LitsStandaloneDelta024.q2 (-7377276137533937970797) 1 (-80)) d2Delta193Check
  simpa only [d2Delta193Fq, d2Delta193Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta193Shift
#print axioms d2Delta193Sites
#print axioms d2Delta193PData
#print axioms d2Delta193Plogs
#print axioms d2Delta193Poles
#print axioms d2Delta193Laurent
#print axioms d2Delta193Small
#print axioms d2Delta193Check
#print axioms d2Delta193Bound

def d2Delta194Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta194Ts : List LTerm := laurentClean []
def d2Delta194Lo : ℚ := (d2LitsStandaloneDelta024.q2 (34358658049) 1 (-35))
def d2Delta194Hi : ℚ := (d2LitsStandaloneDelta024.q2 (68718363649) 1 (-36))
def d2Delta194Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta194Qd : List (ℚ × ℚ) := []
def d2Delta194Ld : List LaurentPieceData := []
def d2Delta194Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-132897029622617513395533428543490711603, 1, -134, 1312741281707875627193829460375003, 1, -137, 1465368475127623593653558508463, 1, -134, 49063234254356708781422709261, 1, -137, 1724331352390681972095093, 1, -131, 301018023103236362545549, 1, -138, 34134063697352530441, 1, -135, 176305577063203003, 1, -138, 5321463815403, 1, -134, 31928699071, 1, -138, 1196249, 1, -135, 2345, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta194S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-2076516110749565529521951926070086051, 1, -128, 2563660337417298823742578235417, 1, -128, 45791040521185946666410367473, 1, -128, 5989072474430308746463421, 1, -122, 1724318552130099120696407, 1, -128, 4703387327579046794045, 1, -128, 8533494638493338177, 1, -128, 11019080606563409, 1, -128, 2660728917079, 1, -126, 7982168319, 1, -128, 1196249, 1, -126, 2345, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta194Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta194Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta194Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta194Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta194Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta194Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta194El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta194Shift : polyRoundApx 128 d2Delta194Lo d2Delta194Hi d2Delta194Fq.poly = (d2Delta194S,d2Delta194Es) := by decide +kernel
theorem d2Delta194Sites : mergeSites d2Delta194Fq.plogs = [] := by decide +kernel
theorem d2Delta194PData : d2Delta194Pd = [] := by decide +kernel
theorem d2Delta194Plogs : plogsRoundM 16 24 20 128 d2Delta194Lo d2Delta194Hi (mergeSites d2Delta194Fq.plogs) d2Delta194Pd = some (d2Delta194Ap,d2Delta194Ep) := by
  rw [d2Delta194Sites,d2Delta194PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta194Poles : polesRoundM 16 24 12 128 d2Delta194Lo d2Delta194Hi d2Delta194Fq.poles d2Delta194Qd = some (d2Delta194Aq,d2Delta194Eq) := by decide +kernel
theorem d2Delta194Laurent : laurentRoundM 16 30 128 d2Delta194Lo d2Delta194Hi d2Delta194Ts d2Delta194Ld = some (d2Delta194Al,d2Delta194El) := by decide +kernel
theorem d2Delta194Small : chebPolyUB (vecAdd d2Delta194S (vecAdd d2Delta194Ap (vecAdd d2Delta194Aq d2Delta194Al))) d2Delta194Gam+d2Delta194Es+d2Delta194Ep+d2Delta194Eq+d2Delta194El ≤ (d2LitsStandaloneDelta024.q2 (-7377257918908092627637) 1 (-80)) := by decide +kernel
theorem d2Delta194Check : chebRoundPieceL d2Delta194Fq d2Delta194Ts 16 24 12 20 30 128 d2Delta194Lo d2Delta194Hi d2Delta194Pd d2Delta194Qd d2Delta194Ld d2Delta194Gam (d2LitsStandaloneDelta024.q2 (-7377257918908092627637) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta194Fq d2Delta194Ts 16 24 12 20 30 128 d2Delta194Lo d2Delta194Hi d2Delta194Pd d2Delta194Qd d2Delta194Ld d2Delta194Gam d2Delta194S d2Delta194Ap d2Delta194Aq d2Delta194Al d2Delta194Es d2Delta194Ep d2Delta194Eq d2Delta194El (by decide +kernel) d2Delta194Shift d2Delta194Plogs d2Delta194Poles d2Delta194Laurent]
  exact decide_eq_true d2Delta194Small
theorem d2Delta194Bound : ∀ x ∈ Icc ((d2Delta194Lo : ℚ) : ℝ) ((d2Delta194Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-7377257918908092627637) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta194Fq d2Delta194Ts 16 24 12 20 30 128 d2Delta194Lo d2Delta194Hi d2Delta194Pd d2Delta194Qd d2Delta194Ld d2Delta194Gam (d2LitsStandaloneDelta024.q2 (-7377257918908092627637) 1 (-80)) d2Delta194Check
  simpa only [d2Delta194Fq, d2Delta194Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta194Shift
#print axioms d2Delta194Sites
#print axioms d2Delta194PData
#print axioms d2Delta194Plogs
#print axioms d2Delta194Poles
#print axioms d2Delta194Laurent
#print axioms d2Delta194Small
#print axioms d2Delta194Check
#print axioms d2Delta194Bound

def d2Delta195Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta195Ts : List LTerm := laurentClean []
def d2Delta195Lo : ℚ := (d2LitsStandaloneDelta024.q2 (68718363649) 1 (-36))
def d2Delta195Hi : ℚ := (d2LitsStandaloneDelta024.q2 (137437774849) 1 (-37))
def d2Delta195Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta195Qd : List (ℚ × ℚ) := []
def d2Delta195Ld : List LaurentPieceData := []
def d2Delta195Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-265793555837997538213459746121873147093, 1, -135, 692151799014409896324943987915751, 1, -137, 760636336875113572695459561191, 1, -135, 6300071165316762478604754333, 1, -137, 439971627910176134740469, 1, -133, 9561432649007851679925, 1, -138, 1081234141521322367, 1, -136, 1393431077821567, 1, -138, 41996733377, 1, -135, 62923715, 1, -138, 2355, 1, -136, 1, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta195S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-2076512160926813400020330430793419339, 1, -128, 1351822068017221724185584596941, 1, -128, 11884832770842696294409405621, 1, -128, 24609559616190992092095507, 1, -127, 109992704246194994350215, 1, -128, 74698616367125045853, 1, -127, 135154183696708845, 1, -128, 87089406969261, 1, -128, 20998360801, 1, -127, 7865463, 1, -127, 2355, 1, -127, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta195Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta195Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta195Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta195Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta195Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta195Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta195El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta195Shift : polyRoundApx 128 d2Delta195Lo d2Delta195Hi d2Delta195Fq.poly = (d2Delta195S,d2Delta195Es) := by decide +kernel
theorem d2Delta195Sites : mergeSites d2Delta195Fq.plogs = [] := by decide +kernel
theorem d2Delta195PData : d2Delta195Pd = [] := by decide +kernel
theorem d2Delta195Plogs : plogsRoundM 16 24 20 128 d2Delta195Lo d2Delta195Hi (mergeSites d2Delta195Fq.plogs) d2Delta195Pd = some (d2Delta195Ap,d2Delta195Ep) := by
  rw [d2Delta195Sites,d2Delta195PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta195Poles : polesRoundM 16 24 12 128 d2Delta195Lo d2Delta195Hi d2Delta195Fq.poles d2Delta195Qd = some (d2Delta195Aq,d2Delta195Eq) := by decide +kernel
theorem d2Delta195Laurent : laurentRoundM 16 30 128 d2Delta195Lo d2Delta195Hi d2Delta195Ts d2Delta195Ld = some (d2Delta195Al,d2Delta195El) := by decide +kernel
theorem d2Delta195Small : chebPolyUB (vecAdd d2Delta195S (vecAdd d2Delta195Ap (vecAdd d2Delta195Aq d2Delta195Al))) d2Delta195Gam+d2Delta195Es+d2Delta195Ep+d2Delta195Eq+d2Delta195El ≤ (d2LitsStandaloneDelta024.q2 (-7377248313284863991465) 1 (-80)) := by decide +kernel
theorem d2Delta195Check : chebRoundPieceL d2Delta195Fq d2Delta195Ts 16 24 12 20 30 128 d2Delta195Lo d2Delta195Hi d2Delta195Pd d2Delta195Qd d2Delta195Ld d2Delta195Gam (d2LitsStandaloneDelta024.q2 (-7377248313284863991465) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta195Fq d2Delta195Ts 16 24 12 20 30 128 d2Delta195Lo d2Delta195Hi d2Delta195Pd d2Delta195Qd d2Delta195Ld d2Delta195Gam d2Delta195S d2Delta195Ap d2Delta195Aq d2Delta195Al d2Delta195Es d2Delta195Ep d2Delta195Eq d2Delta195El (by decide +kernel) d2Delta195Shift d2Delta195Plogs d2Delta195Poles d2Delta195Laurent]
  exact decide_eq_true d2Delta195Small
theorem d2Delta195Bound : ∀ x ∈ Icc ((d2Delta195Lo : ℚ) : ℝ) ((d2Delta195Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-7377248313284863991465) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta195Fq d2Delta195Ts 16 24 12 20 30 128 d2Delta195Lo d2Delta195Hi d2Delta195Pd d2Delta195Qd d2Delta195Ld d2Delta195Gam (d2LitsStandaloneDelta024.q2 (-7377248313284863991465) 1 (-80)) d2Delta195Check
  simpa only [d2Delta195Fq, d2Delta195Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta195Shift
#print axioms d2Delta195Sites
#print axioms d2Delta195PData
#print axioms d2Delta195Plogs
#print axioms d2Delta195Poles
#print axioms d2Delta195Laurent
#print axioms d2Delta195Small
#print axioms d2Delta195Check
#print axioms d2Delta195Bound

def d2Delta196Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta196Ts : List LTerm := laurentClean []
def d2Delta196Lo : ℚ := (d2LitsStandaloneDelta024.q2 (137437774849) 1 (-37))
def d2Delta196Hi : ℚ := (d2LitsStandaloneDelta024.q2 (549754242049) 1 (-39))
def d2Delta196Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta196Qd : List (ℚ × ℚ) := []
def d2Delta196Ld : List LaurentPieceData := []
def d2Delta196Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-265793248660506623926180314376116492283, 1, -135, 66906942694331389202166843784719, 1, -134, 437231696339081316150324323517, 1, -135, 337457907098241976517153507, 1, -134, 140871997944913692456093, 1, -133, 143163119228163169361, 1, -134, 193960537491785089, 1, -136, 5851874757627, 1, -133, 4229284167, 1, -135, 296839, 1, -134, 133, 1, -136, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta196S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-259563719822009528102897296031433203, 1, -125, 261351290317679335900202594671, 1, -126, 6831710037312297185660773655, 1, -128, 21091074455175605511600943, 1, -128, 4402245389829116251165, 1, -125, 35790759325481144309, 1, -128, 3030632340988173, 1, -125, 11703746843703, 1, -128, 2114641751, 1, -127, 296839, 1, -126, 133, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta196Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta196Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta196Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta196Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta196Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta196Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta196El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta196Shift : polyRoundApx 128 d2Delta196Lo d2Delta196Hi d2Delta196Fq.poly = (d2Delta196S,d2Delta196Es) := by decide +kernel
theorem d2Delta196Sites : mergeSites d2Delta196Fq.plogs = [] := by decide +kernel
theorem d2Delta196PData : d2Delta196Pd = [] := by decide +kernel
theorem d2Delta196Plogs : plogsRoundM 16 24 20 128 d2Delta196Lo d2Delta196Hi (mergeSites d2Delta196Fq.plogs) d2Delta196Pd = some (d2Delta196Ap,d2Delta196Ep) := by
  rw [d2Delta196Sites,d2Delta196PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta196Poles : polesRoundM 16 24 12 128 d2Delta196Lo d2Delta196Hi d2Delta196Fq.poles d2Delta196Qd = some (d2Delta196Aq,d2Delta196Eq) := by decide +kernel
theorem d2Delta196Laurent : laurentRoundM 16 30 128 d2Delta196Lo d2Delta196Hi d2Delta196Ts d2Delta196Ld = some (d2Delta196Al,d2Delta196El) := by decide +kernel
theorem d2Delta196Small : chebPolyUB (vecAdd d2Delta196S (vecAdd d2Delta196Ap (vecAdd d2Delta196Aq d2Delta196Al))) d2Delta196Gam+d2Delta196Es+d2Delta196Ep+d2Delta196Eq+d2Delta196El ≤ (d2LitsStandaloneDelta024.q2 (-7377240885084569969479) 1 (-80)) := by decide +kernel
theorem d2Delta196Check : chebRoundPieceL d2Delta196Fq d2Delta196Ts 16 24 12 20 30 128 d2Delta196Lo d2Delta196Hi d2Delta196Pd d2Delta196Qd d2Delta196Ld d2Delta196Gam (d2LitsStandaloneDelta024.q2 (-7377240885084569969479) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta196Fq d2Delta196Ts 16 24 12 20 30 128 d2Delta196Lo d2Delta196Hi d2Delta196Pd d2Delta196Qd d2Delta196Ld d2Delta196Gam d2Delta196S d2Delta196Ap d2Delta196Aq d2Delta196Al d2Delta196Es d2Delta196Ep d2Delta196Eq d2Delta196El (by decide +kernel) d2Delta196Shift d2Delta196Plogs d2Delta196Poles d2Delta196Laurent]
  exact decide_eq_true d2Delta196Small
theorem d2Delta196Bound : ∀ x ∈ Icc ((d2Delta196Lo : ℚ) : ℝ) ((d2Delta196Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-7377240885084569969479) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta196Fq d2Delta196Ts 16 24 12 20 30 128 d2Delta196Lo d2Delta196Hi d2Delta196Pd d2Delta196Qd d2Delta196Ld d2Delta196Gam (d2LitsStandaloneDelta024.q2 (-7377240885084569969479) 1 (-80)) d2Delta196Check
  simpa only [d2Delta196Fq, d2Delta196Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta196Shift
#print axioms d2Delta196Sites
#print axioms d2Delta196PData
#print axioms d2Delta196Plogs
#print axioms d2Delta196Poles
#print axioms d2Delta196Laurent
#print axioms d2Delta196Small
#print axioms d2Delta196Check
#print axioms d2Delta196Bound

def d2Delta197Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta197Ts : List LTerm := laurentClean []
def d2Delta197Lo : ℚ := (d2LitsStandaloneDelta024.q2 (549754242049) 1 (-39))
def d2Delta197Hi : ℚ := (d2LitsStandaloneDelta024.q2 (1048575) 1 (-20))
def d2Delta197Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta197Qd : List (ℚ × ℚ) := []
def d2Delta197Ld : List LaurentPieceData := []
def d2Delta197Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-519127088030728256756228750180003679, 1, -126, 22693069828565367264379987769413, 1, -134, 6147959806774368886528275285, 1, -132, 12610101345543002476908337, 1, -134, 54717931707870669361, 1, -128, 592348305869516307, 1, -134, 16704050344571, 1, -132, 671521237, 1, -131, 5053, 1, -128, 15, 1, -134, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta197S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-2076508352507160460230382392260504043, 1, -128, 88644656243219892097126169675, 1, -126, 768494538103361239907155469, 1, -128, 197032787246899192807889, 1, -126, 437743403550815129655, 1, -128, 37021766766520465, 1, -126, 16704049697787, 1, -127, 5372169761, 1, -128, 5053, 1, -121, 15, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta197Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta197Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta197Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta197Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta197Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta197Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta197El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta197Shift : polyRoundApx 128 d2Delta197Lo d2Delta197Hi d2Delta197Fq.poly = (d2Delta197S,d2Delta197Es) := by decide +kernel
theorem d2Delta197Sites : mergeSites d2Delta197Fq.plogs = [] := by decide +kernel
theorem d2Delta197PData : d2Delta197Pd = [] := by decide +kernel
theorem d2Delta197Plogs : plogsRoundM 16 24 20 128 d2Delta197Lo d2Delta197Hi (mergeSites d2Delta197Fq.plogs) d2Delta197Pd = some (d2Delta197Ap,d2Delta197Ep) := by
  rw [d2Delta197Sites,d2Delta197PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta197Poles : polesRoundM 16 24 12 128 d2Delta197Lo d2Delta197Hi d2Delta197Fq.poles d2Delta197Qd = some (d2Delta197Aq,d2Delta197Eq) := by decide +kernel
theorem d2Delta197Laurent : laurentRoundM 16 30 128 d2Delta197Lo d2Delta197Hi d2Delta197Ts d2Delta197Ld = some (d2Delta197Al,d2Delta197El) := by decide +kernel
theorem d2Delta197Small : chebPolyUB (vecAdd d2Delta197S (vecAdd d2Delta197Ap (vecAdd d2Delta197Aq d2Delta197Al))) d2Delta197Gam+d2Delta197Es+d2Delta197Ep+d2Delta197Eq+d2Delta197El ≤ (d2LitsStandaloneDelta024.q2 (-7377238365646307656955) 1 (-80)) := by decide +kernel
theorem d2Delta197Check : chebRoundPieceL d2Delta197Fq d2Delta197Ts 16 24 12 20 30 128 d2Delta197Lo d2Delta197Hi d2Delta197Pd d2Delta197Qd d2Delta197Ld d2Delta197Gam (d2LitsStandaloneDelta024.q2 (-7377238365646307656955) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta197Fq d2Delta197Ts 16 24 12 20 30 128 d2Delta197Lo d2Delta197Hi d2Delta197Pd d2Delta197Qd d2Delta197Ld d2Delta197Gam d2Delta197S d2Delta197Ap d2Delta197Aq d2Delta197Al d2Delta197Es d2Delta197Ep d2Delta197Eq d2Delta197El (by decide +kernel) d2Delta197Shift d2Delta197Plogs d2Delta197Poles d2Delta197Laurent]
  exact decide_eq_true d2Delta197Small
theorem d2Delta197Bound : ∀ x ∈ Icc ((d2Delta197Lo : ℚ) : ℝ) ((d2Delta197Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-7377238365646307656955) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta197Fq d2Delta197Ts 16 24 12 20 30 128 d2Delta197Lo d2Delta197Hi d2Delta197Pd d2Delta197Qd d2Delta197Ld d2Delta197Gam (d2LitsStandaloneDelta024.q2 (-7377238365646307656955) 1 (-80)) d2Delta197Check
  simpa only [d2Delta197Fq, d2Delta197Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta197Shift
#print axioms d2Delta197Sites
#print axioms d2Delta197PData
#print axioms d2Delta197Plogs
#print axioms d2Delta197Poles
#print axioms d2Delta197Laurent
#print axioms d2Delta197Small
#print axioms d2Delta197Check
#print axioms d2Delta197Bound

def d2Delta198Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta198Ts : List LTerm := laurentClean []
def d2Delta198Lo : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta198Hi : ℚ := (d2LitsStandaloneDelta024.q2 (1) 1 (-10))
def d2Delta198Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta198Qd : List (ℚ × ℚ) := []
def d2Delta198Ld : List LaurentPieceData := []
def d2Delta198Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-2227869188001040753948661415259668319927103227, 1, -158, -712543811319191866063033871796282579326213, 1, -160, 6456712904743581956495176464086290992023, 1, -159, -52751426477345163867114965794312168165, 1, -159, 307794202576971306800790888169471125, 1, -160, 430606480916841866351930221577899, 1, -159, -7029367359615823808724039478415, 1, -160, 1124042610738857747145719555, 1, -159, 70692793969829157260669315, 1, -160, -47426157233287959065771, 1, -159, -450397633466686150967, 1, -160, 454240469667116287, 1, -159, 2022607744280799, 1, -160, -2683641188587, 1, -159, -2745055509, 1, -158, -3792179451, 1, -160, -2929742299, 1, -160, -631522141, 1, -158, -59731107, 1, -155, -814564245, 1, -159, -606907643, 1, -159, -511387441, 1, -159, -187489097, 1, -158, -312355983, 1, -159, -112637477, 1, -158, -185499977, 1, -159, -263024305, 1, -160, -214068699, 1, -160, -149111373, 1, -160, -3747533, 1, -155, -82034699, 1, -160, -65174581, 1, -160])
def d2Delta198S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-1037433937322601125452613281598025537, 1, -127, -165828340326966420598710814036879, 1, -128, 93948580393126894307040526245, 1, -122, -49130599474545315575229235399, 1, -127, 573389940327047186408704533, 1, -128, 3208209658697437286709571, 1, -128, -52377081794528112916691, 1, -128, 8377950386263104927, 1, -126, 2106943668585607277, 1, -128, -5654234177202023, 1, -128, -53694475333177, 1, -128, 216615355281, 1, -128, 120562709, 1, -125, -2556805, 1, -127, -12605, 1, -128, 43, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta198Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta198Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta198Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta198Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta198Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta198Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta198El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta198Shift : polyRoundApx 128 d2Delta198Lo d2Delta198Hi d2Delta198Fq.poly = (d2Delta198S,d2Delta198Es) := by decide +kernel
theorem d2Delta198Sites : mergeSites d2Delta198Fq.plogs = [] := by decide +kernel
theorem d2Delta198PData : d2Delta198Pd = [] := by decide +kernel
theorem d2Delta198Plogs : plogsRoundM 16 24 20 128 d2Delta198Lo d2Delta198Hi (mergeSites d2Delta198Fq.plogs) d2Delta198Pd = some (d2Delta198Ap,d2Delta198Ep) := by
  rw [d2Delta198Sites,d2Delta198PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta198Poles : polesRoundM 16 24 12 128 d2Delta198Lo d2Delta198Hi d2Delta198Fq.poles d2Delta198Qd = some (d2Delta198Aq,d2Delta198Eq) := by decide +kernel
theorem d2Delta198Laurent : laurentRoundM 16 30 128 d2Delta198Lo d2Delta198Hi d2Delta198Ts d2Delta198Ld = some (d2Delta198Al,d2Delta198El) := by decide +kernel
theorem d2Delta198Small : chebPolyUB (vecAdd d2Delta198S (vecAdd d2Delta198Ap (vecAdd d2Delta198Aq d2Delta198Al))) d2Delta198Gam+d2Delta198Es+d2Delta198Ep+d2Delta198Eq+d2Delta198El ≤ (d2LitsStandaloneDelta024.q2 (-7370800626787845804691) 1 (-80)) := by decide +kernel
theorem d2Delta198Check : chebRoundPieceL d2Delta198Fq d2Delta198Ts 16 24 12 20 30 128 d2Delta198Lo d2Delta198Hi d2Delta198Pd d2Delta198Qd d2Delta198Ld d2Delta198Gam (d2LitsStandaloneDelta024.q2 (-7370800626787845804691) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta198Fq d2Delta198Ts 16 24 12 20 30 128 d2Delta198Lo d2Delta198Hi d2Delta198Pd d2Delta198Qd d2Delta198Ld d2Delta198Gam d2Delta198S d2Delta198Ap d2Delta198Aq d2Delta198Al d2Delta198Es d2Delta198Ep d2Delta198Eq d2Delta198El (by decide +kernel) d2Delta198Shift d2Delta198Plogs d2Delta198Poles d2Delta198Laurent]
  exact decide_eq_true d2Delta198Small
theorem d2Delta198Bound : ∀ x ∈ Icc ((d2Delta198Lo : ℚ) : ℝ) ((d2Delta198Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-7370800626787845804691) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta198Fq d2Delta198Ts 16 24 12 20 30 128 d2Delta198Lo d2Delta198Hi d2Delta198Pd d2Delta198Qd d2Delta198Ld d2Delta198Gam (d2LitsStandaloneDelta024.q2 (-7370800626787845804691) 1 (-80)) d2Delta198Check
  simpa only [d2Delta198Fq, d2Delta198Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta198Shift
#print axioms d2Delta198Sites
#print axioms d2Delta198PData
#print axioms d2Delta198Plogs
#print axioms d2Delta198Poles
#print axioms d2Delta198Laurent
#print axioms d2Delta198Small
#print axioms d2Delta198Check
#print axioms d2Delta198Bound

def d2Delta199Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta199Ts : List LTerm := laurentClean []
def d2Delta199Lo : ℚ := (d2LitsStandaloneDelta024.q2 (1048575) 1 (-20))
def d2Delta199Hi : ℚ := (d2LitsStandaloneDelta024.q2 (1) 1 (0))
def d2Delta199Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta199Qd : List (ℚ × ℚ) := []
def d2Delta199Ld : List LaurentPieceData := []
def d2Delta199Gam : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-265793000785427159756120326681631925905, 1, -135, 5715832732887693478349011007351, 1, -133, 386779954413030281681643483, 1, -130, 793085337408272001534037, 1, -133, 110143928886673819495, 1, -133, 9319717814892111, 1, -133, 65745142357, 1, -130, 21159749, 1, -133, 2549, 1, -135, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta199S : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [-1038253909366422335377974930674194501, 1, -127, 178619698550991495378810398361, 1, -128, 193389949670533215025506837, 1, -128, 49567830675605201456873, 1, -127, 1720998839545421861, 1, -124, 2329929416693467, 1, -127, 262980566879, 1, -127, 21159749, 1, -127, 2549, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta199Ap : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta199Aq : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta199Al : List ℚ := d2LitsStandaloneDelta024.q2listC (raw_ints% [])
def d2Delta199Es : ℚ := (d2LitsStandaloneDelta024.q2 (61) 1 (-127))
def d2Delta199Ep : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta199Eq : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
def d2Delta199El : ℚ := (d2LitsStandaloneDelta024.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta199Shift : polyRoundApx 128 d2Delta199Lo d2Delta199Hi d2Delta199Fq.poly = (d2Delta199S,d2Delta199Es) := by decide +kernel
theorem d2Delta199Sites : mergeSites d2Delta199Fq.plogs = [] := by decide +kernel
theorem d2Delta199PData : d2Delta199Pd = [] := by decide +kernel
theorem d2Delta199Plogs : plogsRoundM 16 24 20 128 d2Delta199Lo d2Delta199Hi (mergeSites d2Delta199Fq.plogs) d2Delta199Pd = some (d2Delta199Ap,d2Delta199Ep) := by
  rw [d2Delta199Sites,d2Delta199PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta199Poles : polesRoundM 16 24 12 128 d2Delta199Lo d2Delta199Hi d2Delta199Fq.poles d2Delta199Qd = some (d2Delta199Aq,d2Delta199Eq) := by decide +kernel
theorem d2Delta199Laurent : laurentRoundM 16 30 128 d2Delta199Lo d2Delta199Hi d2Delta199Ts d2Delta199Ld = some (d2Delta199Al,d2Delta199El) := by decide +kernel
theorem d2Delta199Small : chebPolyUB (vecAdd d2Delta199S (vecAdd d2Delta199Ap (vecAdd d2Delta199Aq d2Delta199Al))) d2Delta199Gam+d2Delta199Es+d2Delta199Ep+d2Delta199Eq+d2Delta199El ≤ (d2LitsStandaloneDelta024.q2 (-7377237096476310565023) 1 (-80)) := by decide +kernel
theorem d2Delta199Check : chebRoundPieceL d2Delta199Fq d2Delta199Ts 16 24 12 20 30 128 d2Delta199Lo d2Delta199Hi d2Delta199Pd d2Delta199Qd d2Delta199Ld d2Delta199Gam (d2LitsStandaloneDelta024.q2 (-7377237096476310565023) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta199Fq d2Delta199Ts 16 24 12 20 30 128 d2Delta199Lo d2Delta199Hi d2Delta199Pd d2Delta199Qd d2Delta199Ld d2Delta199Gam d2Delta199S d2Delta199Ap d2Delta199Aq d2Delta199Al d2Delta199Es d2Delta199Ep d2Delta199Eq d2Delta199El (by decide +kernel) d2Delta199Shift d2Delta199Plogs d2Delta199Poles d2Delta199Laurent]
  exact decide_eq_true d2Delta199Small
theorem d2Delta199Bound : ∀ x ∈ Icc ((d2Delta199Lo : ℚ) : ℝ) ((d2Delta199Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta024.q2 (-7377237096476310565023) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta199Fq d2Delta199Ts 16 24 12 20 30 128 d2Delta199Lo d2Delta199Hi d2Delta199Pd d2Delta199Qd d2Delta199Ld d2Delta199Gam (d2LitsStandaloneDelta024.q2 (-7377237096476310565023) 1 (-80)) d2Delta199Check
  simpa only [d2Delta199Fq, d2Delta199Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta199Shift
#print axioms d2Delta199Sites
#print axioms d2Delta199PData
#print axioms d2Delta199Plogs
#print axioms d2Delta199Poles
#print axioms d2Delta199Laurent
#print axioms d2Delta199Small
#print axioms d2Delta199Check
#print axioms d2Delta199Bound

end StandaloneDelta024
end CatalanMeasure.GenD.Signed.Data.Cells
