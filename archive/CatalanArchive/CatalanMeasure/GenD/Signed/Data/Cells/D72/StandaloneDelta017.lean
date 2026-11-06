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
namespace d2LitsStandaloneDelta017
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta017
namespace StandaloneDelta017
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta017.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta017.q2listC (raw_ints% []))⟩
def d2Delta136Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta136Ts : List LTerm := laurentClean []
def d2Delta136Lo : ℚ := (d2LitsStandaloneDelta017.q2 (124789641) 1 (-27))
def d2Delta136Hi : ℚ := (d2LitsStandaloneDelta017.q2 (126884743) 1 (-27))
def d2Delta136Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta136Qd : List (ℚ × ℚ) := []
def d2Delta136Ld : List LaurentPieceData := []
def d2Delta136Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-1114861934951495468981822548004426412153713653, 1, -157, -38293247909910379331257127672400416443325, 1, -160, -14664945779268646797669502093088230875709, 1, -159, 30674977501207140371237681727871590981439, 1, -159, 1991082473748224007056825103026933446797, 1, -157, -3145856553016951741666071034984545005427, 1, -159, -760952796456759432072446182566965147615, 1, -159, 224357734943311721239089937709864478869, 1, -160, 16768560546604170566595016589205792371, 1, -158, -610112023665304870765534302421670421, 1, -158, -1591767372453729893586160109370221647, 1, -160, -23049961062749394791862989419375931, 1, -159, 20592259753636113866504740332582807, 1, -160, 1726504793561856092442395335871965, 1, -160, -1833996129815009060659837491481, 1, -154, -2777990719180959285388561333521, 1, -157, -343773250836552090145928779615, 1, -160, 66862006781895413210402627335, 1, -159, 4874436111574800410011468523, 1, -159, -169518994557387497758127115, 1, -160, -57332506254679585631978641, 1, -160, -1275388412388406901889429, 1, -159, 81617012535973153332379, 1, -160, 6976989917250206665233, 1, -159, 535578456335663776617, 1, -160, -11362711855222935527, 1, -160, -2151065856709593431, 1, -160, -47704637576646691, 1, -159, -419522578166493, 1, -160, 185879941070653, 1, -160, 11657780458967, 1, -160, 161753931631, 1, -159])
def d2Delta136S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-1038290633641684366675704328385791491, 1, -127, -29731730085964875028339527624807, 1, -127, -50224089140054884371170349874873, 1, -128, 89425636938121406578091779514363, 1, -128, 24664543226286684294299786986411, 1, -127, -14760041488309835088109085885283, 1, -127, -15769541154243190577382637059259, 1, -128, 909022559438379388611125742679, 1, -126, 1253609394074720999415673822929, 1, -127, -108175819258951504622441964373, 1, -128, -220272378563767282726086150321, 1, -128, -16833310607483167817573958819, 1, -128, 1322884196757890848069487673, 1, -125, 1979715266381640310591702731, 1, -128, -210787046941593297841763021, 1, -128, -23384577604372979285524539, 1, -126, -252288762665307880762885, 1, -124, 65061762867288195917151, 1, -123, 333000111321809037653865, 1, -128, -6880150291982026135409, 1, -128, -7200782991968492166921, 1, -128, -701812294388333145171, 1, -128, 33262325608538511665, 1, -128, 867102207466166489, 1, -124, 1154924625221260845, 1, -128, -34053810189900577, 1, -128, -16676493822949989, 1, -128, -1572758307032469, 1, -128, -1503848006857, 1, -124, 5485496675321, 1, -127, 365642793161, 1, -126, 86077844801, 1, -128, -183216151, 1, -127, -610654383, 1, -128, -34255585, 1, -127, -2202605, 1, -127, -69025, 1, -127, 3273, 1, -127, 1427, 1, -128, 17, 1, -125, 9, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta136Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta136Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta136Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta136Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta136Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta136Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta136El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta136Shift : polyRoundApx 128 d2Delta136Lo d2Delta136Hi d2Delta136Fq.poly = (d2Delta136S,d2Delta136Es) := by decide +kernel
theorem d2Delta136Sites : mergeSites d2Delta136Fq.plogs = [] := by decide +kernel
theorem d2Delta136PData : d2Delta136Pd = [] := by decide +kernel
theorem d2Delta136Plogs : plogsRoundM 16 24 20 128 d2Delta136Lo d2Delta136Hi (mergeSites d2Delta136Fq.plogs) d2Delta136Pd = some (d2Delta136Ap,d2Delta136Ep) := by
  rw [d2Delta136Sites,d2Delta136PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta136Poles : polesRoundM 16 24 12 128 d2Delta136Lo d2Delta136Hi d2Delta136Fq.poles d2Delta136Qd = some (d2Delta136Aq,d2Delta136Eq) := by decide +kernel
theorem d2Delta136Laurent : laurentRoundM 16 30 128 d2Delta136Lo d2Delta136Hi d2Delta136Ts d2Delta136Ld = some (d2Delta136Al,d2Delta136El) := by decide +kernel
theorem d2Delta136Small : chebPolyUB (vecAdd d2Delta136S (vecAdd d2Delta136Ap (vecAdd d2Delta136Aq d2Delta136Al))) d2Delta136Gam+d2Delta136Es+d2Delta136Ep+d2Delta136Eq+d2Delta136El ≤ (d2LitsStandaloneDelta017.q2 (-7377410858467140272573) 1 (-80)) := by decide +kernel
theorem d2Delta136Check : chebRoundPieceL d2Delta136Fq d2Delta136Ts 16 24 12 20 30 128 d2Delta136Lo d2Delta136Hi d2Delta136Pd d2Delta136Qd d2Delta136Ld d2Delta136Gam (d2LitsStandaloneDelta017.q2 (-7377410858467140272573) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta136Fq d2Delta136Ts 16 24 12 20 30 128 d2Delta136Lo d2Delta136Hi d2Delta136Pd d2Delta136Qd d2Delta136Ld d2Delta136Gam d2Delta136S d2Delta136Ap d2Delta136Aq d2Delta136Al d2Delta136Es d2Delta136Ep d2Delta136Eq d2Delta136El (by decide +kernel) d2Delta136Shift d2Delta136Plogs d2Delta136Poles d2Delta136Laurent]
  exact decide_eq_true d2Delta136Small
theorem d2Delta136Bound : ∀ x ∈ Icc ((d2Delta136Lo : ℚ) : ℝ) ((d2Delta136Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-7377410858467140272573) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta136Fq d2Delta136Ts 16 24 12 20 30 128 d2Delta136Lo d2Delta136Hi d2Delta136Pd d2Delta136Qd d2Delta136Ld d2Delta136Gam (d2LitsStandaloneDelta017.q2 (-7377410858467140272573) 1 (-80)) d2Delta136Check
  simpa only [d2Delta136Fq, d2Delta136Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta136Shift
#print axioms d2Delta136Sites
#print axioms d2Delta136PData
#print axioms d2Delta136Plogs
#print axioms d2Delta136Poles
#print axioms d2Delta136Laurent
#print axioms d2Delta136Small
#print axioms d2Delta136Check
#print axioms d2Delta136Bound

def d2Delta137Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta137Ts : List LTerm := laurentClean []
def d2Delta137Lo : ℚ := (d2LitsStandaloneDelta017.q2 (126884743) 1 (-27))
def d2Delta137Hi : ℚ := (d2LitsStandaloneDelta017.q2 (508586523) 1 (-29))
def d2Delta137Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta137Qd : List (ℚ × ℚ) := []
def d2Delta137Ld : List LaurentPieceData := []
def d2Delta137Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-4459413654280143037174152907907897840657919683, 1, -159, 34354219268818750099618756197518604249959, 1, -159, 300083106631296381776514572504527890709, 1, -157, -68802329881413415373583872473929365289, 1, -158, -555534466394781085744064450144026143, 1, -156, 94839411935606858427176382442007953, 1, -158, 1608248405369117804745483098133967, 1, -157, -51403333386777034341172311476903, 1, -158, -586112379849228728084437640763, 1, -156, 5655437142799733036431834299, 1, -158, 462487992902366433941426993, 1, -157, 5687498986437964029482663, 1, -158, -47491469377578643706693, 1, -156, -2767217928259449316847, 1, -158, 6214527538176340635, 1, -157, 135675512029305855, 1, -156, 1365348760677217, 1, -157, -21975026711043, 1, -157, -329905146215, 1, -157, -1210515461, 1, -158, 11643313, 1, -156, 16557, 1, -158, -79029, 1, -157, -92655, 1, -158, -6557, 1, -156, -14789, 1, -158, -1675, 1, -157, -1829, 1, -158, -77, 1, -156, -163, 1, -158, -9, 1, -157, -37, 1, -160])
def d2Delta137S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-2076576863910668984935048917860092535, 1, -128, 4047525855942504334607133274153, 1, -126, 1134506893773618069331377308785, 1, -128, -129038927624204968085735496241, 1, -127, -8350177786136753251715008315, 1, -127, 88661338694091786135860825, 1, -124, 12052375086891445077375953, 1, -125, -3066896297882590689005427, 1, -128, -280584042074757328950257, 1, -128, 666701154172351995219, 1, -127, 442150369839688601923, 1, -128, 682296953453242409, 1, -125, -90665626491774615, 1, -126, -330849133519159, 1, -123, 94492147857885, 1, -128, 4146186941273, 1, -127, 41848481893, 1, -127, -670272709, 1, -126, -40329223, 1, -127, -74387, 1, -126, 23113, 1, -128, 477, 1, -128, 1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta137Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta137Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta137Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta137Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta137Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta137Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta137El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta137Shift : polyRoundApx 128 d2Delta137Lo d2Delta137Hi d2Delta137Fq.poly = (d2Delta137S,d2Delta137Es) := by decide +kernel
theorem d2Delta137Sites : mergeSites d2Delta137Fq.plogs = [] := by decide +kernel
theorem d2Delta137PData : d2Delta137Pd = [] := by decide +kernel
theorem d2Delta137Plogs : plogsRoundM 16 24 20 128 d2Delta137Lo d2Delta137Hi (mergeSites d2Delta137Fq.plogs) d2Delta137Pd = some (d2Delta137Ap,d2Delta137Ep) := by
  rw [d2Delta137Sites,d2Delta137PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta137Poles : polesRoundM 16 24 12 128 d2Delta137Lo d2Delta137Hi d2Delta137Fq.poles d2Delta137Qd = some (d2Delta137Aq,d2Delta137Eq) := by decide +kernel
theorem d2Delta137Laurent : laurentRoundM 16 30 128 d2Delta137Lo d2Delta137Hi d2Delta137Ts d2Delta137Ld = some (d2Delta137Al,d2Delta137El) := by decide +kernel
theorem d2Delta137Small : chebPolyUB (vecAdd d2Delta137S (vecAdd d2Delta137Ap (vecAdd d2Delta137Aq d2Delta137Al))) d2Delta137Gam+d2Delta137Es+d2Delta137Ep+d2Delta137Eq+d2Delta137El ≤ (d2LitsStandaloneDelta017.q2 (-7377421980952999203363) 1 (-80)) := by decide +kernel
theorem d2Delta137Check : chebRoundPieceL d2Delta137Fq d2Delta137Ts 16 24 12 20 30 128 d2Delta137Lo d2Delta137Hi d2Delta137Pd d2Delta137Qd d2Delta137Ld d2Delta137Gam (d2LitsStandaloneDelta017.q2 (-7377421980952999203363) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta137Fq d2Delta137Ts 16 24 12 20 30 128 d2Delta137Lo d2Delta137Hi d2Delta137Pd d2Delta137Qd d2Delta137Ld d2Delta137Gam d2Delta137S d2Delta137Ap d2Delta137Aq d2Delta137Al d2Delta137Es d2Delta137Ep d2Delta137Eq d2Delta137El (by decide +kernel) d2Delta137Shift d2Delta137Plogs d2Delta137Poles d2Delta137Laurent]
  exact decide_eq_true d2Delta137Small
theorem d2Delta137Bound : ∀ x ∈ Icc ((d2Delta137Lo : ℚ) : ℝ) ((d2Delta137Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-7377421980952999203363) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta137Fq d2Delta137Ts 16 24 12 20 30 128 d2Delta137Lo d2Delta137Hi d2Delta137Pd d2Delta137Qd d2Delta137Ld d2Delta137Gam (d2LitsStandaloneDelta017.q2 (-7377421980952999203363) 1 (-80)) d2Delta137Check
  simpa only [d2Delta137Fq, d2Delta137Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta137Shift
#print axioms d2Delta137Sites
#print axioms d2Delta137PData
#print axioms d2Delta137Plogs
#print axioms d2Delta137Poles
#print axioms d2Delta137Laurent
#print axioms d2Delta137Small
#print axioms d2Delta137Check
#print axioms d2Delta137Bound

def d2Delta138Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta138Ts : List LTerm := laurentClean []
def d2Delta138Lo : ℚ := (d2LitsStandaloneDelta017.q2 (508586523) 1 (-29))
def d2Delta138Hi : ℚ := (d2LitsStandaloneDelta017.q2 (254817037) 1 (-28))
def d2Delta138Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta138Qd : List (ℚ × ℚ) := []
def d2Delta138Ld : List LaurentPieceData := []
def d2Delta138Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-4459341204756001802881697507739608223337045699, 1, -159, 36479758729539788667386976954171207492135, 1, -159, -182150144551553527277508521008004215019, 1, -157, -85624807836367583951009804575036796629, 1, -158, 71992870913053327410064891596272609, 1, -156, 146738571398182778362554221583452565, 1, -158, 405183719552999405803470426480591, 1, -157, -115718428775735552506739468867983, 1, -158, -360635859865688242177055399483, 1, -156, 44501202217237006559273217427, 1, -158, 464415668158057600621682737, 1, -157, -6392989694668954867041997, 1, -158, -74745591092989064394309, 1, -156, -1094313908890574558131, 1, -158, 23896311786487815579, 1, -157, 146748518245318611, 1, -156, -939373554313375, 1, -157, -45272492413915, 1, -157, -282882861671, 1, -157, 4219484015, 1, -158, 21650097, 1, -156, -135023, 1, -158, -80821, 1, -157, -105671, 1, -158, -6557, 1, -156, -16349, 1, -158, -1675, 1, -157, -1945, 1, -158, -77, 1, -156, -167, 1, -158, -9, 1, -157, -37, 1, -160])
def d2Delta138S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-1038271113201301603388626462431655773, 1, -127, 17227128419620516298519526944137, 1, -128, -680694093232671494195698013475, 1, -128, -160858262491876146618484161221, 1, -127, 2109113199083646607855368711, 1, -128, 2198663390042388618572889881, 1, -128, 24495730674819618526455233, 1, -128, -6921244902387859361050161, 1, -128, -173073757637891783858297, 1, -128, 2656665671584978466081, 1, -126, 111153460190437351373, 1, -126, -1520803152169854819, 1, -126, -571540176739828651, 1, -128, -2104052729881489, 1, -127, 364857536916451, 1, -128, 8980315840617, 1, -128, -1781986727, 1, -123, -5531317939, 1, -128, -34638105, 1, -127, 257151, 1, -126, 5337, 1, -125, 403, 1, -128, -3, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta138Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta138Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta138Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta138Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta138Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta138Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta138El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta138Shift : polyRoundApx 128 d2Delta138Lo d2Delta138Hi d2Delta138Fq.poly = (d2Delta138S,d2Delta138Es) := by decide +kernel
theorem d2Delta138Sites : mergeSites d2Delta138Fq.plogs = [] := by decide +kernel
theorem d2Delta138PData : d2Delta138Pd = [] := by decide +kernel
theorem d2Delta138Plogs : plogsRoundM 16 24 20 128 d2Delta138Lo d2Delta138Hi (mergeSites d2Delta138Fq.plogs) d2Delta138Pd = some (d2Delta138Ap,d2Delta138Ep) := by
  rw [d2Delta138Sites,d2Delta138PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta138Poles : polesRoundM 16 24 12 128 d2Delta138Lo d2Delta138Hi d2Delta138Fq.poles d2Delta138Qd = some (d2Delta138Aq,d2Delta138Eq) := by decide +kernel
theorem d2Delta138Laurent : laurentRoundM 16 30 128 d2Delta138Lo d2Delta138Hi d2Delta138Ts d2Delta138Ld = some (d2Delta138Al,d2Delta138El) := by decide +kernel
theorem d2Delta138Small : chebPolyUB (vecAdd d2Delta138S (vecAdd d2Delta138Ap (vecAdd d2Delta138Aq d2Delta138Al))) d2Delta138Gam+d2Delta138Es+d2Delta138Ep+d2Delta138Eq+d2Delta138El ≤ (d2LitsStandaloneDelta017.q2 (-7377299337849035424655) 1 (-80)) := by decide +kernel
theorem d2Delta138Check : chebRoundPieceL d2Delta138Fq d2Delta138Ts 16 24 12 20 30 128 d2Delta138Lo d2Delta138Hi d2Delta138Pd d2Delta138Qd d2Delta138Ld d2Delta138Gam (d2LitsStandaloneDelta017.q2 (-7377299337849035424655) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta138Fq d2Delta138Ts 16 24 12 20 30 128 d2Delta138Lo d2Delta138Hi d2Delta138Pd d2Delta138Qd d2Delta138Ld d2Delta138Gam d2Delta138S d2Delta138Ap d2Delta138Aq d2Delta138Al d2Delta138Es d2Delta138Ep d2Delta138Eq d2Delta138El (by decide +kernel) d2Delta138Shift d2Delta138Plogs d2Delta138Poles d2Delta138Laurent]
  exact decide_eq_true d2Delta138Small
theorem d2Delta138Bound : ∀ x ∈ Icc ((d2Delta138Lo : ℚ) : ℝ) ((d2Delta138Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-7377299337849035424655) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta138Fq d2Delta138Ts 16 24 12 20 30 128 d2Delta138Lo d2Delta138Hi d2Delta138Pd d2Delta138Qd d2Delta138Ld d2Delta138Gam (d2LitsStandaloneDelta017.q2 (-7377299337849035424655) 1 (-80)) d2Delta138Check
  simpa only [d2Delta138Fq, d2Delta138Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta138Shift
#print axioms d2Delta138Sites
#print axioms d2Delta138PData
#print axioms d2Delta138Plogs
#print axioms d2Delta138Poles
#print axioms d2Delta138Laurent
#print axioms d2Delta138Small
#print axioms d2Delta138Check
#print axioms d2Delta138Bound

def d2Delta139Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta139Ts : List LTerm := laurentClean []
def d2Delta139Lo : ℚ := (d2LitsStandaloneDelta017.q2 (254817037) 1 (-28))
def d2Delta139Hi : ℚ := (d2LitsStandaloneDelta017.q2 (63966147) 1 (-26))
def d2Delta139Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta139Qd : List (ℚ × ℚ) := []
def d2Delta139Ld : List LaurentPieceData := []
def d2Delta139Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-4459271740755349726108303835879275009035121539, 1, -159, 11306893987456236242803114835189051305469, 1, -158, -2956753938423768042036216483319176270315, 1, -157, -216124172300350906503592227118961422761, 1, -158, 16355655083299635164943308002025027179, 1, -156, 2486293764879401171486715858134727777, 1, -158, -141661738515956223120593393371885937, 1, -157, -13550330277990389467320385126488869, 1, -158, 130218776575010468915993507650665, 1, -156, 37039489579826178091112136155181, 1, -158, -103772936186556198937930547471, 1, -157, -53516435873235912971580039529, 1, -158, -180266209768488256143514903, 1, -156, 37652716242309136238388689, 1, -158, 629903368935897279926811, 1, -157, -3568606439730671122277, 1, -158, -416588717482508542703, 1, -157, -13222020253819746775, 1, -158, 77898784342227481, 1, -157, 8462877831288891, 1, -158, 23871711190779, 1, -156, -1160045487363, 1, -158, -25541723765, 1, -157, -610971601, 1, -158, 488319, 1, -156, 175625, 1, -158, -331, 1, -157, -565, 1, -158, -79, 1, -156, -35, 1, -158, -9, 1, -157, -1, 1, -158])
def d2Delta139S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-2076504650677864554671354408980488811, 1, -128, 11145875937713504259059304047953, 1, -128, -11506968380208955985778445812791, 1, -128, -426073483899530097302297938661, 1, -127, 250089872624168636557815931045, 1, -127, 601203709529639520200173983, 1, -122, -4284048987293847978770398225, 1, -127, -827672856021046508003886335, 1, -128, 62335892011269775018569043, 1, -128, 8971838657848525871948125, 1, -128, -46285753070102805895, 1, -117, -51504360675996398202513, 1, -128, -704563969331002536271, 1, -127, 17978985923422477461, 1, -125, 4856714374246409031, 1, -127, -51003183540225069, 1, -128, -12755821244976061, 1, -127, -816835533383911, 1, -128, 18783832078147, 1, -128, 2072045398295, 1, -128, 47173423461, 1, -128, -559542965, 1, -127, -24965807, 1, -126, -601039, 1, -126, 931, 1, -124, 2833, 1, -128, 91, 1, -128, 1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta139Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta139Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta139Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta139Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta139Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta139Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta139El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta139Shift : polyRoundApx 128 d2Delta139Lo d2Delta139Hi d2Delta139Fq.poly = (d2Delta139S,d2Delta139Es) := by decide +kernel
theorem d2Delta139Sites : mergeSites d2Delta139Fq.plogs = [] := by decide +kernel
theorem d2Delta139PData : d2Delta139Pd = [] := by decide +kernel
theorem d2Delta139Plogs : plogsRoundM 16 24 20 128 d2Delta139Lo d2Delta139Hi (mergeSites d2Delta139Fq.plogs) d2Delta139Pd = some (d2Delta139Ap,d2Delta139Ep) := by
  rw [d2Delta139Sites,d2Delta139PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta139Poles : polesRoundM 16 24 12 128 d2Delta139Lo d2Delta139Hi d2Delta139Fq.poles d2Delta139Qd = some (d2Delta139Aq,d2Delta139Eq) := by decide +kernel
theorem d2Delta139Laurent : laurentRoundM 16 30 128 d2Delta139Lo d2Delta139Hi d2Delta139Ts d2Delta139Ld = some (d2Delta139Al,d2Delta139El) := by decide +kernel
theorem d2Delta139Small : chebPolyUB (vecAdd d2Delta139S (vecAdd d2Delta139Ap (vecAdd d2Delta139Aq d2Delta139Al))) d2Delta139Gam+d2Delta139Es+d2Delta139Ep+d2Delta139Eq+d2Delta139El ≤ (d2LitsStandaloneDelta017.q2 (-7377188341815812874385) 1 (-80)) := by decide +kernel
theorem d2Delta139Check : chebRoundPieceL d2Delta139Fq d2Delta139Ts 16 24 12 20 30 128 d2Delta139Lo d2Delta139Hi d2Delta139Pd d2Delta139Qd d2Delta139Ld d2Delta139Gam (d2LitsStandaloneDelta017.q2 (-7377188341815812874385) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta139Fq d2Delta139Ts 16 24 12 20 30 128 d2Delta139Lo d2Delta139Hi d2Delta139Pd d2Delta139Qd d2Delta139Ld d2Delta139Gam d2Delta139S d2Delta139Ap d2Delta139Aq d2Delta139Al d2Delta139Es d2Delta139Ep d2Delta139Eq d2Delta139El (by decide +kernel) d2Delta139Shift d2Delta139Plogs d2Delta139Poles d2Delta139Laurent]
  exact decide_eq_true d2Delta139Small
theorem d2Delta139Bound : ∀ x ∈ Icc ((d2Delta139Lo : ℚ) : ℝ) ((d2Delta139Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-7377188341815812874385) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta139Fq d2Delta139Ts 16 24 12 20 30 128 d2Delta139Lo d2Delta139Hi d2Delta139Pd d2Delta139Qd d2Delta139Ld d2Delta139Gam (d2LitsStandaloneDelta017.q2 (-7377188341815812874385) 1 (-80)) d2Delta139Check
  simpa only [d2Delta139Fq, d2Delta139Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta139Shift
#print axioms d2Delta139Sites
#print axioms d2Delta139PData
#print axioms d2Delta139Plogs
#print axioms d2Delta139Poles
#print axioms d2Delta139Laurent
#print axioms d2Delta139Small
#print axioms d2Delta139Check
#print axioms d2Delta139Bound

def d2Delta140Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta140Ts : List LTerm := laurentClean []
def d2Delta140Lo : ℚ := (d2LitsStandaloneDelta017.q2 (63966147) 1 (-26))
def d2Delta140Hi : ℚ := (d2LitsStandaloneDelta017.q2 (256912139) 1 (-28))
def d2Delta140Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta140Qd : List (ℚ × ℚ) := []
def d2Delta140Ld : List LaurentPieceData := []
def d2Delta140Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-139353469738654219296286825299999020040092371, 1, -154, -864176747865678932720817273192589993801, 1, -153, -1010812618280049742459301611848901836499, 1, -157, 194536008006764482523769456337263274165, 1, -156, 7696418469229027551891208954525533589, 1, -156, -1482090459875472070851548216968177959, 1, -156, -134251646798764780853451174002536137, 1, -157, 2249328000582026977680602194801543, 1, -155, 138892285641287251610210998545577, 1, -155, -2397016658868225126184218556913, 1, -155, -1174965630195620003170227701367, 1, -157, -4335083530398840128167466021, 1, -156, 627722935494971526402492935, 1, -156, 16660463820462819677080447, 1, -156, -446712389515632918660925, 1, -157, -4248202112856201841079, 1, -154, -46819750634693574693, 1, -154, 1544916608184280697, 1, -154, 438036392547467857, 1, -157, 1507640626051405, 1, -156, -60423961386891, 1, -156, -1766955438079, 1, -156, -29820389101, 1, -157, 122253713, 1, -155, 4542791, 1, -155, 59513, 1, -155, -19, 1, -157, -53, 1, -156, -17, 1, -156, -1, 1, -156, -1, 1, -157, 0, 1, 0])
def d2Delta140S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-2076526603789944469369286122643893243, 1, -128, -13978153454019702072882351314413, 1, -127, -1999737973102760611907084172189, 1, -127, 3010177389848375247328083335241, 1, -128, 241540626917670705082895807721, 1, -128, -90224156018682443182394006425, 1, -128, -8269397287211507712576213153, 1, -128, 1082803952851842610323358565, 1, -128, 33818881899461214501965995, 1, -126, -4525432386357812229063751, 1, -128, -1134934659092748501588201, 1, -128, -17369085852131666563817, 1, -128, 4812853435394568423571, 1, -128, 258119053951433556827, 1, -128, -6723941497113878835, 1, -128, -1043556636726054867, 1, -128, -23343699385141191, 1, -128, 1501632565079287, 1, -128, 53765514028627, 1, -127, 1508596404457, 1, -128, -3667825177, 1, -123, -3462004435, 1, -127, -118189189, 1, -128, 3773711, 1, -128, 283797, 1, -128, 7505, 1, -128, 33, 1, -128, -3, 1, -127, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta140Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta140Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta140Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta140Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta140Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta140Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta140El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta140Shift : polyRoundApx 128 d2Delta140Lo d2Delta140Hi d2Delta140Fq.poly = (d2Delta140S,d2Delta140Es) := by decide +kernel
theorem d2Delta140Sites : mergeSites d2Delta140Fq.plogs = [] := by decide +kernel
theorem d2Delta140PData : d2Delta140Pd = [] := by decide +kernel
theorem d2Delta140Plogs : plogsRoundM 16 24 20 128 d2Delta140Lo d2Delta140Hi (mergeSites d2Delta140Fq.plogs) d2Delta140Pd = some (d2Delta140Ap,d2Delta140Ep) := by
  rw [d2Delta140Sites,d2Delta140PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta140Poles : polesRoundM 16 24 12 128 d2Delta140Lo d2Delta140Hi d2Delta140Fq.poles d2Delta140Qd = some (d2Delta140Aq,d2Delta140Eq) := by decide +kernel
theorem d2Delta140Laurent : laurentRoundM 16 30 128 d2Delta140Lo d2Delta140Hi d2Delta140Ts d2Delta140Ld = some (d2Delta140Al,d2Delta140El) := by decide +kernel
theorem d2Delta140Small : chebPolyUB (vecAdd d2Delta140S (vecAdd d2Delta140Ap (vecAdd d2Delta140Aq d2Delta140Al))) d2Delta140Gam+d2Delta140Es+d2Delta140Ep+d2Delta140Eq+d2Delta140El ≤ (d2LitsStandaloneDelta017.q2 (-3688605188533968634093) 1 (-79)) := by decide +kernel
theorem d2Delta140Check : chebRoundPieceL d2Delta140Fq d2Delta140Ts 16 24 12 20 30 128 d2Delta140Lo d2Delta140Hi d2Delta140Pd d2Delta140Qd d2Delta140Ld d2Delta140Gam (d2LitsStandaloneDelta017.q2 (-3688605188533968634093) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta140Fq d2Delta140Ts 16 24 12 20 30 128 d2Delta140Lo d2Delta140Hi d2Delta140Pd d2Delta140Qd d2Delta140Ld d2Delta140Gam d2Delta140S d2Delta140Ap d2Delta140Aq d2Delta140Al d2Delta140Es d2Delta140Ep d2Delta140Eq d2Delta140El (by decide +kernel) d2Delta140Shift d2Delta140Plogs d2Delta140Poles d2Delta140Laurent]
  exact decide_eq_true d2Delta140Small
theorem d2Delta140Bound : ∀ x ∈ Icc ((d2Delta140Lo : ℚ) : ℝ) ((d2Delta140Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-3688605188533968634093) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta140Fq d2Delta140Ts 16 24 12 20 30 128 d2Delta140Lo d2Delta140Hi d2Delta140Pd d2Delta140Qd d2Delta140Ld d2Delta140Gam (d2LitsStandaloneDelta017.q2 (-3688605188533968634093) 1 (-79)) d2Delta140Check
  simpa only [d2Delta140Fq, d2Delta140Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta140Shift
#print axioms d2Delta140Sites
#print axioms d2Delta140PData
#print axioms d2Delta140Plogs
#print axioms d2Delta140Poles
#print axioms d2Delta140Laurent
#print axioms d2Delta140Small
#print axioms d2Delta140Check
#print axioms d2Delta140Bound

def d2Delta141Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta141Ts : List LTerm := laurentClean []
def d2Delta141Lo : ℚ := (d2LitsStandaloneDelta017.q2 (256912139) 1 (-28))
def d2Delta141Hi : ℚ := (d2LitsStandaloneDelta017.q2 (514871829) 1 (-29))
def d2Delta141Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta141Qd : List (ℚ × ℚ) := []
def d2Delta141Ld : List LaurentPieceData := []
def d2Delta141Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-69677984488222516368717507123677180820147547, 1, -153, -311045097369448267991037737324631547259, 1, -153, 603584943323615456477051868131948039, 1, -147, 17490127933111399822390536591119040197, 1, -156, -568374059872144456160097412307706427, 1, -155, -48325970728688743989724443842885275, 1, -156, 18659838115426963778775702192845, 1, -150, 30694344904983146755682488036657, 1, -155, -74733927342397493902171616671, 1, -154, -19751346063287674970172533679, 1, -155, -4095961759068523692976881, 1, -150, 12603836918350728662018231, 1, -156, 107497661971519027429847, 1, -155, -1193312627904525791273, 1, -156, -122167960249545339, 1, -147, -104046346248726557, 1, -154, 827282440543395, 1, -153, 33593273651107, 1, -154, 251424863, 1, -145, -10997626523, 1, -156, -86880155, 1, -155, -797179, 1, -156, -27, 1, -150, -2465, 1, -155, -241, 1, -154, -257, 1, -155, -1, 1, -150, -33, 1, -156, -1, 1, -155, -1, 1, -156, 0, 1, 0, 0, 1, 0])
def d2Delta141S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-2076566912528923752523521968614474169, 1, -128, -9466235424149987636996715571937, 1, -128, 2336451681731885846693535293805, 1, -128, 264236605378780758848397081703, 1, -128, -34091456626806731765116992333, 1, -128, -726532326649999525785526807, 1, -126, 142647257567652661926325719, 1, -128, 3680275010698986937317693, 1, -126, -141288123586858261777189, 1, -128, -37804996283933040769309, 1, -128, -504925375263845078077, 1, -128, 48138856759708098417, 1, -128, 411742614554513405, 1, -126, -9056502147065945, 1, -127, -59753244540403, 1, -123, -25541467193527, 1, -128, 50422374395, 1, -124, 16428454905, 1, -127, 126561025, 1, -127, -10724035, 1, -128, -169787, 1, -127, -2987, 1, -128, 29, 1, -127, 1, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta141Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta141Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta141Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta141Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta141Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta141Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta141El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta141Shift : polyRoundApx 128 d2Delta141Lo d2Delta141Hi d2Delta141Fq.poly = (d2Delta141S,d2Delta141Es) := by decide +kernel
theorem d2Delta141Sites : mergeSites d2Delta141Fq.plogs = [] := by decide +kernel
theorem d2Delta141PData : d2Delta141Pd = [] := by decide +kernel
theorem d2Delta141Plogs : plogsRoundM 16 24 20 128 d2Delta141Lo d2Delta141Hi (mergeSites d2Delta141Fq.plogs) d2Delta141Pd = some (d2Delta141Ap,d2Delta141Ep) := by
  rw [d2Delta141Sites,d2Delta141PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta141Poles : polesRoundM 16 24 12 128 d2Delta141Lo d2Delta141Hi d2Delta141Fq.poles d2Delta141Qd = some (d2Delta141Aq,d2Delta141Eq) := by decide +kernel
theorem d2Delta141Laurent : laurentRoundM 16 30 128 d2Delta141Lo d2Delta141Hi d2Delta141Ts d2Delta141Ld = some (d2Delta141Al,d2Delta141El) := by decide +kernel
theorem d2Delta141Small : chebPolyUB (vecAdd d2Delta141S (vecAdd d2Delta141Ap (vecAdd d2Delta141Aq d2Delta141Al))) d2Delta141Gam+d2Delta141Es+d2Delta141Ep+d2Delta141Eq+d2Delta141El ≤ (d2LitsStandaloneDelta017.q2 (-1844351574890648080235) 1 (-78)) := by decide +kernel
theorem d2Delta141Check : chebRoundPieceL d2Delta141Fq d2Delta141Ts 16 24 12 20 30 128 d2Delta141Lo d2Delta141Hi d2Delta141Pd d2Delta141Qd d2Delta141Ld d2Delta141Gam (d2LitsStandaloneDelta017.q2 (-1844351574890648080235) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta141Fq d2Delta141Ts 16 24 12 20 30 128 d2Delta141Lo d2Delta141Hi d2Delta141Pd d2Delta141Qd d2Delta141Ld d2Delta141Gam d2Delta141S d2Delta141Ap d2Delta141Aq d2Delta141Al d2Delta141Es d2Delta141Ep d2Delta141Eq d2Delta141El (by decide +kernel) d2Delta141Shift d2Delta141Plogs d2Delta141Poles d2Delta141Laurent]
  exact decide_eq_true d2Delta141Small
theorem d2Delta141Bound : ∀ x ∈ Icc ((d2Delta141Lo : ℚ) : ℝ) ((d2Delta141Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-1844351574890648080235) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta141Fq d2Delta141Ts 16 24 12 20 30 128 d2Delta141Lo d2Delta141Hi d2Delta141Pd d2Delta141Qd d2Delta141Ld d2Delta141Gam (d2LitsStandaloneDelta017.q2 (-1844351574890648080235) 1 (-78)) d2Delta141Check
  simpa only [d2Delta141Fq, d2Delta141Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta141Shift
#print axioms d2Delta141Sites
#print axioms d2Delta141PData
#print axioms d2Delta141Plogs
#print axioms d2Delta141Poles
#print axioms d2Delta141Laurent
#print axioms d2Delta141Small
#print axioms d2Delta141Check
#print axioms d2Delta141Bound

def d2Delta142Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta142Ts : List LTerm := laurentClean []
def d2Delta142Lo : ℚ := (d2LitsStandaloneDelta017.q2 (514871829) 1 (-29))
def d2Delta142Hi : ℚ := (d2LitsStandaloneDelta017.q2 (128979845) 1 (-27))
def d2Delta142Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta142Qd : List (ℚ × ℚ) := []
def d2Delta142Ld : List LaurentPieceData := []
def d2Delta142Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-69678246792194858073623888561233667954869851, 1, -153, 28354894037711576826356065375405113613, 1, -152, 46930029407548671763426077940659777, 1, -143, -395315840330543947801072895402181101, 1, -152, -844376547149948198785829855227149883, 1, -155, -368786623960780783938023975969799, 1, -154, 39970224516149306653805203466885, 1, -150, 7074702477728129537441798923303, 1, -154, -437738417217726148804059413919, 1, -154, -9055000693893264683346028181, 1, -154, 7505066644315809419576843, 1, -150, 4966118873596767273070005, 1, -154, 26864688902475009121239, 1, -155, -634021706214666560719, 1, -153, -268412686504895125, 1, -148, 39100034140984239, 1, -153, 2012974714968483, 1, -153, 15971222312007, 1, -153, -3493044715, 1, -148, -3293273959, 1, -153, -95628699, 1, -155, 145011, 1, -154, 241, 1, -150, -403, 1, -154, -241, 1, -154, -31, 1, -154, -1, 1, -150, -1, 1, -154, -1, 1, -155, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta142S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-1038287506400929226224458749791705439, 1, -127, 1760743151563793966767563193813, 1, -128, 728720546067551668019376781723, 1, -126, -94134814169669803126650576787, 1, -128, -25393615716666480202576202153, 1, -127, -49895573728749694069675309, 1, -127, 38327556903599250025092147, 1, -125, 3412445159460799069934893, 1, -127, -837208745811638412602991, 1, -128, -8687696882056972241543, 1, -126, 914905960239389660547, 1, -128, 38014301008869510489, 1, -127, 208637405991191789, 1, -127, -77466589838999529, 1, -128, -2104840975198963, 1, -128, 18958995465983, 1, -128, 1967756486151, 1, -128, 31316032013, 1, -128, -217380391, 1, -127, -25740789, 1, -128, -374485, 1, -128, 2313, 1, -128, 3, 1, -122, 3, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta142Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta142Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta142Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta142Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta142Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta142Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta142El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta142Shift : polyRoundApx 128 d2Delta142Lo d2Delta142Hi d2Delta142Fq.poly = (d2Delta142S,d2Delta142Es) := by decide +kernel
theorem d2Delta142Sites : mergeSites d2Delta142Fq.plogs = [] := by decide +kernel
theorem d2Delta142PData : d2Delta142Pd = [] := by decide +kernel
theorem d2Delta142Plogs : plogsRoundM 16 24 20 128 d2Delta142Lo d2Delta142Hi (mergeSites d2Delta142Fq.plogs) d2Delta142Pd = some (d2Delta142Ap,d2Delta142Ep) := by
  rw [d2Delta142Sites,d2Delta142PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta142Poles : polesRoundM 16 24 12 128 d2Delta142Lo d2Delta142Hi d2Delta142Fq.poles d2Delta142Qd = some (d2Delta142Aq,d2Delta142Eq) := by decide +kernel
theorem d2Delta142Laurent : laurentRoundM 16 30 128 d2Delta142Lo d2Delta142Hi d2Delta142Ts d2Delta142Ld = some (d2Delta142Al,d2Delta142El) := by decide +kernel
theorem d2Delta142Small : chebPolyUB (vecAdd d2Delta142S (vecAdd d2Delta142Ap (vecAdd d2Delta142Aq d2Delta142Al))) d2Delta142Gam+d2Delta142Es+d2Delta142Ep+d2Delta142Eq+d2Delta142El ≤ (d2LitsStandaloneDelta017.q2 (-3688730071913094595929) 1 (-79)) := by decide +kernel
theorem d2Delta142Check : chebRoundPieceL d2Delta142Fq d2Delta142Ts 16 24 12 20 30 128 d2Delta142Lo d2Delta142Hi d2Delta142Pd d2Delta142Qd d2Delta142Ld d2Delta142Gam (d2LitsStandaloneDelta017.q2 (-3688730071913094595929) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta142Fq d2Delta142Ts 16 24 12 20 30 128 d2Delta142Lo d2Delta142Hi d2Delta142Pd d2Delta142Qd d2Delta142Ld d2Delta142Gam d2Delta142S d2Delta142Ap d2Delta142Aq d2Delta142Al d2Delta142Es d2Delta142Ep d2Delta142Eq d2Delta142El (by decide +kernel) d2Delta142Shift d2Delta142Plogs d2Delta142Poles d2Delta142Laurent]
  exact decide_eq_true d2Delta142Small
theorem d2Delta142Bound : ∀ x ∈ Icc ((d2Delta142Lo : ℚ) : ℝ) ((d2Delta142Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-3688730071913094595929) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta142Fq d2Delta142Ts 16 24 12 20 30 128 d2Delta142Lo d2Delta142Hi d2Delta142Pd d2Delta142Qd d2Delta142Ld d2Delta142Gam (d2LitsStandaloneDelta017.q2 (-3688730071913094595929) 1 (-79)) d2Delta142Check
  simpa only [d2Delta142Fq, d2Delta142Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta142Shift
#print axioms d2Delta142Sites
#print axioms d2Delta142PData
#print axioms d2Delta142Plogs
#print axioms d2Delta142Poles
#print axioms d2Delta142Laurent
#print axioms d2Delta142Small
#print axioms d2Delta142Check
#print axioms d2Delta142Bound

def d2Delta143Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta143Ts : List LTerm := laurentClean []
def d2Delta143Lo : ℚ := (d2LitsStandaloneDelta017.q2 (128979845) 1 (-27))
def d2Delta143Hi : ℚ := (d2LitsStandaloneDelta017.q2 (519062033) 1 (-29))
def d2Delta143Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta143Qd : List (ℚ × ℚ) := []
def d2Delta143Ld : List LaurentPieceData := []
def d2Delta143Gam : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-4459351485148252541162910472928494150037760061, 1, -159, 9848717882027002745610824072487109934649, 1, -157, -4303722867483565491898673643721384509369, 1, -157, -1681012507736840127525074480360873087657, 1, -157, 48860499542462581467265043387345727655, 1, -156, 43998813964154988170877114842983996417, 1, -157, 98954735423310436083704347940529669, 1, -157, -471479308499602616474609065394511249, 1, -157, -8736177260676876750667064599750517, 1, -156, 2314978531066962440553618076170745, 1, -157, 169604607050539346240266762310651, 1, -157, -3277982443250299515653100454377, 1, -157, -345166339519965513497313374435, 1, -156, -15804933110466446091752973007, 1, -157, 1101348407786849486584508233, 1, -157, 73656361951253510668041407, 1, -157, 690876369655460283446367, 1, -157, -93449813139451329690955, 1, -157, -4448986177256197325453, 1, -157, -45713456085523914085, 1, -157, 1700397228993309399, 1, -156, 173994390916738365, 1, -157, 3306881441874393, 1, -157, -24808476853389, 1, -157, -1753587617203, 1, -156, -113814640027, 1, -157, -1968991385, 1, -157, -5014933, 1, -157, 458085, 1, -156, 37149, 1, -157, 957, 1, -157, 19, 1, -157])
def d2Delta143S : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [-519134788755231514938697047961983587, 1, -126, 28154013121269291643297428542837, 1, -128, -17484398366924526116060122169395, 1, -128, -14213300616092950390708650060229, 1, -128, 1441974500582287473620427721791, 1, -128, 705747649732717101910676698907, 1, -127, 14588080252823205298619093297, 1, -128, -58705311737900380582795590529, 1, -128, -2289522811862454772814201483, 1, -127, 1120561921377585687120357881, 1, -128, 42432106518390298927814561, 1, -126, -2923820510347081223569859, 1, -127, -168246571719601335142827, 1, -124, -129095978975215886949177, 1, -128, 16627366096832531332469, 1, -128, 2296078325575043548885, 1, -128, 23545304115049085361, 1, -127, -1412175610668830409, 1, -125, -275653418844453205, 1, -126, -3013479316581155, 1, -125, 3249182823558477, 1, -128, 340886130509757, 1, -128, 3310998608893, 1, -126, -42900084063, 1, -126, -53994748489, 1, -128, -3552040643, 1, -128, -62320549, 1, -127, -760501, 1, -128, 110947, 1, -127, 2285, 1, -125, 949, 1, -128, 19, 1, -127, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta143Ap : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta143Aq : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta143Al : List ℚ := d2LitsStandaloneDelta017.q2listC (raw_ints% [])
def d2Delta143Es : ℚ := (d2LitsStandaloneDelta017.q2 (61) 1 (-127))
def d2Delta143Ep : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta143Eq : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
def d2Delta143El : ℚ := (d2LitsStandaloneDelta017.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta143Shift : polyRoundApx 128 d2Delta143Lo d2Delta143Hi d2Delta143Fq.poly = (d2Delta143S,d2Delta143Es) := by decide +kernel
theorem d2Delta143Sites : mergeSites d2Delta143Fq.plogs = [] := by decide +kernel
theorem d2Delta143PData : d2Delta143Pd = [] := by decide +kernel
theorem d2Delta143Plogs : plogsRoundM 16 24 20 128 d2Delta143Lo d2Delta143Hi (mergeSites d2Delta143Fq.plogs) d2Delta143Pd = some (d2Delta143Ap,d2Delta143Ep) := by
  rw [d2Delta143Sites,d2Delta143PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta143Poles : polesRoundM 16 24 12 128 d2Delta143Lo d2Delta143Hi d2Delta143Fq.poles d2Delta143Qd = some (d2Delta143Aq,d2Delta143Eq) := by decide +kernel
theorem d2Delta143Laurent : laurentRoundM 16 30 128 d2Delta143Lo d2Delta143Hi d2Delta143Ts d2Delta143Ld = some (d2Delta143Al,d2Delta143El) := by decide +kernel
theorem d2Delta143Small : chebPolyUB (vecAdd d2Delta143S (vecAdd d2Delta143Ap (vecAdd d2Delta143Aq d2Delta143Al))) d2Delta143Gam+d2Delta143Es+d2Delta143Ep+d2Delta143Eq+d2Delta143El ≤ (d2LitsStandaloneDelta017.q2 (-7377272467413896871337) 1 (-80)) := by decide +kernel
theorem d2Delta143Check : chebRoundPieceL d2Delta143Fq d2Delta143Ts 16 24 12 20 30 128 d2Delta143Lo d2Delta143Hi d2Delta143Pd d2Delta143Qd d2Delta143Ld d2Delta143Gam (d2LitsStandaloneDelta017.q2 (-7377272467413896871337) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta143Fq d2Delta143Ts 16 24 12 20 30 128 d2Delta143Lo d2Delta143Hi d2Delta143Pd d2Delta143Qd d2Delta143Ld d2Delta143Gam d2Delta143S d2Delta143Ap d2Delta143Aq d2Delta143Al d2Delta143Es d2Delta143Ep d2Delta143Eq d2Delta143El (by decide +kernel) d2Delta143Shift d2Delta143Plogs d2Delta143Poles d2Delta143Laurent]
  exact decide_eq_true d2Delta143Small
theorem d2Delta143Bound : ∀ x ∈ Icc ((d2Delta143Lo : ℚ) : ℝ) ((d2Delta143Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta017.q2 (-7377272467413896871337) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta143Fq d2Delta143Ts 16 24 12 20 30 128 d2Delta143Lo d2Delta143Hi d2Delta143Pd d2Delta143Qd d2Delta143Ld d2Delta143Gam (d2LitsStandaloneDelta017.q2 (-7377272467413896871337) 1 (-80)) d2Delta143Check
  simpa only [d2Delta143Fq, d2Delta143Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta143Shift
#print axioms d2Delta143Sites
#print axioms d2Delta143PData
#print axioms d2Delta143Plogs
#print axioms d2Delta143Poles
#print axioms d2Delta143Laurent
#print axioms d2Delta143Small
#print axioms d2Delta143Check
#print axioms d2Delta143Bound

end StandaloneDelta017
end CatalanMeasure.GenD.Signed.Data.Cells
