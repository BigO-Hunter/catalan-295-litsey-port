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
namespace d2LitsStandaloneDelta018
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta018
namespace StandaloneDelta018
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta018.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta018.q2listC (raw_ints% []))⟩
def d2Delta144Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta144Ts : List LTerm := laurentClean []
def d2Delta144Lo : ℚ := (d2LitsStandaloneDelta018.q2 (519062033) 1 (-29))
def d2Delta144Hi : ℚ := (d2LitsStandaloneDelta018.q2 (1039171617) 1 (-30))
def d2Delta144Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta144Qd : List (ℚ × ℚ) := []
def d2Delta144Ld : List LaurentPieceData := []
def d2Delta144Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-8709671871969336522913013183840371287270447, 1, -150, -34387211821122760195191080960363884089, 1, -150, -514097824375121326857715004295789549, 1, -148, 2461803054732622985632984015398605, 1, -146, 655693941445201851323709225743553, 1, -148, -1956539763828584342685802305139, 1, -148, -305970089184958564001212930619, 1, -148, -21174764994166185177456158599, 1, -152, 522137881019831676780517329, 1, -151, 10727986063011371269689989, 1, -152, -10837247687578908045299, 1, -149, -235951208421667498401, 1, -149, -457554609431312947, 1, -149, 8655570441813519, 1, -148, 149775805363595, 1, -149, -392015824563, 1, -151, -18027480505, 1, -150, -224894539, 1, -151, 9919, 1, -149, 921, 1, -148, -79, 1, -149, -49, 1, -149, -7, 1, -149, -29, 1, -152, -1, 1, -151, -1, 1, -152, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta144S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-2076547101248273638534437280546976243, 1, -128, -8226732602468781654925117584557, 1, -128, -246392896135385522025199497505, 1, -126, 37601380804858404750029194127, 1, -128, 627070491405412014179079795, 1, -125, -29712794366172156500615909, 1, -128, -9353406271123286441306109, 1, -128, -20285987801707561567449, 1, -126, 7973804809108028001209, 1, -128, 82006521387946514923, 1, -127, -1322234557660628627, 1, -127, -57660220226722765, 1, -127, -112219826206283, 1, -126, 33813680177779, 1, -128, 585625103857, 1, -128, -189546567, 1, -126, -140842591, 1, -128, -1758251, 1, -128, 651, 1, -128, 141, 1, -127, 3, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta144Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta144Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta144Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta144Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta144Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta144Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta144El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta144Shift : polyRoundApx 128 d2Delta144Lo d2Delta144Hi d2Delta144Fq.poly = (d2Delta144S,d2Delta144Es) := by decide +kernel
theorem d2Delta144Sites : mergeSites d2Delta144Fq.plogs = [] := by decide +kernel
theorem d2Delta144PData : d2Delta144Pd = [] := by decide +kernel
theorem d2Delta144Plogs : plogsRoundM 16 24 20 128 d2Delta144Lo d2Delta144Hi (mergeSites d2Delta144Fq.plogs) d2Delta144Pd = some (d2Delta144Ap,d2Delta144Ep) := by
  rw [d2Delta144Sites,d2Delta144PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta144Poles : polesRoundM 16 24 12 128 d2Delta144Lo d2Delta144Hi d2Delta144Fq.poles d2Delta144Qd = some (d2Delta144Aq,d2Delta144Eq) := by decide +kernel
theorem d2Delta144Laurent : laurentRoundM 16 30 128 d2Delta144Lo d2Delta144Hi d2Delta144Ts d2Delta144Ld = some (d2Delta144Al,d2Delta144El) := by decide +kernel
theorem d2Delta144Small : chebPolyUB (vecAdd d2Delta144S (vecAdd d2Delta144Ap (vecAdd d2Delta144Aq d2Delta144Al))) d2Delta144Gam+d2Delta144Es+d2Delta144Ep+d2Delta144Eq+d2Delta144El ≤ (d2LitsStandaloneDelta018.q2 (-7377348130806607557449) 1 (-80)) := by decide +kernel
theorem d2Delta144Check : chebRoundPieceL d2Delta144Fq d2Delta144Ts 16 24 12 20 30 128 d2Delta144Lo d2Delta144Hi d2Delta144Pd d2Delta144Qd d2Delta144Ld d2Delta144Gam (d2LitsStandaloneDelta018.q2 (-7377348130806607557449) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta144Fq d2Delta144Ts 16 24 12 20 30 128 d2Delta144Lo d2Delta144Hi d2Delta144Pd d2Delta144Qd d2Delta144Ld d2Delta144Gam d2Delta144S d2Delta144Ap d2Delta144Aq d2Delta144Al d2Delta144Es d2Delta144Ep d2Delta144Eq d2Delta144El (by decide +kernel) d2Delta144Shift d2Delta144Plogs d2Delta144Poles d2Delta144Laurent]
  exact decide_eq_true d2Delta144Small
theorem d2Delta144Bound : ∀ x ∈ Icc ((d2Delta144Lo : ℚ) : ℝ) ((d2Delta144Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-7377348130806607557449) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta144Fq d2Delta144Ts 16 24 12 20 30 128 d2Delta144Lo d2Delta144Hi d2Delta144Pd d2Delta144Qd d2Delta144Ld d2Delta144Gam (d2LitsStandaloneDelta018.q2 (-7377348130806607557449) 1 (-80)) d2Delta144Check
  simpa only [d2Delta144Fq, d2Delta144Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta144Shift
#print axioms d2Delta144Sites
#print axioms d2Delta144PData
#print axioms d2Delta144Plogs
#print axioms d2Delta144Poles
#print axioms d2Delta144Laurent
#print axioms d2Delta144Small
#print axioms d2Delta144Check
#print axioms d2Delta144Bound

def d2Delta145Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta145Ts : List LTerm := laurentClean []
def d2Delta145Lo : ℚ := (d2LitsStandaloneDelta018.q2 (1039171617) 1 (-30))
def d2Delta145Hi : ℚ := (d2LitsStandaloneDelta018.q2 (32506849) 1 (-25))
def d2Delta145Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta145Qd : List (ℚ × ℚ) := []
def d2Delta145Ld : List LaurentPieceData := []
def d2Delta145Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-8709755111655886593954146428075778611889567, 1, -150, -48256724374831991461738836257713376057, 1, -150, -335592006848041225244734860217098253, 1, -148, 4904549975649115049157170783683549, 1, -146, 541436896418017506435965097967205, 1, -148, -9487931718538954326959947360179, 1, -148, -310515165019651856044101622651, 1, -148, 17587645580147155261637389433, 1, -152, 673889000922189023125603409, 1, -151, 5575416405265286731755141, 1, -152, -21346368692104714604147, 1, -149, -232890613553316248865, 1, -149, 653246827113178753, 1, -149, 12588100453397071, 1, -148, 124176850273579, 1, -149, -3176635778227, 1, -151, -25301992073, 1, -150, -192536139, 1, -151, 229471, 1, -149, 1561, 1, -148, -75, 1, -149, -49, 1, -149, -7, 1, -149, -29, 1, -152, -1, 1, -151, -1, 1, -152, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta145S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-2076567117481438927285647943316532309, 1, -128, -5780736513502997126255332380215, 1, -127, -2516512203352476025712584131, 1, -120, 2344328753938523077929792465, 1, -123, 129533212820132070454209345, 1, -123, -144891615234321670777153097, 1, -128, -9496747669024344512029627, 1, -128, 33449906966363982471405, 1, -127, 10295761057538542383733, 1, -128, 10673377747782210655, 1, -125, -5213427267568153203, 1, -128, -28468991164322353, 1, -126, 318118669619311, 1, -127, 49195522579741, 1, -128, 242928314895, 1, -127, -6197969995, 1, -128, -197736451, 1, -128, -1506211, 1, -128, 449, 1, -123, 221, 1, -127, 1, 1, -126, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta145Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta145Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta145Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta145Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta145Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta145Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta145El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta145Shift : polyRoundApx 128 d2Delta145Lo d2Delta145Hi d2Delta145Fq.poly = (d2Delta145S,d2Delta145Es) := by decide +kernel
theorem d2Delta145Sites : mergeSites d2Delta145Fq.plogs = [] := by decide +kernel
theorem d2Delta145PData : d2Delta145Pd = [] := by decide +kernel
theorem d2Delta145Plogs : plogsRoundM 16 24 20 128 d2Delta145Lo d2Delta145Hi (mergeSites d2Delta145Fq.plogs) d2Delta145Pd = some (d2Delta145Ap,d2Delta145Ep) := by
  rw [d2Delta145Sites,d2Delta145PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta145Poles : polesRoundM 16 24 12 128 d2Delta145Lo d2Delta145Hi d2Delta145Fq.poles d2Delta145Qd = some (d2Delta145Aq,d2Delta145Eq) := by decide +kernel
theorem d2Delta145Laurent : laurentRoundM 16 30 128 d2Delta145Lo d2Delta145Hi d2Delta145Ts d2Delta145Ld = some (d2Delta145Al,d2Delta145El) := by decide +kernel
theorem d2Delta145Small : chebPolyUB (vecAdd d2Delta145S (vecAdd d2Delta145Ap (vecAdd d2Delta145Aq d2Delta145Al))) d2Delta145Gam+d2Delta145Es+d2Delta145Ep+d2Delta145Eq+d2Delta145El ≤ (d2LitsStandaloneDelta018.q2 (-1844351865421741505317) 1 (-78)) := by decide +kernel
theorem d2Delta145Check : chebRoundPieceL d2Delta145Fq d2Delta145Ts 16 24 12 20 30 128 d2Delta145Lo d2Delta145Hi d2Delta145Pd d2Delta145Qd d2Delta145Ld d2Delta145Gam (d2LitsStandaloneDelta018.q2 (-1844351865421741505317) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta145Fq d2Delta145Ts 16 24 12 20 30 128 d2Delta145Lo d2Delta145Hi d2Delta145Pd d2Delta145Qd d2Delta145Ld d2Delta145Gam d2Delta145S d2Delta145Ap d2Delta145Aq d2Delta145Al d2Delta145Es d2Delta145Ep d2Delta145Eq d2Delta145El (by decide +kernel) d2Delta145Shift d2Delta145Plogs d2Delta145Poles d2Delta145Laurent]
  exact decide_eq_true d2Delta145Small
theorem d2Delta145Bound : ∀ x ∈ Icc ((d2Delta145Lo : ℚ) : ℝ) ((d2Delta145Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-1844351865421741505317) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta145Fq d2Delta145Ts 16 24 12 20 30 128 d2Delta145Lo d2Delta145Hi d2Delta145Pd d2Delta145Qd d2Delta145Ld d2Delta145Gam (d2LitsStandaloneDelta018.q2 (-1844351865421741505317) 1 (-78)) d2Delta145Check
  simpa only [d2Delta145Fq, d2Delta145Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta145Shift
#print axioms d2Delta145Sites
#print axioms d2Delta145PData
#print axioms d2Delta145Plogs
#print axioms d2Delta145Poles
#print axioms d2Delta145Laurent
#print axioms d2Delta145Small
#print axioms d2Delta145Check
#print axioms d2Delta145Bound

def d2Delta146Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta146Ts : List LTerm := laurentClean []
def d2Delta146Lo : ℚ := (d2LitsStandaloneDelta018.q2 (32506849) 1 (-25))
def d2Delta146Hi : ℚ := (d2LitsStandaloneDelta018.q2 (261102343) 1 (-28))
def d2Delta146Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta146Qd : List (ℚ × ℚ) := []
def d2Delta146Ld : List LaurentPieceData := []
def d2Delta146Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-69679909926421829144851438150475721826504665, 1, -153, -163690632222225043147739892660852068325, 1, -150, 54038709970704940236141867323346877649, 1, -151, 204040259864835939965119722983482458515, 1, -155, -9775557684941920279899015920515950949, 1, -155, -2646666898502160106912028103718603779, 1, -155, 1343163064664909969220643961113487, 1, -153, 3835271203929291991069325280270433, 1, -153, 206306350468500637373836520944779, 1, -154, -9911171319982448858862211860789, 1, -153, -566363089215146023116791891525, 1, -153, 20199504960552478637467441379, 1, -155, 4729872717722709773270692905, 1, -155, 109932099700836966508898701, 1, -155, -366780092904991999064333, 1, -152, -6666508925591678531761, 1, -150, -879442044569029201615, 1, -153, 1253125274838537775, 1, -149, 645090473998466171, 1, -152, 101366182753923231, 1, -155, -118896142146341, 1, -155, -60489959243727, 1, -155, -447665754707, 1, -153, -6723898663, 1, -153, -34164539, 1, -154, 2084795, 1, -153, 70377, 1, -153, 5935, 1, -155, 97, 1, -155, 1, 1, -155, 0, 1, 0, 0, 1, 0])
def d2Delta146S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-1038314827179768317091957305565133249, 1, -127, -43686941935232727055890215660065, 1, -128, 13467122398785230190195396701475, 1, -128, 6481693982668645626627664815915, 1, -128, -584091399588986234360686069129, 1, -128, -328436664818320629190158944471, 1, -128, 474912932546958700190192541, 1, -128, 3742875699033686802615396181, 1, -127, 415347339145656892549132107, 1, -128, -38013148792291252111072363, 1, -127, -4429694215991553242263869, 1, -127, 71529971488710737671699, 1, -127, 9099165768101095068197, 1, -125, 3452804571568508332229, 1, -128, -87806996650840697217, 1, -127, -818924792473196317, 1, -123, -440756763935119879, 1, -127, 38214190837106627, 1, -128, 315107884066747, 1, -124, 12528109299237, 1, -124, -155311205149, 1, -127, -116931798421, 1, -126, -27952174999, 1, -128, -211735579, 1, -126, -590737, 1, -125, 511207, 1, -127, 34849, 1, -127, 2953, 1, -128, 97, 1, -128, 1, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta146Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta146Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta146Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta146Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta146Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta146Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta146El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta146Shift : polyRoundApx 128 d2Delta146Lo d2Delta146Hi d2Delta146Fq.poly = (d2Delta146S,d2Delta146Es) := by decide +kernel
theorem d2Delta146Sites : mergeSites d2Delta146Fq.plogs = [] := by decide +kernel
theorem d2Delta146PData : d2Delta146Pd = [] := by decide +kernel
theorem d2Delta146Plogs : plogsRoundM 16 24 20 128 d2Delta146Lo d2Delta146Hi (mergeSites d2Delta146Fq.plogs) d2Delta146Pd = some (d2Delta146Ap,d2Delta146Ep) := by
  rw [d2Delta146Sites,d2Delta146PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta146Poles : polesRoundM 16 24 12 128 d2Delta146Lo d2Delta146Hi d2Delta146Fq.poles d2Delta146Qd = some (d2Delta146Aq,d2Delta146Eq) := by decide +kernel
theorem d2Delta146Laurent : laurentRoundM 16 30 128 d2Delta146Lo d2Delta146Hi d2Delta146Ts d2Delta146Ld = some (d2Delta146Al,d2Delta146El) := by decide +kernel
theorem d2Delta146Small : chebPolyUB (vecAdd d2Delta146S (vecAdd d2Delta146Ap (vecAdd d2Delta146Aq d2Delta146Al))) d2Delta146Gam+d2Delta146Es+d2Delta146Ep+d2Delta146Eq+d2Delta146El ≤ (d2LitsStandaloneDelta018.q2 (-7377480165756796994955) 1 (-80)) := by decide +kernel
theorem d2Delta146Check : chebRoundPieceL d2Delta146Fq d2Delta146Ts 16 24 12 20 30 128 d2Delta146Lo d2Delta146Hi d2Delta146Pd d2Delta146Qd d2Delta146Ld d2Delta146Gam (d2LitsStandaloneDelta018.q2 (-7377480165756796994955) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta146Fq d2Delta146Ts 16 24 12 20 30 128 d2Delta146Lo d2Delta146Hi d2Delta146Pd d2Delta146Qd d2Delta146Ld d2Delta146Gam d2Delta146S d2Delta146Ap d2Delta146Aq d2Delta146Al d2Delta146Es d2Delta146Ep d2Delta146Eq d2Delta146El (by decide +kernel) d2Delta146Shift d2Delta146Plogs d2Delta146Poles d2Delta146Laurent]
  exact decide_eq_true d2Delta146Small
theorem d2Delta146Bound : ∀ x ∈ Icc ((d2Delta146Lo : ℚ) : ℝ) ((d2Delta146Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-7377480165756796994955) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta146Fq d2Delta146Ts 16 24 12 20 30 128 d2Delta146Lo d2Delta146Hi d2Delta146Pd d2Delta146Qd d2Delta146Ld d2Delta146Gam (d2LitsStandaloneDelta018.q2 (-7377480165756796994955) 1 (-80)) d2Delta146Check
  simpa only [d2Delta146Fq, d2Delta146Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta146Shift
#print axioms d2Delta146Sites
#print axioms d2Delta146PData
#print axioms d2Delta146Plogs
#print axioms d2Delta146Poles
#print axioms d2Delta146Laurent
#print axioms d2Delta146Small
#print axioms d2Delta146Check
#print axioms d2Delta146Bound

def d2Delta147Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta147Ts : List LTerm := laurentClean []
def d2Delta147Lo : ℚ := (d2LitsStandaloneDelta018.q2 (261102343) 1 (-28))
def d2Delta147Hi : ℚ := (d2LitsStandaloneDelta018.q2 (131074947) 1 (-27))
def d2Delta147Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta147Qd : List (ℚ × ℚ) := []
def d2Delta147Ld : List LaurentPieceData := []
def d2Delta147Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-34839935312986754959158276425188565131690061, 1, -152, 349706665951934943387364948575166849207, 1, -151, 33330776430523963008774928540755003107, 1, -150, -218082579997985904570240516410247120817, 1, -155, -13205181674623337812582626674777501053, 1, -154, 2310476534504047758384707266236838293, 1, -155, 39088850422359587534661687764447545, 1, -152, -344490906666277181881039029133981, 1, -151, -434724160868250678879717309809033, 1, -153, -4571284340762550777053591392979, 1, -152, 516274114829704560161659069509, 1, -152, 232236231124535159601144676899, 1, -155, -349411654698952179681937151, 1, -154, -433616265410440396643573015, 1, -155, -868001605014014815082319, 1, -151, 10659030827255852181591, 1, -152, 2346714708742752386373, 1, -152, 70974741318580117547, 1, -152, 194816446550722745, 1, -151, -341830720158296829, 1, -155, -7107845785812061, 1, -154, -279909818081247, 1, -155, -195959184573, 1, -152, 11683152017, 1, -152, 1018052505, 1, -153, 3213155, 1, -150, 248031, 1, -152, 31719, 1, -155, 217, 1, -154, 5, 1, -155, 0, 1, 0, 0, 1, 0])
def d2Delta147S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-1038315057059962289731737118680239783, 1, -127, 46649165668981330928179107327481, 1, -128, 17509886950697867090765847103391, 1, -128, -6845921835687577493503698902469, 1, -128, -844049831708771465486958713593, 1, -127, 69977466985383097066115507219, 1, -126, 38953615123192377251978548131, 1, -127, -154150603952528889415531623, 1, -124, -424440712987817677231395309, 1, -126, -37339287990352568905359097, 1, -127, 7891660339532807866771911, 1, -127, 1814885448615739248241035, 1, -128, -3833314647534270290811, 1, -127, -6634941935157796635757, 1, -127, -865965148485614867831, 1, -128, 576538013000114513, 1, -124, 4569139562579041673, 1, -128, 280390473376322129, 1, -128, 3321331210804937, 1, -128, -656115813644721, 1, -128, -55391330176947, 1, -128, -275421205507, 1, -125, -26012724139, 1, -128, 2840779831, 1, -128, 251298217, 1, -128, 3186451, 1, -126, 15407, 1, -123, 15787, 1, -128, 217, 1, -127, 5, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta147Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta147Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta147Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta147Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta147Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta147Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta147El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta147Shift : polyRoundApx 128 d2Delta147Lo d2Delta147Hi d2Delta147Fq.poly = (d2Delta147S,d2Delta147Es) := by decide +kernel
theorem d2Delta147Sites : mergeSites d2Delta147Fq.plogs = [] := by decide +kernel
theorem d2Delta147PData : d2Delta147Pd = [] := by decide +kernel
theorem d2Delta147Plogs : plogsRoundM 16 24 20 128 d2Delta147Lo d2Delta147Hi (mergeSites d2Delta147Fq.plogs) d2Delta147Pd = some (d2Delta147Ap,d2Delta147Ep) := by
  rw [d2Delta147Sites,d2Delta147PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta147Poles : polesRoundM 16 24 12 128 d2Delta147Lo d2Delta147Hi d2Delta147Fq.poles d2Delta147Qd = some (d2Delta147Aq,d2Delta147Eq) := by decide +kernel
theorem d2Delta147Laurent : laurentRoundM 16 30 128 d2Delta147Lo d2Delta147Hi d2Delta147Ts d2Delta147Ld = some (d2Delta147Al,d2Delta147El) := by decide +kernel
theorem d2Delta147Small : chebPolyUB (vecAdd d2Delta147S (vecAdd d2Delta147Ap (vecAdd d2Delta147Aq d2Delta147Al))) d2Delta147Gam+d2Delta147Es+d2Delta147Ep+d2Delta147Eq+d2Delta147El ≤ (d2LitsStandaloneDelta018.q2 (-7377460392474799800889) 1 (-80)) := by decide +kernel
theorem d2Delta147Check : chebRoundPieceL d2Delta147Fq d2Delta147Ts 16 24 12 20 30 128 d2Delta147Lo d2Delta147Hi d2Delta147Pd d2Delta147Qd d2Delta147Ld d2Delta147Gam (d2LitsStandaloneDelta018.q2 (-7377460392474799800889) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta147Fq d2Delta147Ts 16 24 12 20 30 128 d2Delta147Lo d2Delta147Hi d2Delta147Pd d2Delta147Qd d2Delta147Ld d2Delta147Gam d2Delta147S d2Delta147Ap d2Delta147Aq d2Delta147Al d2Delta147Es d2Delta147Ep d2Delta147Eq d2Delta147El (by decide +kernel) d2Delta147Shift d2Delta147Plogs d2Delta147Poles d2Delta147Laurent]
  exact decide_eq_true d2Delta147Small
theorem d2Delta147Bound : ∀ x ∈ Icc ((d2Delta147Lo : ℚ) : ℝ) ((d2Delta147Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-7377460392474799800889) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta147Fq d2Delta147Ts 16 24 12 20 30 128 d2Delta147Lo d2Delta147Hi d2Delta147Pd d2Delta147Qd d2Delta147Ld d2Delta147Gam (d2LitsStandaloneDelta018.q2 (-7377460392474799800889) 1 (-80)) d2Delta147Check
  simpa only [d2Delta147Fq, d2Delta147Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta147Shift
#print axioms d2Delta147Sites
#print axioms d2Delta147PData
#print axioms d2Delta147Plogs
#print axioms d2Delta147Poles
#print axioms d2Delta147Laurent
#print axioms d2Delta147Small
#print axioms d2Delta147Check
#print axioms d2Delta147Bound

def d2Delta148Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta148Ts : List LTerm := laurentClean []
def d2Delta148Lo : ℚ := (d2LitsStandaloneDelta018.q2 (131074947) 1 (-27))
def d2Delta148Hi : ℚ := (d2LitsStandaloneDelta018.q2 (1049647127) 1 (-30))
def d2Delta148Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta148Qd : List (ℚ × ℚ) := []
def d2Delta148Ld : List LaurentPieceData := []
def d2Delta148Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-544358086741619053084512413506187718160099, 1, -146, 3241667457026239684368594341191759405, 1, -146, -32618706877117684916229347308298783, 1, -144, -17075519685492114984237907594081077, 1, -147, 180911380460449050318126359023785, 1, -146, 18808985992985772736118578842127, 1, -147, -4954086525812144913026443113, 1, -143, -2320913234586954317239912311, 1, -145, -7102258118114114984766947, 1, -144, 482857937854106563907825, 1, -145, 1868313022946842524667, 1, -143, -105499984557354216317, 1, -148, -4768216756809132531, 1, -147, -77254505479361665, 1, -148, 31621136324975, 1, -145, 4654953639783, 1, -147, 17276422895, 1, -146, 10704215, 1, -147, -501625, 1, -145, -39861, 1, -148, -95, 1, -147, -1, 1, -148, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta148S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-2076560806601869811573404548351310705, 1, -128, 6231933196107744862078421280659, 1, -127, -1000967630536072741285183081751, 1, -128, -130994374424316642713140031449, 1, -128, 5528216787276093481341654603, 1, -128, 575989493294256994214016901, 1, -128, -1202542009034190750441533, 1, -126, -1135380632212192287913219, 1, -128, -1743080216639045057215, 1, -125, 943364008437481170027, 1, -128, 14624139011414059753, 1, -127, -51022870167968161, 1, -127, -4658187447121129, 1, -126, -151160452176655, 1, -127, 983839288795, 1, -127, 72730759987, 1, -127, 2161809165, 1, -128, 692675, 1, -127, -250575, 1, -127, -1245, 1, -125, -95, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta148Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta148Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta148Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta148Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta148Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta148Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta148El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta148Shift : polyRoundApx 128 d2Delta148Lo d2Delta148Hi d2Delta148Fq.poly = (d2Delta148S,d2Delta148Es) := by decide +kernel
theorem d2Delta148Sites : mergeSites d2Delta148Fq.plogs = [] := by decide +kernel
theorem d2Delta148PData : d2Delta148Pd = [] := by decide +kernel
theorem d2Delta148Plogs : plogsRoundM 16 24 20 128 d2Delta148Lo d2Delta148Hi (mergeSites d2Delta148Fq.plogs) d2Delta148Pd = some (d2Delta148Ap,d2Delta148Ep) := by
  rw [d2Delta148Sites,d2Delta148PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta148Poles : polesRoundM 16 24 12 128 d2Delta148Lo d2Delta148Hi d2Delta148Fq.poles d2Delta148Qd = some (d2Delta148Aq,d2Delta148Eq) := by decide +kernel
theorem d2Delta148Laurent : laurentRoundM 16 30 128 d2Delta148Lo d2Delta148Hi d2Delta148Ts d2Delta148Ld = some (d2Delta148Al,d2Delta148El) := by decide +kernel
theorem d2Delta148Small : chebPolyUB (vecAdd d2Delta148S (vecAdd d2Delta148Ap (vecAdd d2Delta148Aq d2Delta148Al))) d2Delta148Gam+d2Delta148Es+d2Delta148Ep+d2Delta148Eq+d2Delta148El ≤ (d2LitsStandaloneDelta018.q2 (-461086370865842605209) 1 (-76)) := by decide +kernel
theorem d2Delta148Check : chebRoundPieceL d2Delta148Fq d2Delta148Ts 16 24 12 20 30 128 d2Delta148Lo d2Delta148Hi d2Delta148Pd d2Delta148Qd d2Delta148Ld d2Delta148Gam (d2LitsStandaloneDelta018.q2 (-461086370865842605209) 1 (-76)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta148Fq d2Delta148Ts 16 24 12 20 30 128 d2Delta148Lo d2Delta148Hi d2Delta148Pd d2Delta148Qd d2Delta148Ld d2Delta148Gam d2Delta148S d2Delta148Ap d2Delta148Aq d2Delta148Al d2Delta148Es d2Delta148Ep d2Delta148Eq d2Delta148El (by decide +kernel) d2Delta148Shift d2Delta148Plogs d2Delta148Poles d2Delta148Laurent]
  exact decide_eq_true d2Delta148Small
theorem d2Delta148Bound : ∀ x ∈ Icc ((d2Delta148Lo : ℚ) : ℝ) ((d2Delta148Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-461086370865842605209) 1 (-76)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta148Fq d2Delta148Ts 16 24 12 20 30 128 d2Delta148Lo d2Delta148Hi d2Delta148Pd d2Delta148Qd d2Delta148Ld d2Delta148Gam (d2LitsStandaloneDelta018.q2 (-461086370865842605209) 1 (-76)) d2Delta148Check
  simpa only [d2Delta148Fq, d2Delta148Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta148Shift
#print axioms d2Delta148Sites
#print axioms d2Delta148PData
#print axioms d2Delta148Plogs
#print axioms d2Delta148Poles
#print axioms d2Delta148Laurent
#print axioms d2Delta148Small
#print axioms d2Delta148Check
#print axioms d2Delta148Bound

def d2Delta149Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta149Ts : List LTerm := laurentClean []
def d2Delta149Lo : ℚ := (d2LitsStandaloneDelta018.q2 (1049647127) 1 (-30))
def d2Delta149Hi : ℚ := (d2LitsStandaloneDelta018.q2 (263197445) 1 (-28))
def d2Delta149Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta149Qd : List (ℚ × ℚ) := []
def d2Delta149Ld : List LaurentPieceData := []
def d2Delta149Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-1088705380136778840585020837201055400730355, 1, -147, 24283321130042583181703960552137617143, 1, -152, -3777053692898932017307875780957560963, 1, -147, 3796827150319670976404817308530262621, 1, -152, 67740216010662248549727523515448215, 1, -147, 54720545113792968319862994257188711, 1, -154, -3407339224003829293193727870034547, 1, -150, -1845924270842932001363806369005435, 1, -154, 1001951165978505181752385497247, 1, -147, 8678243949736916399719968756785, 1, -154, -64552132077994297359497785, 1, -150, -14672483299345878317159611477, 1, -154, -7028449097822936185962477, 1, -148, 1741155170610803231994975, 1, -153, 8603368608332686147, 1, -138, 7249194840396432000541, 1, -153, 163566138114496679, 1, -147, -4567382749359776347, 1, -153, -2344092233581061, 1, -147, -2291055984637321, 1, -153, -11638982721, 1, -148, 1968531508653, 1, -154, 3940040733, 1, -150, 1307401111, 1, -154, 165421, 1, -147, 285779, 1, -154, 207, 1, -150, 33, 1, -154, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta149S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-1038266692081404278062735186334806233, 1, -127, 386371919344641735434576213657, 1, -127, -7728316964840390155551746374591, 1, -127, 443685107865869576936221401329, 1, -127, 268233335439981954393239936899, 1, -126, 4045811772694826903063999131, 1, -126, -26485162344714377545637172977, 1, -128, -1835512726174960743894025309, 1, -128, 122295063854479917153536391, 1, -127, 33721403582062514787747593, 1, -128, 33633590516703746601219, 1, -128, -224555121598478282423519, 1, -128, -6984131258516508936077, 1, -127, 199203522448303518785, 1, -128, 34390556432032059753, 1, -127, 894347066976230489, 1, -126, 12859891085988593, 1, -128, -4417644058015599, 1, -127, -585968290351483, 1, -128, -4514795828585, 1, -126, -8306484543, 1, -127, 30289684331, 1, -128, 1954170897, 1, -128, 20316677, 1, -126, 658993, 1, -126, 35611, 1, -127, 207, 1, -125, 33, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta149Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta149Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta149Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta149Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta149Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta149Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta149El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta149Shift : polyRoundApx 128 d2Delta149Lo d2Delta149Hi d2Delta149Fq.poly = (d2Delta149S,d2Delta149Es) := by decide +kernel
theorem d2Delta149Sites : mergeSites d2Delta149Fq.plogs = [] := by decide +kernel
theorem d2Delta149PData : d2Delta149Pd = [] := by decide +kernel
theorem d2Delta149Plogs : plogsRoundM 16 24 20 128 d2Delta149Lo d2Delta149Hi (mergeSites d2Delta149Fq.plogs) d2Delta149Pd = some (d2Delta149Ap,d2Delta149Ep) := by
  rw [d2Delta149Sites,d2Delta149PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta149Poles : polesRoundM 16 24 12 128 d2Delta149Lo d2Delta149Hi d2Delta149Fq.poles d2Delta149Qd = some (d2Delta149Aq,d2Delta149Eq) := by decide +kernel
theorem d2Delta149Laurent : laurentRoundM 16 30 128 d2Delta149Lo d2Delta149Hi d2Delta149Ts d2Delta149Ld = some (d2Delta149Al,d2Delta149El) := by decide +kernel
theorem d2Delta149Small : chebPolyUB (vecAdd d2Delta149S (vecAdd d2Delta149Ap (vecAdd d2Delta149Aq d2Delta149Al))) d2Delta149Gam+d2Delta149Es+d2Delta149Ep+d2Delta149Eq+d2Delta149El ≤ (d2LitsStandaloneDelta018.q2 (-3688661304601675962449) 1 (-79)) := by decide +kernel
theorem d2Delta149Check : chebRoundPieceL d2Delta149Fq d2Delta149Ts 16 24 12 20 30 128 d2Delta149Lo d2Delta149Hi d2Delta149Pd d2Delta149Qd d2Delta149Ld d2Delta149Gam (d2LitsStandaloneDelta018.q2 (-3688661304601675962449) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta149Fq d2Delta149Ts 16 24 12 20 30 128 d2Delta149Lo d2Delta149Hi d2Delta149Pd d2Delta149Qd d2Delta149Ld d2Delta149Gam d2Delta149S d2Delta149Ap d2Delta149Aq d2Delta149Al d2Delta149Es d2Delta149Ep d2Delta149Eq d2Delta149El (by decide +kernel) d2Delta149Shift d2Delta149Plogs d2Delta149Poles d2Delta149Laurent]
  exact decide_eq_true d2Delta149Small
theorem d2Delta149Bound : ∀ x ∈ Icc ((d2Delta149Lo : ℚ) : ℝ) ((d2Delta149Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-3688661304601675962449) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta149Fq d2Delta149Ts 16 24 12 20 30 128 d2Delta149Lo d2Delta149Hi d2Delta149Pd d2Delta149Qd d2Delta149Ld d2Delta149Gam (d2LitsStandaloneDelta018.q2 (-3688661304601675962449) 1 (-79)) d2Delta149Check
  simpa only [d2Delta149Fq, d2Delta149Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta149Shift
#print axioms d2Delta149Sites
#print axioms d2Delta149PData
#print axioms d2Delta149Plogs
#print axioms d2Delta149Poles
#print axioms d2Delta149Laurent
#print axioms d2Delta149Small
#print axioms d2Delta149Check
#print axioms d2Delta149Bound

def d2Delta150Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta150Ts : List LTerm := laurentClean []
def d2Delta150Lo : ℚ := (d2LitsStandaloneDelta018.q2 (263197445) 1 (-28))
def d2Delta150Hi : ℚ := (d2LitsStandaloneDelta018.q2 (1055932433) 1 (-30))
def d2Delta150Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta150Qd : List (ℚ × ℚ) := []
def d2Delta150Ld : List LaurentPieceData := []
def d2Delta150Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-69677991126834891683223244267505980269917049, 1, -153, -137893194227266867992258718943051657569, 1, -151, 39574600527953294448342044040593155011, 1, -151, 10719802493496921349068842819116063141, 1, -151, -8007686380599881062911974638751594885, 1, -155, -579600801653971434710601395169837493, 1, -153, -5372635960932415235520348731315347, 1, -153, 2837411761173551953757838368361057, 1, -153, 240220327641209344239376072350699, 1, -154, -4249708536623440074412255148411, 1, -153, -434767714920320640739600125551, 1, -153, -7107922200890537997433082633, 1, -153, 1797598882185151486248588233, 1, -155, 12850749033480737221086399, 1, -152, 197397635753950140955049, 1, -152, -5906941821989069932243, 1, -152, -776166130756990101039, 1, -153, -9471058616138376891, 1, -152, -76069580043175167, 1, -152, 3086855811889287, 1, -152, 1246230337082811, 1, -155, 8377698857841, 1, -153, 167525668839, 1, -153, 2727417843, 1, -153, 75366245, 1, -154, 452551, 1, -153, 4795, 1, -153, 45, 1, -153, 1, 1, -155, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta150S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-1038285366023561616314935890947211705, 1, -127, -2544851269164994318914648189937, 1, -125, 9909618027257422752815843754331, 1, -128, 5461819749461873000806352919035, 1, -128, -117257940209680055982096094145, 1, -126, -17868783298746970262801869543, 1, -124, -6054672582337363474418281541, 1, -128, 1371070086811850615061455855, 1, -126, 474861240904667518991112347, 1, -128, -31813412200537754025071507, 1, -128, -3357924189129186190977945, 1, -127, -113572640109967267358343, 1, -127, 6771727741134839460053, 1, -126, 197421631841681417973, 1, -124, 24853097057698108093, 1, -126, -87668893506192445, 1, -122, -755248875811466133, 1, -128, -9305584931868279, 1, -126, -309248742468517, 1, -127, 11715637621819, 1, -126, 1202662133229, 1, -126, 259846643641, 1, -128, 10413919185, 1, -128, 339514831, 1, -128, 9389635, 1, -128, 56417, 1, -126, 1197, 1, -126, 45, 1, -127, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta150Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta150Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta150Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta150Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta150Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta150Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta150El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta150Shift : polyRoundApx 128 d2Delta150Lo d2Delta150Hi d2Delta150Fq.poly = (d2Delta150S,d2Delta150Es) := by decide +kernel
theorem d2Delta150Sites : mergeSites d2Delta150Fq.plogs = [] := by decide +kernel
theorem d2Delta150PData : d2Delta150Pd = [] := by decide +kernel
theorem d2Delta150Plogs : plogsRoundM 16 24 20 128 d2Delta150Lo d2Delta150Hi (mergeSites d2Delta150Fq.plogs) d2Delta150Pd = some (d2Delta150Ap,d2Delta150Ep) := by
  rw [d2Delta150Sites,d2Delta150PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta150Poles : polesRoundM 16 24 12 128 d2Delta150Lo d2Delta150Hi d2Delta150Fq.poles d2Delta150Qd = some (d2Delta150Aq,d2Delta150Eq) := by decide +kernel
theorem d2Delta150Laurent : laurentRoundM 16 30 128 d2Delta150Lo d2Delta150Hi d2Delta150Ts d2Delta150Ld = some (d2Delta150Al,d2Delta150El) := by decide +kernel
theorem d2Delta150Small : chebPolyUB (vecAdd d2Delta150S (vecAdd d2Delta150Ap (vecAdd d2Delta150Aq d2Delta150Al))) d2Delta150Gam+d2Delta150Es+d2Delta150Ep+d2Delta150Eq+d2Delta150El ≤ (d2LitsStandaloneDelta018.q2 (-7377364298105874003433) 1 (-80)) := by decide +kernel
theorem d2Delta150Check : chebRoundPieceL d2Delta150Fq d2Delta150Ts 16 24 12 20 30 128 d2Delta150Lo d2Delta150Hi d2Delta150Pd d2Delta150Qd d2Delta150Ld d2Delta150Gam (d2LitsStandaloneDelta018.q2 (-7377364298105874003433) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta150Fq d2Delta150Ts 16 24 12 20 30 128 d2Delta150Lo d2Delta150Hi d2Delta150Pd d2Delta150Qd d2Delta150Ld d2Delta150Gam d2Delta150S d2Delta150Ap d2Delta150Aq d2Delta150Al d2Delta150Es d2Delta150Ep d2Delta150Eq d2Delta150El (by decide +kernel) d2Delta150Shift d2Delta150Plogs d2Delta150Poles d2Delta150Laurent]
  exact decide_eq_true d2Delta150Small
theorem d2Delta150Bound : ∀ x ∈ Icc ((d2Delta150Lo : ℚ) : ℝ) ((d2Delta150Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-7377364298105874003433) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta150Fq d2Delta150Ts 16 24 12 20 30 128 d2Delta150Lo d2Delta150Hi d2Delta150Pd d2Delta150Qd d2Delta150Ld d2Delta150Gam (d2LitsStandaloneDelta018.q2 (-7377364298105874003433) 1 (-80)) d2Delta150Check
  simpa only [d2Delta150Fq, d2Delta150Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta150Shift
#print axioms d2Delta150Sites
#print axioms d2Delta150PData
#print axioms d2Delta150Plogs
#print axioms d2Delta150Poles
#print axioms d2Delta150Laurent
#print axioms d2Delta150Small
#print axioms d2Delta150Check
#print axioms d2Delta150Bound

def d2Delta151Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta151Ts : List LTerm := laurentClean []
def d2Delta151Lo : ℚ := (d2LitsStandaloneDelta018.q2 (1055932433) 1 (-30))
def d2Delta151Hi : ℚ := (d2LitsStandaloneDelta018.q2 (66061249) 1 (-26))
def d2Delta151Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta151Qd : List (ℚ × ℚ) := []
def d2Delta151Ld : List LaurentPieceData := []
def d2Delta151Gam : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-68045008872388661068105066828801643371543, 1, -143, 2287245257963968132736089053887886229, 1, -146, 18219480301021509147287973055439225, 1, -142, -8368963092608946687268438206419655, 1, -147, -100733667013666455282198407086661, 1, -143, -11527620021960268167295778077023, 1, -147, 5058032773156027204970804767, 1, -139, 6048246889036007342112032573, 1, -145, -4618362630392593242170835, 1, -141, -3160153476645743849261363, 1, -145, -608984790538641456457, 1, -140, 3989709905980834154933, 1, -148, 5203863398728506111, 1, -144, 427100019016187597, 1, -148, -198192125782715, 1, -143, -69010639710809, 1, -147, -36167227677, 1, -143, -1137394169, 1, -147, 2142241, 1, -143, 1108353, 1, -148, 651, 1, -144, 73, 1, -148, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta151S : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [-2076569989384883945243419013624090899, 1, -128, 8772925563127427950665277395365, 1, -128, 2248695307755757830285047506247, 1, -128, -15851947615328301530512216189, 1, -126, -6177954552309125208980825225, 1, -126, -356973644561575113114418357, 1, -128, 79175919108840872009026719, 1, -128, 1483571827488791060289697, 1, -127, -562273901135835075515, 1, -121, -3091441262533786867021, 1, -127, -76611199261899500847, 1, -128, 972691695514123081, 1, -126, 162793914160288099, 1, -128, 838222786661835, 1, -127, -49403290299437, 1, -128, -1077987809529, 1, -127, -4525716585, 1, -125, -71744789, 1, -127, 2135731, 1, -126, 276705, 1, -128, 651, 1, -125, 73, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta151Ap : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta151Aq : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta151Al : List ℚ := d2LitsStandaloneDelta018.q2listC (raw_ints% [])
def d2Delta151Es : ℚ := (d2LitsStandaloneDelta018.q2 (61) 1 (-127))
def d2Delta151Ep : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta151Eq : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
def d2Delta151El : ℚ := (d2LitsStandaloneDelta018.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta151Shift : polyRoundApx 128 d2Delta151Lo d2Delta151Hi d2Delta151Fq.poly = (d2Delta151S,d2Delta151Es) := by decide +kernel
theorem d2Delta151Sites : mergeSites d2Delta151Fq.plogs = [] := by decide +kernel
theorem d2Delta151PData : d2Delta151Pd = [] := by decide +kernel
theorem d2Delta151Plogs : plogsRoundM 16 24 20 128 d2Delta151Lo d2Delta151Hi (mergeSites d2Delta151Fq.plogs) d2Delta151Pd = some (d2Delta151Ap,d2Delta151Ep) := by
  rw [d2Delta151Sites,d2Delta151PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta151Poles : polesRoundM 16 24 12 128 d2Delta151Lo d2Delta151Hi d2Delta151Fq.poles d2Delta151Qd = some (d2Delta151Aq,d2Delta151Eq) := by decide +kernel
theorem d2Delta151Laurent : laurentRoundM 16 30 128 d2Delta151Lo d2Delta151Hi d2Delta151Ts d2Delta151Ld = some (d2Delta151Al,d2Delta151El) := by decide +kernel
theorem d2Delta151Small : chebPolyUB (vecAdd d2Delta151S (vecAdd d2Delta151Ap (vecAdd d2Delta151Aq d2Delta151Al))) d2Delta151Gam+d2Delta151Es+d2Delta151Ep+d2Delta151Eq+d2Delta151El ≤ (d2LitsStandaloneDelta018.q2 (-7377419628231504777361) 1 (-80)) := by decide +kernel
theorem d2Delta151Check : chebRoundPieceL d2Delta151Fq d2Delta151Ts 16 24 12 20 30 128 d2Delta151Lo d2Delta151Hi d2Delta151Pd d2Delta151Qd d2Delta151Ld d2Delta151Gam (d2LitsStandaloneDelta018.q2 (-7377419628231504777361) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta151Fq d2Delta151Ts 16 24 12 20 30 128 d2Delta151Lo d2Delta151Hi d2Delta151Pd d2Delta151Qd d2Delta151Ld d2Delta151Gam d2Delta151S d2Delta151Ap d2Delta151Aq d2Delta151Al d2Delta151Es d2Delta151Ep d2Delta151Eq d2Delta151El (by decide +kernel) d2Delta151Shift d2Delta151Plogs d2Delta151Poles d2Delta151Laurent]
  exact decide_eq_true d2Delta151Small
theorem d2Delta151Bound : ∀ x ∈ Icc ((d2Delta151Lo : ℚ) : ℝ) ((d2Delta151Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta018.q2 (-7377419628231504777361) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta151Fq d2Delta151Ts 16 24 12 20 30 128 d2Delta151Lo d2Delta151Hi d2Delta151Pd d2Delta151Qd d2Delta151Ld d2Delta151Gam (d2LitsStandaloneDelta018.q2 (-7377419628231504777361) 1 (-80)) d2Delta151Check
  simpa only [d2Delta151Fq, d2Delta151Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta151Shift
#print axioms d2Delta151Sites
#print axioms d2Delta151PData
#print axioms d2Delta151Plogs
#print axioms d2Delta151Poles
#print axioms d2Delta151Laurent
#print axioms d2Delta151Small
#print axioms d2Delta151Check
#print axioms d2Delta151Bound

end StandaloneDelta018
end CatalanMeasure.GenD.Signed.Data.Cells
