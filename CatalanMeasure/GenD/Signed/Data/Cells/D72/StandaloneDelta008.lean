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
namespace d2LitsStandaloneDelta008
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta008
namespace StandaloneDelta008
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta008.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta008.q2listC (raw_ints% []))⟩
def d2Delta64Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta64Ts : List LTerm := laurentClean []
def d2Delta64Lo : ℚ := (d2LitsStandaloneDelta008.q2 (92185513) 1 (-30))
def d2Delta64Hi : ℚ := (d2LitsStandaloneDelta008.q2 (11654133) 1 (-27))
def d2Delta64Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta64Qd : List (ℚ × ℚ) := []
def d2Delta64Ld : List LaurentPieceData := []
def d2Delta64Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918799620407785122761029150806783434680892563, 1, -160, 1773943655467228541505553747360729374857, 1, -160, 52582139054703830118819647260666938865, 1, -160, -140875707180142436629196814711663369, 1, -158, -618319480269782341540956856022359, 1, -157, 11078529363000530956167888374915, 1, -158, 162031189567197752868009551733, 1, -160, -1531793702134301641085547303, 1, -160, -258782595047004846395527, 1, -157, 27707994462683762975707, 1, -160, 3385077003719840419, 1, -160, -71464541391978581, 1, -158, 164667667665645, 1, -160, 451914699305, 1, -158, -6039319117, 1, -160, -3558887911, 1, -160, -1410844347, 1, -159, -1168770181, 1, -159, -457265617, 1, -158, -1495963501, 1, -160, -1153622467, 1, -160, -930321597, 1, -160, -707508165, 1, -160, -561987127, 1, -160, -26353163, 1, -156, -329652181, 1, -160, -30504227, 1, -157, -11731273, 1, -156, -137070413, 1, -160, -51848223, 1, -159, -37335289, 1, -159, -13888795, 1, -158])
def d2Delta64S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-1038284934241658879367201281676744063, 1, -127, 413422096877987570139988784559, 1, -128, 1530917557433314316304043959, 1, -124, -262504639455011506831449437, 1, -127, -9215489161575299432361479, 1, -128, 165122899249400667238771, 1, -128, 1207349835125655029217, 1, -128, -22829220990277940713, 1, -128, -61699587173860817, 1, -128, 1651712597624875, 1, -128, 201648520675, 1, -127, -68159515025, 1, -128, 78534643, 1, -128, 1729033, 1, -128, -859, 1, -126, -15, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta64Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta64Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta64Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta64Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta64Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta64Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta64El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta64Shift : polyRoundApx 128 d2Delta64Lo d2Delta64Hi d2Delta64Fq.poly = (d2Delta64S,d2Delta64Es) := by decide +kernel
theorem d2Delta64Sites : mergeSites d2Delta64Fq.plogs = [] := by decide +kernel
theorem d2Delta64PData : d2Delta64Pd = [] := by decide +kernel
theorem d2Delta64Plogs : plogsRoundM 16 24 20 128 d2Delta64Lo d2Delta64Hi (mergeSites d2Delta64Fq.plogs) d2Delta64Pd = some (d2Delta64Ap,d2Delta64Ep) := by
  rw [d2Delta64Sites,d2Delta64PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta64Poles : polesRoundM 16 24 12 128 d2Delta64Lo d2Delta64Hi d2Delta64Fq.poles d2Delta64Qd = some (d2Delta64Aq,d2Delta64Eq) := by decide +kernel
theorem d2Delta64Laurent : laurentRoundM 16 30 128 d2Delta64Lo d2Delta64Hi d2Delta64Ts d2Delta64Ld = some (d2Delta64Al,d2Delta64El) := by decide +kernel
theorem d2Delta64Small : chebPolyUB (vecAdd d2Delta64S (vecAdd d2Delta64Ap (vecAdd d2Delta64Aq d2Delta64Al))) d2Delta64Gam+d2Delta64Es+d2Delta64Ep+d2Delta64Eq+d2Delta64El ≤ (d2LitsStandaloneDelta008.q2 (-7377456621909649746365) 1 (-80)) := by decide +kernel
theorem d2Delta64Check : chebRoundPieceL d2Delta64Fq d2Delta64Ts 16 24 12 20 30 128 d2Delta64Lo d2Delta64Hi d2Delta64Pd d2Delta64Qd d2Delta64Ld d2Delta64Gam (d2LitsStandaloneDelta008.q2 (-7377456621909649746365) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta64Fq d2Delta64Ts 16 24 12 20 30 128 d2Delta64Lo d2Delta64Hi d2Delta64Pd d2Delta64Qd d2Delta64Ld d2Delta64Gam d2Delta64S d2Delta64Ap d2Delta64Aq d2Delta64Al d2Delta64Es d2Delta64Ep d2Delta64Eq d2Delta64El (by decide +kernel) d2Delta64Shift d2Delta64Plogs d2Delta64Poles d2Delta64Laurent]
  exact decide_eq_true d2Delta64Small
theorem d2Delta64Bound : ∀ x ∈ Icc ((d2Delta64Lo : ℚ) : ℝ) ((d2Delta64Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-7377456621909649746365) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta64Fq d2Delta64Ts 16 24 12 20 30 128 d2Delta64Lo d2Delta64Hi d2Delta64Pd d2Delta64Qd d2Delta64Ld d2Delta64Gam (d2LitsStandaloneDelta008.q2 (-7377456621909649746365) 1 (-80)) d2Delta64Check
  simpa only [d2Delta64Fq, d2Delta64Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta64Shift
#print axioms d2Delta64Sites
#print axioms d2Delta64PData
#print axioms d2Delta64Plogs
#print axioms d2Delta64Poles
#print axioms d2Delta64Laurent
#print axioms d2Delta64Small
#print axioms d2Delta64Check
#print axioms d2Delta64Bound

def d2Delta65Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta65Ts : List LTerm := laurentClean []
def d2Delta65Lo : ℚ := (d2LitsStandaloneDelta008.q2 (11654133) 1 (-27))
def d2Delta65Hi : ℚ := (d2LitsStandaloneDelta008.q2 (47664083) 1 (-29))
def d2Delta65Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta65Qd : List (ℚ × ℚ) := []
def d2Delta65Ld : List LaurentPieceData := []
def d2Delta65Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918793297399883472258405645829755782740114579, 1, -160, 583503044517534474925897027098339153207, 1, -157, 165712844435510853126151177589351564785, 1, -160, -1329798662862689751901318787574436491, 1, -158, -7079426799869937549940711937307991, 1, -157, 1565925097835742594645013497021511, 1, -160, 6150352363471531342384112740213, 1, -160, -204102703926158767270483172185, 1, -160, -18530458108136833176998023, 1, -157, 7000503842393999027529803, 1, -159, -15329188128382631505245, 1, -160, -275458587064878321471, 1, -159, 1226081105143550701, 1, -160, 13378932509409851, 1, -160, -40218394145357, 1, -160, -111862735781, 1, -159, -1007732411, 1, -159, -318190685, 1, -157, -457265617, 1, -158, -820271887, 1, -159, -1153622467, 1, -160, -256944525, 1, -158, -707508165, 1, -160, -626027315, 1, -160, -26353163, 1, -156, -185231387, 1, -159, -30504227, 1, -157, -53210281, 1, -158, -137070413, 1, -160, -59321107, 1, -159, -37335289, 1, -159, -64121543, 1, -160])
def d2Delta65S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-2076568422645649284280093870675807449, 1, -128, 272644088321188592686987399069, 1, -126, 77271573920105340767432365785, 1, -128, -38759223642394159243900307, 1, -121, -105560420969961283237963011, 1, -128, 1459712344066106018376817, 1, -126, 2864532999755597998653, 1, -124, -3043245333995889633791, 1, -128, -2206717532381197777, 1, -127, 208721587708514875, 1, -126, -1829135918436495, 1, -128, -131390361811547, 1, -128, 584909531295, 1, -128, 12762295307, 1, -128, -19181755, 1, -126, -838909, 1, -128, 6151, 1, -128, 39, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta65Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta65Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta65Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta65Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta65Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta65Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta65El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta65Shift : polyRoundApx 128 d2Delta65Lo d2Delta65Hi d2Delta65Fq.poly = (d2Delta65S,d2Delta65Es) := by decide +kernel
theorem d2Delta65Sites : mergeSites d2Delta65Fq.plogs = [] := by decide +kernel
theorem d2Delta65PData : d2Delta65Pd = [] := by decide +kernel
theorem d2Delta65Plogs : plogsRoundM 16 24 20 128 d2Delta65Lo d2Delta65Hi (mergeSites d2Delta65Fq.plogs) d2Delta65Pd = some (d2Delta65Ap,d2Delta65Ep) := by
  rw [d2Delta65Sites,d2Delta65PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta65Poles : polesRoundM 16 24 12 128 d2Delta65Lo d2Delta65Hi d2Delta65Fq.poles d2Delta65Qd = some (d2Delta65Aq,d2Delta65Eq) := by decide +kernel
theorem d2Delta65Laurent : laurentRoundM 16 30 128 d2Delta65Lo d2Delta65Hi d2Delta65Ts d2Delta65Ld = some (d2Delta65Al,d2Delta65El) := by decide +kernel
theorem d2Delta65Small : chebPolyUB (vecAdd d2Delta65S (vecAdd d2Delta65Ap (vecAdd d2Delta65Aq d2Delta65Al))) d2Delta65Gam+d2Delta65Es+d2Delta65Ep+d2Delta65Eq+d2Delta65El ≤ (d2LitsStandaloneDelta008.q2 (-3688724450077645840223) 1 (-79)) := by decide +kernel
theorem d2Delta65Check : chebRoundPieceL d2Delta65Fq d2Delta65Ts 16 24 12 20 30 128 d2Delta65Lo d2Delta65Hi d2Delta65Pd d2Delta65Qd d2Delta65Ld d2Delta65Gam (d2LitsStandaloneDelta008.q2 (-3688724450077645840223) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta65Fq d2Delta65Ts 16 24 12 20 30 128 d2Delta65Lo d2Delta65Hi d2Delta65Pd d2Delta65Qd d2Delta65Ld d2Delta65Gam d2Delta65S d2Delta65Ap d2Delta65Aq d2Delta65Al d2Delta65Es d2Delta65Ep d2Delta65Eq d2Delta65El (by decide +kernel) d2Delta65Shift d2Delta65Plogs d2Delta65Poles d2Delta65Laurent]
  exact decide_eq_true d2Delta65Small
theorem d2Delta65Bound : ∀ x ∈ Icc ((d2Delta65Lo : ℚ) : ℝ) ((d2Delta65Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-3688724450077645840223) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta65Fq d2Delta65Ts 16 24 12 20 30 128 d2Delta65Lo d2Delta65Hi d2Delta65Pd d2Delta65Qd d2Delta65Ld d2Delta65Gam (d2LitsStandaloneDelta008.q2 (-3688724450077645840223) 1 (-79)) d2Delta65Check
  simpa only [d2Delta65Fq, d2Delta65Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta65Shift
#print axioms d2Delta65Sites
#print axioms d2Delta65PData
#print axioms d2Delta65Plogs
#print axioms d2Delta65Poles
#print axioms d2Delta65Laurent
#print axioms d2Delta65Small
#print axioms d2Delta65Check
#print axioms d2Delta65Bound

def d2Delta66Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta66Ts : List LTerm := laurentClean []
def d2Delta66Lo : ℚ := (d2LitsStandaloneDelta008.q2 (47664083) 1 (-29))
def d2Delta66Hi : ℚ := (d2LitsStandaloneDelta008.q2 (24355817) 1 (-28))
def d2Delta66Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta66Qd : List (ℚ × ℚ) := []
def d2Delta66Ld : List LaurentPieceData := []
def d2Delta66Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918782847055829104754394731712334918430990883, 1, -160, 2862711791134743530001186375008478743939, 1, -159, 48749839534305726217043954029744037089, 1, -159, -5968739994857493863624157245839674703, 1, -160, -24304545990463817357595566556235071, 1, -160, 411219835515276162305143543399709, 1, -158, 55465516128452909947833102989, 1, -157, -3139789698159598062885253833, 1, -154, 339089087234313033123308235, 1, -160, 1615343151255041021574787, 1, -157, -19020147824698156942957, 1, -159, -238190576150522102253, 1, -159, 1857212689020579055, 1, -160, 10788000114816279, 1, -160, -51758392910567, 1, -160, -167045114833, 1, -160, -1027584917, 1, -159, -2547665897, 1, -160, -981146243, 1, -159, -822925957, 1, -159, -1243947903, 1, -160, -1032680485, 1, -160, -766219699, 1, -160, -629485417, 1, -160, -229112503, 1, -159, -372596001, 1, -160, -265860473, 1, -160, -214037299, 1, -160, -37385697, 1, -158, -119259697, 1, -160, -81491409, 1, -160, -4026011, 1, -156])
def d2Delta66S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-2076565973595672557768717613395743829, 1, -128, 668612544897188425743860954133, 1, -127, 11361774667243483998128838163, 1, -126, -1391621121486434130025199147, 1, -126, -45275691061381303912151147, 1, -128, 1533223611113321159451383, 1, -126, 1642890590099163385091, 1, -127, -2996070181601618860607, 1, -128, 5058491088318249963, 1, -127, 770568019388962913, 1, -128, -2268706928915983, 1, -127, -113611557735661, 1, -128, 885933565835, 1, -128, 10290578871, 1, -128, -98741873, 1, -128, -622693, 1, -128, 3643, 1, -127, 13, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta66Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta66Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta66Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta66Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta66Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta66Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta66El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta66Shift : polyRoundApx 128 d2Delta66Lo d2Delta66Hi d2Delta66Fq.poly = (d2Delta66S,d2Delta66Es) := by decide +kernel
theorem d2Delta66Sites : mergeSites d2Delta66Fq.plogs = [] := by decide +kernel
theorem d2Delta66PData : d2Delta66Pd = [] := by decide +kernel
theorem d2Delta66Plogs : plogsRoundM 16 24 20 128 d2Delta66Lo d2Delta66Hi (mergeSites d2Delta66Fq.plogs) d2Delta66Pd = some (d2Delta66Ap,d2Delta66Ep) := by
  rw [d2Delta66Sites,d2Delta66PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta66Poles : polesRoundM 16 24 12 128 d2Delta66Lo d2Delta66Hi d2Delta66Fq.poles d2Delta66Qd = some (d2Delta66Aq,d2Delta66Eq) := by decide +kernel
theorem d2Delta66Laurent : laurentRoundM 16 30 128 d2Delta66Lo d2Delta66Hi d2Delta66Ts d2Delta66Ld = some (d2Delta66Al,d2Delta66El) := by decide +kernel
theorem d2Delta66Small : chebPolyUB (vecAdd d2Delta66S (vecAdd d2Delta66Ap (vecAdd d2Delta66Aq d2Delta66Al))) d2Delta66Gam+d2Delta66Es+d2Delta66Ep+d2Delta66Eq+d2Delta66El ≤ (d2LitsStandaloneDelta008.q2 (-3688719718543577647249) 1 (-79)) := by decide +kernel
theorem d2Delta66Check : chebRoundPieceL d2Delta66Fq d2Delta66Ts 16 24 12 20 30 128 d2Delta66Lo d2Delta66Hi d2Delta66Pd d2Delta66Qd d2Delta66Ld d2Delta66Gam (d2LitsStandaloneDelta008.q2 (-3688719718543577647249) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta66Fq d2Delta66Ts 16 24 12 20 30 128 d2Delta66Lo d2Delta66Hi d2Delta66Pd d2Delta66Qd d2Delta66Ld d2Delta66Gam d2Delta66S d2Delta66Ap d2Delta66Aq d2Delta66Al d2Delta66Es d2Delta66Ep d2Delta66Eq d2Delta66El (by decide +kernel) d2Delta66Shift d2Delta66Plogs d2Delta66Poles d2Delta66Laurent]
  exact decide_eq_true d2Delta66Small
theorem d2Delta66Bound : ∀ x ∈ Icc ((d2Delta66Lo : ℚ) : ℝ) ((d2Delta66Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-3688719718543577647249) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta66Fq d2Delta66Ts 16 24 12 20 30 128 d2Delta66Lo d2Delta66Hi d2Delta66Pd d2Delta66Qd d2Delta66Ld d2Delta66Gam (d2LitsStandaloneDelta008.q2 (-3688719718543577647249) 1 (-79)) d2Delta66Check
  simpa only [d2Delta66Fq, d2Delta66Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta66Shift
#print axioms d2Delta66Sites
#print axioms d2Delta66PData
#print axioms d2Delta66Plogs
#print axioms d2Delta66Poles
#print axioms d2Delta66Laurent
#print axioms d2Delta66Small
#print axioms d2Delta66Check
#print axioms d2Delta66Bound

def d2Delta67Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta67Ts : List LTerm := laurentClean []
def d2Delta67Lo : ℚ := (d2LitsStandaloneDelta008.q2 (24355817) 1 (-28))
def d2Delta67Hi : ℚ := (d2LitsStandaloneDelta008.q2 (49759185) 1 (-29))
def d2Delta67Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta67Qd : List (ℚ × ℚ) := []
def d2Delta67Ld : List LaurentPieceData := []
def d2Delta67Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918770846045013640257481528462354561372105807, 1, -160, 6214805245240117449068586539072562573779, 1, -160, 24623895245733705702920656770931202371, 1, -160, -6095738976836260486288640635990085869, 1, -160, 8251907486198490471894842318950355, 1, -160, 1589655207367854405124434885205941, 1, -160, -4963252347287015748461865092401, 1, -160, -182985210088119238014069500155, 1, -160, 772120283974046724068989933, 1, -160, 11010043501131487585062327, 1, -160, -56855707269116738891101, 1, -160, -375033164189856516245, 1, -160, 584632871836139773, 1, -158, 956353986782975, 1, -157, -59651440933549, 1, -160, -102835870839, 1, -160, -1777042105, 1, -160, -1277613293, 1, -159, -1825978185, 1, -160, -412479141, 1, -158, -1150799797, 1, -160, -1035505711, 1, -160, -352569487, 1, -159, -39463471, 1, -156, -419803259, 1, -160, -373831659, 1, -160, -242685451, 1, -160, -53693057, 1, -158, -136144729, 1, -160, -119665911, 1, -160, -74070945, 1, -160, -64625073, 1, -160])
def d2Delta67S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-2076563162417302842829484565154523833, 1, -128, 725628390410875277003888879095, 1, -127, 5725501788352252947500629655, 1, -127, -355281507072292904168007075, 1, -124, 15425872887542327806863341, 1, -128, 2963349970315629088269103, 1, -127, -2314071776238500888165, 1, -124, -1364084459709243630523, 1, -127, 11513962855040506531, 1, -127, 164123913098412157, 1, -126, -6781074314145075, 1, -128, -11179823695979, 1, -125, 1115496951459, 1, -128, 7297823317, 1, -128, -28449951, 1, -126, -377639, 1, -128, 7947, 1, -128, 3, 1, -126, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta67Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta67Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta67Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta67Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta67Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta67Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta67El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta67Shift : polyRoundApx 128 d2Delta67Lo d2Delta67Hi d2Delta67Fq.poly = (d2Delta67S,d2Delta67Es) := by decide +kernel
theorem d2Delta67Sites : mergeSites d2Delta67Fq.plogs = [] := by decide +kernel
theorem d2Delta67PData : d2Delta67Pd = [] := by decide +kernel
theorem d2Delta67Plogs : plogsRoundM 16 24 20 128 d2Delta67Lo d2Delta67Hi (mergeSites d2Delta67Fq.plogs) d2Delta67Pd = some (d2Delta67Ap,d2Delta67Ep) := by
  rw [d2Delta67Sites,d2Delta67PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta67Poles : polesRoundM 16 24 12 128 d2Delta67Lo d2Delta67Hi d2Delta67Fq.poles d2Delta67Qd = some (d2Delta67Aq,d2Delta67Eq) := by decide +kernel
theorem d2Delta67Laurent : laurentRoundM 16 30 128 d2Delta67Lo d2Delta67Hi d2Delta67Ts d2Delta67Ld = some (d2Delta67Al,d2Delta67El) := by decide +kernel
theorem d2Delta67Small : chebPolyUB (vecAdd d2Delta67S (vecAdd d2Delta67Ap (vecAdd d2Delta67Aq d2Delta67Al))) d2Delta67Gam+d2Delta67Es+d2Delta67Ep+d2Delta67Eq+d2Delta67El ≤ (d2LitsStandaloneDelta008.q2 (-3688714582733179374851) 1 (-79)) := by decide +kernel
theorem d2Delta67Check : chebRoundPieceL d2Delta67Fq d2Delta67Ts 16 24 12 20 30 128 d2Delta67Lo d2Delta67Hi d2Delta67Pd d2Delta67Qd d2Delta67Ld d2Delta67Gam (d2LitsStandaloneDelta008.q2 (-3688714582733179374851) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta67Fq d2Delta67Ts 16 24 12 20 30 128 d2Delta67Lo d2Delta67Hi d2Delta67Pd d2Delta67Qd d2Delta67Ld d2Delta67Gam d2Delta67S d2Delta67Ap d2Delta67Aq d2Delta67Al d2Delta67Es d2Delta67Ep d2Delta67Eq d2Delta67El (by decide +kernel) d2Delta67Shift d2Delta67Plogs d2Delta67Poles d2Delta67Laurent]
  exact decide_eq_true d2Delta67Small
theorem d2Delta67Bound : ∀ x ∈ Icc ((d2Delta67Lo : ℚ) : ℝ) ((d2Delta67Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-3688714582733179374851) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta67Fq d2Delta67Ts 16 24 12 20 30 128 d2Delta67Lo d2Delta67Hi d2Delta67Pd d2Delta67Qd d2Delta67Ld d2Delta67Gam (d2LitsStandaloneDelta008.q2 (-3688714582733179374851) 1 (-79)) d2Delta67Check
  simpa only [d2Delta67Fq, d2Delta67Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta67Shift
#print axioms d2Delta67Sites
#print axioms d2Delta67PData
#print axioms d2Delta67Plogs
#print axioms d2Delta67Poles
#print axioms d2Delta67Laurent
#print axioms d2Delta67Small
#print axioms d2Delta67Check
#print axioms d2Delta67Bound

def d2Delta68Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta68Ts : List LTerm := laurentClean []
def d2Delta68Lo : ℚ := (d2LitsStandaloneDelta008.q2 (49759185) 1 (-29))
def d2Delta68Hi : ℚ := (d2LitsStandaloneDelta008.q2 (100565921) 1 (-30))
def d2Delta68Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta68Qd : List (ℚ × ℚ) := []
def d2Delta68Ld : List LaurentPieceData := []
def d2Delta68Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918761499586625319045543402775077821414878287, 1, -160, 3106489556020019655184259774157261973065, 1, -160, -7360314411011962971681542505906988733, 1, -160, -366405092693670883006510237834402017, 1, -159, 1955854907841844692405286651727827, 1, -160, 22935606160884488549576250304281, 1, -159, -134272212166511793326530643249, 1, -160, -78683841130183374652683113, 1, -156, 4083159828525726734736365, 1, -160, 557585954852412159183, 1, -155, -66222281825706274141, 1, -160, -69854310628438359, 1, -159, 157936713679101, 1, -158, 613346013135, 1, -160, -8079964845, 1, -160, -1832697701, 1, -159, -2818671289, 1, -160, -607789103, 1, -158, -1825978185, 1, -160, -49097069, 1, -155, -1150799797, 1, -160, -61764333, 1, -156, -352569487, 1, -159, -604532887, 1, -160, -419803259, 1, -160, -359356387, 1, -160, -242685451, 1, -160, -207398033, 1, -160, -136144729, 1, -160, -29028843, 1, -158, -74070945, 1, -160, -7876399, 1, -157])
def d2Delta68S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-2076560978829943323240020124669628543, 1, -128, 361898939118377869031398635083, 1, -127, -107220534688655928212298081, 1, -123, -10667129522693959214088401, 1, -122, 3644564417714907814013987, 1, -128, 170916413492488042658781, 1, -128, -1000649331234325619673, 1, -128, -18762082591432438637, 1, -128, 121707382364850637, 1, -128, 531801205583055, 1, -127, -7895214933101, 1, -128, -8327761717, 1, -126, 150634497, 1, -127, 295041, 1, -127, -7333, 1, -128, -3, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta68Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta68Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta68Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta68Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta68Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta68Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta68El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta68Shift : polyRoundApx 128 d2Delta68Lo d2Delta68Hi d2Delta68Fq.poly = (d2Delta68S,d2Delta68Es) := by decide +kernel
theorem d2Delta68Sites : mergeSites d2Delta68Fq.plogs = [] := by decide +kernel
theorem d2Delta68PData : d2Delta68Pd = [] := by decide +kernel
theorem d2Delta68Plogs : plogsRoundM 16 24 20 128 d2Delta68Lo d2Delta68Hi (mergeSites d2Delta68Fq.plogs) d2Delta68Pd = some (d2Delta68Ap,d2Delta68Ep) := by
  rw [d2Delta68Sites,d2Delta68PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta68Poles : polesRoundM 16 24 12 128 d2Delta68Lo d2Delta68Hi d2Delta68Fq.poles d2Delta68Qd = some (d2Delta68Aq,d2Delta68Eq) := by decide +kernel
theorem d2Delta68Laurent : laurentRoundM 16 30 128 d2Delta68Lo d2Delta68Hi d2Delta68Ts d2Delta68Ld = some (d2Delta68Al,d2Delta68El) := by decide +kernel
theorem d2Delta68Small : chebPolyUB (vecAdd d2Delta68S (vecAdd d2Delta68Ap (vecAdd d2Delta68Aq d2Delta68Al))) d2Delta68Gam+d2Delta68Es+d2Delta68Ep+d2Delta68Eq+d2Delta68El ≤ (d2LitsStandaloneDelta008.q2 (-7377424024118358912781) 1 (-80)) := by decide +kernel
theorem d2Delta68Check : chebRoundPieceL d2Delta68Fq d2Delta68Ts 16 24 12 20 30 128 d2Delta68Lo d2Delta68Hi d2Delta68Pd d2Delta68Qd d2Delta68Ld d2Delta68Gam (d2LitsStandaloneDelta008.q2 (-7377424024118358912781) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta68Fq d2Delta68Ts 16 24 12 20 30 128 d2Delta68Lo d2Delta68Hi d2Delta68Pd d2Delta68Qd d2Delta68Ld d2Delta68Gam d2Delta68S d2Delta68Ap d2Delta68Aq d2Delta68Al d2Delta68Es d2Delta68Ep d2Delta68Eq d2Delta68El (by decide +kernel) d2Delta68Shift d2Delta68Plogs d2Delta68Poles d2Delta68Laurent]
  exact decide_eq_true d2Delta68Small
theorem d2Delta68Bound : ∀ x ∈ Icc ((d2Delta68Lo : ℚ) : ℝ) ((d2Delta68Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-7377424024118358912781) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta68Fq d2Delta68Ts 16 24 12 20 30 128 d2Delta68Lo d2Delta68Hi d2Delta68Pd d2Delta68Qd d2Delta68Ld d2Delta68Gam (d2LitsStandaloneDelta008.q2 (-7377424024118358912781) 1 (-80)) d2Delta68Check
  simpa only [d2Delta68Fq, d2Delta68Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta68Shift
#print axioms d2Delta68Sites
#print axioms d2Delta68PData
#print axioms d2Delta68Plogs
#print axioms d2Delta68Poles
#print axioms d2Delta68Laurent
#print axioms d2Delta68Small
#print axioms d2Delta68Check
#print axioms d2Delta68Bound

def d2Delta69Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta69Ts : List LTerm := laurentClean []
def d2Delta69Lo : ℚ := (d2LitsStandaloneDelta008.q2 (100565921) 1 (-30))
def d2Delta69Hi : ℚ := (d2LitsStandaloneDelta008.q2 (3175421) 1 (-25))
def d2Delta69Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta69Qd : List (ℚ × ℚ) := []
def d2Delta69Ld : List LaurentPieceData := []
def d2Delta69Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918755372916080609526196108112944594886098713, 1, -160, 3013032672658932919256104361475217119013, 1, -160, -3984149705526720953699846393144826283, 1, -158, -173590978981105077128932622876036741, 1, -158, 177392331333475341716833769902141, 1, -156, 21120507280689773590526630586695, 1, -159, -167600464294685357722200103921, 1, -160, -1118525640481461071264382575, 1, -160, 4676419397455000154607075, 1, -160, 15079947640526553763255, 1, -160, -71691971734115701029, 1, -160, -54351257628914513, 1, -159, 658288085993091, 1, -160, 197958355327, 1, -159, -1049722293, 1, -157, -1928262383, 1, -159, -3013066351, 1, -160, -2559897587, 1, -160, -982647323, 1, -159, -1653458617, 1, -160, -1246722607, 1, -160, -1038286675, 1, -160, -768571799, 1, -160, -633412125, 1, -160, -460078069, 1, -160, -187579117, 1, -159, -133613957, 1, -159, -215591583, 1, -160, -75246315, 1, -159, -120137661, 1, -160, -82114465, 1, -160, -64878683, 1, -160])
def d2Delta69S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-1038279775178134830495439924075110691, 1, -127, 702011393294578604931822554977, 1, -128, -7426344528697072244956975089, 1, -128, -646873504535330997221154337, 1, -128, 5288576702872936048402999, 1, -128, 78694605544265124703059, 1, -127, -1248999522322101431513, 1, -128, -520917291191033487, 1, -123, 139389525435000371, 1, -128, 898906194819157, 1, -128, -8547290749637, 1, -128, -25917941967, 1, -128, 313925381, 1, -128, 187, 1, -117, -3721, 1, -127, -1, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta69Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta69Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta69Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta69Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta69Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta69Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta69El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta69Shift : polyRoundApx 128 d2Delta69Lo d2Delta69Hi d2Delta69Fq.poly = (d2Delta69S,d2Delta69Es) := by decide +kernel
theorem d2Delta69Sites : mergeSites d2Delta69Fq.plogs = [] := by decide +kernel
theorem d2Delta69PData : d2Delta69Pd = [] := by decide +kernel
theorem d2Delta69Plogs : plogsRoundM 16 24 20 128 d2Delta69Lo d2Delta69Hi (mergeSites d2Delta69Fq.plogs) d2Delta69Pd = some (d2Delta69Ap,d2Delta69Ep) := by
  rw [d2Delta69Sites,d2Delta69PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta69Poles : polesRoundM 16 24 12 128 d2Delta69Lo d2Delta69Hi d2Delta69Fq.poles d2Delta69Qd = some (d2Delta69Aq,d2Delta69Eq) := by decide +kernel
theorem d2Delta69Laurent : laurentRoundM 16 30 128 d2Delta69Lo d2Delta69Hi d2Delta69Ts d2Delta69Ld = some (d2Delta69Al,d2Delta69El) := by decide +kernel
theorem d2Delta69Small : chebPolyUB (vecAdd d2Delta69S (vecAdd d2Delta69Ap (vecAdd d2Delta69Aq d2Delta69Al))) d2Delta69Gam+d2Delta69Es+d2Delta69Ep+d2Delta69Eq+d2Delta69El ≤ (d2LitsStandaloneDelta008.q2 (-115272172289030089439) 1 (-74)) := by decide +kernel
theorem d2Delta69Check : chebRoundPieceL d2Delta69Fq d2Delta69Ts 16 24 12 20 30 128 d2Delta69Lo d2Delta69Hi d2Delta69Pd d2Delta69Qd d2Delta69Ld d2Delta69Gam (d2LitsStandaloneDelta008.q2 (-115272172289030089439) 1 (-74)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta69Fq d2Delta69Ts 16 24 12 20 30 128 d2Delta69Lo d2Delta69Hi d2Delta69Pd d2Delta69Qd d2Delta69Ld d2Delta69Gam d2Delta69S d2Delta69Ap d2Delta69Aq d2Delta69Al d2Delta69Es d2Delta69Ep d2Delta69Eq d2Delta69El (by decide +kernel) d2Delta69Shift d2Delta69Plogs d2Delta69Poles d2Delta69Laurent]
  exact decide_eq_true d2Delta69Small
theorem d2Delta69Bound : ∀ x ∈ Icc ((d2Delta69Lo : ℚ) : ℝ) ((d2Delta69Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-115272172289030089439) 1 (-74)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta69Fq d2Delta69Ts 16 24 12 20 30 128 d2Delta69Lo d2Delta69Hi d2Delta69Pd d2Delta69Qd d2Delta69Ld d2Delta69Gam (d2LitsStandaloneDelta008.q2 (-115272172289030089439) 1 (-74)) d2Delta69Check
  simpa only [d2Delta69Fq, d2Delta69Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta69Shift
#print axioms d2Delta69Sites
#print axioms d2Delta69PData
#print axioms d2Delta69Plogs
#print axioms d2Delta69Poles
#print axioms d2Delta69Laurent
#print axioms d2Delta69Small
#print axioms d2Delta69Check
#print axioms d2Delta69Bound

def d2Delta70Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta70Ts : List LTerm := laurentClean []
def d2Delta70Lo : ℚ := (d2LitsStandaloneDelta008.q2 (3175421) 1 (-25))
def d2Delta70Hi : ℚ := (d2LitsStandaloneDelta008.q2 (26450919) 1 (-28))
def d2Delta70Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta70Qd : List (ℚ × ℚ) := []
def d2Delta70Ld : List LaurentPieceData := []
def d2Delta70Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918741961273543009300218274601505581239648025, 1, -160, 618796067796012407270722870461977086021, 1, -156, -137555458305914071113889812166858545579, 1, -158, -34564224616884162433312258154830895715, 1, -160, 74277728133112318300952559482250301, 1, -156, 30763235086865853294955277791960909, 1, -160, -946208893416189443384005890464753, 1, -160, -11436597099592209437449202411703, 1, -160, 372538432561785122687320329699, 1, -160, 1954351930240753593536212235, 1, -160, -82949996052212381545517349, 1, -160, -58765741562385928891931, 1, -159, 11312856864857016215171, 1, -160, -146563255388565495, 1, -154, -126593151216348597, 1, -157, 2216644332780341, 1, -160, 63957741535633, 1, -160, -199807381973, 1, -160, -2489827867, 1, -159, -11832479, 1, -153, -1246616111, 1, -160, -949095159, 1, -160, -768571799, 1, -160, -573250273, 1, -160, -460078069, 1, -160, -20999409, 1, -156, -133613957, 1, -159, -190986385, 1, -160, -75246315, 1, -159, -105228401, 1, -160, -82114465, 1, -160, -28084389, 1, -159])
def d2Delta70S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-2076556303040664539206616269675228479, 1, -128, 2329373651844462261102150849461, 1, -128, -129217312128028202972876300295, 1, -127, -32333844307172025810572187389, 1, -128, 2224237394347103901727089403, 1, -128, 57450205167966580866165091, 1, -127, -3536016141600472147537327, 1, -127, -42670188236554520038571, 1, -126, 2781812426666145485819, 1, -126, 58282737917966280353, 1, -127, -2476150641992378339, 1, -126, -27992568710030039, 1, -128, 5401154494906137, 1, -128, -8977243003599, 1, -128, -966805443127, 1, -127, 8468650321, 1, -128, 488395929, 1, -128, -3015713, 1, -128, -92057, 1, -128, 687, 1, -128, 13, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta70Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta70Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta70Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta70Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta70Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta70Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta70El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta70Shift : polyRoundApx 128 d2Delta70Lo d2Delta70Hi d2Delta70Fq.poly = (d2Delta70S,d2Delta70Es) := by decide +kernel
theorem d2Delta70Sites : mergeSites d2Delta70Fq.plogs = [] := by decide +kernel
theorem d2Delta70PData : d2Delta70Pd = [] := by decide +kernel
theorem d2Delta70Plogs : plogsRoundM 16 24 20 128 d2Delta70Lo d2Delta70Hi (mergeSites d2Delta70Fq.plogs) d2Delta70Pd = some (d2Delta70Ap,d2Delta70Ep) := by
  rw [d2Delta70Sites,d2Delta70PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta70Poles : polesRoundM 16 24 12 128 d2Delta70Lo d2Delta70Hi d2Delta70Fq.poles d2Delta70Qd = some (d2Delta70Aq,d2Delta70Eq) := by decide +kernel
theorem d2Delta70Laurent : laurentRoundM 16 30 128 d2Delta70Lo d2Delta70Hi d2Delta70Ts d2Delta70Ld = some (d2Delta70Al,d2Delta70El) := by decide +kernel
theorem d2Delta70Small : chebPolyUB (vecAdd d2Delta70S (vecAdd d2Delta70Ap (vecAdd d2Delta70Aq d2Delta70Al))) d2Delta70Gam+d2Delta70Es+d2Delta70Ep+d2Delta70Eq+d2Delta70El ≤ (d2LitsStandaloneDelta008.q2 (-922175220537235995765) 1 (-77)) := by decide +kernel
theorem d2Delta70Check : chebRoundPieceL d2Delta70Fq d2Delta70Ts 16 24 12 20 30 128 d2Delta70Lo d2Delta70Hi d2Delta70Pd d2Delta70Qd d2Delta70Ld d2Delta70Gam (d2LitsStandaloneDelta008.q2 (-922175220537235995765) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta70Fq d2Delta70Ts 16 24 12 20 30 128 d2Delta70Lo d2Delta70Hi d2Delta70Pd d2Delta70Qd d2Delta70Ld d2Delta70Gam d2Delta70S d2Delta70Ap d2Delta70Aq d2Delta70Al d2Delta70Es d2Delta70Ep d2Delta70Eq d2Delta70El (by decide +kernel) d2Delta70Shift d2Delta70Plogs d2Delta70Poles d2Delta70Laurent]
  exact decide_eq_true d2Delta70Small
theorem d2Delta70Bound : ∀ x ∈ Icc ((d2Delta70Lo : ℚ) : ℝ) ((d2Delta70Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-922175220537235995765) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta70Fq d2Delta70Ts 16 24 12 20 30 128 d2Delta70Lo d2Delta70Hi d2Delta70Pd d2Delta70Qd d2Delta70Ld d2Delta70Gam (d2LitsStandaloneDelta008.q2 (-922175220537235995765) 1 (-77)) d2Delta70Check
  simpa only [d2Delta70Fq, d2Delta70Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta70Shift
#print axioms d2Delta70Sites
#print axioms d2Delta70PData
#print axioms d2Delta70Plogs
#print axioms d2Delta70Poles
#print axioms d2Delta70Laurent
#print axioms d2Delta70Small
#print axioms d2Delta70Check
#print axioms d2Delta70Bound

def d2Delta71Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta71Ts : List LTerm := laurentClean []
def d2Delta71Lo : ℚ := (d2LitsStandaloneDelta008.q2 (26450919) 1 (-28))
def d2Delta71Hi : ℚ := (d2LitsStandaloneDelta008.q2 (106851227) 1 (-30))
def d2Delta71Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta71Qd : List (ℚ × ℚ) := []
def d2Delta71Ld : List LaurentPieceData := []
def d2Delta71Gam : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-8918730932863718186931091308930319458252182969, 1, -160, 207962911518161115499011402177143141919, 1, -157, -47873582315865656512472394577557068367, 1, -160, -41317561553085570722124216336351257, 1, -157, 2900496567523440919699736615081919, 1, -159, 1884124766053926321949295988883, 1, -157, -132107123184120105806371126535, 1, -159, -226031454990011170823859095, 1, -160, 3004958957846244555610565, 1, -159, -470109509381789742427, 1, -160, -38964874419569747505, 1, -159, 50582229921716915, 1, -160, 155923528027835, 1, -158, -161064039845, 1, -158, -7529825761, 1, -160, -3413811095, 1, -160, -1407936589, 1, -159, -560788997, 1, -158, -1823056947, 1, -160, -1433106239, 1, -160, -143509235, 1, -157, -13917565, 1, -154, -351402991, 1, -159, -269113837, 1, -159, -208973421, 1, -159, -157988815, 1, -159, -241301005, 1, -160, -180102169, 1, -160, -135172183, 1, -160, -49799317, 1, -159, -73425257, 1, -160, -53401605, 1, -160])
def d2Delta71S : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [-2076553852526548927116704068736231133, 1, -128, 48449000721713988919505592129, 1, -125, -696990008384894783214391661, 1, -123, -76977503620961910724329205, 1, -126, 10808144771917436546552541, 1, -128, 3509824242424100859109, 1, -124, -1968907776766842723427, 1, -128, -1684034032961045651, 1, -127, 89566368562896749, 1, -127, -28053877087197, 1, -128, -1161355279205, 1, -125, 12061726335, 1, -128, 297425489, 1, -128, -609633, 1, -128, -393, 1, -124, 1, 1, -124, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta71Ap : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta71Aq : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta71Al : List ℚ := d2LitsStandaloneDelta008.q2listC (raw_ints% [])
def d2Delta71Es : ℚ := (d2LitsStandaloneDelta008.q2 (61) 1 (-127))
def d2Delta71Ep : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta71Eq : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
def d2Delta71El : ℚ := (d2LitsStandaloneDelta008.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta71Shift : polyRoundApx 128 d2Delta71Lo d2Delta71Hi d2Delta71Fq.poly = (d2Delta71S,d2Delta71Es) := by decide +kernel
theorem d2Delta71Sites : mergeSites d2Delta71Fq.plogs = [] := by decide +kernel
theorem d2Delta71PData : d2Delta71Pd = [] := by decide +kernel
theorem d2Delta71Plogs : plogsRoundM 16 24 20 128 d2Delta71Lo d2Delta71Hi (mergeSites d2Delta71Fq.plogs) d2Delta71Pd = some (d2Delta71Ap,d2Delta71Ep) := by
  rw [d2Delta71Sites,d2Delta71PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta71Poles : polesRoundM 16 24 12 128 d2Delta71Lo d2Delta71Hi d2Delta71Fq.poles d2Delta71Qd = some (d2Delta71Aq,d2Delta71Eq) := by decide +kernel
theorem d2Delta71Laurent : laurentRoundM 16 30 128 d2Delta71Lo d2Delta71Hi d2Delta71Ts d2Delta71Ld = some (d2Delta71Al,d2Delta71El) := by decide +kernel
theorem d2Delta71Small : chebPolyUB (vecAdd d2Delta71S (vecAdd d2Delta71Ap (vecAdd d2Delta71Aq d2Delta71Al))) d2Delta71Gam+d2Delta71Es+d2Delta71Ep+d2Delta71Eq+d2Delta71El ≤ (d2LitsStandaloneDelta008.q2 (-7377399900180411061803) 1 (-80)) := by decide +kernel
theorem d2Delta71Check : chebRoundPieceL d2Delta71Fq d2Delta71Ts 16 24 12 20 30 128 d2Delta71Lo d2Delta71Hi d2Delta71Pd d2Delta71Qd d2Delta71Ld d2Delta71Gam (d2LitsStandaloneDelta008.q2 (-7377399900180411061803) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta71Fq d2Delta71Ts 16 24 12 20 30 128 d2Delta71Lo d2Delta71Hi d2Delta71Pd d2Delta71Qd d2Delta71Ld d2Delta71Gam d2Delta71S d2Delta71Ap d2Delta71Aq d2Delta71Al d2Delta71Es d2Delta71Ep d2Delta71Eq d2Delta71El (by decide +kernel) d2Delta71Shift d2Delta71Plogs d2Delta71Poles d2Delta71Laurent]
  exact decide_eq_true d2Delta71Small
theorem d2Delta71Bound : ∀ x ∈ Icc ((d2Delta71Lo : ℚ) : ℝ) ((d2Delta71Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta008.q2 (-7377399900180411061803) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta71Fq d2Delta71Ts 16 24 12 20 30 128 d2Delta71Lo d2Delta71Hi d2Delta71Pd d2Delta71Qd d2Delta71Ld d2Delta71Gam (d2LitsStandaloneDelta008.q2 (-7377399900180411061803) 1 (-80)) d2Delta71Check
  simpa only [d2Delta71Fq, d2Delta71Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta71Shift
#print axioms d2Delta71Sites
#print axioms d2Delta71PData
#print axioms d2Delta71Plogs
#print axioms d2Delta71Poles
#print axioms d2Delta71Laurent
#print axioms d2Delta71Small
#print axioms d2Delta71Check
#print axioms d2Delta71Bound

end StandaloneDelta008
end CatalanMeasure.GenD.Signed.Data.Cells
