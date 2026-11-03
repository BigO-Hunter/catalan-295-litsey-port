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
namespace d2LitsStandaloneDelta003
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta003
namespace StandaloneDelta003
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta003.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta003.q2listC (raw_ints% []))⟩
def d2Delta24Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta24Ts : List LTerm := laurentClean []
def d2Delta24Lo : ℚ := (d2LitsStandaloneDelta003.q2 (42951641) 1 (-31))
def d2Delta24Hi : ℚ := (d2LitsStandaloneDelta003.q2 (86950833) 1 (-32))
def d2Delta24Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta24Qd : List (ℚ × ℚ) := []
def d2Delta24Ld : List LaurentPieceData := []
def d2Delta24Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-8918798704939807226765204094363421619697528275, 1, -160, 83716661939070042493385489262495376617, 1, -155, 3997923132666942556723490506583133607, 1, -160, -160866737203678907783306908960273769, 1, -160, 315093116189220286019853364261591, 1, -159, -110880584682930166980773381289, 1, -157, 77314028793983042402222801, 1, -159, 386282092195502918315615, 1, -159, -522417792083948954891, 1, -160, -71661277822305051, 1, -158, 22125995443049, 1, -156, 37398722373, 1, -160, -1651154395, 1, -158, -2608460477, 1, -159, -4468726939, 1, -160, -1762375071, 1, -159, -3008251977, 1, -160, -2319465063, 1, -160, -1970585265, 1, -160, -742782707, 1, -159, -1255237457, 1, -160, -925439931, 1, -160, -777106975, 1, -160, -140094103, 1, -158, -116842139, 1, -158, -82405981, 1, -158, -272929087, 1, -160, -94118297, 1, -159, -154673595, 1, -160, -3259335, 1, -155, -21254091, 1, -158, -28019329, 1, -159])
def d2Delta24S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-2076569644021126482019758967338359125, 1, -128, 623850100167706515929337673449, 1, -128, 465126054958567217856243987, 1, -126, -149814693228784653726777037, 1, -128, 36681612522786405793183, 1, -123, -3304519077466694616331, 1, -128, 1152099944224160649, 1, -128, 11512141886337151, 1, -128, -7784684484145, 1, -127, -17085408859, 1, -128, 42203273, 1, -128, 5355, 1, -127, -67, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta24Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta24Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta24Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta24Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta24Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta24Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta24El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta24Shift : polyRoundApx 128 d2Delta24Lo d2Delta24Hi d2Delta24Fq.poly = (d2Delta24S,d2Delta24Es) := by decide +kernel
theorem d2Delta24Sites : mergeSites d2Delta24Fq.plogs = [] := by decide +kernel
theorem d2Delta24PData : d2Delta24Pd = [] := by decide +kernel
theorem d2Delta24Plogs : plogsRoundM 16 24 20 128 d2Delta24Lo d2Delta24Hi (mergeSites d2Delta24Fq.plogs) d2Delta24Pd = some (d2Delta24Ap,d2Delta24Ep) := by
  rw [d2Delta24Sites,d2Delta24PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta24Poles : polesRoundM 16 24 12 128 d2Delta24Lo d2Delta24Hi d2Delta24Fq.poles d2Delta24Qd = some (d2Delta24Aq,d2Delta24Eq) := by decide +kernel
theorem d2Delta24Laurent : laurentRoundM 16 30 128 d2Delta24Lo d2Delta24Hi d2Delta24Ts d2Delta24Ld = some (d2Delta24Al,d2Delta24El) := by decide +kernel
theorem d2Delta24Small : chebPolyUB (vecAdd d2Delta24S (vecAdd d2Delta24Ap (vecAdd d2Delta24Aq d2Delta24Al))) d2Delta24Gam+d2Delta24Es+d2Delta24Ep+d2Delta24Eq+d2Delta24El ≤ (d2LitsStandaloneDelta003.q2 (-7377455156587076794739) 1 (-80)) := by decide +kernel
theorem d2Delta24Check : chebRoundPieceL d2Delta24Fq d2Delta24Ts 16 24 12 20 30 128 d2Delta24Lo d2Delta24Hi d2Delta24Pd d2Delta24Qd d2Delta24Ld d2Delta24Gam (d2LitsStandaloneDelta003.q2 (-7377455156587076794739) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta24Fq d2Delta24Ts 16 24 12 20 30 128 d2Delta24Lo d2Delta24Hi d2Delta24Pd d2Delta24Qd d2Delta24Ld d2Delta24Gam d2Delta24S d2Delta24Ap d2Delta24Aq d2Delta24Al d2Delta24Es d2Delta24Ep d2Delta24Eq d2Delta24El (by decide +kernel) d2Delta24Shift d2Delta24Plogs d2Delta24Poles d2Delta24Laurent]
  exact decide_eq_true d2Delta24Small
theorem d2Delta24Bound : ∀ x ∈ Icc ((d2Delta24Lo : ℚ) : ℝ) ((d2Delta24Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-7377455156587076794739) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta24Fq d2Delta24Ts 16 24 12 20 30 128 d2Delta24Lo d2Delta24Hi d2Delta24Pd d2Delta24Qd d2Delta24Ld d2Delta24Gam (d2LitsStandaloneDelta003.q2 (-7377455156587076794739) 1 (-80)) d2Delta24Check
  simpa only [d2Delta24Fq, d2Delta24Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta24Shift
#print axioms d2Delta24Sites
#print axioms d2Delta24PData
#print axioms d2Delta24Plogs
#print axioms d2Delta24Poles
#print axioms d2Delta24Laurent
#print axioms d2Delta24Small
#print axioms d2Delta24Check
#print axioms d2Delta24Bound

def d2Delta25Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta25Ts : List LTerm := laurentClean []
def d2Delta25Lo : ℚ := (d2LitsStandaloneDelta003.q2 (86950833) 1 (-32))
def d2Delta25Hi : ℚ := (d2LitsStandaloneDelta003.q2 (5499899) 1 (-28))
def d2Delta25Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta25Qd : List (ℚ × ℚ) := []
def d2Delta25Ld : List LaurentPieceData := []
def d2Delta25Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-8918793321082886293563282367657331615195770323, 1, -160, 2703365027419482424788082880018581998993, 1, -160, 2127435388206775540877623456343084455, 1, -160, -75462737839163720873381667862812855, 1, -159, 306242095967756925002306575692503, 1, -159, -883075921015266228415390608401, 1, -160, 88012139882066739799884497, 1, -159, 755684444288368157399289, 1, -160, -532481659255818511627, 1, -160, -272446548189667745, 1, -160, 22240329024361, 1, -156, 30327921327, 1, -160, -1651154395, 1, -158, -2758498761, 1, -159, -4468726939, 1, -160, -938702211, 1, -158, -3008251977, 1, -160, -2489180499, 1, -160, -1970585265, 1, -160, -803004313, 1, -159, -1255237457, 1, -160, -1007647203, 1, -160, -777106975, 1, -160, -307162467, 1, -159, -116842139, 1, -158, -363652991, 1, -160, -272929087, 1, -160, -13053767, 1, -156, -154673595, 1, -160, -116303547, 1, -160, -21254091, 1, -158, -31373619, 1, -159])
def d2Delta25S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-2076568390058751496894785018388903477, 1, -128, 314765819282169979093995642623, 1, -127, 989523461565030982284923395, 1, -128, -140556190431250981075862191, 1, -128, 570419370922432853119501, 1, -127, -1644866933699198638135, 1, -127, 1311514821871089649, 1, -128, 11260612253977353, 1, -128, -7934648063699, 1, -127, -16239104133, 1, -128, 42421347, 1, -128, 4557, 1, -127, -67, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta25Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta25Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta25Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta25Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta25Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta25Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta25El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta25Shift : polyRoundApx 128 d2Delta25Lo d2Delta25Hi d2Delta25Fq.poly = (d2Delta25S,d2Delta25Es) := by decide +kernel
theorem d2Delta25Sites : mergeSites d2Delta25Fq.plogs = [] := by decide +kernel
theorem d2Delta25PData : d2Delta25Pd = [] := by decide +kernel
theorem d2Delta25Plogs : plogsRoundM 16 24 20 128 d2Delta25Lo d2Delta25Hi (mergeSites d2Delta25Fq.plogs) d2Delta25Pd = some (d2Delta25Ap,d2Delta25Ep) := by
  rw [d2Delta25Sites,d2Delta25PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta25Poles : polesRoundM 16 24 12 128 d2Delta25Lo d2Delta25Hi d2Delta25Fq.poles d2Delta25Qd = some (d2Delta25Aq,d2Delta25Eq) := by decide +kernel
theorem d2Delta25Laurent : laurentRoundM 16 30 128 d2Delta25Lo d2Delta25Hi d2Delta25Ts d2Delta25Ld = some (d2Delta25Al,d2Delta25El) := by decide +kernel
theorem d2Delta25Small : chebPolyUB (vecAdd d2Delta25S (vecAdd d2Delta25Ap (vecAdd d2Delta25Aq d2Delta25Al))) d2Delta25Gam+d2Delta25Es+d2Delta25Ep+d2Delta25Eq+d2Delta25El ≤ (d2LitsStandaloneDelta003.q2 (-7377450684510931284109) 1 (-80)) := by decide +kernel
theorem d2Delta25Check : chebRoundPieceL d2Delta25Fq d2Delta25Ts 16 24 12 20 30 128 d2Delta25Lo d2Delta25Hi d2Delta25Pd d2Delta25Qd d2Delta25Ld d2Delta25Gam (d2LitsStandaloneDelta003.q2 (-7377450684510931284109) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta25Fq d2Delta25Ts 16 24 12 20 30 128 d2Delta25Lo d2Delta25Hi d2Delta25Pd d2Delta25Qd d2Delta25Ld d2Delta25Gam d2Delta25S d2Delta25Ap d2Delta25Aq d2Delta25Al d2Delta25Es d2Delta25Ep d2Delta25Eq d2Delta25El (by decide +kernel) d2Delta25Shift d2Delta25Plogs d2Delta25Poles d2Delta25Laurent]
  exact decide_eq_true d2Delta25Small
theorem d2Delta25Bound : ∀ x ∈ Icc ((d2Delta25Lo : ℚ) : ℝ) ((d2Delta25Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-7377450684510931284109) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta25Fq d2Delta25Ts 16 24 12 20 30 128 d2Delta25Lo d2Delta25Hi d2Delta25Pd d2Delta25Qd d2Delta25Ld d2Delta25Gam (d2LitsStandaloneDelta003.q2 (-7377450684510931284109) 1 (-80)) d2Delta25Check
  simpa only [d2Delta25Fq, d2Delta25Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta25Shift
#print axioms d2Delta25Sites
#print axioms d2Delta25PData
#print axioms d2Delta25Plogs
#print axioms d2Delta25Poles
#print axioms d2Delta25Laurent
#print axioms d2Delta25Small
#print axioms d2Delta25Check
#print axioms d2Delta25Bound

def d2Delta26Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta26Ts : List LTerm := laurentClean []
def d2Delta26Lo : ℚ := (d2LitsStandaloneDelta003.q2 (5499899) 1 (-28))
def d2Delta26Hi : ℚ := (d2LitsStandaloneDelta003.q2 (12047349) 1 (-29))
def d2Delta26Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta26Qd : List (ℚ × ℚ) := []
def d2Delta26Ld : List LaurentPieceData := []
def d2Delta26Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-278711542483312664735373938359665769281505119, 1, -155, 21010869845495420422556786347877107632169, 1, -160, -75976894488163872303378535551917704817, 1, -158, -14071687929295031633606339784780674675, 1, -158, 1093865042947776950691132802209810399, 1, -159, -28141254088291272446689279778794761, 1, -160, 34864666479147199126999397043131, 1, -159, 1417594263370175116900785279979, 1, -160, -9582692896512798635827442371, 1, -160, -27901658708079808840331493, 1, -160, 96733682453978471040917, 1, -158, 72630114034562416247, 1, -160, -2339563427174292879, 1, -158, 4843713109305763, 1, -159, 158233196769535, 1, -160, -144557247991, 1, -159, -5009798637, 1, -160, -290480377, 1, -157, -1972931655, 1, -160, -1494425847, 1, -160, -1256114881, 1, -160, -233305277, 1, -158, -777376675, 1, -160, -141672917, 1, -158, -116858941, 1, -158, -334408147, 1, -160, -272942355, 1, -160, -95820231, 1, -159, -154675595, 1, -160, -26645571, 1, -158, -21254145, 1, -158, -28743557, 1, -159])
def d2Delta26S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-1038281369648264601349011185533853399, 1, -127, 4931257428706881680171802902777, 1, -128, -72796333250335492221662741025, 1, -127, -13072515278957302038260550699, 1, -126, 4074185189278048436340538651, 1, -128, -52435655149603708733288545, 1, -127, 520095289090500884787543, 1, -128, 21127542577576063351775, 1, -128, -285701833641227752047, 1, -128, -1663116038416187655, 1, -128, 46139602785748639, 1, -128, 17286336834169, 1, -128, -4463419550557, 1, -128, 1155342547, 1, -125, 301875337, 1, -128, -544859, 1, -127, -119, 1, -121, 73, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta26Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta26Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta26Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta26Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta26Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta26Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta26El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta26Shift : polyRoundApx 128 d2Delta26Lo d2Delta26Hi d2Delta26Fq.poly = (d2Delta26S,d2Delta26Es) := by decide +kernel
theorem d2Delta26Sites : mergeSites d2Delta26Fq.plogs = [] := by decide +kernel
theorem d2Delta26PData : d2Delta26Pd = [] := by decide +kernel
theorem d2Delta26Plogs : plogsRoundM 16 24 20 128 d2Delta26Lo d2Delta26Hi (mergeSites d2Delta26Fq.plogs) d2Delta26Pd = some (d2Delta26Ap,d2Delta26Ep) := by
  rw [d2Delta26Sites,d2Delta26PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta26Poles : polesRoundM 16 24 12 128 d2Delta26Lo d2Delta26Hi d2Delta26Fq.poles d2Delta26Qd = some (d2Delta26Aq,d2Delta26Eq) := by decide +kernel
theorem d2Delta26Laurent : laurentRoundM 16 30 128 d2Delta26Lo d2Delta26Hi d2Delta26Ts d2Delta26Ld = some (d2Delta26Al,d2Delta26El) := by decide +kernel
theorem d2Delta26Small : chebPolyUB (vecAdd d2Delta26S (vecAdd d2Delta26Ap (vecAdd d2Delta26Aq d2Delta26Al))) d2Delta26Gam+d2Delta26Es+d2Delta26Ep+d2Delta26Eq+d2Delta26El ≤ (d2LitsStandaloneDelta003.q2 (-7377415422419324520363) 1 (-80)) := by decide +kernel
theorem d2Delta26Check : chebRoundPieceL d2Delta26Fq d2Delta26Ts 16 24 12 20 30 128 d2Delta26Lo d2Delta26Hi d2Delta26Pd d2Delta26Qd d2Delta26Ld d2Delta26Gam (d2LitsStandaloneDelta003.q2 (-7377415422419324520363) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta26Fq d2Delta26Ts 16 24 12 20 30 128 d2Delta26Lo d2Delta26Hi d2Delta26Pd d2Delta26Qd d2Delta26Ld d2Delta26Gam d2Delta26S d2Delta26Ap d2Delta26Aq d2Delta26Al d2Delta26Es d2Delta26Ep d2Delta26Eq d2Delta26El (by decide +kernel) d2Delta26Shift d2Delta26Plogs d2Delta26Poles d2Delta26Laurent]
  exact decide_eq_true d2Delta26Small
theorem d2Delta26Bound : ∀ x ∈ Icc ((d2Delta26Lo : ℚ) : ℝ) ((d2Delta26Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-7377415422419324520363) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta26Fq d2Delta26Ts 16 24 12 20 30 128 d2Delta26Lo d2Delta26Hi d2Delta26Pd d2Delta26Qd d2Delta26Ld d2Delta26Gam (d2LitsStandaloneDelta003.q2 (-7377415422419324520363) 1 (-80)) d2Delta26Check
  simpa only [d2Delta26Fq, d2Delta26Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta26Shift
#print axioms d2Delta26Sites
#print axioms d2Delta26PData
#print axioms d2Delta26Plogs
#print axioms d2Delta26Poles
#print axioms d2Delta26Laurent
#print axioms d2Delta26Small
#print axioms d2Delta26Check
#print axioms d2Delta26Bound

def d2Delta27Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta27Ts : List LTerm := laurentClean []
def d2Delta27Lo : ℚ := (d2LitsStandaloneDelta003.q2 (12047349) 1 (-29))
def d2Delta27Hi : ℚ := (d2LitsStandaloneDelta003.q2 (27237351) 1 (-30))
def d2Delta27Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta27Qd : List (ℚ × ℚ) := []
def d2Delta27Ld : List LaurentPieceData := []
def d2Delta27Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-278710149883265643144355544937139100079092637, 1, -155, 22077131184367804465463136235712005908895, 1, -160, -476746539560459012460347929079644628375, 1, -158, -32938659098055380943582351795542293273, 1, -159, 3839906861402675667226390014552418279, 1, -159, -96310170837636300201838471724893049, 1, -159, 639529701668017157171944289313623, 1, -159, 8670191486965862635565660495493, 1, -159, -266531442376049090811549273379, 1, -160, -83748726169258011945270411, 1, -158, 5417718785851267480600967, 1, -158, -20011744634859358767965, 1, -159, -271971977098948596707, 1, -158, 3867904979661939235, 1, -160, 38313823859957271, 1, -160, -93490949328417, 1, -159, -1002274030637, 1, -160, 3720023325, 1, -160, -1954810559, 1, -160, -1583319123, 1, -160, -1256599729, 1, -160, -988727583, 1, -160, -777491083, 1, -160, -599846647, 1, -160, -116864037, 1, -158, -176663037, 1, -159, -272944939, 1, -160, -201954407, 1, -160, -154675803, 1, -160, -13994531, 1, -157, -21254147, 1, -158, -60163487, 1, -160])
def d2Delta27S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-2076551989093378172706446292711658833, 1, -128, 324126448189229486986981782129, 1, -124, -451154517320306632157685472171, 1, -127, -15113962281571030231331691087, 1, -126, 7145231621966538591938484173, 1, -127, -718018909535817936276207657, 1, -128, 4772813668390838194358081, 1, -127, 32304592740604306324201, 1, -125, -7949716147228382769501, 1, -128, -19940995861876988619, 1, -128, 161557888603376575, 1, -124, -4777167900238833, 1, -127, -519001200637623, 1, -128, 1845698544355, 1, -127, 73108328079, 1, -128, -713666233, 1, -128, -7626431, 1, -128, 94405, 1, -128, 301, 1, -127, -5, 1, -127, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta27Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta27Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta27Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta27Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta27Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta27Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta27El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta27Shift : polyRoundApx 128 d2Delta27Lo d2Delta27Hi d2Delta27Fq.poly = (d2Delta27S,d2Delta27Es) := by decide +kernel
theorem d2Delta27Sites : mergeSites d2Delta27Fq.plogs = [] := by decide +kernel
theorem d2Delta27PData : d2Delta27Pd = [] := by decide +kernel
theorem d2Delta27Plogs : plogsRoundM 16 24 20 128 d2Delta27Lo d2Delta27Hi (mergeSites d2Delta27Fq.plogs) d2Delta27Pd = some (d2Delta27Ap,d2Delta27Ep) := by
  rw [d2Delta27Sites,d2Delta27PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta27Poles : polesRoundM 16 24 12 128 d2Delta27Lo d2Delta27Hi d2Delta27Fq.poles d2Delta27Qd = some (d2Delta27Aq,d2Delta27Eq) := by decide +kernel
theorem d2Delta27Laurent : laurentRoundM 16 30 128 d2Delta27Lo d2Delta27Hi d2Delta27Ts d2Delta27Ld = some (d2Delta27Al,d2Delta27El) := by decide +kernel
theorem d2Delta27Small : chebPolyUB (vecAdd d2Delta27S (vecAdd d2Delta27Ap (vecAdd d2Delta27Aq d2Delta27Al))) d2Delta27Gam+d2Delta27Es+d2Delta27Ep+d2Delta27Eq+d2Delta27El ≤ (d2LitsStandaloneDelta003.q2 (-3688688169981816854713) 1 (-79)) := by decide +kernel
theorem d2Delta27Check : chebRoundPieceL d2Delta27Fq d2Delta27Ts 16 24 12 20 30 128 d2Delta27Lo d2Delta27Hi d2Delta27Pd d2Delta27Qd d2Delta27Ld d2Delta27Gam (d2LitsStandaloneDelta003.q2 (-3688688169981816854713) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta27Fq d2Delta27Ts 16 24 12 20 30 128 d2Delta27Lo d2Delta27Hi d2Delta27Pd d2Delta27Qd d2Delta27Ld d2Delta27Gam d2Delta27S d2Delta27Ap d2Delta27Aq d2Delta27Al d2Delta27Es d2Delta27Ep d2Delta27Eq d2Delta27El (by decide +kernel) d2Delta27Shift d2Delta27Plogs d2Delta27Poles d2Delta27Laurent]
  exact decide_eq_true d2Delta27Small
theorem d2Delta27Bound : ∀ x ∈ Icc ((d2Delta27Lo : ℚ) : ℝ) ((d2Delta27Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-3688688169981816854713) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta27Fq d2Delta27Ts 16 24 12 20 30 128 d2Delta27Lo d2Delta27Hi d2Delta27Pd d2Delta27Qd d2Delta27Ld d2Delta27Gam (d2LitsStandaloneDelta003.q2 (-3688688169981816854713) 1 (-79)) d2Delta27Check
  simpa only [d2Delta27Fq, d2Delta27Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta27Shift
#print axioms d2Delta27Sites
#print axioms d2Delta27PData
#print axioms d2Delta27Plogs
#print axioms d2Delta27Poles
#print axioms d2Delta27Laurent
#print axioms d2Delta27Small
#print axioms d2Delta27Check
#print axioms d2Delta27Bound

def d2Delta28Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta28Ts : List LTerm := laurentClean []
def d2Delta28Lo : ℚ := (d2LitsStandaloneDelta003.q2 (27237351) 1 (-30))
def d2Delta28Hi : ℚ := (d2LitsStandaloneDelta003.q2 (112092057) 1 (-32))
def d2Delta28Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta28Qd : List (ℚ × ℚ) := []
def d2Delta28Ld : List LaurentPieceData := []
def d2Delta28Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-278709424890933904895938560940520477447786861, 1, -155, 1476357961675875229095019726003319519275, 1, -159, -33825423611999452786210537855130339863, 1, -158, 2031896553799710446397189500787369, 1, -160, 10531841898687534542288852854225895, 1, -159, -167457823114401366618436322479705, 1, -160, 187698179539124985160714933655, 1, -159, 365396804347371979760585997, 1, -159, -4093755039073197490049571, 1, -160, 181287678077664453361, 1, -158, 4804363505856473383, 1, -158, -4209746997076923, 1, -158, -14041453929187, 1, -158, 17616843629, 1, -158, -4381064425, 1, -160, -3563098989, 1, -160, -3020651053, 1, -160, -294691443, 1, -157, -1975414207, 1, -160, -1519108941, 1, -160, -1256791217, 1, -160, -59524103, 1, -156, -777520395, 1, -160, -72549987, 1, -157, -116864741, 1, -158, -171757631, 1, -159, -272945067, 1, -160, -197290645, 1, -160, -154675803, 1, -160, -54934289, 1, -159, -21254147, 1, -158, -59284143, 1, -160])
def d2Delta28S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-2076547001764906384114944513113349643, 1, -128, 687481134749915902111107856303, 1, -128, -63043993806724706271601461687, 1, -128, 1336073456546516883366035, 1, -127, 39229972916365671762625911, 1, -128, -155962015176268167773529, 1, -126, 1398582420465274664887, 1, -127, 10889576101264448933, 1, -128, -122009134788696091, 1, -128, 43233391405803, 1, -128, 2290979379777, 1, -128, -4014960471, 1, -128, -6694901, 1, -126, 72209, 1, -128, 217, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta28Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta28Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta28Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta28Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta28Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta28Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta28El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta28Shift : polyRoundApx 128 d2Delta28Lo d2Delta28Hi d2Delta28Fq.poly = (d2Delta28S,d2Delta28Es) := by decide +kernel
theorem d2Delta28Sites : mergeSites d2Delta28Fq.plogs = [] := by decide +kernel
theorem d2Delta28PData : d2Delta28Pd = [] := by decide +kernel
theorem d2Delta28Plogs : plogsRoundM 16 24 20 128 d2Delta28Lo d2Delta28Hi (mergeSites d2Delta28Fq.plogs) d2Delta28Pd = some (d2Delta28Ap,d2Delta28Ep) := by
  rw [d2Delta28Sites,d2Delta28PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta28Poles : polesRoundM 16 24 12 128 d2Delta28Lo d2Delta28Hi d2Delta28Fq.poles d2Delta28Qd = some (d2Delta28Aq,d2Delta28Eq) := by decide +kernel
theorem d2Delta28Laurent : laurentRoundM 16 30 128 d2Delta28Lo d2Delta28Hi d2Delta28Ts d2Delta28Ld = some (d2Delta28Al,d2Delta28El) := by decide +kernel
theorem d2Delta28Small : chebPolyUB (vecAdd d2Delta28S (vecAdd d2Delta28Ap (vecAdd d2Delta28Aq d2Delta28Al))) d2Delta28Gam+d2Delta28Es+d2Delta28Ep+d2Delta28Eq+d2Delta28El ≤ (d2LitsStandaloneDelta003.q2 (-7377374495411164797865) 1 (-80)) := by decide +kernel
theorem d2Delta28Check : chebRoundPieceL d2Delta28Fq d2Delta28Ts 16 24 12 20 30 128 d2Delta28Lo d2Delta28Hi d2Delta28Pd d2Delta28Qd d2Delta28Ld d2Delta28Gam (d2LitsStandaloneDelta003.q2 (-7377374495411164797865) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta28Fq d2Delta28Ts 16 24 12 20 30 128 d2Delta28Lo d2Delta28Hi d2Delta28Pd d2Delta28Qd d2Delta28Ld d2Delta28Gam d2Delta28S d2Delta28Ap d2Delta28Aq d2Delta28Al d2Delta28Es d2Delta28Ep d2Delta28Eq d2Delta28El (by decide +kernel) d2Delta28Shift d2Delta28Plogs d2Delta28Poles d2Delta28Laurent]
  exact decide_eq_true d2Delta28Small
theorem d2Delta28Bound : ∀ x ∈ Icc ((d2Delta28Lo : ℚ) : ℝ) ((d2Delta28Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-7377374495411164797865) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta28Fq d2Delta28Ts 16 24 12 20 30 128 d2Delta28Lo d2Delta28Hi d2Delta28Pd d2Delta28Qd d2Delta28Ld d2Delta28Gam (d2LitsStandaloneDelta003.q2 (-7377374495411164797865) 1 (-80)) d2Delta28Check
  simpa only [d2Delta28Fq, d2Delta28Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta28Shift
#print axioms d2Delta28Sites
#print axioms d2Delta28PData
#print axioms d2Delta28Plogs
#print axioms d2Delta28Poles
#print axioms d2Delta28Laurent
#print axioms d2Delta28Small
#print axioms d2Delta28Check
#print axioms d2Delta28Bound

def d2Delta29Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta29Ts : List LTerm := laurentClean []
def d2Delta29Lo : ℚ := (d2LitsStandaloneDelta003.q2 (112092057) 1 (-32))
def d2Delta29Hi : ℚ := (d2LitsStandaloneDelta003.q2 (57617355) 1 (-31))
def d2Delta29Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta29Qd : List (ℚ × ℚ) := []
def d2Delta29Ld : List LaurentPieceData := []
def d2Delta29Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-278709274047997615264609508373622935084860525, 1, -155, 937938949360925030911640509809045888547, 1, -159, -33341029041192921465071383207926363671, 1, -158, 312753793658261109989369764048786799, 1, -160, 8903101759317395708198227453119463, 1, -159, -79108768736695611882697593766309, 1, -159, 197014775741897706588378197399, 1, -159, 300178998430868659247181541, 1, -159, -4053998726685587465540131, 1, -160, 1478251420439558664361, 1, -160, 4604663342724153127, 1, -158, -19437551421018485, 1, -160, -13017165422307, 1, -158, 19125071955, 1, -158, -4408628457, 1, -160, -892233717, 1, -158, -3023804973, 1, -160, -147657087, 1, -156, -1975887295, 1, -160, -1522870745, 1, -160, -1256836273, 1, -160, -477470797, 1, -159, -777522443, 1, -160, -581976969, 1, -160, -116864741, 1, -158, -344403499, 1, -160, -272945067, 1, -160, -49437139, 1, -158, -154675803, 1, -160, -110084915, 1, -160, -21254147, 1, -158, -59377815, 1, -160])
def d2Delta29S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-2076545878349338125952237545790804745, 1, -128, 436543218383794980790381906593, 1, -128, -62135671001167687229671153253, 1, -128, 292011433980051124059440077, 1, -128, 33162234835783006943893191, 1, -128, -73677739100276944632081, 1, -125, 733997643214217567971, 1, -126, 8945833023543485961, 1, -128, -60412033141117563, 1, -127, 22030848842067, 1, -126, 274468632537, 1, -125, -1158631247, 1, -126, -24825819, 1, -128, 4873, 1, -124, 193, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta29Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta29Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta29Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta29Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta29Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta29Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta29El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta29Shift : polyRoundApx 128 d2Delta29Lo d2Delta29Hi d2Delta29Fq.poly = (d2Delta29S,d2Delta29Es) := by decide +kernel
theorem d2Delta29Sites : mergeSites d2Delta29Fq.plogs = [] := by decide +kernel
theorem d2Delta29PData : d2Delta29Pd = [] := by decide +kernel
theorem d2Delta29Plogs : plogsRoundM 16 24 20 128 d2Delta29Lo d2Delta29Hi (mergeSites d2Delta29Fq.plogs) d2Delta29Pd = some (d2Delta29Ap,d2Delta29Ep) := by
  rw [d2Delta29Sites,d2Delta29PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta29Poles : polesRoundM 16 24 12 128 d2Delta29Lo d2Delta29Hi d2Delta29Fq.poles d2Delta29Qd = some (d2Delta29Aq,d2Delta29Eq) := by decide +kernel
theorem d2Delta29Laurent : laurentRoundM 16 30 128 d2Delta29Lo d2Delta29Hi d2Delta29Ts d2Delta29Ld = some (d2Delta29Al,d2Delta29El) := by decide +kernel
theorem d2Delta29Small : chebPolyUB (vecAdd d2Delta29S (vecAdd d2Delta29Ap (vecAdd d2Delta29Aq d2Delta29Al))) d2Delta29Gam+d2Delta29Es+d2Delta29Ep+d2Delta29Eq+d2Delta29El ≤ (d2LitsStandaloneDelta003.q2 (-1844342848679957446723) 1 (-78)) := by decide +kernel
theorem d2Delta29Check : chebRoundPieceL d2Delta29Fq d2Delta29Ts 16 24 12 20 30 128 d2Delta29Lo d2Delta29Hi d2Delta29Pd d2Delta29Qd d2Delta29Ld d2Delta29Gam (d2LitsStandaloneDelta003.q2 (-1844342848679957446723) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta29Fq d2Delta29Ts 16 24 12 20 30 128 d2Delta29Lo d2Delta29Hi d2Delta29Pd d2Delta29Qd d2Delta29Ld d2Delta29Gam d2Delta29S d2Delta29Ap d2Delta29Aq d2Delta29Al d2Delta29Es d2Delta29Ep d2Delta29Eq d2Delta29El (by decide +kernel) d2Delta29Shift d2Delta29Plogs d2Delta29Poles d2Delta29Laurent]
  exact decide_eq_true d2Delta29Small
theorem d2Delta29Bound : ∀ x ∈ Icc ((d2Delta29Lo : ℚ) : ℝ) ((d2Delta29Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-1844342848679957446723) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta29Fq d2Delta29Ts 16 24 12 20 30 128 d2Delta29Lo d2Delta29Hi d2Delta29Pd d2Delta29Qd d2Delta29Ld d2Delta29Gam (d2LitsStandaloneDelta003.q2 (-1844342848679957446723) 1 (-78)) d2Delta29Check
  simpa only [d2Delta29Fq, d2Delta29Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta29Shift
#print axioms d2Delta29Sites
#print axioms d2Delta29PData
#print axioms d2Delta29Plogs
#print axioms d2Delta29Poles
#print axioms d2Delta29Laurent
#print axioms d2Delta29Small
#print axioms d2Delta29Check
#print axioms d2Delta29Bound

def d2Delta30Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta30Ts : List LTerm := laurentClean []
def d2Delta30Lo : ℚ := (d2LitsStandaloneDelta003.q2 (57617355) 1 (-31))
def d2Delta30Hi : ℚ := (d2LitsStandaloneDelta003.q2 (7595001) 1 (-28))
def d2Delta30Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta30Qd : List (ℚ × ℚ) := []
def d2Delta30Ld : List LaurentPieceData := []
def d2Delta30Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-278709183276934115282708800755265772904065645, 1, -155, 330157738127334959488270094927465139153, 1, -159, -124067419689591999640366401062903100951, 1, -158, 2730930219817802947852055463395328981, 1, -159, 106272932179247105183999753737513959, 1, -159, -4595807397097847422173809215951113, 1, -160, 13283052027159014251405587017111, 1, -159, 52252201118651687514668223221, 1, -160, -1009805122056557432220586531, 1, -160, 1301364236273195415821097, 1, -160, 4356000326436953292583, 1, -158, -23496060613391902043, 1, -159, -46460210498893539, 1, -158, 366298647037785, 1, -159, 1329485327127, 1, -160, -5516598995, 1, -159, -3028539949, 1, -160, -1183825535, 1, -159, -1975723455, 1, -160, -1526588801, 1, -160, -1256828081, 1, -160, -239338449, 1, -158, -777522443, 1, -160, -145847911, 1, -158, -116864741, 1, -158, -345156811, 1, -160, -272945067, 1, -160, -198113555, 1, -160, -154675803, 1, -160, -110245923, 1, -160, -21254147, 1, -158, -59442433, 1, -160])
def d2Delta30S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-2076545117511342659926522922843487267, 1, -128, 74960630798365911121573822059, 1, -127, -57872340910219141396350830189, 1, -126, 5108155503974172549524413603, 1, -128, 98900146566887684858868425, 1, -126, -4280519790356257071662291, 1, -126, 197993093022371390681335, 1, -128, 48652744640370463649, 1, -124, -30099730852404244137, 1, -128, 77598166300525343, 1, -128, 2077368676483845, 1, -128, -5603032794437, 1, -127, -88624721493, 1, -128, 698770929, 1, -128, 318071, 1, -125, -28451, 1, -128, -49, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta30Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta30Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta30Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta30Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta30Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta30Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta30El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta30Shift : polyRoundApx 128 d2Delta30Lo d2Delta30Hi d2Delta30Fq.poly = (d2Delta30S,d2Delta30Es) := by decide +kernel
theorem d2Delta30Sites : mergeSites d2Delta30Fq.plogs = [] := by decide +kernel
theorem d2Delta30PData : d2Delta30Pd = [] := by decide +kernel
theorem d2Delta30Plogs : plogsRoundM 16 24 20 128 d2Delta30Lo d2Delta30Hi (mergeSites d2Delta30Fq.plogs) d2Delta30Pd = some (d2Delta30Ap,d2Delta30Ep) := by
  rw [d2Delta30Sites,d2Delta30PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta30Poles : polesRoundM 16 24 12 128 d2Delta30Lo d2Delta30Hi d2Delta30Fq.poles d2Delta30Qd = some (d2Delta30Aq,d2Delta30Eq) := by decide +kernel
theorem d2Delta30Laurent : laurentRoundM 16 30 128 d2Delta30Lo d2Delta30Hi d2Delta30Ts d2Delta30Ld = some (d2Delta30Al,d2Delta30El) := by decide +kernel
theorem d2Delta30Small : chebPolyUB (vecAdd d2Delta30S (vecAdd d2Delta30Ap (vecAdd d2Delta30Aq d2Delta30Al))) d2Delta30Gam+d2Delta30Es+d2Delta30Ep+d2Delta30Eq+d2Delta30El ≤ (d2LitsStandaloneDelta003.q2 (-7377369692906989936159) 1 (-80)) := by decide +kernel
theorem d2Delta30Check : chebRoundPieceL d2Delta30Fq d2Delta30Ts 16 24 12 20 30 128 d2Delta30Lo d2Delta30Hi d2Delta30Pd d2Delta30Qd d2Delta30Ld d2Delta30Gam (d2LitsStandaloneDelta003.q2 (-7377369692906989936159) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta30Fq d2Delta30Ts 16 24 12 20 30 128 d2Delta30Lo d2Delta30Hi d2Delta30Pd d2Delta30Qd d2Delta30Ld d2Delta30Gam d2Delta30S d2Delta30Ap d2Delta30Aq d2Delta30Al d2Delta30Es d2Delta30Ep d2Delta30Eq d2Delta30El (by decide +kernel) d2Delta30Shift d2Delta30Plogs d2Delta30Poles d2Delta30Laurent]
  exact decide_eq_true d2Delta30Small
theorem d2Delta30Bound : ∀ x ∈ Icc ((d2Delta30Lo : ℚ) : ℝ) ((d2Delta30Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-7377369692906989936159) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta30Fq d2Delta30Ts 16 24 12 20 30 128 d2Delta30Lo d2Delta30Hi d2Delta30Pd d2Delta30Qd d2Delta30Ld d2Delta30Gam (d2LitsStandaloneDelta003.q2 (-7377369692906989936159) 1 (-80)) d2Delta30Check
  simpa only [d2Delta30Fq, d2Delta30Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta30Shift
#print axioms d2Delta30Sites
#print axioms d2Delta30PData
#print axioms d2Delta30Plogs
#print axioms d2Delta30Poles
#print axioms d2Delta30Laurent
#print axioms d2Delta30Small
#print axioms d2Delta30Check
#print axioms d2Delta30Bound

def d2Delta31Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta31Ts : List LTerm := laurentClean []
def d2Delta31Lo : ℚ := (d2LitsStandaloneDelta003.q2 (7595001) 1 (-28))
def d2Delta31Hi : ℚ := (d2LitsStandaloneDelta003.q2 (16237553) 1 (-29))
def d2Delta31Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta31Qd : List (ℚ × ℚ) := []
def d2Delta31Ld : List LaurentPieceData := []
def d2Delta31Gam : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-278709301865155316335507785512311781210071661, 1, -155, -2344338643894989251917958294451654205445, 1, -159, -176110270147667669241822387385224525335, 1, -158, 20074957758774978582485571408349753355, 1, -160, 180576622500322060113436690715028455, 1, -159, -4038762501204958153359262248332209, 1, -158, 77718058079611430162548485746071, 1, -159, 14789226599725026585217655545, 1, -157, -9377309709790893923060584995, 1, -160, 27353233814735197424650499, 1, -160, 65549323558544472538919, 1, -158, -664164154116401063255, 1, -159, -1097774947745658595, 1, -158, 8442825913970927, 1, -158, 44847655004951, 1, -160, -584784439937, 1, -160, -3216562733, 1, -160, -592691387, 1, -158, -1975756223, 1, -160, -1533648163, 1, -160, -1256828081, 1, -160, -961572041, 1, -160, -777522443, 1, -160, -292825981, 1, -159, -116864741, 1, -158, -346246767, 1, -160, -272945067, 1, -160, -198587165, 1, -160, -154675803, 1, -160, -27607829, 1, -158, -21254147, 1, -158, -59507711, 1, -160])
def d2Delta31S : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [-1038272976279595370003797484470316199, 1, -127, -69106797122284159335171846529, 1, -124, -82175747316282278624754651665, 1, -126, 18771490700889180264606564509, 1, -128, 41935178537897796074518317, 1, -124, -60185333575568410719722587, 1, -128, 579324155354120962453891, 1, -127, 1759343970444104793279, 1, -128, -279543755050362444609, 1, -128, 1631250835741794223, 1, -128, 15631317549066837, 1, -127, -158401416248349, 1, -127, -2094138972677, 1, -128, 32215144869, 1, -128, 85554619, 1, -128, -1108783, 1, -127, -1479, 1, -128, 113, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta31Ap : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta31Aq : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta31Al : List ℚ := d2LitsStandaloneDelta003.q2listC (raw_ints% [])
def d2Delta31Es : ℚ := (d2LitsStandaloneDelta003.q2 (61) 1 (-127))
def d2Delta31Ep : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta31Eq : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
def d2Delta31El : ℚ := (d2LitsStandaloneDelta003.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta31Shift : polyRoundApx 128 d2Delta31Lo d2Delta31Hi d2Delta31Fq.poly = (d2Delta31S,d2Delta31Es) := by decide +kernel
theorem d2Delta31Sites : mergeSites d2Delta31Fq.plogs = [] := by decide +kernel
theorem d2Delta31PData : d2Delta31Pd = [] := by decide +kernel
theorem d2Delta31Plogs : plogsRoundM 16 24 20 128 d2Delta31Lo d2Delta31Hi (mergeSites d2Delta31Fq.plogs) d2Delta31Pd = some (d2Delta31Ap,d2Delta31Ep) := by
  rw [d2Delta31Sites,d2Delta31PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta31Poles : polesRoundM 16 24 12 128 d2Delta31Lo d2Delta31Hi d2Delta31Fq.poles d2Delta31Qd = some (d2Delta31Aq,d2Delta31Eq) := by decide +kernel
theorem d2Delta31Laurent : laurentRoundM 16 30 128 d2Delta31Lo d2Delta31Hi d2Delta31Ts d2Delta31Ld = some (d2Delta31Al,d2Delta31El) := by decide +kernel
theorem d2Delta31Small : chebPolyUB (vecAdd d2Delta31S (vecAdd d2Delta31Ap (vecAdd d2Delta31Aq d2Delta31Al))) d2Delta31Gam+d2Delta31Es+d2Delta31Ep+d2Delta31Eq+d2Delta31El ≤ (d2LitsStandaloneDelta003.q2 (-922171164414083221625) 1 (-77)) := by decide +kernel
theorem d2Delta31Check : chebRoundPieceL d2Delta31Fq d2Delta31Ts 16 24 12 20 30 128 d2Delta31Lo d2Delta31Hi d2Delta31Pd d2Delta31Qd d2Delta31Ld d2Delta31Gam (d2LitsStandaloneDelta003.q2 (-922171164414083221625) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta31Fq d2Delta31Ts 16 24 12 20 30 128 d2Delta31Lo d2Delta31Hi d2Delta31Pd d2Delta31Qd d2Delta31Ld d2Delta31Gam d2Delta31S d2Delta31Ap d2Delta31Aq d2Delta31Al d2Delta31Es d2Delta31Ep d2Delta31Eq d2Delta31El (by decide +kernel) d2Delta31Shift d2Delta31Plogs d2Delta31Poles d2Delta31Laurent]
  exact decide_eq_true d2Delta31Small
theorem d2Delta31Bound : ∀ x ∈ Icc ((d2Delta31Lo : ℚ) : ℝ) ((d2Delta31Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta003.q2 (-922171164414083221625) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta31Fq d2Delta31Ts 16 24 12 20 30 128 d2Delta31Lo d2Delta31Hi d2Delta31Pd d2Delta31Qd d2Delta31Ld d2Delta31Gam (d2LitsStandaloneDelta003.q2 (-922171164414083221625) 1 (-77)) d2Delta31Check
  simpa only [d2Delta31Fq, d2Delta31Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta31Shift
#print axioms d2Delta31Sites
#print axioms d2Delta31PData
#print axioms d2Delta31Plogs
#print axioms d2Delta31Poles
#print axioms d2Delta31Laurent
#print axioms d2Delta31Small
#print axioms d2Delta31Check
#print axioms d2Delta31Bound

end StandaloneDelta003
end CatalanMeasure.GenD.Signed.Data.Cells
