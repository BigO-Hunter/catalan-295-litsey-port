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
namespace d2LitsStandaloneDelta023
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta023
namespace StandaloneDelta023
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta023.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta023.q2listC (raw_ints% []))⟩
def d2Delta184Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta184Ts : List LTerm := laurentClean []
def d2Delta184Lo : ℚ := (d2LitsStandaloneDelta023.q2 (1099381730427) 1 (-40))
def d2Delta184Hi : ℚ := (d2LitsStandaloneDelta023.q2 (549691388989) 1 (-39))
def d2Delta184Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta184Qd : List (ℚ × ℚ) := []
def d2Delta184Ld : List LaurentPieceData := []
def d2Delta184Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-265797300615717616446083005550908496067, 1, -135, 6392125812711535365568022188081, 1, -134, 2069773822598502224674250159, 1, -133, 1192180970591926041513899, 1, -134, 88712655940912224023, 1, -133, 15666830411050433, 1, -134, 454648454289, 1, -133, 37302307, 1, -134, 2279, 1, -135, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta184S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-2076541411124974307668956191441800121, 1, -128, 24969227485033991890397233525, 1, -126, 129360841734242659553839597, 1, -128, 74511305766110906780877, 1, -128, 22178163303255377421, 1, -128, 3916707537483571, 1, -128, 454648449731, 1, -128, 37302307, 1, -128, 2279, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta184Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta184Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta184Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta184Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta184Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta184Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta184El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta184Shift : polyRoundApx 128 d2Delta184Lo d2Delta184Hi d2Delta184Fq.poly = (d2Delta184S,d2Delta184Es) := by decide +kernel
theorem d2Delta184Sites : mergeSites d2Delta184Fq.plogs = [] := by decide +kernel
theorem d2Delta184PData : d2Delta184Pd = [] := by decide +kernel
theorem d2Delta184Plogs : plogsRoundM 16 24 20 128 d2Delta184Lo d2Delta184Hi (mergeSites d2Delta184Fq.plogs) d2Delta184Pd = some (d2Delta184Ap,d2Delta184Ep) := by
  rw [d2Delta184Sites,d2Delta184PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta184Poles : polesRoundM 16 24 12 128 d2Delta184Lo d2Delta184Hi d2Delta184Fq.poles d2Delta184Qd = some (d2Delta184Aq,d2Delta184Eq) := by decide +kernel
theorem d2Delta184Laurent : laurentRoundM 16 30 128 d2Delta184Lo d2Delta184Hi d2Delta184Ts d2Delta184Ld = some (d2Delta184Al,d2Delta184El) := by decide +kernel
theorem d2Delta184Small : chebPolyUB (vecAdd d2Delta184S (vecAdd d2Delta184Ap (vecAdd d2Delta184Aq d2Delta184Al))) d2Delta184Gam+d2Delta184Es+d2Delta184Ep+d2Delta184Eq+d2Delta184El ≤ (d2LitsStandaloneDelta023.q2 (-3688678360302739975493) 1 (-79)) := by decide +kernel
theorem d2Delta184Check : chebRoundPieceL d2Delta184Fq d2Delta184Ts 16 24 12 20 30 128 d2Delta184Lo d2Delta184Hi d2Delta184Pd d2Delta184Qd d2Delta184Ld d2Delta184Gam (d2LitsStandaloneDelta023.q2 (-3688678360302739975493) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta184Fq d2Delta184Ts 16 24 12 20 30 128 d2Delta184Lo d2Delta184Hi d2Delta184Pd d2Delta184Qd d2Delta184Ld d2Delta184Gam d2Delta184S d2Delta184Ap d2Delta184Aq d2Delta184Al d2Delta184Es d2Delta184Ep d2Delta184Eq d2Delta184El (by decide +kernel) d2Delta184Shift d2Delta184Plogs d2Delta184Poles d2Delta184Laurent]
  exact decide_eq_true d2Delta184Small
theorem d2Delta184Bound : ∀ x ∈ Icc ((d2Delta184Lo : ℚ) : ℝ) ((d2Delta184Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-3688678360302739975493) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta184Fq d2Delta184Ts 16 24 12 20 30 128 d2Delta184Lo d2Delta184Hi d2Delta184Pd d2Delta184Qd d2Delta184Ld d2Delta184Gam (d2LitsStandaloneDelta023.q2 (-3688678360302739975493) 1 (-79)) d2Delta184Check
  simpa only [d2Delta184Fq, d2Delta184Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta184Shift
#print axioms d2Delta184Sites
#print axioms d2Delta184PData
#print axioms d2Delta184Plogs
#print axioms d2Delta184Poles
#print axioms d2Delta184Laurent
#print axioms d2Delta184Small
#print axioms d2Delta184Check
#print axioms d2Delta184Bound

def d2Delta185Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta185Ts : List LTerm := laurentClean []
def d2Delta185Lo : ℚ := (d2LitsStandaloneDelta023.q2 (549691388989) 1 (-39))
def d2Delta185Hi : ℚ := (d2LitsStandaloneDelta023.q2 (137423109135) 1 (-37))
def d2Delta185Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta185Qd : List (ℚ × ℚ) := []
def d2Delta185Ld : List LaurentPieceData := []
def d2Delta185Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-132898631044346745040765770459780926819, 1, -134, 25767760262669913344589139585831, 1, -135, 8322094791227379511423170493, 1, -133, 2392890115185164514125311, 1, -132, 177895824493730038979, 1, -130, 251193505578366513, 1, -133, 29147673032451, 1, -133, 19126810371, 1, -136, 292147, 1, -134, 55, 1, -136, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta185S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-1038270555163991654506932780299159507, 1, -127, 201310178385251349770979875567, 1, -128, 260065284330039313784902439, 1, -127, 37388898237522145377625, 1, -124, 355791605265951259649, 1, -128, 31399186105300953, 1, -126, 29147671863863, 1, -128, 4781702469, 1, -128, 292147, 1, -127, 55, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta185Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta185Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta185Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta185Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta185Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta185Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta185El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta185Shift : polyRoundApx 128 d2Delta185Lo d2Delta185Hi d2Delta185Fq.poly = (d2Delta185S,d2Delta185Es) := by decide +kernel
theorem d2Delta185Sites : mergeSites d2Delta185Fq.plogs = [] := by decide +kernel
theorem d2Delta185PData : d2Delta185Pd = [] := by decide +kernel
theorem d2Delta185Plogs : plogsRoundM 16 24 20 128 d2Delta185Lo d2Delta185Hi (mergeSites d2Delta185Fq.plogs) d2Delta185Pd = some (d2Delta185Ap,d2Delta185Ep) := by
  rw [d2Delta185Sites,d2Delta185PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta185Poles : polesRoundM 16 24 12 128 d2Delta185Lo d2Delta185Hi d2Delta185Fq.poles d2Delta185Qd = some (d2Delta185Aq,d2Delta185Eq) := by decide +kernel
theorem d2Delta185Laurent : laurentRoundM 16 30 128 d2Delta185Lo d2Delta185Hi d2Delta185Ts d2Delta185Ld = some (d2Delta185Al,d2Delta185El) := by decide +kernel
theorem d2Delta185Small : chebPolyUB (vecAdd d2Delta185S (vecAdd d2Delta185Ap (vecAdd d2Delta185Aq d2Delta185Al))) d2Delta185Gam+d2Delta185Es+d2Delta185Ep+d2Delta185Eq+d2Delta185El ≤ (d2LitsStandaloneDelta023.q2 (-461084705637898778899) 1 (-76)) := by decide +kernel
theorem d2Delta185Check : chebRoundPieceL d2Delta185Fq d2Delta185Ts 16 24 12 20 30 128 d2Delta185Lo d2Delta185Hi d2Delta185Pd d2Delta185Qd d2Delta185Ld d2Delta185Gam (d2LitsStandaloneDelta023.q2 (-461084705637898778899) 1 (-76)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta185Fq d2Delta185Ts 16 24 12 20 30 128 d2Delta185Lo d2Delta185Hi d2Delta185Pd d2Delta185Qd d2Delta185Ld d2Delta185Gam d2Delta185S d2Delta185Ap d2Delta185Aq d2Delta185Al d2Delta185Es d2Delta185Ep d2Delta185Eq d2Delta185El (by decide +kernel) d2Delta185Shift d2Delta185Plogs d2Delta185Poles d2Delta185Laurent]
  exact decide_eq_true d2Delta185Small
theorem d2Delta185Bound : ∀ x ∈ Icc ((d2Delta185Lo : ℚ) : ℝ) ((d2Delta185Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-461084705637898778899) 1 (-76)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta185Fq d2Delta185Ts 16 24 12 20 30 128 d2Delta185Lo d2Delta185Hi d2Delta185Pd d2Delta185Qd d2Delta185Ld d2Delta185Gam (d2LitsStandaloneDelta023.q2 (-461084705637898778899) 1 (-76)) d2Delta185Check
  simpa only [d2Delta185Fq, d2Delta185Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta185Shift
#print axioms d2Delta185Sites
#print axioms d2Delta185PData
#print axioms d2Delta185Plogs
#print axioms d2Delta185Poles
#print axioms d2Delta185Laurent
#print axioms d2Delta185Small
#print axioms d2Delta185Check
#print axioms d2Delta185Bound

def d2Delta186Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta186Ts : List LTerm := laurentClean []
def d2Delta186Lo : ℚ := (d2LitsStandaloneDelta023.q2 (137423109135) 1 (-37))
def d2Delta186Hi : ℚ := (d2LitsStandaloneDelta023.q2 (274847265821) 1 (-38))
def d2Delta186Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta186Qd : List (ℚ × ℚ) := []
def d2Delta186Ld : List LaurentPieceData := []
def d2Delta186Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-132898592041537433737125898602743222641, 1, -134, 52338933705852364243001346617341, 1, -135, 67268511669497381043933473633, 1, -134, 77120489105342329634080919, 1, -134, 11445749484141463020495, 1, -132, 16143659610975294163, 1, -134, 7487549355459197, 1, -135, 2455420911243, 1, -136, 74981013, 1, -134, 28371, 1, -136, 1, 1, -135, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta186S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-2076540501700092181619204482116052545, 1, -128, 408894304555306006066713453217, 1, -128, 2102135266798104023482031747, 1, -128, 4820025524190804295661667, 1, -128, 2861435967119955332789, 1, -127, 1008978457124305687, 1, -126, 467971759735189, 1, -126, 76731895497, 1, -125, 4686313, 1, -123, 28371, 1, -128, 1, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta186Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta186Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta186Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta186Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta186Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta186Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta186El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta186Shift : polyRoundApx 128 d2Delta186Lo d2Delta186Hi d2Delta186Fq.poly = (d2Delta186S,d2Delta186Es) := by decide +kernel
theorem d2Delta186Sites : mergeSites d2Delta186Fq.plogs = [] := by decide +kernel
theorem d2Delta186PData : d2Delta186Pd = [] := by decide +kernel
theorem d2Delta186Plogs : plogsRoundM 16 24 20 128 d2Delta186Lo d2Delta186Hi (mergeSites d2Delta186Fq.plogs) d2Delta186Pd = some (d2Delta186Ap,d2Delta186Ep) := by
  rw [d2Delta186Sites,d2Delta186PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta186Poles : polesRoundM 16 24 12 128 d2Delta186Lo d2Delta186Hi d2Delta186Fq.poles d2Delta186Qd = some (d2Delta186Aq,d2Delta186Eq) := by decide +kernel
theorem d2Delta186Laurent : laurentRoundM 16 30 128 d2Delta186Lo d2Delta186Hi d2Delta186Ts d2Delta186Ld = some (d2Delta186Al,d2Delta186El) := by decide +kernel
theorem d2Delta186Small : chebPolyUB (vecAdd d2Delta186S (vecAdd d2Delta186Ap (vecAdd d2Delta186Aq d2Delta186Al))) d2Delta186Gam+d2Delta186Es+d2Delta186Ep+d2Delta186Eq+d2Delta186El ≤ (d2LitsStandaloneDelta023.q2 (-922169048100419267247) 1 (-77)) := by decide +kernel
theorem d2Delta186Check : chebRoundPieceL d2Delta186Fq d2Delta186Ts 16 24 12 20 30 128 d2Delta186Lo d2Delta186Hi d2Delta186Pd d2Delta186Qd d2Delta186Ld d2Delta186Gam (d2LitsStandaloneDelta023.q2 (-922169048100419267247) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta186Fq d2Delta186Ts 16 24 12 20 30 128 d2Delta186Lo d2Delta186Hi d2Delta186Pd d2Delta186Qd d2Delta186Ld d2Delta186Gam d2Delta186S d2Delta186Ap d2Delta186Aq d2Delta186Al d2Delta186Es d2Delta186Ep d2Delta186Eq d2Delta186El (by decide +kernel) d2Delta186Shift d2Delta186Plogs d2Delta186Poles d2Delta186Laurent]
  exact decide_eq_true d2Delta186Small
theorem d2Delta186Bound : ∀ x ∈ Icc ((d2Delta186Lo : ℚ) : ℝ) ((d2Delta186Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-922169048100419267247) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta186Fq d2Delta186Ts 16 24 12 20 30 128 d2Delta186Lo d2Delta186Hi d2Delta186Pd d2Delta186Qd d2Delta186Ld d2Delta186Gam (d2LitsStandaloneDelta023.q2 (-922169048100419267247) 1 (-77)) d2Delta186Check
  simpa only [d2Delta186Fq, d2Delta186Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta186Shift
#print axioms d2Delta186Sites
#print axioms d2Delta186PData
#print axioms d2Delta186Plogs
#print axioms d2Delta186Poles
#print axioms d2Delta186Laurent
#print axioms d2Delta186Small
#print axioms d2Delta186Check
#print axioms d2Delta186Bound

def d2Delta187Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta187Ts : List LTerm := laurentClean []
def d2Delta187Lo : ℚ := (d2LitsStandaloneDelta023.q2 (274847265821) 1 (-38))
def d2Delta187Hi : ℚ := (d2LitsStandaloneDelta023.q2 (68712078343) 1 (-36))
def d2Delta187Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta187Qd : List (ℚ × ℚ) := []
def d2Delta187Ld : List LaurentPieceData := []
def d2Delta187Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-66449269580758124705617183393071218373, 1, -133, 53422658414609530496828584916685, 1, -135, 68198363377208426155175892575, 1, -134, 38927802472798050915230747, 1, -133, 11526692757083479166897, 1, -132, 4058429182491194827, 1, -132, 7521992508036929, 1, -135, 2465034839477, 1, -136, 37618371, 1, -133, 28457, 1, -136, 1, 1, -135, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta187S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-2076539675464290104401180087555944429, 1, -128, 417360869383923391241325219771, 1, -128, 2131193092192442555768487517, 1, -128, 2432985118031908738384053, 1, -127, 1440835889448684290363, 1, -126, 4058428104038500577, 1, -128, 1880497826062273, 1, -128, 616258645841, 1, -128, 75236737, 1, -127, 28457, 1, -128, 1, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta187Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta187Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta187Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta187Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta187Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta187Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta187El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta187Shift : polyRoundApx 128 d2Delta187Lo d2Delta187Hi d2Delta187Fq.poly = (d2Delta187S,d2Delta187Es) := by decide +kernel
theorem d2Delta187Sites : mergeSites d2Delta187Fq.plogs = [] := by decide +kernel
theorem d2Delta187PData : d2Delta187Pd = [] := by decide +kernel
theorem d2Delta187Plogs : plogsRoundM 16 24 20 128 d2Delta187Lo d2Delta187Hi (mergeSites d2Delta187Fq.plogs) d2Delta187Pd = some (d2Delta187Ap,d2Delta187Ep) := by
  rw [d2Delta187Sites,d2Delta187PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta187Poles : polesRoundM 16 24 12 128 d2Delta187Lo d2Delta187Hi d2Delta187Fq.poles d2Delta187Qd = some (d2Delta187Aq,d2Delta187Eq) := by decide +kernel
theorem d2Delta187Laurent : laurentRoundM 16 30 128 d2Delta187Lo d2Delta187Hi d2Delta187Ts d2Delta187Ld = some (d2Delta187Al,d2Delta187El) := by decide +kernel
theorem d2Delta187Small : chebPolyUB (vecAdd d2Delta187S (vecAdd d2Delta187Ap (vecAdd d2Delta187Aq d2Delta187Al))) d2Delta187Gam+d2Delta187Es+d2Delta187Ep+d2Delta187Eq+d2Delta187El ≤ (d2LitsStandaloneDelta023.q2 (-7377349419241439998435) 1 (-80)) := by decide +kernel
theorem d2Delta187Check : chebRoundPieceL d2Delta187Fq d2Delta187Ts 16 24 12 20 30 128 d2Delta187Lo d2Delta187Hi d2Delta187Pd d2Delta187Qd d2Delta187Ld d2Delta187Gam (d2LitsStandaloneDelta023.q2 (-7377349419241439998435) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta187Fq d2Delta187Ts 16 24 12 20 30 128 d2Delta187Lo d2Delta187Hi d2Delta187Pd d2Delta187Qd d2Delta187Ld d2Delta187Gam d2Delta187S d2Delta187Ap d2Delta187Aq d2Delta187Al d2Delta187Es d2Delta187Ep d2Delta187Eq d2Delta187El (by decide +kernel) d2Delta187Shift d2Delta187Plogs d2Delta187Poles d2Delta187Laurent]
  exact decide_eq_true d2Delta187Small
theorem d2Delta187Bound : ∀ x ∈ Icc ((d2Delta187Lo : ℚ) : ℝ) ((d2Delta187Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-7377349419241439998435) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta187Fq d2Delta187Ts 16 24 12 20 30 128 d2Delta187Lo d2Delta187Hi d2Delta187Pd d2Delta187Qd d2Delta187Ld d2Delta187Gam (d2LitsStandaloneDelta023.q2 (-7377349419241439998435) 1 (-80)) d2Delta187Check
  simpa only [d2Delta187Fq, d2Delta187Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta187Shift
#print axioms d2Delta187Sites
#print axioms d2Delta187PData
#print axioms d2Delta187Plogs
#print axioms d2Delta187Poles
#print axioms d2Delta187Laurent
#print axioms d2Delta187Small
#print axioms d2Delta187Check
#print axioms d2Delta187Bound

def d2Delta188Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta188Ts : List LTerm := laurentClean []
def d2Delta188Lo : ℚ := (d2LitsStandaloneDelta023.q2 (68712078343) 1 (-36))
def d2Delta188Hi : ℚ := (d2LitsStandaloneDelta023.q2 (137425204237) 1 (-37))
def d2Delta188Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta188Qd : List (ℚ × ℚ) := []
def d2Delta188Ld : List LaurentPieceData := []
def d2Delta188Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-265796915163963120048262719714164506457, 1, -135, 440621915905834782985150376593171, 1, -137, 556882544859852776405955139979, 1, -135, 5053969506802208734211896349, 1, -137, 372767090601471622598457, 1, -133, 8381231318536208200853, 1, -138, 969460967169615435, 1, -136, 1269513217148571, 1, -138, 38718362485, 1, -135, 58544751, 1, -138, 2207, 1, -136, 1, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta188S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-8111478140894902766120538961135733, 1, -120, 860560066441928613695297392261, 1, -128, 8701196571730714478011922843, 1, -128, 39483973076037492072916117, 1, -128, 46595795438242479648189, 1, -127, 130956600499144826079, 1, -128, 121182543459486615, 1, -128, 39672271570183, 1, -127, 19359175725, 1, -127, 14636185, 1, -128, 2207, 1, -127, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta188Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta188Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta188Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta188Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta188Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta188Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta188El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta188Shift : polyRoundApx 128 d2Delta188Lo d2Delta188Hi d2Delta188Fq.poly = (d2Delta188S,d2Delta188Es) := by decide +kernel
theorem d2Delta188Sites : mergeSites d2Delta188Fq.plogs = [] := by decide +kernel
theorem d2Delta188PData : d2Delta188Pd = [] := by decide +kernel
theorem d2Delta188Plogs : plogsRoundM 16 24 20 128 d2Delta188Lo d2Delta188Hi (mergeSites d2Delta188Fq.plogs) d2Delta188Pd = some (d2Delta188Ap,d2Delta188Ep) := by
  rw [d2Delta188Sites,d2Delta188PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta188Poles : polesRoundM 16 24 12 128 d2Delta188Lo d2Delta188Hi d2Delta188Fq.poles d2Delta188Qd = some (d2Delta188Aq,d2Delta188Eq) := by decide +kernel
theorem d2Delta188Laurent : laurentRoundM 16 30 128 d2Delta188Lo d2Delta188Hi d2Delta188Ts d2Delta188Ld = some (d2Delta188Al,d2Delta188El) := by decide +kernel
theorem d2Delta188Small : chebPolyUB (vecAdd d2Delta188S (vecAdd d2Delta188Ap (vecAdd d2Delta188Aq d2Delta188Al))) d2Delta188Gam+d2Delta188Es+d2Delta188Ep+d2Delta188Eq+d2Delta188El ≤ (d2LitsStandaloneDelta023.q2 (-7377343304313849610035) 1 (-80)) := by decide +kernel
theorem d2Delta188Check : chebRoundPieceL d2Delta188Fq d2Delta188Ts 16 24 12 20 30 128 d2Delta188Lo d2Delta188Hi d2Delta188Pd d2Delta188Qd d2Delta188Ld d2Delta188Gam (d2LitsStandaloneDelta023.q2 (-7377343304313849610035) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta188Fq d2Delta188Ts 16 24 12 20 30 128 d2Delta188Lo d2Delta188Hi d2Delta188Pd d2Delta188Qd d2Delta188Ld d2Delta188Gam d2Delta188S d2Delta188Ap d2Delta188Aq d2Delta188Al d2Delta188Es d2Delta188Ep d2Delta188Eq d2Delta188El (by decide +kernel) d2Delta188Shift d2Delta188Plogs d2Delta188Poles d2Delta188Laurent]
  exact decide_eq_true d2Delta188Small
theorem d2Delta188Bound : ∀ x ∈ Icc ((d2Delta188Lo : ℚ) : ℝ) ((d2Delta188Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-7377343304313849610035) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta188Fq d2Delta188Ts 16 24 12 20 30 128 d2Delta188Lo d2Delta188Hi d2Delta188Pd d2Delta188Qd d2Delta188Ld d2Delta188Gam (d2LitsStandaloneDelta023.q2 (-7377343304313849610035) 1 (-80)) d2Delta188Check
  simpa only [d2Delta188Fq, d2Delta188Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta188Shift
#print axioms d2Delta188Sites
#print axioms d2Delta188PData
#print axioms d2Delta188Plogs
#print axioms d2Delta188Poles
#print axioms d2Delta188Laurent
#print axioms d2Delta188Small
#print axioms d2Delta188Check
#print axioms d2Delta188Bound

def d2Delta189Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta189Ts : List LTerm := laurentClean []
def d2Delta189Lo : ℚ := (d2LitsStandaloneDelta023.q2 (137425204237) 1 (-37))
def d2Delta189Hi : ℚ := (d2LitsStandaloneDelta023.q2 (34356562947) 1 (-35))
def d2Delta189Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta189Qd : List (ℚ × ℚ) := []
def d2Delta189Ld : List LaurentPieceData := []
def d2Delta189Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-132898345174822380235761517087709829885, 1, -134, 458686376546247266270132609667511, 1, -137, 572188289446269602251616867983, 1, -135, 5150070914908841587402960549, 1, -137, 47254316770308977745727, 1, -130, 8474727249820115379493, 1, -138, 978382330675131063, 1, -136, 1279458907983943, 1, -138, 19491305005, 1, -134, 58898907, 1, -138, 2219, 1, -136, 1, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta189S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-519134161956702222226846050129108635, 1, -126, 895841653036502643343388235031, 1, -128, 1117543439254151801888245649, 1, -125, 628668179699667144602895, 1, -122, 94508450093979682163425, 1, -128, 33104368334411522509, 1, -126, 122297713369181071, 1, -128, 19991537154591, 1, -126, 38982598915, 1, -128, 3681181, 1, -126, 2219, 1, -127, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta189Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta189Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta189Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta189Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta189Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta189Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta189El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta189Shift : polyRoundApx 128 d2Delta189Lo d2Delta189Hi d2Delta189Fq.poly = (d2Delta189S,d2Delta189Es) := by decide +kernel
theorem d2Delta189Sites : mergeSites d2Delta189Fq.plogs = [] := by decide +kernel
theorem d2Delta189PData : d2Delta189Pd = [] := by decide +kernel
theorem d2Delta189Plogs : plogsRoundM 16 24 20 128 d2Delta189Lo d2Delta189Hi (mergeSites d2Delta189Fq.plogs) d2Delta189Pd = some (d2Delta189Ap,d2Delta189Ep) := by
  rw [d2Delta189Sites,d2Delta189PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta189Poles : polesRoundM 16 24 12 128 d2Delta189Lo d2Delta189Hi d2Delta189Fq.poles d2Delta189Qd = some (d2Delta189Aq,d2Delta189Eq) := by decide +kernel
theorem d2Delta189Laurent : laurentRoundM 16 30 128 d2Delta189Lo d2Delta189Hi d2Delta189Ts d2Delta189Ld = some (d2Delta189Al,d2Delta189El) := by decide +kernel
theorem d2Delta189Small : chebPolyUB (vecAdd d2Delta189S (vecAdd d2Delta189Ap (vecAdd d2Delta189Aq d2Delta189Al))) d2Delta189Gam+d2Delta189Es+d2Delta189Ep+d2Delta189Eq+d2Delta189El ≤ (d2LitsStandaloneDelta023.q2 (-57635444833516983717) 1 (-73)) := by decide +kernel
theorem d2Delta189Check : chebRoundPieceL d2Delta189Fq d2Delta189Ts 16 24 12 20 30 128 d2Delta189Lo d2Delta189Hi d2Delta189Pd d2Delta189Qd d2Delta189Ld d2Delta189Gam (d2LitsStandaloneDelta023.q2 (-57635444833516983717) 1 (-73)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta189Fq d2Delta189Ts 16 24 12 20 30 128 d2Delta189Lo d2Delta189Hi d2Delta189Pd d2Delta189Qd d2Delta189Ld d2Delta189Gam d2Delta189S d2Delta189Ap d2Delta189Aq d2Delta189Al d2Delta189Es d2Delta189Ep d2Delta189Eq d2Delta189El (by decide +kernel) d2Delta189Shift d2Delta189Plogs d2Delta189Poles d2Delta189Laurent]
  exact decide_eq_true d2Delta189Small
theorem d2Delta189Bound : ∀ x ∈ Icc ((d2Delta189Lo : ℚ) : ℝ) ((d2Delta189Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-57635444833516983717) 1 (-73)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta189Fq d2Delta189Ts 16 24 12 20 30 128 d2Delta189Lo d2Delta189Hi d2Delta189Pd d2Delta189Qd d2Delta189Ld d2Delta189Gam (d2LitsStandaloneDelta023.q2 (-57635444833516983717) 1 (-73)) d2Delta189Check
  simpa only [d2Delta189Fq, d2Delta189Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta189Shift
#print axioms d2Delta189Sites
#print axioms d2Delta189PData
#print axioms d2Delta189Plogs
#print axioms d2Delta189Poles
#print axioms d2Delta189Laurent
#print axioms d2Delta189Small
#print axioms d2Delta189Check
#print axioms d2Delta189Bound

def d2Delta190Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta190Ts : List LTerm := laurentClean []
def d2Delta190Lo : ℚ := (d2LitsStandaloneDelta023.q2 (34356562947) 1 (-35))
def d2Delta190Hi : ℚ := (d2LitsStandaloneDelta023.q2 (68714173445) 1 (-36))
def d2Delta190Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta190Qd : List (ℚ × ℚ) := []
def d2Delta190Ld : List LaurentPieceData := []
def d2Delta190Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-531592668193002887667080415413295792737, 1, -136, 973521388900555801946089657238577, 1, -137, 4765688724795488819281074932909, 1, -136, 42374678440172412452908877091, 1, -137, 12353541388429141654583999, 1, -134, 275731601856042830093499, 1, -138, 126962866823528221185, 1, -137, 165696819077991721, 1, -138, 20163591104101, 1, -136, 30430100133, 1, -138, 4582565, 1, -137, 2255, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta190S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-2076533878744696087345691138187217529, 1, -128, 1901160674911257244941617516227, 1, -128, 37230398974254738524242798443, 1, -128, 41380848742507470334890767, 1, -125, 772090385398740120956099, 1, -127, 4308288155923920260647, 1, -128, 1983789753222358521, 1, -126, 10356034075449359, 1, -128, 5040892047819, 1, -127, 475469927, 1, -124, 4582565, 1, -128, 2255, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta190Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta190Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta190Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta190Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta190Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta190Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta190El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta190Shift : polyRoundApx 128 d2Delta190Lo d2Delta190Hi d2Delta190Fq.poly = (d2Delta190S,d2Delta190Es) := by decide +kernel
theorem d2Delta190Sites : mergeSites d2Delta190Fq.plogs = [] := by decide +kernel
theorem d2Delta190PData : d2Delta190Pd = [] := by decide +kernel
theorem d2Delta190Plogs : plogsRoundM 16 24 20 128 d2Delta190Lo d2Delta190Hi (mergeSites d2Delta190Fq.plogs) d2Delta190Pd = some (d2Delta190Ap,d2Delta190Ep) := by
  rw [d2Delta190Sites,d2Delta190PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta190Poles : polesRoundM 16 24 12 128 d2Delta190Lo d2Delta190Hi d2Delta190Fq.poles d2Delta190Qd = some (d2Delta190Aq,d2Delta190Eq) := by decide +kernel
theorem d2Delta190Laurent : laurentRoundM 16 30 128 d2Delta190Lo d2Delta190Hi d2Delta190Ts d2Delta190Ld = some (d2Delta190Al,d2Delta190El) := by decide +kernel
theorem d2Delta190Small : chebPolyUB (vecAdd d2Delta190S (vecAdd d2Delta190Ap (vecAdd d2Delta190Aq d2Delta190Al))) d2Delta190Gam+d2Delta190Es+d2Delta190Ep+d2Delta190Eq+d2Delta190El ≤ (d2LitsStandaloneDelta023.q2 (-1844330856944710918989) 1 (-78)) := by decide +kernel
theorem d2Delta190Check : chebRoundPieceL d2Delta190Fq d2Delta190Ts 16 24 12 20 30 128 d2Delta190Lo d2Delta190Hi d2Delta190Pd d2Delta190Qd d2Delta190Ld d2Delta190Gam (d2LitsStandaloneDelta023.q2 (-1844330856944710918989) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta190Fq d2Delta190Ts 16 24 12 20 30 128 d2Delta190Lo d2Delta190Hi d2Delta190Pd d2Delta190Qd d2Delta190Ld d2Delta190Gam d2Delta190S d2Delta190Ap d2Delta190Aq d2Delta190Al d2Delta190Es d2Delta190Ep d2Delta190Eq d2Delta190El (by decide +kernel) d2Delta190Shift d2Delta190Plogs d2Delta190Poles d2Delta190Laurent]
  exact decide_eq_true d2Delta190Small
theorem d2Delta190Bound : ∀ x ∈ Icc ((d2Delta190Lo : ℚ) : ℝ) ((d2Delta190Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-1844330856944710918989) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta190Fq d2Delta190Ts 16 24 12 20 30 128 d2Delta190Lo d2Delta190Hi d2Delta190Pd d2Delta190Qd d2Delta190Ld d2Delta190Gam (d2LitsStandaloneDelta023.q2 (-1844330856944710918989) 1 (-78)) d2Delta190Check
  simpa only [d2Delta190Fq, d2Delta190Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta190Shift
#print axioms d2Delta190Sites
#print axioms d2Delta190PData
#print axioms d2Delta190Plogs
#print axioms d2Delta190Poles
#print axioms d2Delta190Laurent
#print axioms d2Delta190Small
#print axioms d2Delta190Check
#print axioms d2Delta190Bound

def d2Delta191Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta191Ts : List LTerm := laurentClean []
def d2Delta191Lo : ℚ := (d2LitsStandaloneDelta023.q2 (68714173445) 1 (-36))
def d2Delta191Hi : ℚ := (d2LitsStandaloneDelta023.q2 (17178805249) 1 (-34))
def d2Delta191Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta191Qd : List (ℚ × ℚ) := []
def d2Delta191Ld : List LaurentPieceData := []
def d2Delta191Gam : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-132897913932857091974452964666177180775, 1, -134, 1051833485004046364189578968873939, 1, -137, 2512363160135126171078459775327, 1, -135, 43978156616965041917124311761, 1, -137, 3175509589687835425589787, 1, -132, 281881786255725435497001, 1, -138, 64650385732444015627, 1, -136, 168295357426356683, 1, -138, 5109779431003, 1, -134, 30798696927, 1, -138, 2316215, 1, -136, 2277, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta191S : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [-2076529924828530781559685784172450957, 1, -128, 2054104592263475284510798411243, 1, -128, 39254086626862230197311345829, 1, -128, 343573843075605231590153709, 1, -128, 1587742672909367324500385, 1, -128, 4404384502953984619405, 1, -128, 4040638888723955691, 1, -127, 10518442514886533, 1, -128, 10219547280931, 1, -128, 3849833985, 1, -127, 2316215, 1, -127, 2277, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta191Ap : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta191Aq : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta191Al : List ℚ := d2LitsStandaloneDelta023.q2listC (raw_ints% [])
def d2Delta191Es : ℚ := (d2LitsStandaloneDelta023.q2 (61) 1 (-127))
def d2Delta191Ep : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta191Eq : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
def d2Delta191El : ℚ := (d2LitsStandaloneDelta023.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta191Shift : polyRoundApx 128 d2Delta191Lo d2Delta191Hi d2Delta191Fq.poly = (d2Delta191S,d2Delta191Es) := by decide +kernel
theorem d2Delta191Sites : mergeSites d2Delta191Fq.plogs = [] := by decide +kernel
theorem d2Delta191PData : d2Delta191Pd = [] := by decide +kernel
theorem d2Delta191Plogs : plogsRoundM 16 24 20 128 d2Delta191Lo d2Delta191Hi (mergeSites d2Delta191Fq.plogs) d2Delta191Pd = some (d2Delta191Ap,d2Delta191Ep) := by
  rw [d2Delta191Sites,d2Delta191PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta191Poles : polesRoundM 16 24 12 128 d2Delta191Lo d2Delta191Hi d2Delta191Fq.poles d2Delta191Qd = some (d2Delta191Aq,d2Delta191Eq) := by decide +kernel
theorem d2Delta191Laurent : laurentRoundM 16 30 128 d2Delta191Lo d2Delta191Hi d2Delta191Ts d2Delta191Ld = some (d2Delta191Al,d2Delta191El) := by decide +kernel
theorem d2Delta191Small : chebPolyUB (vecAdd d2Delta191S (vecAdd d2Delta191Ap (vecAdd d2Delta191Aq d2Delta191Al))) d2Delta191Gam+d2Delta191Es+d2Delta191Ep+d2Delta191Eq+d2Delta191El ≤ (d2LitsStandaloneDelta023.q2 (-7377308830046608154153) 1 (-80)) := by decide +kernel
theorem d2Delta191Check : chebRoundPieceL d2Delta191Fq d2Delta191Ts 16 24 12 20 30 128 d2Delta191Lo d2Delta191Hi d2Delta191Pd d2Delta191Qd d2Delta191Ld d2Delta191Gam (d2LitsStandaloneDelta023.q2 (-7377308830046608154153) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta191Fq d2Delta191Ts 16 24 12 20 30 128 d2Delta191Lo d2Delta191Hi d2Delta191Pd d2Delta191Qd d2Delta191Ld d2Delta191Gam d2Delta191S d2Delta191Ap d2Delta191Aq d2Delta191Al d2Delta191Es d2Delta191Ep d2Delta191Eq d2Delta191El (by decide +kernel) d2Delta191Shift d2Delta191Plogs d2Delta191Poles d2Delta191Laurent]
  exact decide_eq_true d2Delta191Small
theorem d2Delta191Bound : ∀ x ∈ Icc ((d2Delta191Lo : ℚ) : ℝ) ((d2Delta191Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta023.q2 (-7377308830046608154153) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta191Fq d2Delta191Ts 16 24 12 20 30 128 d2Delta191Lo d2Delta191Hi d2Delta191Pd d2Delta191Qd d2Delta191Ld d2Delta191Gam (d2LitsStandaloneDelta023.q2 (-7377308830046608154153) 1 (-80)) d2Delta191Check
  simpa only [d2Delta191Fq, d2Delta191Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta191Shift
#print axioms d2Delta191Sites
#print axioms d2Delta191PData
#print axioms d2Delta191Plogs
#print axioms d2Delta191Poles
#print axioms d2Delta191Laurent
#print axioms d2Delta191Small
#print axioms d2Delta191Check
#print axioms d2Delta191Bound

end StandaloneDelta023
end CatalanMeasure.GenD.Signed.Data.Cells
