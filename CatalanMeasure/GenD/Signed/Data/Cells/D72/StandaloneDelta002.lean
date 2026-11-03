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
namespace d2LitsStandaloneDelta002
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta002
namespace StandaloneDelta002
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta002.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta002.q2listC (raw_ints% []))⟩
def d2Delta16Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta16Ts : List LTerm := laurentClean []
def d2Delta16Lo : ℚ := (d2LitsStandaloneDelta002.q2 (59714507) 1 (-32))
def d2Delta16Hi : ℚ := (d2LitsStandaloneDelta002.q2 (120476565) 1 (-33))
def d2Delta16Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta16Qd : List (ℚ × ℚ) := []
def d2Delta16Ld : List LaurentPieceData := []
def d2Delta16Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-8918793259296810061451324832179382869478944901, 1, -160, -1528288595906985072126973773197090807015, 1, -159, 12563094642046819006874771147788837689, 1, -159, -63255153916684502494154593168506951, 1, -160, 66912341090651377098931693793527, 1, -160, -12340241326134617091974853441, 1, -159, -7946899405339711575436371, 1, -160, 8190208707949954802821, 1, -160, -13932419917052947, 1, -155, -286975927259825, 1, -158, 98970236503, 1, -159, -971333103, 1, -157, -6663336091, 1, -160, -5512615995, 1, -160, -2289326663, 1, -159, -3761362827, 1, -160, -383120439, 1, -157, -1249492987, 1, -159, -1997767527, 1, -160, -202034471, 1, -157, -1267376327, 1, -160, -508587631, 1, -159, -391079779, 1, -159, -38905669, 1, -156, -58665425, 1, -157, -11568813, 1, -155, -136814079, 1, -159, -213810435, 1, -160, -77451439, 1, -159, -119846195, 1, -160, -21271181, 1, -158, -16288823, 1, -158])
def d2Delta16S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-1038284190514000648771869635161981471, 1, -127, -711620651761913337125275875505, 1, -128, 5850084506594052845781318199, 1, -127, -58910837875824960127133365, 1, -128, 124634036369694196392341, 1, -128, -22985544040576725295, 1, -126, -59208987941094049, 1, -128, 61021887056559, 1, -127, -13287052459, 1, -128, -68419805, 1, -128, 24723, 1, -128, 23, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta16Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta16Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta16Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta16Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta16Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta16Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta16El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta16Shift : polyRoundApx 128 d2Delta16Lo d2Delta16Hi d2Delta16Fq.poly = (d2Delta16S,d2Delta16Es) := by decide +kernel
theorem d2Delta16Sites : mergeSites d2Delta16Fq.plogs = [] := by decide +kernel
theorem d2Delta16PData : d2Delta16Pd = [] := by decide +kernel
theorem d2Delta16Plogs : plogsRoundM 16 24 20 128 d2Delta16Lo d2Delta16Hi (mergeSites d2Delta16Fq.plogs) d2Delta16Pd = some (d2Delta16Ap,d2Delta16Ep) := by
  rw [d2Delta16Sites,d2Delta16PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta16Poles : polesRoundM 16 24 12 128 d2Delta16Lo d2Delta16Hi d2Delta16Fq.poles d2Delta16Qd = some (d2Delta16Aq,d2Delta16Eq) := by decide +kernel
theorem d2Delta16Laurent : laurentRoundM 16 30 128 d2Delta16Lo d2Delta16Hi d2Delta16Ts d2Delta16Ld = some (d2Delta16Al,d2Delta16El) := by decide +kernel
theorem d2Delta16Small : chebPolyUB (vecAdd d2Delta16S (vecAdd d2Delta16Ap (vecAdd d2Delta16Aq d2Delta16Al))) d2Delta16Gam+d2Delta16Es+d2Delta16Ep+d2Delta16Eq+d2Delta16El ≤ (d2LitsStandaloneDelta002.q2 (-1844362580570320061429) 1 (-78)) := by decide +kernel
theorem d2Delta16Check : chebRoundPieceL d2Delta16Fq d2Delta16Ts 16 24 12 20 30 128 d2Delta16Lo d2Delta16Hi d2Delta16Pd d2Delta16Qd d2Delta16Ld d2Delta16Gam (d2LitsStandaloneDelta002.q2 (-1844362580570320061429) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta16Fq d2Delta16Ts 16 24 12 20 30 128 d2Delta16Lo d2Delta16Hi d2Delta16Pd d2Delta16Qd d2Delta16Ld d2Delta16Gam d2Delta16S d2Delta16Ap d2Delta16Aq d2Delta16Al d2Delta16Es d2Delta16Ep d2Delta16Eq d2Delta16El (by decide +kernel) d2Delta16Shift d2Delta16Plogs d2Delta16Poles d2Delta16Laurent]
  exact decide_eq_true d2Delta16Small
theorem d2Delta16Bound : ∀ x ∈ Icc ((d2Delta16Lo : ℚ) : ℝ) ((d2Delta16Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-1844362580570320061429) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta16Fq d2Delta16Ts 16 24 12 20 30 128 d2Delta16Lo d2Delta16Hi d2Delta16Pd d2Delta16Qd d2Delta16Ld d2Delta16Gam (d2LitsStandaloneDelta002.q2 (-1844362580570320061429) 1 (-78)) d2Delta16Check
  simpa only [d2Delta16Fq, d2Delta16Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta16Shift
#print axioms d2Delta16Sites
#print axioms d2Delta16PData
#print axioms d2Delta16Plogs
#print axioms d2Delta16Poles
#print axioms d2Delta16Laurent
#print axioms d2Delta16Small
#print axioms d2Delta16Check
#print axioms d2Delta16Bound

def d2Delta17Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta17Ts : List LTerm := laurentClean []
def d2Delta17Lo : ℚ := (d2LitsStandaloneDelta002.q2 (120476565) 1 (-33))
def d2Delta17Hi : ℚ := (d2LitsStandaloneDelta002.q2 (30381029) 1 (-31))
def d2Delta17Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta17Qd : List (ℚ × ℚ) := []
def d2Delta17Ld : List LaurentPieceData := []
def d2Delta17Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-8918799173832552867999466456869557913976647813, 1, -160, -1429292881176859009887398809301021416679, 1, -159, 12186767349682422875658765795171689273, 1, -159, -62188515621273974039267754522427463, 1, -160, 66416842748648427979569693569271, 1, -160, -12434228989072842893710029633, 1, -159, -7717779497613604603833427, 1, -160, 8175282333810395653253, 1, -160, -15219099908209683, 1, -155, -284880121631409, 1, -158, 101151274583, 1, -159, -971333103, 1, -157, -6663336091, 1, -160, -5512615995, 1, -160, -2289326663, 1, -159, -3761362827, 1, -160, -383120439, 1, -157, -1249492987, 1, -159, -1997767527, 1, -160, -202034471, 1, -157, -1267376327, 1, -160, -508587631, 1, -159, -391079779, 1, -159, -38905669, 1, -156, -58665425, 1, -157, -11568813, 1, -155, -136814079, 1, -159, -213810435, 1, -160, -77451439, 1, -159, -119846195, 1, -160, -21271181, 1, -158, -16288823, 1, -158])
def d2Delta17S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-1038284878968962136483034791977669547, 1, -127, -83190365605149317561019993055, 1, -125, 5674843916651883895955811069, 1, -127, -57917452677031633745860351, 1, -128, 123711096225894379293261, 1, -128, -46321219215454141255, 1, -127, -57501909148072479, 1, -128, 121821352681747, 1, -128, -3628531855, 1, -126, -33960063, 1, -127, 25243, 1, -128, 23, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta17Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta17Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta17Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta17Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta17Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta17Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta17El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta17Shift : polyRoundApx 128 d2Delta17Lo d2Delta17Hi d2Delta17Fq.poly = (d2Delta17S,d2Delta17Es) := by decide +kernel
theorem d2Delta17Sites : mergeSites d2Delta17Fq.plogs = [] := by decide +kernel
theorem d2Delta17PData : d2Delta17Pd = [] := by decide +kernel
theorem d2Delta17Plogs : plogsRoundM 16 24 20 128 d2Delta17Lo d2Delta17Hi (mergeSites d2Delta17Fq.plogs) d2Delta17Pd = some (d2Delta17Ap,d2Delta17Ep) := by
  rw [d2Delta17Sites,d2Delta17PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta17Poles : polesRoundM 16 24 12 128 d2Delta17Lo d2Delta17Hi d2Delta17Fq.poles d2Delta17Qd = some (d2Delta17Aq,d2Delta17Eq) := by decide +kernel
theorem d2Delta17Laurent : laurentRoundM 16 30 128 d2Delta17Lo d2Delta17Hi d2Delta17Ts d2Delta17Ld = some (d2Delta17Al,d2Delta17El) := by decide +kernel
theorem d2Delta17Small : chebPolyUB (vecAdd d2Delta17S (vecAdd d2Delta17Ap (vecAdd d2Delta17Aq d2Delta17Al))) d2Delta17Gam+d2Delta17Es+d2Delta17Ep+d2Delta17Eq+d2Delta17El ≤ (d2LitsStandaloneDelta002.q2 (-7377455379068714841061) 1 (-80)) := by decide +kernel
theorem d2Delta17Check : chebRoundPieceL d2Delta17Fq d2Delta17Ts 16 24 12 20 30 128 d2Delta17Lo d2Delta17Hi d2Delta17Pd d2Delta17Qd d2Delta17Ld d2Delta17Gam (d2LitsStandaloneDelta002.q2 (-7377455379068714841061) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta17Fq d2Delta17Ts 16 24 12 20 30 128 d2Delta17Lo d2Delta17Hi d2Delta17Pd d2Delta17Qd d2Delta17Ld d2Delta17Gam d2Delta17S d2Delta17Ap d2Delta17Aq d2Delta17Al d2Delta17Es d2Delta17Ep d2Delta17Eq d2Delta17El (by decide +kernel) d2Delta17Shift d2Delta17Plogs d2Delta17Poles d2Delta17Laurent]
  exact decide_eq_true d2Delta17Small
theorem d2Delta17Bound : ∀ x ∈ Icc ((d2Delta17Lo : ℚ) : ℝ) ((d2Delta17Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-7377455379068714841061) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta17Fq d2Delta17Ts 16 24 12 20 30 128 d2Delta17Lo d2Delta17Hi d2Delta17Pd d2Delta17Qd d2Delta17Ld d2Delta17Gam (d2LitsStandaloneDelta002.q2 (-7377455379068714841061) 1 (-80)) d2Delta17Check
  simpa only [d2Delta17Fq, d2Delta17Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta17Shift
#print axioms d2Delta17Sites
#print axioms d2Delta17PData
#print axioms d2Delta17Plogs
#print axioms d2Delta17Poles
#print axioms d2Delta17Laurent
#print axioms d2Delta17Small
#print axioms d2Delta17Check
#print axioms d2Delta17Bound

def d2Delta18Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta18Ts : List LTerm := laurentClean []
def d2Delta18Lo : ℚ := (d2LitsStandaloneDelta002.q2 (30381029) 1 (-31))
def d2Delta18Hi : ℚ := (d2LitsStandaloneDelta002.q2 (122571667) 1 (-33))
def d2Delta18Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta18Qd : List (ℚ × ℚ) := []
def d2Delta18Ld : List LaurentPieceData := []
def d2Delta18Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-8918804698366236499458890961374769872266145925, 1, -160, -1333282252996223830326087460662623919335, 1, -159, 11816816041621920126919553630891598649, 1, -159, -61129835076760047426586763648811079, 1, -160, 65917639854284520037353707122935, 1, -160, -12525469795051338576879121217, 1, -159, -7489095928598486671174739, 1, -160, 8159043261639972562053, 1, -160, -16496251104951315, 1, -155, -282740993036977, 1, -158, 103302952535, 1, -159, -971333103, 1, -157, -6663336091, 1, -160, -5512615995, 1, -160, -2289326663, 1, -159, -3761362827, 1, -160, -383120439, 1, -157, -1249492987, 1, -159, -1997767527, 1, -160, -202034471, 1, -157, -1267376327, 1, -160, -508587631, 1, -159, -391079779, 1, -159, -38905669, 1, -156, -58665425, 1, -157, -11568813, 1, -155, -136814079, 1, -159, -213810435, 1, -160, -77451439, 1, -159, -119846195, 1, -160, -21271181, 1, -158, -16288823, 1, -158])
def d2Delta18S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-1038285522023192917119640372145585895, 1, -127, -620815231607405500387242426377, 1, -128, 5502572379218652206670413101, 1, -127, -1779108710527299853088605, 1, -123, 61390627910242913306637, 1, -127, -93322234986111687337, 1, -128, -55798081349959439, 1, -128, 121579370502179, 1, -128, -15732114997, 1, -128, -33705059, 1, -127, 6439, 1, -126, 23, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta18Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta18Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta18Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta18Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta18Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta18Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta18El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta18Shift : polyRoundApx 128 d2Delta18Lo d2Delta18Hi d2Delta18Fq.poly = (d2Delta18S,d2Delta18Es) := by decide +kernel
theorem d2Delta18Sites : mergeSites d2Delta18Fq.plogs = [] := by decide +kernel
theorem d2Delta18PData : d2Delta18Pd = [] := by decide +kernel
theorem d2Delta18Plogs : plogsRoundM 16 24 20 128 d2Delta18Lo d2Delta18Hi (mergeSites d2Delta18Fq.plogs) d2Delta18Pd = some (d2Delta18Ap,d2Delta18Ep) := by
  rw [d2Delta18Sites,d2Delta18PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta18Poles : polesRoundM 16 24 12 128 d2Delta18Lo d2Delta18Hi d2Delta18Fq.poles d2Delta18Qd = some (d2Delta18Aq,d2Delta18Eq) := by decide +kernel
theorem d2Delta18Laurent : laurentRoundM 16 30 128 d2Delta18Lo d2Delta18Hi d2Delta18Ts d2Delta18Ld = some (d2Delta18Al,d2Delta18El) := by decide +kernel
theorem d2Delta18Small : chebPolyUB (vecAdd d2Delta18S (vecAdd d2Delta18Ap (vecAdd d2Delta18Aq d2Delta18Al))) d2Delta18Gam+d2Delta18Es+d2Delta18Ep+d2Delta18Eq+d2Delta18El ≤ (d2LitsStandaloneDelta002.q2 (-3688730054152520514659) 1 (-79)) := by decide +kernel
theorem d2Delta18Check : chebRoundPieceL d2Delta18Fq d2Delta18Ts 16 24 12 20 30 128 d2Delta18Lo d2Delta18Hi d2Delta18Pd d2Delta18Qd d2Delta18Ld d2Delta18Gam (d2LitsStandaloneDelta002.q2 (-3688730054152520514659) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta18Fq d2Delta18Ts 16 24 12 20 30 128 d2Delta18Lo d2Delta18Hi d2Delta18Pd d2Delta18Qd d2Delta18Ld d2Delta18Gam d2Delta18S d2Delta18Ap d2Delta18Aq d2Delta18Al d2Delta18Es d2Delta18Ep d2Delta18Eq d2Delta18El (by decide +kernel) d2Delta18Shift d2Delta18Plogs d2Delta18Poles d2Delta18Laurent]
  exact decide_eq_true d2Delta18Small
theorem d2Delta18Bound : ∀ x ∈ Icc ((d2Delta18Lo : ℚ) : ℝ) ((d2Delta18Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-3688730054152520514659) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta18Fq d2Delta18Ts 16 24 12 20 30 128 d2Delta18Lo d2Delta18Hi d2Delta18Pd d2Delta18Qd d2Delta18Ld d2Delta18Gam (d2LitsStandaloneDelta002.q2 (-3688730054152520514659) 1 (-79)) d2Delta18Check
  simpa only [d2Delta18Fq, d2Delta18Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta18Shift
#print axioms d2Delta18Sites
#print axioms d2Delta18PData
#print axioms d2Delta18Plogs
#print axioms d2Delta18Poles
#print axioms d2Delta18Laurent
#print axioms d2Delta18Small
#print axioms d2Delta18Check
#print axioms d2Delta18Bound

def d2Delta19Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta19Ts : List LTerm := laurentClean []
def d2Delta19Lo : ℚ := (d2LitsStandaloneDelta002.q2 (122571667) 1 (-33))
def d2Delta19Hi : ℚ := (d2LitsStandaloneDelta002.q2 (7857145) 1 (-29))
def d2Delta19Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta19Qd : List (ℚ × ℚ) := []
def d2Delta19Ld : List LaurentPieceData := []
def d2Delta19Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-8918814447032373406839002388802929165557080069, 1, -160, -3452165469238537687600982243089565146343, 1, -159, 97531241103516527818329235666396427, 1, -149, -1594015065835013508792020452732551239, 1, -160, 1314391488490402368892738074298409, 1, -158, -3085979876524312565157375210305, 1, -159, -2563609766991880948435330495, 1, -159, 17764096649629759966487685, 1, -160, -3993420060595061649307, 1, -160, -5478375506982474417, 1, -158, 6627830746042261, 1, -159, 2090225279505, 1, -157, -21486863225, 1, -160, -5521004603, 1, -160, -4433007459, 1, -160, -3761362827, 1, -160, -2983573175, 1, -160, -1249492987, 1, -159, -1955909639, 1, -160, -202034471, 1, -157, -623805051, 1, -159, -508587631, 1, -159, -773612001, 1, -160, -38905669, 1, -156, -465949365, 1, -160, -11568813, 1, -155, -136208483, 1, -159, -213810435, 1, -160, -19313655, 1, -157, -119846195, 1, -160, -84969513, 1, -160, -16288823, 1, -158])
def d2Delta19S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-1038286677418637277530468326378053431, 1, -127, -1606426416928761976024248447955, 1, -128, 46501623343220234528005704163, 1, -127, -185564184303808754212871597, 1, -125, 9793037021903217423978249, 1, -128, -22992805027651929785921, 1, -128, -38200524346227400471, 1, -128, 264708606479824103, 1, -128, -119017142596893, 1, -128, -1306157472367, 1, -128, 1580220621, 1, -128, 1994345, 1, -127, -449, 1, -124, -9, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta19Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta19Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta19Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta19Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta19Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta19Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta19El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta19Shift : polyRoundApx 128 d2Delta19Lo d2Delta19Hi d2Delta19Fq.poly = (d2Delta19S,d2Delta19Es) := by decide +kernel
theorem d2Delta19Sites : mergeSites d2Delta19Fq.plogs = [] := by decide +kernel
theorem d2Delta19PData : d2Delta19Pd = [] := by decide +kernel
theorem d2Delta19Plogs : plogsRoundM 16 24 20 128 d2Delta19Lo d2Delta19Hi (mergeSites d2Delta19Fq.plogs) d2Delta19Pd = some (d2Delta19Ap,d2Delta19Ep) := by
  rw [d2Delta19Sites,d2Delta19PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta19Poles : polesRoundM 16 24 12 128 d2Delta19Lo d2Delta19Hi d2Delta19Fq.poles d2Delta19Qd = some (d2Delta19Aq,d2Delta19Eq) := by decide +kernel
theorem d2Delta19Laurent : laurentRoundM 16 30 128 d2Delta19Lo d2Delta19Hi d2Delta19Ts d2Delta19Ld = some (d2Delta19Al,d2Delta19El) := by decide +kernel
theorem d2Delta19Small : chebPolyUB (vecAdd d2Delta19S (vecAdd d2Delta19Ap (vecAdd d2Delta19Aq d2Delta19Al))) d2Delta19Gam+d2Delta19Es+d2Delta19Ep+d2Delta19Eq+d2Delta19El ≤ (d2LitsStandaloneDelta002.q2 (-7377464519867094849099) 1 (-80)) := by decide +kernel
theorem d2Delta19Check : chebRoundPieceL d2Delta19Fq d2Delta19Ts 16 24 12 20 30 128 d2Delta19Lo d2Delta19Hi d2Delta19Pd d2Delta19Qd d2Delta19Ld d2Delta19Gam (d2LitsStandaloneDelta002.q2 (-7377464519867094849099) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta19Fq d2Delta19Ts 16 24 12 20 30 128 d2Delta19Lo d2Delta19Hi d2Delta19Pd d2Delta19Qd d2Delta19Ld d2Delta19Gam d2Delta19S d2Delta19Ap d2Delta19Aq d2Delta19Al d2Delta19Es d2Delta19Ep d2Delta19Eq d2Delta19El (by decide +kernel) d2Delta19Shift d2Delta19Plogs d2Delta19Poles d2Delta19Laurent]
  exact decide_eq_true d2Delta19Small
theorem d2Delta19Bound : ∀ x ∈ Icc ((d2Delta19Lo : ℚ) : ℝ) ((d2Delta19Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-7377464519867094849099) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta19Fq d2Delta19Ts 16 24 12 20 30 128 d2Delta19Lo d2Delta19Hi d2Delta19Pd d2Delta19Qd d2Delta19Ld d2Delta19Gam (d2LitsStandaloneDelta002.q2 (-7377464519867094849099) 1 (-80)) d2Delta19Check
  simpa only [d2Delta19Fq, d2Delta19Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta19Shift
#print axioms d2Delta19Sites
#print axioms d2Delta19PData
#print axioms d2Delta19Plogs
#print axioms d2Delta19Poles
#print axioms d2Delta19Laurent
#print axioms d2Delta19Small
#print axioms d2Delta19Check
#print axioms d2Delta19Bound

def d2Delta20Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta20Ts : List LTerm := laurentClean []
def d2Delta20Lo : ℚ := (d2LitsStandaloneDelta002.q2 (7857145) 1 (-29))
def d2Delta20Hi : ℚ := (d2LitsStandaloneDelta002.q2 (9952247) 1 (-29))
def d2Delta20Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta20Qd : List (ℚ × ℚ) := []
def d2Delta20Ld : List LaurentPieceData := []
def d2Delta20Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-8918838073435724377831879139065818588155195581, 1, -160, -1675365126271381839866592118218747731175, 1, -159, 12124577663875783833422772154199317876449, 1, -160, -1385722995859172259934095497072450977863, 1, -160, 58278377474937207492934052410946427401, 1, -160, -461007462721520651749446536980427585, 1, -159, -3412057204998844887045764803290977, 1, -160, 260679753272791048189613724607621, 1, -160, -344322970528101202056916657957, 1, -158, -8199604403706339142119789233, 1, -158, 323315577866930523691086103, 1, -160, 309767740498787565314577, 1, -157, -9297208779082527367317, 1, -158, -116708175619029588027, 1, -160, 2857352109385883875, 1, -160, 2660276925245557, 1, -160, -40386606219943, 1, -158, 32437583877, 1, -159, 5051205329, 1, -160, -203230503, 1, -157, -1262723515, 1, -160, -508587631, 1, -159, -194907331, 1, -158, -38905669, 1, -156, -234079567, 1, -159, -11568813, 1, -155, -273151223, 1, -160, -213810435, 1, -160, -154729107, 1, -160, -119846195, 1, -160, -21257139, 1, -158, -16288823, 1, -158])
def d2Delta20S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-129786351167882095601653288845864057, 1, -124, 93344929087214633403629084771, 1, -127, 692172527051643954824556567945, 1, -125, -1286258241842801121501745476303, 1, -128, 54295009240656973824865301415, 1, -127, -1720787155375004953074456931, 1, -127, -12669814935813585679585997, 1, -127, 3888831259128105706253877, 1, -128, -41142912110338239971259, 1, -128, -978281639896398156775, 1, -127, 38595445628322543863, 1, -128, 591196863572299477, 1, -128, -17752101349961371, 1, -128, -55669818782773, 1, -127, 5454898373755, 1, -128, 10143790709, 1, -128, -1233445311, 1, -128, 1030821, 1, -128, 215007, 1, -128, -73, 1, -125, -15, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta20Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta20Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta20Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta20Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta20Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta20Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta20El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta20Shift : polyRoundApx 128 d2Delta20Lo d2Delta20Hi d2Delta20Fq.poly = (d2Delta20S,d2Delta20Es) := by decide +kernel
theorem d2Delta20Sites : mergeSites d2Delta20Fq.plogs = [] := by decide +kernel
theorem d2Delta20PData : d2Delta20Pd = [] := by decide +kernel
theorem d2Delta20Plogs : plogsRoundM 16 24 20 128 d2Delta20Lo d2Delta20Hi (mergeSites d2Delta20Fq.plogs) d2Delta20Pd = some (d2Delta20Ap,d2Delta20Ep) := by
  rw [d2Delta20Sites,d2Delta20PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta20Poles : polesRoundM 16 24 12 128 d2Delta20Lo d2Delta20Hi d2Delta20Fq.poles d2Delta20Qd = some (d2Delta20Aq,d2Delta20Eq) := by decide +kernel
theorem d2Delta20Laurent : laurentRoundM 16 30 128 d2Delta20Lo d2Delta20Hi d2Delta20Ts d2Delta20Ld = some (d2Delta20Al,d2Delta20El) := by decide +kernel
theorem d2Delta20Small : chebPolyUB (vecAdd d2Delta20S (vecAdd d2Delta20Ap (vecAdd d2Delta20Aq d2Delta20Al))) d2Delta20Gam+d2Delta20Es+d2Delta20Ep+d2Delta20Eq+d2Delta20El ≤ (d2LitsStandaloneDelta002.q2 (-7377475944755493389803) 1 (-80)) := by decide +kernel
theorem d2Delta20Check : chebRoundPieceL d2Delta20Fq d2Delta20Ts 16 24 12 20 30 128 d2Delta20Lo d2Delta20Hi d2Delta20Pd d2Delta20Qd d2Delta20Ld d2Delta20Gam (d2LitsStandaloneDelta002.q2 (-7377475944755493389803) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta20Fq d2Delta20Ts 16 24 12 20 30 128 d2Delta20Lo d2Delta20Hi d2Delta20Pd d2Delta20Qd d2Delta20Ld d2Delta20Gam d2Delta20S d2Delta20Ap d2Delta20Aq d2Delta20Al d2Delta20Es d2Delta20Ep d2Delta20Eq d2Delta20El (by decide +kernel) d2Delta20Shift d2Delta20Plogs d2Delta20Poles d2Delta20Laurent]
  exact decide_eq_true d2Delta20Small
theorem d2Delta20Bound : ∀ x ∈ Icc ((d2Delta20Lo : ℚ) : ℝ) ((d2Delta20Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-7377475944755493389803) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta20Fq d2Delta20Ts 16 24 12 20 30 128 d2Delta20Lo d2Delta20Hi d2Delta20Pd d2Delta20Qd d2Delta20Ld d2Delta20Gam (d2LitsStandaloneDelta002.q2 (-7377475944755493389803) 1 (-80)) d2Delta20Check
  simpa only [d2Delta20Fq, d2Delta20Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta20Shift
#print axioms d2Delta20Sites
#print axioms d2Delta20PData
#print axioms d2Delta20Plogs
#print axioms d2Delta20Poles
#print axioms d2Delta20Laurent
#print axioms d2Delta20Small
#print axioms d2Delta20Check
#print axioms d2Delta20Bound

def d2Delta21Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta21Ts : List LTerm := laurentClean []
def d2Delta21Lo : ℚ := (d2LitsStandaloneDelta002.q2 (9952247) 1 (-29))
def d2Delta21Hi : ℚ := (d2LitsStandaloneDelta002.q2 (20952045) 1 (-30))
def d2Delta21Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta21Qd : List (ℚ × ℚ) := []
def d2Delta21Ld : List LaurentPieceData := []
def d2Delta21Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-8918821449542190647629938528488324707007885141, 1, -160, 4708029437187632652652837478270773943195, 1, -159, 224071540237339749355626123704495644235, 1, -160, -13388588233395592733820224533168090973, 1, -160, 181917418514400326985857518791698411, 1, -160, -57486887393551669740872026839471, 1, -156, 215602526560683582408885006295, 1, -160, 13830646892871535418155287415, 1, -160, -120529611068759325949689, 1, -152, -91587123476968624472695, 1, -160, 179365553037131367529, 1, -159, 78809548235159749, 1, -158, -18340869533595, 1, -153, -124288410319, 1, -159, 3060194275, 1, -159, -3764871499, 1, -160, -3002421513, 1, -160, -624241055, 1, -158, -1967580245, 1, -160, -1613906333, 1, -160, -626962943, 1, -159, -253726937, 1, -158, -97077775, 1, -157, -155124531, 1, -158, -467217647, 1, -160, -368562593, 1, -160, -68222485, 1, -158, -212537971, 1, -160, -19333159, 1, -157, -118909973, 1, -160, -85014949, 1, -160, -64500195, 1, -160])
def d2Delta21S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-1038287495429605907072391134800765361, 1, -127, 1100848899226128734512705902617, 1, -127, 104002595182600703718669126041, 1, -128, -12464811176780894835476788589, 1, -128, 338845186460970747117900545, 1, -128, -3426846173770552217459379, 1, -128, 1608203230500251437993, 1, -128, 206104981762965720947, 1, -128, -919674869520579937, 1, -128, -5459224648056301, 1, -128, 21383719348679, 1, -127, 37579698593, 1, -127, -279876347, 1, -126, -231747, 1, -128, 20179, 1, -128, -7, 1, -127, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta21Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta21Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta21Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta21Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta21Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta21Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta21El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta21Shift : polyRoundApx 128 d2Delta21Lo d2Delta21Hi d2Delta21Fq.poly = (d2Delta21S,d2Delta21Es) := by decide +kernel
theorem d2Delta21Sites : mergeSites d2Delta21Fq.plogs = [] := by decide +kernel
theorem d2Delta21PData : d2Delta21Pd = [] := by decide +kernel
theorem d2Delta21Plogs : plogsRoundM 16 24 20 128 d2Delta21Lo d2Delta21Hi (mergeSites d2Delta21Fq.plogs) d2Delta21Pd = some (d2Delta21Ap,d2Delta21Ep) := by
  rw [d2Delta21Sites,d2Delta21PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta21Poles : polesRoundM 16 24 12 128 d2Delta21Lo d2Delta21Hi d2Delta21Fq.poles d2Delta21Qd = some (d2Delta21Aq,d2Delta21Eq) := by decide +kernel
theorem d2Delta21Laurent : laurentRoundM 16 30 128 d2Delta21Lo d2Delta21Hi d2Delta21Ts d2Delta21Ld = some (d2Delta21Al,d2Delta21El) := by decide +kernel
theorem d2Delta21Small : chebPolyUB (vecAdd d2Delta21S (vecAdd d2Delta21Ap (vecAdd d2Delta21Aq d2Delta21Al))) d2Delta21Gam+d2Delta21Es+d2Delta21Ep+d2Delta21Eq+d2Delta21El ≤ (d2LitsStandaloneDelta002.q2 (-1844367051132097454501) 1 (-78)) := by decide +kernel
theorem d2Delta21Check : chebRoundPieceL d2Delta21Fq d2Delta21Ts 16 24 12 20 30 128 d2Delta21Lo d2Delta21Hi d2Delta21Pd d2Delta21Qd d2Delta21Ld d2Delta21Gam (d2LitsStandaloneDelta002.q2 (-1844367051132097454501) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta21Fq d2Delta21Ts 16 24 12 20 30 128 d2Delta21Lo d2Delta21Hi d2Delta21Pd d2Delta21Qd d2Delta21Ld d2Delta21Gam d2Delta21S d2Delta21Ap d2Delta21Aq d2Delta21Al d2Delta21Es d2Delta21Ep d2Delta21Eq d2Delta21El (by decide +kernel) d2Delta21Shift d2Delta21Plogs d2Delta21Poles d2Delta21Laurent]
  exact decide_eq_true d2Delta21Small
theorem d2Delta21Bound : ∀ x ∈ Icc ((d2Delta21Lo : ℚ) : ℝ) ((d2Delta21Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-1844367051132097454501) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta21Fq d2Delta21Ts 16 24 12 20 30 128 d2Delta21Lo d2Delta21Hi d2Delta21Pd d2Delta21Qd d2Delta21Ld d2Delta21Gam (d2LitsStandaloneDelta002.q2 (-1844367051132097454501) 1 (-78)) d2Delta21Check
  simpa only [d2Delta21Fq, d2Delta21Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta21Shift
#print axioms d2Delta21Sites
#print axioms d2Delta21PData
#print axioms d2Delta21Plogs
#print axioms d2Delta21Poles
#print axioms d2Delta21Laurent
#print axioms d2Delta21Small
#print axioms d2Delta21Check
#print axioms d2Delta21Bound

def d2Delta22Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta22Ts : List LTerm := laurentClean []
def d2Delta22Lo : ℚ := (d2LitsStandaloneDelta002.q2 (20952045) 1 (-30))
def d2Delta22Hi : ℚ := (d2LitsStandaloneDelta002.q2 (84855731) 1 (-32))
def d2Delta22Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta22Qd : List (ℚ × ℚ) := []
def d2Delta22Ld : List LaurentPieceData := []
def d2Delta22Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-1114851156019597059532035675002902187169377505, 1, -157, 2582750161176643087977142397472740038491, 1, -160, 2026325665917957705686775409710512209, 1, -158, -45400470644371409553948479313890541, 1, -158, 10403162884961035377727804971251, 1, -154, -893413637826613116559544798165, 1, -160, 55220472428257972844727195, 1, -159, 805316777824332884908495, 1, -160, -500763836309673361865, 1, -160, -314793222931971525, 1, -160, 87367932653269, 1, -158, 50829268635, 1, -160, -6761077293, 1, -160, -5215375227, 1, -160, -4543827601, 1, -160, -3522436537, 1, -160, -1520012667, 1, -159, -36199793, 1, -154, -1982353175, 1, -160, -370717591, 1, -158, -1259019999, 1, -160, -922981809, 1, -160, -778150435, 1, -160, -558303297, 1, -160, -233806015, 1, -159, -327989301, 1, -160, -272976211, 1, -160, -187023485, 1, -160, -77340479, 1, -159, -12930959, 1, -157, -10627157, 1, -157, -55472621, 1, -160])
def d2Delta22S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-1038286049880717571081351507702708045, 1, -127, 300735114416724736632132703263, 1, -127, 471635689898816479464827845, 1, -125, -42281443136283676330202899, 1, -126, 620076211152432328908535, 1, -127, -3328246157812168107177, 1, -128, 822879008795605539, 1, -128, 12000197335568459, 1, -128, -3731007360783, 1, -126, -4690793965, 1, -126, 41661597, 1, -128, 1739, 1, -125, -67, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta22Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta22Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta22Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta22Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta22Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta22Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta22El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta22Shift : polyRoundApx 128 d2Delta22Lo d2Delta22Hi d2Delta22Fq.poly = (d2Delta22S,d2Delta22Es) := by decide +kernel
theorem d2Delta22Sites : mergeSites d2Delta22Fq.plogs = [] := by decide +kernel
theorem d2Delta22PData : d2Delta22Pd = [] := by decide +kernel
theorem d2Delta22Plogs : plogsRoundM 16 24 20 128 d2Delta22Lo d2Delta22Hi (mergeSites d2Delta22Fq.plogs) d2Delta22Pd = some (d2Delta22Ap,d2Delta22Ep) := by
  rw [d2Delta22Sites,d2Delta22PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta22Poles : polesRoundM 16 24 12 128 d2Delta22Lo d2Delta22Hi d2Delta22Fq.poles d2Delta22Qd = some (d2Delta22Aq,d2Delta22Eq) := by decide +kernel
theorem d2Delta22Laurent : laurentRoundM 16 30 128 d2Delta22Lo d2Delta22Hi d2Delta22Ts d2Delta22Ld = some (d2Delta22Al,d2Delta22El) := by decide +kernel
theorem d2Delta22Small : chebPolyUB (vecAdd d2Delta22S (vecAdd d2Delta22Ap (vecAdd d2Delta22Aq d2Delta22Al))) d2Delta22Gam+d2Delta22Es+d2Delta22Ep+d2Delta22Eq+d2Delta22El ≤ (d2LitsStandaloneDelta002.q2 (-7377463953877751928481) 1 (-80)) := by decide +kernel
theorem d2Delta22Check : chebRoundPieceL d2Delta22Fq d2Delta22Ts 16 24 12 20 30 128 d2Delta22Lo d2Delta22Hi d2Delta22Pd d2Delta22Qd d2Delta22Ld d2Delta22Gam (d2LitsStandaloneDelta002.q2 (-7377463953877751928481) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta22Fq d2Delta22Ts 16 24 12 20 30 128 d2Delta22Lo d2Delta22Hi d2Delta22Pd d2Delta22Qd d2Delta22Ld d2Delta22Gam d2Delta22S d2Delta22Ap d2Delta22Aq d2Delta22Al d2Delta22Es d2Delta22Ep d2Delta22Eq d2Delta22El (by decide +kernel) d2Delta22Shift d2Delta22Plogs d2Delta22Poles d2Delta22Laurent]
  exact decide_eq_true d2Delta22Small
theorem d2Delta22Bound : ∀ x ∈ Icc ((d2Delta22Lo : ℚ) : ℝ) ((d2Delta22Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-7377463953877751928481) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta22Fq d2Delta22Ts 16 24 12 20 30 128 d2Delta22Lo d2Delta22Hi d2Delta22Pd d2Delta22Qd d2Delta22Ld d2Delta22Gam (d2LitsStandaloneDelta002.q2 (-7377463953877751928481) 1 (-80)) d2Delta22Check
  simpa only [d2Delta22Fq, d2Delta22Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta22Shift
#print axioms d2Delta22Sites
#print axioms d2Delta22PData
#print axioms d2Delta22Plogs
#print axioms d2Delta22Poles
#print axioms d2Delta22Laurent
#print axioms d2Delta22Small
#print axioms d2Delta22Check
#print axioms d2Delta22Bound

def d2Delta23Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta23Ts : List LTerm := laurentClean []
def d2Delta23Lo : ℚ := (d2LitsStandaloneDelta002.q2 (84855731) 1 (-32))
def d2Delta23Hi : ℚ := (d2LitsStandaloneDelta002.q2 (42951641) 1 (-31))
def d2Delta23Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta23Qd : List (ℚ × ℚ) := []
def d2Delta23Ld : List LaurentPieceData := []
def d2Delta23Gam : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-8918804024587964874036321207070482430695353811, 1, -160, 2639055433366655729187992066089310528115, 1, -160, 5989407939877974926509440283591134631, 1, -160, -171091838316440824350770518781499649, 1, -160, 323981237381916920289130693030615, 1, -159, -890494289849439466202678425759, 1, -160, 66381894020009141106475729, 1, -159, 197278429267624485801207, 1, -158, -511844164780859811083, 1, -160, -300764605923229469, 1, -160, 21993231041385, 1, -156, 43732451367, 1, -160, -1651154395, 1, -158, -5518646879, 1, -160, -4468726939, 1, -160, -1878613747, 1, -159, -3008251977, 1, -160, -2491948259, 1, -160, -1970585265, 1, -160, -1608767697, 1, -160, -1255237457, 1, -160, -1010141501, 1, -160, -777106975, 1, -160, -308204879, 1, -159, -116842139, 1, -158, -365281507, 1, -160, -272929087, 1, -160, -210056907, 1, -160, -154673595, 1, -160, -58567099, 1, -159, -21254091, 1, -158, -63293493, 1, -160])
def d2Delta23S : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [-2076570883061905589786427235143231091, 1, -128, 614572480420844647710938162909, 1, -128, 348478560986335032679066393, 1, -125, -79668772329550225330289319, 1, -127, 1206922676732519081939137, 1, -128, -3317370316585822432531, 1, -128, 247299452881613727, 1, -126, 11758751034053249, 1, -128, -7627124842763, 1, -127, -8963500347, 1, -127, 41950045, 1, -128, 6155, 1, -127, -67, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta23Ap : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta23Aq : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta23Al : List ℚ := d2LitsStandaloneDelta002.q2listC (raw_ints% [])
def d2Delta23Es : ℚ := (d2LitsStandaloneDelta002.q2 (61) 1 (-127))
def d2Delta23Ep : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta23Eq : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
def d2Delta23El : ℚ := (d2LitsStandaloneDelta002.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta23Shift : polyRoundApx 128 d2Delta23Lo d2Delta23Hi d2Delta23Fq.poly = (d2Delta23S,d2Delta23Es) := by decide +kernel
theorem d2Delta23Sites : mergeSites d2Delta23Fq.plogs = [] := by decide +kernel
theorem d2Delta23PData : d2Delta23Pd = [] := by decide +kernel
theorem d2Delta23Plogs : plogsRoundM 16 24 20 128 d2Delta23Lo d2Delta23Hi (mergeSites d2Delta23Fq.plogs) d2Delta23Pd = some (d2Delta23Ap,d2Delta23Ep) := by
  rw [d2Delta23Sites,d2Delta23PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta23Poles : polesRoundM 16 24 12 128 d2Delta23Lo d2Delta23Hi d2Delta23Fq.poles d2Delta23Qd = some (d2Delta23Aq,d2Delta23Eq) := by decide +kernel
theorem d2Delta23Laurent : laurentRoundM 16 30 128 d2Delta23Lo d2Delta23Hi d2Delta23Ts d2Delta23Ld = some (d2Delta23Al,d2Delta23El) := by decide +kernel
theorem d2Delta23Small : chebPolyUB (vecAdd d2Delta23S (vecAdd d2Delta23Ap (vecAdd d2Delta23Aq d2Delta23Al))) d2Delta23Gam+d2Delta23Es+d2Delta23Ep+d2Delta23Eq+d2Delta23El ≤ (d2LitsStandaloneDelta002.q2 (-3688729794113604326099) 1 (-79)) := by decide +kernel
theorem d2Delta23Check : chebRoundPieceL d2Delta23Fq d2Delta23Ts 16 24 12 20 30 128 d2Delta23Lo d2Delta23Hi d2Delta23Pd d2Delta23Qd d2Delta23Ld d2Delta23Gam (d2LitsStandaloneDelta002.q2 (-3688729794113604326099) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta23Fq d2Delta23Ts 16 24 12 20 30 128 d2Delta23Lo d2Delta23Hi d2Delta23Pd d2Delta23Qd d2Delta23Ld d2Delta23Gam d2Delta23S d2Delta23Ap d2Delta23Aq d2Delta23Al d2Delta23Es d2Delta23Ep d2Delta23Eq d2Delta23El (by decide +kernel) d2Delta23Shift d2Delta23Plogs d2Delta23Poles d2Delta23Laurent]
  exact decide_eq_true d2Delta23Small
theorem d2Delta23Bound : ∀ x ∈ Icc ((d2Delta23Lo : ℚ) : ℝ) ((d2Delta23Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta002.q2 (-3688729794113604326099) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta23Fq d2Delta23Ts 16 24 12 20 30 128 d2Delta23Lo d2Delta23Hi d2Delta23Pd d2Delta23Qd d2Delta23Ld d2Delta23Gam (d2LitsStandaloneDelta002.q2 (-3688729794113604326099) 1 (-79)) d2Delta23Check
  simpa only [d2Delta23Fq, d2Delta23Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta23Shift
#print axioms d2Delta23Sites
#print axioms d2Delta23PData
#print axioms d2Delta23Plogs
#print axioms d2Delta23Poles
#print axioms d2Delta23Laurent
#print axioms d2Delta23Small
#print axioms d2Delta23Check
#print axioms d2Delta23Bound

end StandaloneDelta002
end CatalanMeasure.GenD.Signed.Data.Cells
