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
namespace d2LitsStandaloneDelta021
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta021
namespace StandaloneDelta021
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta021.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta021.q2listC (raw_ints% []))⟩
def d2Delta168Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta168Ts : List LTerm := laurentClean []
def d2Delta168Lo : ℚ := (d2LitsStandaloneDelta021.q2 (8578403339) 1 (-33))
def d2Delta168Hi : ℚ := (d2LitsStandaloneDelta021.q2 (17157854229) 1 (-34))
def d2Delta168Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta168Qd : List (ℚ × ℚ) := []
def d2Delta168Ld : List LaurentPieceData := []
def d2Delta168Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-4252819025074355801385841507405929521767, 1, -139, 272702821154496318513533808761221, 1, -136, -106136004035029394460052216985121, 1, -141, -274480167923479567424640149001, 1, -138, 4462798544422013532215761085, 1, -140, 30110768543623640282561715, 1, -138, 1532717377094372296746693, 1, -141, 341378355143628364715, 1, -137, 3269617677418337391, 1, -139, 1432252935887803, 1, -137, 30933991743311, 1, -141, 4164799973, 1, -138, 14691123, 1, -140, 2705, 1, -138, 13, 1, -141, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta168S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-1038285888314971625129969860663064901, 1, -127, 533024841636142167814016994341, 1, -127, -25920823395785554559805983917, 1, -128, -268194054890321949757371349, 1, -126, 8707422896630203444937501, 1, -128, 14700190099605941081197, 1, -123, 5986768556294458320931, 1, -128, 42670683119853845363, 1, -128, 102173135713613711, 1, -127, 179028753696983, 1, -126, 1933352447335, 1, -128, 520595601, 1, -125, 1836379, 1, -126, 2705, 1, -126, 13, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta168Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta168Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta168Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta168Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta168Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta168Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta168El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta168Shift : polyRoundApx 128 d2Delta168Lo d2Delta168Hi d2Delta168Fq.poly = (d2Delta168S,d2Delta168Es) := by decide +kernel
theorem d2Delta168Sites : mergeSites d2Delta168Fq.plogs = [] := by decide +kernel
theorem d2Delta168PData : d2Delta168Pd = [] := by decide +kernel
theorem d2Delta168Plogs : plogsRoundM 16 24 20 128 d2Delta168Lo d2Delta168Hi (mergeSites d2Delta168Fq.plogs) d2Delta168Pd = some (d2Delta168Ap,d2Delta168Ep) := by
  rw [d2Delta168Sites,d2Delta168PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta168Poles : polesRoundM 16 24 12 128 d2Delta168Lo d2Delta168Hi d2Delta168Fq.poles d2Delta168Qd = some (d2Delta168Aq,d2Delta168Eq) := by decide +kernel
theorem d2Delta168Laurent : laurentRoundM 16 30 128 d2Delta168Lo d2Delta168Hi d2Delta168Ts d2Delta168Ld = some (d2Delta168Al,d2Delta168El) := by decide +kernel
theorem d2Delta168Small : chebPolyUB (vecAdd d2Delta168S (vecAdd d2Delta168Ap (vecAdd d2Delta168Aq d2Delta168Al))) d2Delta168Gam+d2Delta168Es+d2Delta168Ep+d2Delta168Eq+d2Delta168El ≤ (d2LitsStandaloneDelta021.q2 (-7377461170379971010675) 1 (-80)) := by decide +kernel
theorem d2Delta168Check : chebRoundPieceL d2Delta168Fq d2Delta168Ts 16 24 12 20 30 128 d2Delta168Lo d2Delta168Hi d2Delta168Pd d2Delta168Qd d2Delta168Ld d2Delta168Gam (d2LitsStandaloneDelta021.q2 (-7377461170379971010675) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta168Fq d2Delta168Ts 16 24 12 20 30 128 d2Delta168Lo d2Delta168Hi d2Delta168Pd d2Delta168Qd d2Delta168Ld d2Delta168Gam d2Delta168S d2Delta168Ap d2Delta168Aq d2Delta168Al d2Delta168Es d2Delta168Ep d2Delta168Eq d2Delta168El (by decide +kernel) d2Delta168Shift d2Delta168Plogs d2Delta168Poles d2Delta168Laurent]
  exact decide_eq_true d2Delta168Small
theorem d2Delta168Bound : ∀ x ∈ Icc ((d2Delta168Lo : ℚ) : ℝ) ((d2Delta168Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-7377461170379971010675) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta168Fq d2Delta168Ts 16 24 12 20 30 128 d2Delta168Lo d2Delta168Hi d2Delta168Pd d2Delta168Qd d2Delta168Ld d2Delta168Gam (d2LitsStandaloneDelta021.q2 (-7377461170379971010675) 1 (-80)) d2Delta168Check
  simpa only [d2Delta168Fq, d2Delta168Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta168Shift
#print axioms d2Delta168Sites
#print axioms d2Delta168PData
#print axioms d2Delta168Plogs
#print axioms d2Delta168Poles
#print axioms d2Delta168Laurent
#print axioms d2Delta168Small
#print axioms d2Delta168Check
#print axioms d2Delta168Bound

def d2Delta169Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta169Ts : List LTerm := laurentClean []
def d2Delta169Lo : ℚ := (d2LitsStandaloneDelta021.q2 (17157854229) 1 (-34))
def d2Delta169Hi : ℚ := (d2LitsStandaloneDelta021.q2 (4289725445) 1 (-32))
def d2Delta169Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta169Qd : List (ℚ × ℚ) := []
def d2Delta169Ld : List LaurentPieceData := []
def d2Delta169Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-4252814894470863011457825734019468880031, 1, -139, 971851127045580656675610329593765, 1, -138, -131463639630434410630662168647777, 1, -141, -1006219241670045081561261345229, 1, -140, 7061903920300498418083220581, 1, -140, 139777339037735502961809151, 1, -140, 1691639776061023312479909, 1, -141, 1473501522751698808191, 1, -139, 3481519498133890663, 1, -139, 6045786496941831, 1, -139, 32431429775791, 1, -141, 17378037609, 1, -140, 15263755, 1, -140, 11205, 1, -140, 13, 1, -141, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta169S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-519142439160329904149845621461234027, 1, -126, 949810513860693124543477029987, 1, -128, -4013675526039478958309721243, 1, -125, -491659222220485287237563097, 1, -127, 13782869414516180643280675, 1, -128, 545924649776906687134753, 1, -128, 3303766344867538380965, 1, -127, 23022611110242848205, 1, -127, 217589901248223243, 1, -128, 755711364762393, 1, -128, 2026941465417, 1, -128, 2172236493, 1, -127, 953979, 1, -125, 11205, 1, -128, 13, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta169Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta169Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta169Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta169Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta169Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta169Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta169El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta169Shift : polyRoundApx 128 d2Delta169Lo d2Delta169Hi d2Delta169Fq.poly = (d2Delta169S,d2Delta169Es) := by decide +kernel
theorem d2Delta169Sites : mergeSites d2Delta169Fq.plogs = [] := by decide +kernel
theorem d2Delta169PData : d2Delta169Pd = [] := by decide +kernel
theorem d2Delta169Plogs : plogsRoundM 16 24 20 128 d2Delta169Lo d2Delta169Hi (mergeSites d2Delta169Fq.plogs) d2Delta169Pd = some (d2Delta169Ap,d2Delta169Ep) := by
  rw [d2Delta169Sites,d2Delta169PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta169Poles : polesRoundM 16 24 12 128 d2Delta169Lo d2Delta169Hi d2Delta169Fq.poles d2Delta169Qd = some (d2Delta169Aq,d2Delta169Eq) := by decide +kernel
theorem d2Delta169Laurent : laurentRoundM 16 30 128 d2Delta169Lo d2Delta169Hi d2Delta169Ts d2Delta169Ld = some (d2Delta169Al,d2Delta169El) := by decide +kernel
theorem d2Delta169Small : chebPolyUB (vecAdd d2Delta169S (vecAdd d2Delta169Ap (vecAdd d2Delta169Aq d2Delta169Al))) d2Delta169Gam+d2Delta169Es+d2Delta169Ep+d2Delta169Eq+d2Delta169El ≤ (d2LitsStandaloneDelta021.q2 (-7377454406744234303363) 1 (-80)) := by decide +kernel
theorem d2Delta169Check : chebRoundPieceL d2Delta169Fq d2Delta169Ts 16 24 12 20 30 128 d2Delta169Lo d2Delta169Hi d2Delta169Pd d2Delta169Qd d2Delta169Ld d2Delta169Gam (d2LitsStandaloneDelta021.q2 (-7377454406744234303363) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta169Fq d2Delta169Ts 16 24 12 20 30 128 d2Delta169Lo d2Delta169Hi d2Delta169Pd d2Delta169Qd d2Delta169Ld d2Delta169Gam d2Delta169S d2Delta169Ap d2Delta169Aq d2Delta169Al d2Delta169Es d2Delta169Ep d2Delta169Eq d2Delta169El (by decide +kernel) d2Delta169Shift d2Delta169Plogs d2Delta169Poles d2Delta169Laurent]
  exact decide_eq_true d2Delta169Small
theorem d2Delta169Bound : ∀ x ∈ Icc ((d2Delta169Lo : ℚ) : ℝ) ((d2Delta169Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-7377454406744234303363) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta169Fq d2Delta169Ts 16 24 12 20 30 128 d2Delta169Lo d2Delta169Hi d2Delta169Pd d2Delta169Qd d2Delta169Ld d2Delta169Gam (d2LitsStandaloneDelta021.q2 (-7377454406744234303363) 1 (-80)) d2Delta169Check
  simpa only [d2Delta169Fq, d2Delta169Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta169Shift
#print axioms d2Delta169Sites
#print axioms d2Delta169PData
#print axioms d2Delta169Plogs
#print axioms d2Delta169Poles
#print axioms d2Delta169Laurent
#print axioms d2Delta169Small
#print axioms d2Delta169Check
#print axioms d2Delta169Bound

def d2Delta170Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta170Ts : List LTerm := laurentClean []
def d2Delta170Lo : ℚ := (d2LitsStandaloneDelta021.q2 (4289725445) 1 (-32))
def d2Delta170Hi : ℚ := (d2LitsStandaloneDelta021.q2 (17159949331) 1 (-34))
def d2Delta170Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta170Qd : List (ℚ × ℚ) := []
def d2Delta170Ld : List LaurentPieceData := []
def d2Delta170Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-531601411045191100136423859574050222749, 1, -136, 828848008103291454279290136550841, 1, -138, -77032604392695347001932693382003, 1, -140, -869732941913503010096778905411, 1, -140, 314601972674394214814926587, 1, -135, 161092794449790803582808109, 1, -140, 931521755607261812205815, 1, -140, 1588455866681742792431, 1, -139, 463137324648838113, 1, -136, 6377856000247279, 1, -139, 16996674589301, 1, -140, 18124847395, 1, -140, 495523, 1, -135, 11603, 1, -140, 7, 1, -140, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta170S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-2076567993086031952606494034043486831, 1, -128, 202514772746621112534737123361, 1, -126, -9408308723342337857210266455, 1, -126, -212533779640959562350840831, 1, -126, 19651707311035283903843951, 1, -128, 629181860984609717132537, 1, -128, 7277050583004598403129, 1, -128, 24818726037132598509, 1, -127, 7236354715324003, 1, -123, 797219539245463, 1, -128, 1062280269313, 1, -127, 4531174139, 1, -128, 7928319, 1, -128, 11603, 1, -128, 7, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta170Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta170Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta170Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta170Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta170Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta170Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta170El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta170Shift : polyRoundApx 128 d2Delta170Lo d2Delta170Hi d2Delta170Fq.poly = (d2Delta170S,d2Delta170Es) := by decide +kernel
theorem d2Delta170Sites : mergeSites d2Delta170Fq.plogs = [] := by decide +kernel
theorem d2Delta170PData : d2Delta170Pd = [] := by decide +kernel
theorem d2Delta170Plogs : plogsRoundM 16 24 20 128 d2Delta170Lo d2Delta170Hi (mergeSites d2Delta170Fq.plogs) d2Delta170Pd = some (d2Delta170Ap,d2Delta170Ep) := by
  rw [d2Delta170Sites,d2Delta170PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta170Poles : polesRoundM 16 24 12 128 d2Delta170Lo d2Delta170Hi d2Delta170Fq.poles d2Delta170Qd = some (d2Delta170Aq,d2Delta170Eq) := by decide +kernel
theorem d2Delta170Laurent : laurentRoundM 16 30 128 d2Delta170Lo d2Delta170Hi d2Delta170Ts d2Delta170Ld = some (d2Delta170Al,d2Delta170El) := by decide +kernel
theorem d2Delta170Small : chebPolyUB (vecAdd d2Delta170S (vecAdd d2Delta170Ap (vecAdd d2Delta170Aq d2Delta170Al))) d2Delta170Gam+d2Delta170Es+d2Delta170Ep+d2Delta170Eq+d2Delta170El ≤ (d2LitsStandaloneDelta021.q2 (-3688724318798669994909) 1 (-79)) := by decide +kernel
theorem d2Delta170Check : chebRoundPieceL d2Delta170Fq d2Delta170Ts 16 24 12 20 30 128 d2Delta170Lo d2Delta170Hi d2Delta170Pd d2Delta170Qd d2Delta170Ld d2Delta170Gam (d2LitsStandaloneDelta021.q2 (-3688724318798669994909) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta170Fq d2Delta170Ts 16 24 12 20 30 128 d2Delta170Lo d2Delta170Hi d2Delta170Pd d2Delta170Qd d2Delta170Ld d2Delta170Gam d2Delta170S d2Delta170Ap d2Delta170Aq d2Delta170Al d2Delta170Es d2Delta170Ep d2Delta170Eq d2Delta170El (by decide +kernel) d2Delta170Shift d2Delta170Plogs d2Delta170Poles d2Delta170Laurent]
  exact decide_eq_true d2Delta170Small
theorem d2Delta170Bound : ∀ x ∈ Icc ((d2Delta170Lo : ℚ) : ℝ) ((d2Delta170Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-3688724318798669994909) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta170Fq d2Delta170Ts 16 24 12 20 30 128 d2Delta170Lo d2Delta170Hi d2Delta170Pd d2Delta170Qd d2Delta170Ld d2Delta170Gam (d2LitsStandaloneDelta021.q2 (-3688724318798669994909) 1 (-79)) d2Delta170Check
  simpa only [d2Delta170Fq, d2Delta170Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta170Shift
#print axioms d2Delta170Sites
#print axioms d2Delta170PData
#print axioms d2Delta170Plogs
#print axioms d2Delta170Poles
#print axioms d2Delta170Laurent
#print axioms d2Delta170Small
#print axioms d2Delta170Check
#print axioms d2Delta170Bound

def d2Delta171Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta171Ts : List LTerm := laurentClean []
def d2Delta171Lo : ℚ := (d2LitsStandaloneDelta021.q2 (17159949331) 1 (-34))
def d2Delta171Hi : ℚ := (d2LitsStandaloneDelta021.q2 (1072693249) 1 (-30))
def d2Delta171Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta171Qd : List (ℚ × ℚ) := []
def d2Delta171Ld : List LaurentPieceData := []
def d2Delta171Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-68044901825616755591142113099960988585241, 1, -143, 46324790805743827992822387263001981, 1, -143, -416646472820907994593523057621779, 1, -139, -46008405603158011807135369716819, 1, -142, 1418996789825660426334708800063, 1, -140, 204607488957155391120413799679, 1, -142, 409628274885234865683425083, 1, -139, 16107890510521623698196345, 1, -141, 109970460707962875467059, 1, -141, 34895011103483277673, 1, -137, 550986591447506457, 1, -139, 13964624255721677, 1, -142, 9091497909369, 1, -140, 79320912295, 1, -142, 18391487, 1, -139, 940093, 1, -144, 653, 1, -143, 1, 1, -144, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta171S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-2076565403684319145218934717762612923, 1, -128, 711103620349907112764692308785, 1, -127, -204824599700172566730035497945, 1, -127, -11482175796022445500366684865, 1, -128, 2761879590188568326231606977, 1, -128, 199591805310764082194157803, 1, -128, 799625689937188519764379, 1, -125, 3931363753940007019973, 1, -123, 858972048641963286557, 1, -127, 17445105462506978361, 1, -128, 68866505484522547, 1, -127, 218181142265841, 1, -126, 4545491478111, 1, -128, 2478668343, 1, -125, 9195417, 1, -125, 235019, 1, -128, 653, 1, -128, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta171Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta171Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta171Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta171Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta171Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta171Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta171El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta171Shift : polyRoundApx 128 d2Delta171Lo d2Delta171Hi d2Delta171Fq.poly = (d2Delta171S,d2Delta171Es) := by decide +kernel
theorem d2Delta171Sites : mergeSites d2Delta171Fq.plogs = [] := by decide +kernel
theorem d2Delta171PData : d2Delta171Pd = [] := by decide +kernel
theorem d2Delta171Plogs : plogsRoundM 16 24 20 128 d2Delta171Lo d2Delta171Hi (mergeSites d2Delta171Fq.plogs) d2Delta171Pd = some (d2Delta171Ap,d2Delta171Ep) := by
  rw [d2Delta171Sites,d2Delta171PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta171Poles : polesRoundM 16 24 12 128 d2Delta171Lo d2Delta171Hi d2Delta171Fq.poles d2Delta171Qd = some (d2Delta171Aq,d2Delta171Eq) := by decide +kernel
theorem d2Delta171Laurent : laurentRoundM 16 30 128 d2Delta171Lo d2Delta171Hi d2Delta171Ts d2Delta171Ld = some (d2Delta171Al,d2Delta171El) := by decide +kernel
theorem d2Delta171Small : chebPolyUB (vecAdd d2Delta171S (vecAdd d2Delta171Ap (vecAdd d2Delta171Aq d2Delta171Al))) d2Delta171Gam+d2Delta171Es+d2Delta171Ep+d2Delta171Eq+d2Delta171El ≤ (d2LitsStandaloneDelta021.q2 (-7377437282027003596643) 1 (-80)) := by decide +kernel
theorem d2Delta171Check : chebRoundPieceL d2Delta171Fq d2Delta171Ts 16 24 12 20 30 128 d2Delta171Lo d2Delta171Hi d2Delta171Pd d2Delta171Qd d2Delta171Ld d2Delta171Gam (d2LitsStandaloneDelta021.q2 (-7377437282027003596643) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta171Fq d2Delta171Ts 16 24 12 20 30 128 d2Delta171Lo d2Delta171Hi d2Delta171Pd d2Delta171Qd d2Delta171Ld d2Delta171Gam d2Delta171S d2Delta171Ap d2Delta171Aq d2Delta171Al d2Delta171Es d2Delta171Ep d2Delta171Eq d2Delta171El (by decide +kernel) d2Delta171Shift d2Delta171Plogs d2Delta171Poles d2Delta171Laurent]
  exact decide_eq_true d2Delta171Small
theorem d2Delta171Bound : ∀ x ∈ Icc ((d2Delta171Lo : ℚ) : ℝ) ((d2Delta171Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-7377437282027003596643) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta171Fq d2Delta171Ts 16 24 12 20 30 128 d2Delta171Lo d2Delta171Hi d2Delta171Pd d2Delta171Qd d2Delta171Ld d2Delta171Gam (d2LitsStandaloneDelta021.q2 (-7377437282027003596643) 1 (-80)) d2Delta171Check
  simpa only [d2Delta171Fq, d2Delta171Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta171Shift
#print axioms d2Delta171Sites
#print axioms d2Delta171PData
#print axioms d2Delta171Plogs
#print axioms d2Delta171Poles
#print axioms d2Delta171Laurent
#print axioms d2Delta171Small
#print axioms d2Delta171Check
#print axioms d2Delta171Bound

def d2Delta172Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta172Ts : List LTerm := laurentClean []
def d2Delta172Lo : ℚ := (d2LitsStandaloneDelta021.q2 (1072693249) 1 (-30))
def d2Delta172Hi : ℚ := (d2LitsStandaloneDelta021.q2 (2146434049) 1 (-31))
def d2Delta172Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta172Qd : List (ℚ × ℚ) := []
def d2Delta172Ld : List LaurentPieceData := []
def d2Delta172Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-68044919851702328282180275510197874978901, 1, -143, -329977318322781219244897752589761065, 1, -145, -32276859865988324155154726298283715, 1, -144, 41277414299396454333321345532049145, 1, -145, 3339728685140168688943615767498497, 1, -144, 211721318352347977986875720158563, 1, -144, 3823772148397230143447293879307, 1, -143, 182522034150480303240989751357, 1, -144, 390749117496342491324830265, 1, -141, 40523690806509443181197521, 1, -144, 206428221063555839387007, 1, -143, 3399619200840097304495, 1, -144, 46247631853215830909, 1, -145, 528839030313427231, 1, -146, 1289108786572019, 1, -145, 10846951936177, 1, -146, 4972964625, 1, -143, 128325737, 1, -146, 183403, 1, -145, 935, 1, -146, 1, 1, -145, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta172S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-2076565614234321962777031180187182489, 1, -128, -3446158619816387656075397985317, 1, -128, -1390594382124154958276338648479, 1, -128, 1195230386406911427674943547383, 1, -128, 25130507801649529342714315833, 1, -124, 51378114743945257398762793117, 1, -128, 930487158283751333604316151, 1, -126, 88944077390548365859626341, 1, -127, 3048696898535331047068525, 1, -127, 39537405847840573001889, 1, -126, 402909185510917790755, 1, -125, 13273049679819600157, 1, -126, 361168643741070085, 1, -127, 8260567832883211, 1, -128, 314646128319, 1, -120, 338899079399, 1, -127, 2486069677, 1, -127, 32076993, 1, -128, 183383, 1, -128, 935, 1, -128, 1, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta172Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta172Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta172Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta172Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta172Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta172Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta172El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta172Shift : polyRoundApx 128 d2Delta172Lo d2Delta172Hi d2Delta172Fq.poly = (d2Delta172S,d2Delta172Es) := by decide +kernel
theorem d2Delta172Sites : mergeSites d2Delta172Fq.plogs = [] := by decide +kernel
theorem d2Delta172PData : d2Delta172Pd = [] := by decide +kernel
theorem d2Delta172Plogs : plogsRoundM 16 24 20 128 d2Delta172Lo d2Delta172Hi (mergeSites d2Delta172Fq.plogs) d2Delta172Pd = some (d2Delta172Ap,d2Delta172Ep) := by
  rw [d2Delta172Sites,d2Delta172PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta172Poles : polesRoundM 16 24 12 128 d2Delta172Lo d2Delta172Hi d2Delta172Fq.poles d2Delta172Qd = some (d2Delta172Aq,d2Delta172Eq) := by decide +kernel
theorem d2Delta172Laurent : laurentRoundM 16 30 128 d2Delta172Lo d2Delta172Hi d2Delta172Ts d2Delta172Ld = some (d2Delta172Al,d2Delta172El) := by decide +kernel
theorem d2Delta172Small : chebPolyUB (vecAdd d2Delta172S (vecAdd d2Delta172Ap (vecAdd d2Delta172Aq d2Delta172Al))) d2Delta172Gam+d2Delta172Es+d2Delta172Ep+d2Delta172Eq+d2Delta172El ≤ (d2LitsStandaloneDelta021.q2 (-3688716493710433807477) 1 (-79)) := by decide +kernel
theorem d2Delta172Check : chebRoundPieceL d2Delta172Fq d2Delta172Ts 16 24 12 20 30 128 d2Delta172Lo d2Delta172Hi d2Delta172Pd d2Delta172Qd d2Delta172Ld d2Delta172Gam (d2LitsStandaloneDelta021.q2 (-3688716493710433807477) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta172Fq d2Delta172Ts 16 24 12 20 30 128 d2Delta172Lo d2Delta172Hi d2Delta172Pd d2Delta172Qd d2Delta172Ld d2Delta172Gam d2Delta172S d2Delta172Ap d2Delta172Aq d2Delta172Al d2Delta172Es d2Delta172Ep d2Delta172Eq d2Delta172El (by decide +kernel) d2Delta172Shift d2Delta172Plogs d2Delta172Poles d2Delta172Laurent]
  exact decide_eq_true d2Delta172Small
theorem d2Delta172Bound : ∀ x ∈ Icc ((d2Delta172Lo : ℚ) : ℝ) ((d2Delta172Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-3688716493710433807477) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta172Fq d2Delta172Ts 16 24 12 20 30 128 d2Delta172Lo d2Delta172Hi d2Delta172Pd d2Delta172Qd d2Delta172Ld d2Delta172Gam (d2LitsStandaloneDelta021.q2 (-3688716493710433807477) 1 (-79)) d2Delta172Check
  simpa only [d2Delta172Fq, d2Delta172Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta172Shift
#print axioms d2Delta172Sites
#print axioms d2Delta172PData
#print axioms d2Delta172Plogs
#print axioms d2Delta172Poles
#print axioms d2Delta172Laurent
#print axioms d2Delta172Small
#print axioms d2Delta172Check
#print axioms d2Delta172Bound

def d2Delta173Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta173Ts : List LTerm := laurentClean []
def d2Delta173Lo : ℚ := (d2LitsStandaloneDelta021.q2 (2146434049) 1 (-31))
def d2Delta173Hi : ℚ := (d2LitsStandaloneDelta021.q2 (34343992335) 1 (-35))
def d2Delta173Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta173Qd : List (ℚ × ℚ) := []
def d2Delta173Ld : List LaurentPieceData := []
def d2Delta173Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-1063203232231667712098924576697937722413, 1, -137, -432902143180355371845454378717, 1, -135, 1459590139910429853269480612353, 1, -135, 447776085451373256862397044923, 1, -139, 1457287119482137684048211603, 1, -138, 9736382788833967676572709, 1, -139, 2505597398439473243365, 1, -136, 7052185862056929007, 1, -137, 7249843752926197, 1, -137, 5701220074389, 1, -137, 1773768217, 1, -136, 7169759, 1, -139, 1501, 1, -138, 1, 1, -139, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta173S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-1038284412177050423039150847629469885, 1, -127, -2018973111700029919230915169, 1, -127, 22794711056653876219566351451, 1, -128, 437233792902686339016784781, 1, -127, 11384585823707566656671351, 1, -128, 76063947876918447644713, 1, -128, 156598024945408961509, 1, -127, 220379204723597713, 1, -126, 453113017350149, 1, -126, 89081255587, 1, -123, 886881857, 1, -126, 3584873, 1, -128, 1501, 1, -127, 1, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta173Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta173Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta173Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta173Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta173Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta173Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta173El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta173Shift : polyRoundApx 128 d2Delta173Lo d2Delta173Hi d2Delta173Fq.poly = (d2Delta173S,d2Delta173Es) := by decide +kernel
theorem d2Delta173Sites : mergeSites d2Delta173Fq.plogs = [] := by decide +kernel
theorem d2Delta173PData : d2Delta173Pd = [] := by decide +kernel
theorem d2Delta173Plogs : plogsRoundM 16 24 20 128 d2Delta173Lo d2Delta173Hi (mergeSites d2Delta173Fq.plogs) d2Delta173Pd = some (d2Delta173Ap,d2Delta173Ep) := by
  rw [d2Delta173Sites,d2Delta173PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta173Poles : polesRoundM 16 24 12 128 d2Delta173Lo d2Delta173Hi d2Delta173Fq.poles d2Delta173Qd = some (d2Delta173Aq,d2Delta173Eq) := by decide +kernel
theorem d2Delta173Laurent : laurentRoundM 16 30 128 d2Delta173Lo d2Delta173Hi d2Delta173Ts d2Delta173Ld = some (d2Delta173Al,d2Delta173El) := by decide +kernel
theorem d2Delta173Small : chebPolyUB (vecAdd d2Delta173S (vecAdd d2Delta173Ap (vecAdd d2Delta173Aq d2Delta173Al))) d2Delta173Gam+d2Delta173Es+d2Delta173Ep+d2Delta173Eq+d2Delta173El ≤ (d2LitsStandaloneDelta021.q2 (-3688727186718863528325) 1 (-79)) := by decide +kernel
theorem d2Delta173Check : chebRoundPieceL d2Delta173Fq d2Delta173Ts 16 24 12 20 30 128 d2Delta173Lo d2Delta173Hi d2Delta173Pd d2Delta173Qd d2Delta173Ld d2Delta173Gam (d2LitsStandaloneDelta021.q2 (-3688727186718863528325) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta173Fq d2Delta173Ts 16 24 12 20 30 128 d2Delta173Lo d2Delta173Hi d2Delta173Pd d2Delta173Qd d2Delta173Ld d2Delta173Gam d2Delta173S d2Delta173Ap d2Delta173Aq d2Delta173Al d2Delta173Es d2Delta173Ep d2Delta173Eq d2Delta173El (by decide +kernel) d2Delta173Shift d2Delta173Plogs d2Delta173Poles d2Delta173Laurent]
  exact decide_eq_true d2Delta173Small
theorem d2Delta173Bound : ∀ x ∈ Icc ((d2Delta173Lo : ℚ) : ℝ) ((d2Delta173Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-3688727186718863528325) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta173Fq d2Delta173Ts 16 24 12 20 30 128 d2Delta173Lo d2Delta173Hi d2Delta173Pd d2Delta173Qd d2Delta173Ld d2Delta173Gam (d2LitsStandaloneDelta021.q2 (-3688727186718863528325) 1 (-79)) d2Delta173Check
  simpa only [d2Delta173Fq, d2Delta173Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta173Shift
#print axioms d2Delta173Sites
#print axioms d2Delta173PData
#print axioms d2Delta173Plogs
#print axioms d2Delta173Poles
#print axioms d2Delta173Laurent
#print axioms d2Delta173Small
#print axioms d2Delta173Check
#print axioms d2Delta173Bound

def d2Delta174Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta174Ts : List LTerm := laurentClean []
def d2Delta174Lo : ℚ := (d2LitsStandaloneDelta021.q2 (34343992335) 1 (-35))
def d2Delta174Hi : ℚ := (d2LitsStandaloneDelta021.q2 (17172519943) 1 (-34))
def d2Delta174Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta174Qd : List (ℚ × ℚ) := []
def d2Delta174Ld : List LaurentPieceData := []
def d2Delta174Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-2126406369183524194358910945463360388385, 1, -138, 25275261296809512924493501502013, 1, -136, 3626633226380061735318267278755, 1, -136, 495993503356650038907212685827, 1, -139, 3114177164349778287730464703, 1, -139, 10227041251386451147527545, 1, -139, 5211934982173915910303, 1, -137, 3643746153397996237, 1, -136, 14915322011582793, 1, -138, 1461177383187, 1, -135, 3627201307, 1, -137, 7315203, 1, -139, 3057, 1, -139, 1, 1, -139, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta174S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-1038284367035400401230877952453925249, 1, -127, 12250620178186545449054033601, 1, -125, 28320907509777614099330604017, 1, -128, 968637438590804637631462955, 1, -128, 12164265931667258862390581, 1, -128, 79897165642446007234411, 1, -128, 325742207563301346205, 1, -128, 910929963061333117, 1, -128, 1864406183454899, 1, -128, 1461172353989, 1, -127, 453399017, 1, -125, 3657595, 1, -128, 3057, 1, -128, 1, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta174Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta174Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta174Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta174Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta174Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta174Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta174El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta174Shift : polyRoundApx 128 d2Delta174Lo d2Delta174Hi d2Delta174Fq.poly = (d2Delta174S,d2Delta174Es) := by decide +kernel
theorem d2Delta174Sites : mergeSites d2Delta174Fq.plogs = [] := by decide +kernel
theorem d2Delta174PData : d2Delta174Pd = [] := by decide +kernel
theorem d2Delta174Plogs : plogsRoundM 16 24 20 128 d2Delta174Lo d2Delta174Hi (mergeSites d2Delta174Fq.plogs) d2Delta174Pd = some (d2Delta174Ap,d2Delta174Ep) := by
  rw [d2Delta174Sites,d2Delta174PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta174Poles : polesRoundM 16 24 12 128 d2Delta174Lo d2Delta174Hi d2Delta174Fq.poles d2Delta174Qd = some (d2Delta174Aq,d2Delta174Eq) := by decide +kernel
theorem d2Delta174Laurent : laurentRoundM 16 30 128 d2Delta174Lo d2Delta174Hi d2Delta174Ts d2Delta174Ld = some (d2Delta174Al,d2Delta174El) := by decide +kernel
theorem d2Delta174Small : chebPolyUB (vecAdd d2Delta174S (vecAdd d2Delta174Ap (vecAdd d2Delta174Aq d2Delta174Al))) d2Delta174Gam+d2Delta174Es+d2Delta174Ep+d2Delta174Eq+d2Delta174El ≤ (d2LitsStandaloneDelta021.q2 (-922181711777292329501) 1 (-77)) := by decide +kernel
theorem d2Delta174Check : chebRoundPieceL d2Delta174Fq d2Delta174Ts 16 24 12 20 30 128 d2Delta174Lo d2Delta174Hi d2Delta174Pd d2Delta174Qd d2Delta174Ld d2Delta174Gam (d2LitsStandaloneDelta021.q2 (-922181711777292329501) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta174Fq d2Delta174Ts 16 24 12 20 30 128 d2Delta174Lo d2Delta174Hi d2Delta174Pd d2Delta174Qd d2Delta174Ld d2Delta174Gam d2Delta174S d2Delta174Ap d2Delta174Aq d2Delta174Al d2Delta174Es d2Delta174Ep d2Delta174Eq d2Delta174El (by decide +kernel) d2Delta174Shift d2Delta174Plogs d2Delta174Poles d2Delta174Laurent]
  exact decide_eq_true d2Delta174Small
theorem d2Delta174Bound : ∀ x ∈ Icc ((d2Delta174Lo : ℚ) : ℝ) ((d2Delta174Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-922181711777292329501) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta174Fq d2Delta174Ts 16 24 12 20 30 128 d2Delta174Lo d2Delta174Hi d2Delta174Pd d2Delta174Qd d2Delta174Ld d2Delta174Gam (d2LitsStandaloneDelta021.q2 (-922181711777292329501) 1 (-77)) d2Delta174Check
  simpa only [d2Delta174Fq, d2Delta174Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta174Shift
#print axioms d2Delta174Sites
#print axioms d2Delta174PData
#print axioms d2Delta174Plogs
#print axioms d2Delta174Poles
#print axioms d2Delta174Laurent
#print axioms d2Delta174Small
#print axioms d2Delta174Check
#print axioms d2Delta174Bound

def d2Delta175Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta175Ts : List LTerm := laurentClean []
def d2Delta175Lo : ℚ := (d2LitsStandaloneDelta021.q2 (17172519943) 1 (-34))
def d2Delta175Hi : ℚ := (d2LitsStandaloneDelta021.q2 (68691127323) 1 (-36))
def d2Delta175Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta175Qd : List (ℚ × ℚ) := []
def d2Delta175Ld : List LaurentPieceData := []
def d2Delta175Gam : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-531601540071381655356200127180116271781, 1, -136, 12151544981906055310885586255715, 1, -135, 1051197076915307352750871905801, 1, -136, 4173875071439087841011819431, 1, -135, 6387361262639047832898111, 1, -134, 41436324809852991708093, 1, -136, 83856553558241557845, 1, -137, 29173209281433437, 1, -136, 14876792497833, 1, -136, 5814863373, 1, -136, 3601561, 1, -137, 453, 1, -136, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta175S : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [-1038284260004986685289814815707005209, 1, -127, 94836120783456624732724311979, 1, -128, 4105839373095544456910146877, 1, -127, 65215179387988681035619455, 1, -127, 399206148143641443231821, 1, -127, 2589757537346563934389, 1, -128, 5241019720605477947, 1, -128, 7293289236920753, 1, -128, 3719193622507, 1, -127, 2907429195, 1, -127, 3601561, 1, -128, 453, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta175Ap : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta175Aq : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta175Al : List ℚ := d2LitsStandaloneDelta021.q2listC (raw_ints% [])
def d2Delta175Es : ℚ := (d2LitsStandaloneDelta021.q2 (61) 1 (-127))
def d2Delta175Ep : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta175Eq : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
def d2Delta175El : ℚ := (d2LitsStandaloneDelta021.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta175Shift : polyRoundApx 128 d2Delta175Lo d2Delta175Hi d2Delta175Fq.poly = (d2Delta175S,d2Delta175Es) := by decide +kernel
theorem d2Delta175Sites : mergeSites d2Delta175Fq.plogs = [] := by decide +kernel
theorem d2Delta175PData : d2Delta175Pd = [] := by decide +kernel
theorem d2Delta175Plogs : plogsRoundM 16 24 20 128 d2Delta175Lo d2Delta175Hi (mergeSites d2Delta175Fq.plogs) d2Delta175Pd = some (d2Delta175Ap,d2Delta175Ep) := by
  rw [d2Delta175Sites,d2Delta175PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta175Poles : polesRoundM 16 24 12 128 d2Delta175Lo d2Delta175Hi d2Delta175Fq.poles d2Delta175Qd = some (d2Delta175Aq,d2Delta175Eq) := by decide +kernel
theorem d2Delta175Laurent : laurentRoundM 16 30 128 d2Delta175Lo d2Delta175Hi d2Delta175Ts d2Delta175Ld = some (d2Delta175Al,d2Delta175El) := by decide +kernel
theorem d2Delta175Small : chebPolyUB (vecAdd d2Delta175S (vecAdd d2Delta175Ap (vecAdd d2Delta175Aq d2Delta175Al))) d2Delta175Gam+d2Delta175Es+d2Delta175Ep+d2Delta175Eq+d2Delta175El ≤ (d2LitsStandaloneDelta021.q2 (-7377453019440389691587) 1 (-80)) := by decide +kernel
theorem d2Delta175Check : chebRoundPieceL d2Delta175Fq d2Delta175Ts 16 24 12 20 30 128 d2Delta175Lo d2Delta175Hi d2Delta175Pd d2Delta175Qd d2Delta175Ld d2Delta175Gam (d2LitsStandaloneDelta021.q2 (-7377453019440389691587) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta175Fq d2Delta175Ts 16 24 12 20 30 128 d2Delta175Lo d2Delta175Hi d2Delta175Pd d2Delta175Qd d2Delta175Ld d2Delta175Gam d2Delta175S d2Delta175Ap d2Delta175Aq d2Delta175Al d2Delta175Es d2Delta175Ep d2Delta175Eq d2Delta175El (by decide +kernel) d2Delta175Shift d2Delta175Plogs d2Delta175Poles d2Delta175Laurent]
  exact decide_eq_true d2Delta175Small
theorem d2Delta175Bound : ∀ x ∈ Icc ((d2Delta175Lo : ℚ) : ℝ) ((d2Delta175Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta021.q2 (-7377453019440389691587) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta175Fq d2Delta175Ts 16 24 12 20 30 128 d2Delta175Lo d2Delta175Hi d2Delta175Pd d2Delta175Qd d2Delta175Ld d2Delta175Gam (d2LitsStandaloneDelta021.q2 (-7377453019440389691587) 1 (-80)) d2Delta175Check
  simpa only [d2Delta175Fq, d2Delta175Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta175Shift
#print axioms d2Delta175Sites
#print axioms d2Delta175PData
#print axioms d2Delta175Plogs
#print axioms d2Delta175Poles
#print axioms d2Delta175Laurent
#print axioms d2Delta175Small
#print axioms d2Delta175Check
#print axioms d2Delta175Bound

end StandaloneDelta021
end CatalanMeasure.GenD.Signed.Data.Cells
