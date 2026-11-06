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
namespace d2LitsStandaloneDelta022
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta022
namespace StandaloneDelta022
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta022.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta022.q2listC (raw_ints% []))⟩
def d2Delta176Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta176Ts : List LTerm := laurentClean []
def d2Delta176Lo : ℚ := (d2LitsStandaloneDelta022.q2 (68691127323) 1 (-36))
def d2Delta176Hi : ℚ := (d2LitsStandaloneDelta022.q2 (34346087437) 1 (-35))
def d2Delta176Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta176Qd : List (ℚ × ℚ) := []
def d2Delta176Ld : List LaurentPieceData := []
def d2Delta176Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-531601482733463369760757951394123883843, 1, -136, 66240742749718654006889737975609, 1, -137, 1153850351195303233772939472119, 1, -136, 17526452057657660373409233755, 1, -137, 6597075194214751189995981, 1, -134, 169809838557102948369907, 1, -138, 85503646022843785187, 1, -137, 118610519775169489, 1, -138, 15087428960655, 1, -136, 23549179373, 1, -138, 3641647, 1, -137, 1831, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta176S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-1038284148217358071675851824387301025, 1, -127, 129273757457167699769167264459, 1, -128, 9013631237320015339514677499, 1, -128, 68461045054263831645417403, 1, -127, 824626383319458897400009, 1, -128, 1326632877219533983481, 1, -127, 2671981394503371011, 1, -127, 7413144239539731, 1, -128, 3771852688105, 1, -127, 367955613, 1, -124, 3641647, 1, -128, 1831, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta176Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta176Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta176Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta176Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta176Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta176Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta176El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta176Shift : polyRoundApx 128 d2Delta176Lo d2Delta176Hi d2Delta176Fq.poly = (d2Delta176S,d2Delta176Es) := by decide +kernel
theorem d2Delta176Sites : mergeSites d2Delta176Fq.plogs = [] := by decide +kernel
theorem d2Delta176PData : d2Delta176Pd = [] := by decide +kernel
theorem d2Delta176Plogs : plogsRoundM 16 24 20 128 d2Delta176Lo d2Delta176Hi (mergeSites d2Delta176Fq.plogs) d2Delta176Pd = some (d2Delta176Ap,d2Delta176Ep) := by
  rw [d2Delta176Sites,d2Delta176PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta176Poles : polesRoundM 16 24 12 128 d2Delta176Lo d2Delta176Hi d2Delta176Fq.poles d2Delta176Qd = some (d2Delta176Aq,d2Delta176Eq) := by decide +kernel
theorem d2Delta176Laurent : laurentRoundM 16 30 128 d2Delta176Lo d2Delta176Hi d2Delta176Ts d2Delta176Ld = some (d2Delta176Al,d2Delta176El) := by decide +kernel
theorem d2Delta176Small : chebPolyUB (vecAdd d2Delta176S (vecAdd d2Delta176Ap (vecAdd d2Delta176Aq d2Delta176Al))) d2Delta176Gam+d2Delta176Es+d2Delta176Ep+d2Delta176Eq+d2Delta176El ≤ (d2LitsStandaloneDelta022.q2 (-7377452099922188017995) 1 (-80)) := by decide +kernel
theorem d2Delta176Check : chebRoundPieceL d2Delta176Fq d2Delta176Ts 16 24 12 20 30 128 d2Delta176Lo d2Delta176Hi d2Delta176Pd d2Delta176Qd d2Delta176Ld d2Delta176Gam (d2LitsStandaloneDelta022.q2 (-7377452099922188017995) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta176Fq d2Delta176Ts 16 24 12 20 30 128 d2Delta176Lo d2Delta176Hi d2Delta176Pd d2Delta176Qd d2Delta176Ld d2Delta176Gam d2Delta176S d2Delta176Ap d2Delta176Aq d2Delta176Al d2Delta176Es d2Delta176Ep d2Delta176Eq d2Delta176El (by decide +kernel) d2Delta176Shift d2Delta176Plogs d2Delta176Poles d2Delta176Laurent]
  exact decide_eq_true d2Delta176Small
theorem d2Delta176Bound : ∀ x ∈ Icc ((d2Delta176Lo : ℚ) : ℝ) ((d2Delta176Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-7377452099922188017995) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta176Fq d2Delta176Ts 16 24 12 20 30 128 d2Delta176Lo d2Delta176Hi d2Delta176Pd d2Delta176Qd d2Delta176Ld d2Delta176Gam (d2LitsStandaloneDelta022.q2 (-7377452099922188017995) 1 (-80)) d2Delta176Check
  simpa only [d2Delta176Fq, d2Delta176Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta176Shift
#print axioms d2Delta176Sites
#print axioms d2Delta176PData
#print axioms d2Delta176Plogs
#print axioms d2Delta176Poles
#print axioms d2Delta176Laurent
#print axioms d2Delta176Small
#print axioms d2Delta176Check
#print axioms d2Delta176Bound

def d2Delta177Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta177Ts : List LTerm := laurentClean []
def d2Delta177Lo : ℚ := (d2LitsStandaloneDelta022.q2 (34346087437) 1 (-35))
def d2Delta177Hi : ℚ := (d2LitsStandaloneDelta022.q2 (8586783747) 1 (-33))
def d2Delta177Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta177Qd : List (ℚ × ℚ) := []
def d2Delta177Ld : List LaurentPieceData := []
def d2Delta177Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-2126405430414198994896903440865275003695, 1, -138, 96042899864025600428511907616403, 1, -136, 2635428731797479460534042359497, 1, -135, 602411261923910537830968118355, 1, -139, 3543805388892925723361503693, 1, -139, 11267779822787325879783729, 1, -139, 2816826818377914763893, 1, -136, 1944618617767859703, 1, -135, 15778165314740759, 1, -138, 3070704999407, 1, -136, 1895702393, 1, -136, 7614203, 1, -139, 3171, 1, -139, 1, 1, -139, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta177S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-2076567823726422810399984528935410401, 1, -128, 93571291682753221275284720631, 1, -126, 41164731142592896179638831443, 1, -128, 1176474459883575067603102923, 1, -128, 13842461647799880616257199, 1, -128, 22006957082354311666163, 1, -126, 352099407764204352717, 1, -128, 486151199904075355, 1, -127, 493065296460333, 1, -126, 1535347264943, 1, -127, 3791395273, 1, -128, 3807095, 1, -128, 3171, 1, -128, 1, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta177Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta177Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta177Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta177Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta177Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta177Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta177El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta177Shift : polyRoundApx 128 d2Delta177Lo d2Delta177Hi d2Delta177Fq.poly = (d2Delta177S,d2Delta177Es) := by decide +kernel
theorem d2Delta177Sites : mergeSites d2Delta177Fq.plogs = [] := by decide +kernel
theorem d2Delta177PData : d2Delta177Pd = [] := by decide +kernel
theorem d2Delta177Plogs : plogsRoundM 16 24 20 128 d2Delta177Lo d2Delta177Hi (mergeSites d2Delta177Fq.plogs) d2Delta177Pd = some (d2Delta177Ap,d2Delta177Ep) := by
  rw [d2Delta177Sites,d2Delta177PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta177Poles : polesRoundM 16 24 12 128 d2Delta177Lo d2Delta177Hi d2Delta177Fq.poles d2Delta177Qd = some (d2Delta177Aq,d2Delta177Eq) := by decide +kernel
theorem d2Delta177Laurent : laurentRoundM 16 30 128 d2Delta177Lo d2Delta177Hi d2Delta177Ts d2Delta177Ld = some (d2Delta177Al,d2Delta177El) := by decide +kernel
theorem d2Delta177Small : chebPolyUB (vecAdd d2Delta177S (vecAdd d2Delta177Ap (vecAdd d2Delta177Aq d2Delta177Al))) d2Delta177Gam+d2Delta177Es+d2Delta177Ep+d2Delta177Eq+d2Delta177El ≤ (d2LitsStandaloneDelta022.q2 (-1844362358026536372045) 1 (-78)) := by decide +kernel
theorem d2Delta177Check : chebRoundPieceL d2Delta177Fq d2Delta177Ts 16 24 12 20 30 128 d2Delta177Lo d2Delta177Hi d2Delta177Pd d2Delta177Qd d2Delta177Ld d2Delta177Gam (d2LitsStandaloneDelta022.q2 (-1844362358026536372045) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta177Fq d2Delta177Ts 16 24 12 20 30 128 d2Delta177Lo d2Delta177Hi d2Delta177Pd d2Delta177Qd d2Delta177Ld d2Delta177Gam d2Delta177S d2Delta177Ap d2Delta177Aq d2Delta177Al d2Delta177Es d2Delta177Ep d2Delta177Eq d2Delta177El (by decide +kernel) d2Delta177Shift d2Delta177Plogs d2Delta177Poles d2Delta177Laurent]
  exact decide_eq_true d2Delta177Small
theorem d2Delta177Bound : ∀ x ∈ Icc ((d2Delta177Lo : ℚ) : ℝ) ((d2Delta177Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-1844362358026536372045) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta177Fq d2Delta177Ts 16 24 12 20 30 128 d2Delta177Lo d2Delta177Hi d2Delta177Pd d2Delta177Qd d2Delta177Ld d2Delta177Gam (d2LitsStandaloneDelta022.q2 (-1844362358026536372045) 1 (-78)) d2Delta177Check
  simpa only [d2Delta177Fq, d2Delta177Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta177Shift
#print axioms d2Delta177Sites
#print axioms d2Delta177PData
#print axioms d2Delta177Plogs
#print axioms d2Delta177Poles
#print axioms d2Delta177Laurent
#print axioms d2Delta177Small
#print axioms d2Delta177Check
#print axioms d2Delta177Bound

def d2Delta178Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta178Ts : List LTerm := laurentClean []
def d2Delta178Lo : ℚ := (d2LitsStandaloneDelta022.q2 (8586783747) 1 (-33))
def d2Delta178Hi : ℚ := (d2LitsStandaloneDelta022.q2 (17174615045) 1 (-34))
def d2Delta178Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta178Qd : List (ℚ × ℚ) := []
def d2Delta178Ld : List LaurentPieceData := []
def d2Delta178Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-2126403780956137852039666779278352446427, 1, -138, 1348859009665044778669308416158979, 1, -138, 430780788678173682427297217596249, 1, -140, 11068802701786706882822909061573, 1, -140, 62314826892295663051336395397, 1, -139, 774631760503136941924910985, 1, -140, 3055929353765467477094731, 1, -140, 4180675121431452341945, 1, -139, 4212248025591475987, 1, -138, 13051424861668401, 1, -139, 32104202019665, 1, -140, 32136326063, 1, -140, 13352715, 1, -139, 18723, 1, -140, 11, 1, -140, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta178S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-1038283148740321470759309451144682751, 1, -127, 327284759744573504207686049799, 1, -126, 210098778108461873994658229941, 1, -128, 5402797685567534919174680765, 1, -127, 121690740767038056775225963, 1, -127, 3025676686547700662611399, 1, -128, 5968348755766196542083, 1, -126, 130642426853584219979, 1, -128, 263260485340434347, 1, -127, 407851503515111, 1, -126, 4012985194419, 1, -128, 4017010333, 1, -127, 6676319, 1, -127, 18723, 1, -128, 11, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta178Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta178Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta178Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta178Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta178Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta178Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta178El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta178Shift : polyRoundApx 128 d2Delta178Lo d2Delta178Hi d2Delta178Fq.poly = (d2Delta178S,d2Delta178Es) := by decide +kernel
theorem d2Delta178Sites : mergeSites d2Delta178Fq.plogs = [] := by decide +kernel
theorem d2Delta178PData : d2Delta178Pd = [] := by decide +kernel
theorem d2Delta178Plogs : plogsRoundM 16 24 20 128 d2Delta178Lo d2Delta178Hi (mergeSites d2Delta178Fq.plogs) d2Delta178Pd = some (d2Delta178Ap,d2Delta178Ep) := by
  rw [d2Delta178Sites,d2Delta178PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta178Poles : polesRoundM 16 24 12 128 d2Delta178Lo d2Delta178Hi d2Delta178Fq.poles d2Delta178Qd = some (d2Delta178Aq,d2Delta178Eq) := by decide +kernel
theorem d2Delta178Laurent : laurentRoundM 16 30 128 d2Delta178Lo d2Delta178Hi d2Delta178Ts d2Delta178Ld = some (d2Delta178Al,d2Delta178El) := by decide +kernel
theorem d2Delta178Small : chebPolyUB (vecAdd d2Delta178S (vecAdd d2Delta178Ap (vecAdd d2Delta178Aq d2Delta178Al))) d2Delta178Gam+d2Delta178Es+d2Delta178Ep+d2Delta178Eq+d2Delta178El ≤ (d2LitsStandaloneDelta022.q2 (-7377440053313930408909) 1 (-80)) := by decide +kernel
theorem d2Delta178Check : chebRoundPieceL d2Delta178Fq d2Delta178Ts 16 24 12 20 30 128 d2Delta178Lo d2Delta178Hi d2Delta178Pd d2Delta178Qd d2Delta178Ld d2Delta178Gam (d2LitsStandaloneDelta022.q2 (-7377440053313930408909) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta178Fq d2Delta178Ts 16 24 12 20 30 128 d2Delta178Lo d2Delta178Hi d2Delta178Pd d2Delta178Qd d2Delta178Ld d2Delta178Gam d2Delta178S d2Delta178Ap d2Delta178Aq d2Delta178Al d2Delta178Es d2Delta178Ep d2Delta178Eq d2Delta178El (by decide +kernel) d2Delta178Shift d2Delta178Plogs d2Delta178Poles d2Delta178Laurent]
  exact decide_eq_true d2Delta178Small
theorem d2Delta178Bound : ∀ x ∈ Icc ((d2Delta178Lo : ℚ) : ℝ) ((d2Delta178Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-7377440053313930408909) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta178Fq d2Delta178Ts 16 24 12 20 30 128 d2Delta178Lo d2Delta178Hi d2Delta178Pd d2Delta178Qd d2Delta178Ld d2Delta178Gam (d2LitsStandaloneDelta022.q2 (-7377440053313930408909) 1 (-80)) d2Delta178Check
  simpa only [d2Delta178Fq, d2Delta178Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta178Shift
#print axioms d2Delta178Sites
#print axioms d2Delta178PData
#print axioms d2Delta178Plogs
#print axioms d2Delta178Poles
#print axioms d2Delta178Laurent
#print axioms d2Delta178Small
#print axioms d2Delta178Check
#print axioms d2Delta178Bound

def d2Delta179Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta179Ts : List LTerm := laurentClean []
def d2Delta179Lo : ℚ := (d2LitsStandaloneDelta022.q2 (17174615045) 1 (-34))
def d2Delta179Hi : ℚ := (d2LitsStandaloneDelta022.q2 (137421014033) 1 (-37))
def d2Delta179Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta179Qd : List (ℚ × ℚ) := []
def d2Delta179Ld : List LaurentPieceData := []
def d2Delta179Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-17011145850077636426926488282008991779941, 1, -141, 337063936320943836605526200585765701, 1, -143, 6128433794195691632017832853286717, 1, -140, 1469639750136959707450231685065917, 1, -142, 673364053345768131380876731523, 1, -136, 729284018057142727808259886823, 1, -142, 1999084343828882836385714503, 1, -140, 30737452765858810309977059, 1, -141, 43786504495011604368331, 1, -139, 385178980925124557883, 1, -140, 1348603670832312677, 1, -140, 15401014642760501, 1, -142, 571143132387, 1, -136, 73273374151, 1, -142, 31426071, 1, -140, 746541, 1, -144, 121, 1, -141, 1, 1, -144, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta179S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-2076557383471871716893250621115496111, 1, -128, 10017498468007864529170605356581, 1, -128, 742841367814883117978199069525, 1, -126, 22369296121965496935974145797, 1, -124, 21019203318089975354516748901, 1, -128, 711771225895082792564026805, 1, -128, 121971667905094461095749, 1, -121, 60020546646521025248975, 1, -126, 2736235107711748517415, 1, -128, 6017759833211507271, 1, -126, 42140437930333767, 1, -126, 481251940802925, 1, -127, 4568925079745, 1, -128, 18317643663, 1, -128, 31425103, 1, -127, 186631, 1, -128, 121, 1, -126, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta179Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta179Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta179Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta179Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta179Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta179Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta179El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta179Shift : polyRoundApx 128 d2Delta179Lo d2Delta179Hi d2Delta179Fq.poly = (d2Delta179S,d2Delta179Es) := by decide +kernel
theorem d2Delta179Sites : mergeSites d2Delta179Fq.plogs = [] := by decide +kernel
theorem d2Delta179PData : d2Delta179Pd = [] := by decide +kernel
theorem d2Delta179Plogs : plogsRoundM 16 24 20 128 d2Delta179Lo d2Delta179Hi (mergeSites d2Delta179Fq.plogs) d2Delta179Pd = some (d2Delta179Ap,d2Delta179Ep) := by
  rw [d2Delta179Sites,d2Delta179PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta179Poles : polesRoundM 16 24 12 128 d2Delta179Lo d2Delta179Hi d2Delta179Fq.poles d2Delta179Qd = some (d2Delta179Aq,d2Delta179Eq) := by decide +kernel
theorem d2Delta179Laurent : laurentRoundM 16 30 128 d2Delta179Lo d2Delta179Hi d2Delta179Ts d2Delta179Ld = some (d2Delta179Al,d2Delta179El) := by decide +kernel
theorem d2Delta179Small : chebPolyUB (vecAdd d2Delta179S (vecAdd d2Delta179Ap (vecAdd d2Delta179Aq d2Delta179Al))) d2Delta179Gam+d2Delta179Es+d2Delta179Ep+d2Delta179Eq+d2Delta179El ≤ (d2LitsStandaloneDelta022.q2 (-7377366326552578136631) 1 (-80)) := by decide +kernel
theorem d2Delta179Check : chebRoundPieceL d2Delta179Fq d2Delta179Ts 16 24 12 20 30 128 d2Delta179Lo d2Delta179Hi d2Delta179Pd d2Delta179Qd d2Delta179Ld d2Delta179Gam (d2LitsStandaloneDelta022.q2 (-7377366326552578136631) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta179Fq d2Delta179Ts 16 24 12 20 30 128 d2Delta179Lo d2Delta179Hi d2Delta179Pd d2Delta179Qd d2Delta179Ld d2Delta179Gam d2Delta179S d2Delta179Ap d2Delta179Aq d2Delta179Al d2Delta179Es d2Delta179Ep d2Delta179Eq d2Delta179El (by decide +kernel) d2Delta179Shift d2Delta179Plogs d2Delta179Poles d2Delta179Laurent]
  exact decide_eq_true d2Delta179Small
theorem d2Delta179Bound : ∀ x ∈ Icc ((d2Delta179Lo : ℚ) : ℝ) ((d2Delta179Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-7377366326552578136631) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta179Fq d2Delta179Ts 16 24 12 20 30 128 d2Delta179Lo d2Delta179Hi d2Delta179Pd d2Delta179Qd d2Delta179Ld d2Delta179Gam (d2LitsStandaloneDelta022.q2 (-7377366326552578136631) 1 (-80)) d2Delta179Check
  simpa only [d2Delta179Fq, d2Delta179Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta179Shift
#print axioms d2Delta179Sites
#print axioms d2Delta179PData
#print axioms d2Delta179Plogs
#print axioms d2Delta179Poles
#print axioms d2Delta179Laurent
#print axioms d2Delta179Small
#print axioms d2Delta179Check
#print axioms d2Delta179Bound

def d2Delta180Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta180Ts : List LTerm := laurentClean []
def d2Delta180Lo : ℚ := (d2LitsStandaloneDelta022.q2 (137421014033) 1 (-37))
def d2Delta180Hi : ℚ := (d2LitsStandaloneDelta022.q2 (8588878849) 1 (-33))
def d2Delta180Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta180Qd : List (ℚ × ℚ) := []
def d2Delta180Ld : List LaurentPieceData := []
def d2Delta180Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-531595074199037770387041375398527484567, 1, -136, 389303435616372352779492460087407, 1, -137, 1025334175291177355006173411727, 1, -136, 4773652180722610348831391829, 1, -137, 714623295374283011553609, 1, -134, 8105835717572964299013, 1, -138, 1886222596077122283, 1, -137, 1240079186161807, 1, -138, 75870243827, 1, -136, 57493731, 1, -138, 4343, 1, -137, 1, 1, -138, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta180S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-2076543262595191746820235720682902349, 1, -128, 5940080485230938261445640317, 1, -121, 4005166958308356902134420927, 1, -127, 37293999344859351327041961, 1, -128, 44663867544232206556493, 1, -127, 126653547453440835891, 1, -128, 14736104548073227, 1, -125, 19376229198723, 1, -126, 2370944441, 1, -124, 7186715, 1, -127, 4343, 1, -128, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta180Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta180Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta180Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta180Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta180Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta180Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta180El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta180Shift : polyRoundApx 128 d2Delta180Lo d2Delta180Hi d2Delta180Fq.poly = (d2Delta180S,d2Delta180Es) := by decide +kernel
theorem d2Delta180Sites : mergeSites d2Delta180Fq.plogs = [] := by decide +kernel
theorem d2Delta180PData : d2Delta180Pd = [] := by decide +kernel
theorem d2Delta180Plogs : plogsRoundM 16 24 20 128 d2Delta180Lo d2Delta180Hi (mergeSites d2Delta180Fq.plogs) d2Delta180Pd = some (d2Delta180Ap,d2Delta180Ep) := by
  rw [d2Delta180Sites,d2Delta180PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta180Poles : polesRoundM 16 24 12 128 d2Delta180Lo d2Delta180Hi d2Delta180Fq.poles d2Delta180Qd = some (d2Delta180Aq,d2Delta180Eq) := by decide +kernel
theorem d2Delta180Laurent : laurentRoundM 16 30 128 d2Delta180Lo d2Delta180Hi d2Delta180Ts d2Delta180Ld = some (d2Delta180Al,d2Delta180El) := by decide +kernel
theorem d2Delta180Small : chebPolyUB (vecAdd d2Delta180S (vecAdd d2Delta180Ap (vecAdd d2Delta180Aq d2Delta180Al))) d2Delta180Gam+d2Delta180Es+d2Delta180Ep+d2Delta180Eq+d2Delta180El ≤ (d2LitsStandaloneDelta022.q2 (-7377360923815858011181) 1 (-80)) := by decide +kernel
theorem d2Delta180Check : chebRoundPieceL d2Delta180Fq d2Delta180Ts 16 24 12 20 30 128 d2Delta180Lo d2Delta180Hi d2Delta180Pd d2Delta180Qd d2Delta180Ld d2Delta180Gam (d2LitsStandaloneDelta022.q2 (-7377360923815858011181) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta180Fq d2Delta180Ts 16 24 12 20 30 128 d2Delta180Lo d2Delta180Hi d2Delta180Pd d2Delta180Qd d2Delta180Ld d2Delta180Gam d2Delta180S d2Delta180Ap d2Delta180Aq d2Delta180Al d2Delta180Es d2Delta180Ep d2Delta180Eq d2Delta180El (by decide +kernel) d2Delta180Shift d2Delta180Plogs d2Delta180Poles d2Delta180Laurent]
  exact decide_eq_true d2Delta180Small
theorem d2Delta180Bound : ∀ x ∈ Icc ((d2Delta180Lo : ℚ) : ℝ) ((d2Delta180Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-7377360923815858011181) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta180Fq d2Delta180Ts 16 24 12 20 30 128 d2Delta180Lo d2Delta180Hi d2Delta180Pd d2Delta180Qd d2Delta180Ld d2Delta180Gam (d2LitsStandaloneDelta022.q2 (-7377360923815858011181) 1 (-80)) d2Delta180Check
  simpa only [d2Delta180Fq, d2Delta180Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta180Shift
#print axioms d2Delta180Sites
#print axioms d2Delta180PData
#print axioms d2Delta180Plogs
#print axioms d2Delta180Poles
#print axioms d2Delta180Laurent
#print axioms d2Delta180Small
#print axioms d2Delta180Check
#print axioms d2Delta180Bound

def d2Delta181Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta181Ts : List LTerm := laurentClean []
def d2Delta181Lo : ℚ := (d2LitsStandaloneDelta022.q2 (8588878849) 1 (-33))
def d2Delta181Hi : ℚ := (d2LitsStandaloneDelta022.q2 (549689293887) 1 (-39))
def d2Delta181Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta181Qd : List (ℚ × ℚ) := []
def d2Delta181Ld : List LaurentPieceData := []
def d2Delta181Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-265797414315313836198254229082231516303, 1, -135, 24977069476156299526787248216125, 1, -135, 8151031972331618142168169417, 1, -133, 9435657889431454411408449, 1, -134, 1408157800002190206707, 1, -133, 498204177846350233, 1, -134, 28947429489783, 1, -133, 19014911975, 1, -136, 581315, 1, -135, 55, 1, -136, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta181S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-1038271149796554525214646943093206035, 1, -127, 24391614123255805644309268629, 1, -125, 254719573115646208133450793, 1, -127, 589728462400664483240549, 1, -128, 176019703289702021823, 1, -127, 62275518071281831, 1, -127, 28947428327153, 1, -128, 2376863935, 1, -127, 581315, 1, -128, 55, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta181Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta181Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta181Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta181Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta181Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta181Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta181El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta181Shift : polyRoundApx 128 d2Delta181Lo d2Delta181Hi d2Delta181Fq.poly = (d2Delta181S,d2Delta181Es) := by decide +kernel
theorem d2Delta181Sites : mergeSites d2Delta181Fq.plogs = [] := by decide +kernel
theorem d2Delta181PData : d2Delta181Pd = [] := by decide +kernel
theorem d2Delta181Plogs : plogsRoundM 16 24 20 128 d2Delta181Lo d2Delta181Hi (mergeSites d2Delta181Fq.plogs) d2Delta181Pd = some (d2Delta181Ap,d2Delta181Ep) := by
  rw [d2Delta181Sites,d2Delta181PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta181Poles : polesRoundM 16 24 12 128 d2Delta181Lo d2Delta181Hi d2Delta181Fq.poles d2Delta181Qd = some (d2Delta181Aq,d2Delta181Eq) := by decide +kernel
theorem d2Delta181Laurent : laurentRoundM 16 30 128 d2Delta181Lo d2Delta181Hi d2Delta181Ts d2Delta181Ld = some (d2Delta181Al,d2Delta181El) := by decide +kernel
theorem d2Delta181Small : chebPolyUB (vecAdd d2Delta181S (vecAdd d2Delta181Ap (vecAdd d2Delta181Aq d2Delta181Al))) d2Delta181Gam+d2Delta181Es+d2Delta181Ep+d2Delta181Eq+d2Delta181El ≤ (d2LitsStandaloneDelta022.q2 (-7377359537308929438115) 1 (-80)) := by decide +kernel
theorem d2Delta181Check : chebRoundPieceL d2Delta181Fq d2Delta181Ts 16 24 12 20 30 128 d2Delta181Lo d2Delta181Hi d2Delta181Pd d2Delta181Qd d2Delta181Ld d2Delta181Gam (d2LitsStandaloneDelta022.q2 (-7377359537308929438115) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta181Fq d2Delta181Ts 16 24 12 20 30 128 d2Delta181Lo d2Delta181Hi d2Delta181Pd d2Delta181Qd d2Delta181Ld d2Delta181Gam d2Delta181S d2Delta181Ap d2Delta181Aq d2Delta181Al d2Delta181Es d2Delta181Ep d2Delta181Eq d2Delta181El (by decide +kernel) d2Delta181Shift d2Delta181Plogs d2Delta181Poles d2Delta181Laurent]
  exact decide_eq_true d2Delta181Small
theorem d2Delta181Bound : ∀ x ∈ Icc ((d2Delta181Lo : ℚ) : ℝ) ((d2Delta181Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-7377359537308929438115) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta181Fq d2Delta181Ts 16 24 12 20 30 128 d2Delta181Lo d2Delta181Hi d2Delta181Pd d2Delta181Qd d2Delta181Ld d2Delta181Gam (d2LitsStandaloneDelta022.q2 (-7377359537308929438115) 1 (-80)) d2Delta181Check
  simpa only [d2Delta181Fq, d2Delta181Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta181Shift
#print axioms d2Delta181Sites
#print axioms d2Delta181PData
#print axioms d2Delta181Plogs
#print axioms d2Delta181Poles
#print axioms d2Delta181Laurent
#print axioms d2Delta181Small
#print axioms d2Delta181Check
#print axioms d2Delta181Bound

def d2Delta182Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta182Ts : List LTerm := laurentClean []
def d2Delta182Lo : ℚ := (d2LitsStandaloneDelta022.q2 (549689293887) 1 (-39))
def d2Delta182Hi : ℚ := (d2LitsStandaloneDelta022.q2 (1099379635325) 1 (-40))
def d2Delta182Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta182Qd : List (ℚ × ℚ) := []
def d2Delta182Ld : List LaurentPieceData := []
def d2Delta182Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-265797376727231636125299899282030130453, 1, -135, 393330653636418514607361662505, 1, -130, 2048391077174046291390908983, 1, -133, 295921771098466064519051, 1, -132, 88243631940484175741, 1, -133, 3900368431370735, 1, -132, 453084053113, 1, -133, 4649129, 1, -131, 2273, 1, -135, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta182S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-1038271002872754687816490462882786225, 1, -127, 98332607923773766554584053671, 1, -128, 8001526266404385184416699, 1, -124, 73980437899156009460247, 1, -128, 22060907305494967107, 1, -128, 3900368366282929, 1, -128, 453084048567, 1, -128, 4649129, 1, -125, 2273, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta182Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta182Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta182Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta182Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta182Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta182Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta182El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta182Shift : polyRoundApx 128 d2Delta182Lo d2Delta182Hi d2Delta182Fq.poly = (d2Delta182S,d2Delta182Es) := by decide +kernel
theorem d2Delta182Sites : mergeSites d2Delta182Fq.plogs = [] := by decide +kernel
theorem d2Delta182PData : d2Delta182Pd = [] := by decide +kernel
theorem d2Delta182Plogs : plogsRoundM 16 24 20 128 d2Delta182Lo d2Delta182Hi (mergeSites d2Delta182Fq.plogs) d2Delta182Pd = some (d2Delta182Ap,d2Delta182Ep) := by
  rw [d2Delta182Sites,d2Delta182PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta182Poles : polesRoundM 16 24 12 128 d2Delta182Lo d2Delta182Hi d2Delta182Fq.poles d2Delta182Qd = some (d2Delta182Aq,d2Delta182Eq) := by decide +kernel
theorem d2Delta182Laurent : laurentRoundM 16 30 128 d2Delta182Lo d2Delta182Hi d2Delta182Ts d2Delta182Ld = some (d2Delta182Al,d2Delta182El) := by decide +kernel
theorem d2Delta182Small : chebPolyUB (vecAdd d2Delta182S (vecAdd d2Delta182Ap (vecAdd d2Delta182Aq d2Delta182Al))) d2Delta182Gam+d2Delta182Es+d2Delta182Ep+d2Delta182Eq+d2Delta182El ≤ (d2LitsStandaloneDelta022.q2 (-7377358838613201289625) 1 (-80)) := by decide +kernel
theorem d2Delta182Check : chebRoundPieceL d2Delta182Fq d2Delta182Ts 16 24 12 20 30 128 d2Delta182Lo d2Delta182Hi d2Delta182Pd d2Delta182Qd d2Delta182Ld d2Delta182Gam (d2LitsStandaloneDelta022.q2 (-7377358838613201289625) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta182Fq d2Delta182Ts 16 24 12 20 30 128 d2Delta182Lo d2Delta182Hi d2Delta182Pd d2Delta182Qd d2Delta182Ld d2Delta182Gam d2Delta182S d2Delta182Ap d2Delta182Aq d2Delta182Al d2Delta182Es d2Delta182Ep d2Delta182Eq d2Delta182El (by decide +kernel) d2Delta182Shift d2Delta182Plogs d2Delta182Poles d2Delta182Laurent]
  exact decide_eq_true d2Delta182Small
theorem d2Delta182Bound : ∀ x ∈ Icc ((d2Delta182Lo : ℚ) : ℝ) ((d2Delta182Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-7377358838613201289625) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta182Fq d2Delta182Ts 16 24 12 20 30 128 d2Delta182Lo d2Delta182Hi d2Delta182Pd d2Delta182Qd d2Delta182Ld d2Delta182Gam (d2LitsStandaloneDelta022.q2 (-7377358838613201289625) 1 (-80)) d2Delta182Check
  simpa only [d2Delta182Fq, d2Delta182Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta182Shift
#print axioms d2Delta182Sites
#print axioms d2Delta182PData
#print axioms d2Delta182Plogs
#print axioms d2Delta182Poles
#print axioms d2Delta182Laurent
#print axioms d2Delta182Small
#print axioms d2Delta182Check
#print axioms d2Delta182Bound

def d2Delta183Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta183Ts : List LTerm := laurentClean []
def d2Delta183Lo : ℚ := (d2LitsStandaloneDelta022.q2 (1099379635325) 1 (-40))
def d2Delta183Hi : ℚ := (d2LitsStandaloneDelta022.q2 (1099381730427) 1 (-40))
def d2Delta183Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta183Qd : List (ℚ × ℚ) := []
def d2Delta183Ld : List LaurentPieceData := []
def d2Delta183Gam : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-265797338795018695223717536504509298311, 1, -135, 25370362121709937474680182233311, 1, -135, 4118128800771524722926933003, 1, -132, 2375857267436835729418411, 1, -132, 1415646512364172448093, 1, -133, 250145995060003845, 1, -133, 14523702197269, 1, -132, 19070789683, 1, -136, 582803, 1, -135, 55, 1, -136, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta183S : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [-2076541709593466562244560945475405979, 1, -128, 198205508602660327425446316443, 1, -128, 514765746184828838487580829, 1, -128, 593964160517966191587417, 1, -128, 22119474032496078045, 1, -124, 125072989186531529, 1, -128, 7261850807233, 1, -126, 4767697297, 1, -128, 582803, 1, -128, 55, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta183Ap : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta183Aq : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta183Al : List ℚ := d2LitsStandaloneDelta022.q2listC (raw_ints% [])
def d2Delta183Es : ℚ := (d2LitsStandaloneDelta022.q2 (61) 1 (-127))
def d2Delta183Ep : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta183Eq : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
def d2Delta183El : ℚ := (d2LitsStandaloneDelta022.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta183Shift : polyRoundApx 128 d2Delta183Lo d2Delta183Hi d2Delta183Fq.poly = (d2Delta183S,d2Delta183Es) := by decide +kernel
theorem d2Delta183Sites : mergeSites d2Delta183Fq.plogs = [] := by decide +kernel
theorem d2Delta183PData : d2Delta183Pd = [] := by decide +kernel
theorem d2Delta183Plogs : plogsRoundM 16 24 20 128 d2Delta183Lo d2Delta183Hi (mergeSites d2Delta183Fq.plogs) d2Delta183Pd = some (d2Delta183Ap,d2Delta183Ep) := by
  rw [d2Delta183Sites,d2Delta183PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta183Poles : polesRoundM 16 24 12 128 d2Delta183Lo d2Delta183Hi d2Delta183Fq.poles d2Delta183Qd = some (d2Delta183Aq,d2Delta183Eq) := by decide +kernel
theorem d2Delta183Laurent : laurentRoundM 16 30 128 d2Delta183Lo d2Delta183Hi d2Delta183Ts d2Delta183Ld = some (d2Delta183Al,d2Delta183El) := by decide +kernel
theorem d2Delta183Small : chebPolyUB (vecAdd d2Delta183S (vecAdd d2Delta183Ap (vecAdd d2Delta183Aq d2Delta183Al))) d2Delta183Gam+d2Delta183Es+d2Delta183Ep+d2Delta183Eq+d2Delta183El ≤ (d2LitsStandaloneDelta022.q2 (-7377357430274137666977) 1 (-80)) := by decide +kernel
theorem d2Delta183Check : chebRoundPieceL d2Delta183Fq d2Delta183Ts 16 24 12 20 30 128 d2Delta183Lo d2Delta183Hi d2Delta183Pd d2Delta183Qd d2Delta183Ld d2Delta183Gam (d2LitsStandaloneDelta022.q2 (-7377357430274137666977) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta183Fq d2Delta183Ts 16 24 12 20 30 128 d2Delta183Lo d2Delta183Hi d2Delta183Pd d2Delta183Qd d2Delta183Ld d2Delta183Gam d2Delta183S d2Delta183Ap d2Delta183Aq d2Delta183Al d2Delta183Es d2Delta183Ep d2Delta183Eq d2Delta183El (by decide +kernel) d2Delta183Shift d2Delta183Plogs d2Delta183Poles d2Delta183Laurent]
  exact decide_eq_true d2Delta183Small
theorem d2Delta183Bound : ∀ x ∈ Icc ((d2Delta183Lo : ℚ) : ℝ) ((d2Delta183Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta022.q2 (-7377357430274137666977) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta183Fq d2Delta183Ts 16 24 12 20 30 128 d2Delta183Lo d2Delta183Hi d2Delta183Pd d2Delta183Qd d2Delta183Ld d2Delta183Gam (d2LitsStandaloneDelta022.q2 (-7377357430274137666977) 1 (-80)) d2Delta183Check
  simpa only [d2Delta183Fq, d2Delta183Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta183Shift
#print axioms d2Delta183Sites
#print axioms d2Delta183PData
#print axioms d2Delta183Plogs
#print axioms d2Delta183Poles
#print axioms d2Delta183Laurent
#print axioms d2Delta183Small
#print axioms d2Delta183Check
#print axioms d2Delta183Bound

end StandaloneDelta022
end CatalanMeasure.GenD.Signed.Data.Cells
