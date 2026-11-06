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
namespace d2LitsStandaloneDelta001
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta001
namespace StandaloneDelta001
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta001.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta001.q2listC (raw_ints% []))⟩
def d2Delta8Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta8Ts : List LTerm := laurentClean []
def d2Delta8Lo : ℚ := (d2LitsStandaloneDelta001.q2 (74384321) 1 (-33))
def d2Delta8Hi : ℚ := (d2LitsStandaloneDelta001.q2 (149816193) 1 (-34))
def d2Delta8Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta8Qd : List (ℚ × ℚ) := []
def d2Delta8Ld : List LaurentPieceData := []
def d2Delta8Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-1114744672381296275424146932646776778790105379, 1, -157, -4729234942953119447331646936213724495527, 1, -159, 17778853581895936527600286264874757595, 1, -160, -14483020770348447183550733730576887, 1, -160, 2600144379644308327450961710895, 1, -159, -176423070882509097091681881, 1, -159, -276693218062147391479801, 1, -160, 58391581460315267621, 1, -160, 5956381044816249, 1, -160, -645377872329, 1, -158, -9089636073, 1, -160, -998541009, 1, -157, -6392741311, 1, -160, -5559851979, 1, -160, -1100216703, 1, -158, -3777372107, 1, -160, -2955213371, 1, -160, -1251852315, 1, -159, -967022487, 1, -159, -202183549, 1, -157, -616269019, 1, -159, -508712711, 1, -159, -382102321, 1, -159, -38908255, 1, -156, -230295969, 1, -159, -5784485, 1, -154, -134809631, 1, -159, -213810835, 1, -160, -76582521, 1, -159, -119846211, 1, -160, -84373953, 1, -160, -16288823, 1, -158])
def d2Delta8S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-1038186880390767308999793139162220417, 1, -127, -2202211515243559163166049263581, 1, -128, 4139457079753840606211639271, 1, -127, -6744181274490859767534803, 1, -127, 4843147862188559170421, 1, -127, -328613957861585451, 1, -126, -1030762738411427, 1, -127, 870102712637, 1, -128, 177514369, 1, -128, -153203, 1, -128, -3, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta8Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta8Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta8Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta8Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta8Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta8Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta8El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta8Shift : polyRoundApx 128 d2Delta8Lo d2Delta8Hi d2Delta8Fq.poly = (d2Delta8S,d2Delta8Es) := by decide +kernel
theorem d2Delta8Sites : mergeSites d2Delta8Fq.plogs = [] := by decide +kernel
theorem d2Delta8PData : d2Delta8Pd = [] := by decide +kernel
theorem d2Delta8Plogs : plogsRoundM 16 24 20 128 d2Delta8Lo d2Delta8Hi (mergeSites d2Delta8Fq.plogs) d2Delta8Pd = some (d2Delta8Ap,d2Delta8Ep) := by
  rw [d2Delta8Sites,d2Delta8PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta8Poles : polesRoundM 16 24 12 128 d2Delta8Lo d2Delta8Hi d2Delta8Fq.poles d2Delta8Qd = some (d2Delta8Aq,d2Delta8Eq) := by decide +kernel
theorem d2Delta8Laurent : laurentRoundM 16 30 128 d2Delta8Lo d2Delta8Hi d2Delta8Ts d2Delta8Ld = some (d2Delta8Al,d2Delta8El) := by decide +kernel
theorem d2Delta8Small : chebPolyUB (vecAdd d2Delta8S (vecAdd d2Delta8Ap (vecAdd d2Delta8Aq d2Delta8Al))) d2Delta8Gam+d2Delta8Es+d2Delta8Ep+d2Delta8Eq+d2Delta8El ≤ (d2LitsStandaloneDelta001.q2 (-7376753608943457027093) 1 (-80)) := by decide +kernel
theorem d2Delta8Check : chebRoundPieceL d2Delta8Fq d2Delta8Ts 16 24 12 20 30 128 d2Delta8Lo d2Delta8Hi d2Delta8Pd d2Delta8Qd d2Delta8Ld d2Delta8Gam (d2LitsStandaloneDelta001.q2 (-7376753608943457027093) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta8Fq d2Delta8Ts 16 24 12 20 30 128 d2Delta8Lo d2Delta8Hi d2Delta8Pd d2Delta8Qd d2Delta8Ld d2Delta8Gam d2Delta8S d2Delta8Ap d2Delta8Aq d2Delta8Al d2Delta8Es d2Delta8Ep d2Delta8Eq d2Delta8El (by decide +kernel) d2Delta8Shift d2Delta8Plogs d2Delta8Poles d2Delta8Laurent]
  exact decide_eq_true d2Delta8Small
theorem d2Delta8Bound : ∀ x ∈ Icc ((d2Delta8Lo : ℚ) : ℝ) ((d2Delta8Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-7376753608943457027093) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta8Fq d2Delta8Ts 16 24 12 20 30 128 d2Delta8Lo d2Delta8Hi d2Delta8Pd d2Delta8Qd d2Delta8Ld d2Delta8Gam (d2LitsStandaloneDelta001.q2 (-7376753608943457027093) 1 (-80)) d2Delta8Check
  simpa only [d2Delta8Fq, d2Delta8Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta8Shift
#print axioms d2Delta8Sites
#print axioms d2Delta8PData
#print axioms d2Delta8Plogs
#print axioms d2Delta8Poles
#print axioms d2Delta8Laurent
#print axioms d2Delta8Small
#print axioms d2Delta8Check
#print axioms d2Delta8Bound

def d2Delta9Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta9Ts : List LTerm := laurentClean []
def d2Delta9Lo : ℚ := (d2LitsStandaloneDelta001.q2 (149816193) 1 (-34))
def d2Delta9Hi : ℚ := (d2LitsStandaloneDelta001.q2 (1178623) 1 (-27))
def d2Delta9Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta9Qd : List (ℚ × ℚ) := []
def d2Delta9Ld : List LaurentPieceData := []
def d2Delta9Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-1114747019288583756195189472075927329998729507, 1, -157, -4658466414154086560220049344645643009703, 1, -159, 17605556326326960962836598379679837659, 1, -160, -14399872965834193813226145569700343, 1, -160, 2596582781312019205641805696815, 1, -159, -179733568987159868960624217, 1, -159, -275055599228342064013305, 1, -160, 58580705372109038117, 1, -160, 5863832787532153, 1, -160, -645608559049, 1, -158, -9089636073, 1, -160, -998541009, 1, -157, -6392741311, 1, -160, -5559851979, 1, -160, -1100216703, 1, -158, -3777372107, 1, -160, -2955213371, 1, -160, -1251852315, 1, -159, -967022487, 1, -159, -202183549, 1, -157, -616269019, 1, -159, -508712711, 1, -159, -382102321, 1, -159, -38908255, 1, -156, -230295969, 1, -159, -5784485, 1, -154, -134809631, 1, -159, -213810835, 1, -160, -76582521, 1, -159, -119846211, 1, -160, -84373953, 1, -160, -16288823, 1, -158])
def d2Delta9S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-2076378132196660428941864301404103999, 1, -128, -2169257409100204928302810427347, 1, -128, 1024777043707566042791358005, 1, -125, -6705462545388230966252727, 1, -127, 9673027718361003432729, 1, -128, -1339120969322796363, 1, -128, -2049324260198241, 1, -128, 13639388729, 1, -122, 21844527, 1, -125, -76629, 1, -127, -3, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta9Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta9Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta9Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta9Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta9Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta9Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta9El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta9Shift : polyRoundApx 128 d2Delta9Lo d2Delta9Hi d2Delta9Fq.poly = (d2Delta9S,d2Delta9Es) := by decide +kernel
theorem d2Delta9Sites : mergeSites d2Delta9Fq.plogs = [] := by decide +kernel
theorem d2Delta9PData : d2Delta9Pd = [] := by decide +kernel
theorem d2Delta9Plogs : plogsRoundM 16 24 20 128 d2Delta9Lo d2Delta9Hi (mergeSites d2Delta9Fq.plogs) d2Delta9Pd = some (d2Delta9Ap,d2Delta9Ep) := by
  rw [d2Delta9Sites,d2Delta9PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta9Poles : polesRoundM 16 24 12 128 d2Delta9Lo d2Delta9Hi d2Delta9Fq.poles d2Delta9Qd = some (d2Delta9Aq,d2Delta9Eq) := by decide +kernel
theorem d2Delta9Laurent : laurentRoundM 16 30 128 d2Delta9Lo d2Delta9Hi d2Delta9Ts d2Delta9Ld = some (d2Delta9Al,d2Delta9El) := by decide +kernel
theorem d2Delta9Small : chebPolyUB (vecAdd d2Delta9S (vecAdd d2Delta9Ap (vecAdd d2Delta9Aq d2Delta9Al))) d2Delta9Gam+d2Delta9Es+d2Delta9Ep+d2Delta9Eq+d2Delta9El ≤ (d2LitsStandaloneDelta001.q2 (-7376769256693245252239) 1 (-80)) := by decide +kernel
theorem d2Delta9Check : chebRoundPieceL d2Delta9Fq d2Delta9Ts 16 24 12 20 30 128 d2Delta9Lo d2Delta9Hi d2Delta9Pd d2Delta9Qd d2Delta9Ld d2Delta9Gam (d2LitsStandaloneDelta001.q2 (-7376769256693245252239) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta9Fq d2Delta9Ts 16 24 12 20 30 128 d2Delta9Lo d2Delta9Hi d2Delta9Pd d2Delta9Qd d2Delta9Ld d2Delta9Gam d2Delta9S d2Delta9Ap d2Delta9Aq d2Delta9Al d2Delta9Es d2Delta9Ep d2Delta9Eq d2Delta9El (by decide +kernel) d2Delta9Shift d2Delta9Plogs d2Delta9Poles d2Delta9Laurent]
  exact decide_eq_true d2Delta9Small
theorem d2Delta9Bound : ∀ x ∈ Icc ((d2Delta9Lo : ℚ) : ℝ) ((d2Delta9Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-7376769256693245252239) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta9Fq d2Delta9Ts 16 24 12 20 30 128 d2Delta9Lo d2Delta9Hi d2Delta9Pd d2Delta9Qd d2Delta9Ld d2Delta9Gam (d2LitsStandaloneDelta001.q2 (-7376769256693245252239) 1 (-80)) d2Delta9Check
  simpa only [d2Delta9Fq, d2Delta9Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta9Shift
#print axioms d2Delta9Sites
#print axioms d2Delta9PData
#print axioms d2Delta9Plogs
#print axioms d2Delta9Poles
#print axioms d2Delta9Laurent
#print axioms d2Delta9Small
#print axioms d2Delta9Check
#print axioms d2Delta9Bound

def d2Delta10Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta10Ts : List LTerm := laurentClean []
def d2Delta10Lo : ℚ := (d2LitsStandaloneDelta001.q2 (1178623) 1 (-27))
def d2Delta10Hi : ℚ := (d2LitsStandaloneDelta001.q2 (151911295) 1 (-34))
def d2Delta10Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta10Qd : List (ℚ × ℚ) := []
def d2Delta10Ld : List LaurentPieceData := []
def d2Delta10Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-1114749330984509312732228070933082653106204963, 1, -157, -4588389079803800995377800147703985766055, 1, -159, 17433256156222341347816941618393771483, 1, -160, -14316840189688717785331264160659959, 1, -160, 2592955169745498805980555841327, 1, -159, -183024384060330102200421977, 1, -159, -273412726391498347536377, 1, -160, 58766867226119135781, 1, -160, 5771253089745273, 1, -160, -645814079945, 1, -158, -9089636073, 1, -160, -998541009, 1, -157, -6392741311, 1, -160, -5559851979, 1, -160, -1100216703, 1, -158, -3777372107, 1, -160, -2955213371, 1, -160, -1251852315, 1, -159, -967022487, 1, -159, -202183549, 1, -157, -616269019, 1, -159, -508712711, 1, -159, -382102321, 1, -159, -38908255, 1, -156, -230295969, 1, -159, -5784485, 1, -154, -134809631, 1, -159, -213810835, 1, -160, -76582521, 1, -159, -119846211, 1, -160, -84373953, 1, -160, -16288823, 1, -158])
def d2Delta10S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-259547804753218238246905181194650595, 1, -125, -2136625165373287901481198076257, 1, -128, 8117982844160181781834284835, 1, -128, -6666797380635540208691627, 1, -127, 2414878448456279647623, 1, -126, -681819728554785847, 1, -127, -509270974549665, 1, -126, 875694906561, 1, -128, 85998563, 1, -127, -153307, 1, -128, -3, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta10Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta10Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta10Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta10Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta10Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta10Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta10El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta10Shift : polyRoundApx 128 d2Delta10Lo d2Delta10Hi d2Delta10Fq.poly = (d2Delta10S,d2Delta10Es) := by decide +kernel
theorem d2Delta10Sites : mergeSites d2Delta10Fq.plogs = [] := by decide +kernel
theorem d2Delta10PData : d2Delta10Pd = [] := by decide +kernel
theorem d2Delta10Plogs : plogsRoundM 16 24 20 128 d2Delta10Lo d2Delta10Hi (mergeSites d2Delta10Fq.plogs) d2Delta10Pd = some (d2Delta10Ap,d2Delta10Ep) := by
  rw [d2Delta10Sites,d2Delta10PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta10Poles : polesRoundM 16 24 12 128 d2Delta10Lo d2Delta10Hi d2Delta10Fq.poles d2Delta10Qd = some (d2Delta10Aq,d2Delta10Eq) := by decide +kernel
theorem d2Delta10Laurent : laurentRoundM 16 30 128 d2Delta10Lo d2Delta10Hi d2Delta10Ts d2Delta10Ld = some (d2Delta10Al,d2Delta10El) := by decide +kernel
theorem d2Delta10Small : chebPolyUB (vecAdd d2Delta10S (vecAdd d2Delta10Ap (vecAdd d2Delta10Aq d2Delta10Al))) d2Delta10Gam+d2Delta10Es+d2Delta10Ep+d2Delta10Eq+d2Delta10El ≤ (d2LitsStandaloneDelta001.q2 (-7376784670289475915049) 1 (-80)) := by decide +kernel
theorem d2Delta10Check : chebRoundPieceL d2Delta10Fq d2Delta10Ts 16 24 12 20 30 128 d2Delta10Lo d2Delta10Hi d2Delta10Pd d2Delta10Qd d2Delta10Ld d2Delta10Gam (d2LitsStandaloneDelta001.q2 (-7376784670289475915049) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta10Fq d2Delta10Ts 16 24 12 20 30 128 d2Delta10Lo d2Delta10Hi d2Delta10Pd d2Delta10Qd d2Delta10Ld d2Delta10Gam d2Delta10S d2Delta10Ap d2Delta10Aq d2Delta10Al d2Delta10Es d2Delta10Ep d2Delta10Eq d2Delta10El (by decide +kernel) d2Delta10Shift d2Delta10Plogs d2Delta10Poles d2Delta10Laurent]
  exact decide_eq_true d2Delta10Small
theorem d2Delta10Bound : ∀ x ∈ Icc ((d2Delta10Lo : ℚ) : ℝ) ((d2Delta10Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-7376784670289475915049) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta10Fq d2Delta10Ts 16 24 12 20 30 128 d2Delta10Lo d2Delta10Hi d2Delta10Pd d2Delta10Qd d2Delta10Ld d2Delta10Gam (d2LitsStandaloneDelta001.q2 (-7376784670289475915049) 1 (-80)) d2Delta10Check
  simpa only [d2Delta10Fq, d2Delta10Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta10Shift
#print axioms d2Delta10Sites
#print axioms d2Delta10PData
#print axioms d2Delta10Plogs
#print axioms d2Delta10Poles
#print axioms d2Delta10Laurent
#print axioms d2Delta10Small
#print axioms d2Delta10Check
#print axioms d2Delta10Bound

def d2Delta11Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta11Ts : List LTerm := laurentClean []
def d2Delta11Lo : ℚ := (d2LitsStandaloneDelta001.q2 (151911295) 1 (-34))
def d2Delta11Hi : ℚ := (d2LitsStandaloneDelta001.q2 (38763487) 1 (-32))
def d2Delta11Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta11Qd : List (ℚ × ℚ) := []
def d2Delta11Ld : List LaurentPieceData := []
def d2Delta11Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-1114753833026910107049639533942868547021664547, 1, -157, -13351385614456100288440781309529847398055, 1, -159, 153826262524831274300221586134362484187, 1, -160, -382080869045834793418100311180048887, 1, -160, 209425257213012985388844812799791, 1, -159, -46059449643421260310454685273, 1, -159, -196911059719955133265502201, 1, -160, 129317563429718581076517, 1, -160, 36649929555678771577, 1, -160, -12662682008474057, 1, -158, -774491395817, 1, -160, 488339759, 1, -157, -6392741311, 1, -160, -5559851979, 1, -160, -1100216703, 1, -158, -3777372107, 1, -160, -2955213371, 1, -160, -1251852315, 1, -159, -967022487, 1, -159, -202183549, 1, -157, -616269019, 1, -159, -508712711, 1, -159, -382102321, 1, -159, -38908255, 1, -156, -230295969, 1, -159, -5784485, 1, -154, -134809631, 1, -159, -213810835, 1, -160, -76582521, 1, -159, -119846211, 1, -160, -84373953, 1, -160, -16288823, 1, -158])
def d2Delta11S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-2076390855489560526450409891415357441, 1, -128, -777119566534112046768391760587, 1, -125, 71630155258346986990636208579, 1, -128, -177920054853673983271214575, 1, -127, 780172079602474885318513, 1, -128, -343173014041610430957, 1, -128, -1467103905375439317, 1, -128, 1926988650660347, 1, -128, 1092253244593, 1, -128, -377378223, 1, -125, -45623, 1, -127, 709, 1, -126, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta11Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta11Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta11Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta11Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta11Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta11Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta11El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta11Shift : polyRoundApx 128 d2Delta11Lo d2Delta11Hi d2Delta11Fq.poly = (d2Delta11S,d2Delta11Es) := by decide +kernel
theorem d2Delta11Sites : mergeSites d2Delta11Fq.plogs = [] := by decide +kernel
theorem d2Delta11PData : d2Delta11Pd = [] := by decide +kernel
theorem d2Delta11Plogs : plogsRoundM 16 24 20 128 d2Delta11Lo d2Delta11Hi (mergeSites d2Delta11Fq.plogs) d2Delta11Pd = some (d2Delta11Ap,d2Delta11Ep) := by
  rw [d2Delta11Sites,d2Delta11PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta11Poles : polesRoundM 16 24 12 128 d2Delta11Lo d2Delta11Hi d2Delta11Fq.poles d2Delta11Qd = some (d2Delta11Aq,d2Delta11Eq) := by decide +kernel
theorem d2Delta11Laurent : laurentRoundM 16 30 128 d2Delta11Lo d2Delta11Hi d2Delta11Ts d2Delta11Ld = some (d2Delta11Al,d2Delta11El) := by decide +kernel
theorem d2Delta11Small : chebPolyUB (vecAdd d2Delta11S (vecAdd d2Delta11Ap (vecAdd d2Delta11Aq d2Delta11Al))) d2Delta11Gam+d2Delta11Es+d2Delta11Ep+d2Delta11Eq+d2Delta11El ≤ (d2LitsStandaloneDelta001.q2 (-7376799852019119795529) 1 (-80)) := by decide +kernel
theorem d2Delta11Check : chebRoundPieceL d2Delta11Fq d2Delta11Ts 16 24 12 20 30 128 d2Delta11Lo d2Delta11Hi d2Delta11Pd d2Delta11Qd d2Delta11Ld d2Delta11Gam (d2LitsStandaloneDelta001.q2 (-7376799852019119795529) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta11Fq d2Delta11Ts 16 24 12 20 30 128 d2Delta11Lo d2Delta11Hi d2Delta11Pd d2Delta11Qd d2Delta11Ld d2Delta11Gam d2Delta11S d2Delta11Ap d2Delta11Aq d2Delta11Al d2Delta11Es d2Delta11Ep d2Delta11Eq d2Delta11El (by decide +kernel) d2Delta11Shift d2Delta11Plogs d2Delta11Poles d2Delta11Laurent]
  exact decide_eq_true d2Delta11Small
theorem d2Delta11Bound : ∀ x ∈ Icc ((d2Delta11Lo : ℚ) : ℝ) ((d2Delta11Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-7376799852019119795529) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta11Fq d2Delta11Ts 16 24 12 20 30 128 d2Delta11Lo d2Delta11Hi d2Delta11Pd d2Delta11Qd d2Delta11Ld d2Delta11Gam (d2LitsStandaloneDelta001.q2 (-7376799852019119795529) 1 (-80)) d2Delta11Check
  simpa only [d2Delta11Fq, d2Delta11Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta11Shift
#print axioms d2Delta11Sites
#print axioms d2Delta11PData
#print axioms d2Delta11Plogs
#print axioms d2Delta11Poles
#print axioms d2Delta11Laurent
#print axioms d2Delta11Small
#print axioms d2Delta11Check
#print axioms d2Delta11Bound

def d2Delta12Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta12Ts : List LTerm := laurentClean []
def d2Delta12Lo : ℚ := (d2LitsStandaloneDelta001.q2 (38763487) 1 (-32))
def d2Delta12Hi : ℚ := (d2LitsStandaloneDelta001.q2 (5762043) 1 (-29))
def d2Delta12Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta12Qd : List (ℚ × ℚ) := []
def d2Delta12Ld : List LaurentPieceData := []
def d2Delta12Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-8918264094724156310960121085194135927813654485, 1, -160, -97576902130804678051243542546216778719079, 1, -159, 11441391384486467393209383640168698307967, 1, -160, -282882368717778050104155867564064219975, 1, -160, 387023248101810253626517104737145029, 1, -157, -4082253343655554107639040686840417, 1, -159, -3672505508916452691752630145745, 1, -155, 830175761516355273144127651013, 1, -160, 1568159244322188097737233135, 1, -160, -6788038570477712050374881, 1, -158, 2379788606096467312539, 1, -158, 67443730973956283241, 1, -157, -190940331082749991, 1, -158, -7528229834897595, 1, -160, 16017995537699, 1, -160, 74419662069, 1, -160, -1586719169, 1, -159, -1248347067, 1, -159, -969160121, 1, -159, -201946039, 1, -157, -1235747295, 1, -160, -508522703, 1, -159, -191598193, 1, -158, -38904601, 1, -156, -461957579, 1, -160, -11568767, 1, -155, -135201477, 1, -159, -213810371, 1, -160, -38394903, 1, -158, -119846195, 1, -160, -84576361, 1, -160, -16288823, 1, -158])
def d2Delta12S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-2076447832635426263061491124023570867, 1, -128, -45240204311860942564358437476593, 1, -128, 5322045452352861215943545876451, 1, -128, -263416706175605057766401785943, 1, -128, 5768409254466933824966506803, 1, -128, -30436808805135767989716387, 1, -128, -218921753067570017294565, 1, -126, 6187112291501911074277, 1, -127, 23365974598101796917, 1, -127, -1618748296474976051, 1, -128, 1135864352465879, 1, -128, 64331021517717, 1, -127, -182148374015, 1, -127, -7180592533, 1, -128, 15283405, 1, -127, 298241, 1, -128, -1627, 1, -128, -5, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta12Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta12Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta12Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta12Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta12Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta12Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta12El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta12Shift : polyRoundApx 128 d2Delta12Lo d2Delta12Hi d2Delta12Fq.poly = (d2Delta12S,d2Delta12Es) := by decide +kernel
theorem d2Delta12Sites : mergeSites d2Delta12Fq.plogs = [] := by decide +kernel
theorem d2Delta12PData : d2Delta12Pd = [] := by decide +kernel
theorem d2Delta12Plogs : plogsRoundM 16 24 20 128 d2Delta12Lo d2Delta12Hi (mergeSites d2Delta12Fq.plogs) d2Delta12Pd = some (d2Delta12Ap,d2Delta12Ep) := by
  rw [d2Delta12Sites,d2Delta12PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta12Poles : polesRoundM 16 24 12 128 d2Delta12Lo d2Delta12Hi d2Delta12Fq.poles d2Delta12Qd = some (d2Delta12Aq,d2Delta12Eq) := by decide +kernel
theorem d2Delta12Laurent : laurentRoundM 16 30 128 d2Delta12Lo d2Delta12Hi d2Delta12Ts d2Delta12Ld = some (d2Delta12Al,d2Delta12El) := by decide +kernel
theorem d2Delta12Small : chebPolyUB (vecAdd d2Delta12S (vecAdd d2Delta12Ap (vecAdd d2Delta12Aq d2Delta12Al))) d2Delta12Gam+d2Delta12Es+d2Delta12Ep+d2Delta12Eq+d2Delta12El ≤ (d2LitsStandaloneDelta001.q2 (-7376844028680347918539) 1 (-80)) := by decide +kernel
theorem d2Delta12Check : chebRoundPieceL d2Delta12Fq d2Delta12Ts 16 24 12 20 30 128 d2Delta12Lo d2Delta12Hi d2Delta12Pd d2Delta12Qd d2Delta12Ld d2Delta12Gam (d2LitsStandaloneDelta001.q2 (-7376844028680347918539) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta12Fq d2Delta12Ts 16 24 12 20 30 128 d2Delta12Lo d2Delta12Hi d2Delta12Pd d2Delta12Qd d2Delta12Ld d2Delta12Gam d2Delta12S d2Delta12Ap d2Delta12Aq d2Delta12Al d2Delta12Es d2Delta12Ep d2Delta12Eq d2Delta12El (by decide +kernel) d2Delta12Shift d2Delta12Plogs d2Delta12Poles d2Delta12Laurent]
  exact decide_eq_true d2Delta12Small
theorem d2Delta12Bound : ∀ x ∈ Icc ((d2Delta12Lo : ℚ) : ℝ) ((d2Delta12Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-7376844028680347918539) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta12Fq d2Delta12Ts 16 24 12 20 30 128 d2Delta12Lo d2Delta12Hi d2Delta12Pd d2Delta12Qd d2Delta12Ld d2Delta12Gam (d2LitsStandaloneDelta001.q2 (-7376844028680347918539) 1 (-80)) d2Delta12Check
  simpa only [d2Delta12Fq, d2Delta12Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta12Shift
#print axioms d2Delta12Sites
#print axioms d2Delta12PData
#print axioms d2Delta12Plogs
#print axioms d2Delta12Poles
#print axioms d2Delta12Laurent
#print axioms d2Delta12Small
#print axioms d2Delta12Check
#print axioms d2Delta12Bound

def d2Delta13Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta13Ts : List LTerm := laurentClean []
def d2Delta13Lo : ℚ := (d2LitsStandaloneDelta001.q2 (5762043) 1 (-29))
def d2Delta13Hi : ℚ := (d2LitsStandaloneDelta001.q2 (28285927) 1 (-31))
def d2Delta13Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta13Qd : List (ℚ × ℚ) := []
def d2Delta13Ld : List LaurentPieceData := []
def d2Delta13Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-4459306066926440793650917864051412979651076653, 1, -159, -73772168882177105575921836773007139676391, 1, -159, 15834726800889565757165837623044711540233, 1, -160, -655882890689191829179667853398141720647, 1, -160, 5954134515590133901588943819691958733, 1, -159, -33211082422211741160997719605262145, 1, -159, -376185502659532717001595756429297, 1, -159, 10540259450814996157187458387077, 1, -160, 3484107391159022345193617397, 1, -159, -161115779988833136080539057, 1, -158, 1306476605894558985154079, 1, -160, 3045918641475979530641, 1, -157, -21684322856362230565, 1, -158, -645955238484780091, 1, -160, 1552972100134627, 1, -159, 12593930265717, 1, -160, -80262563095, 1, -160, -1340635643, 1, -159, -2005167049, 1, -160, -202012839, 1, -157, -636601487, 1, -159, -508577903, 1, -159, -196401921, 1, -158, -38905605, 1, -156, -471166235, 1, -160, -11568813, 1, -155, -274520209, 1, -160, -213810435, 1, -160, -19411801, 1, -157, -119846195, 1, -160, -85240505, 1, -160, -16288823, 1, -158])
def d2Delta13S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-2076529887661026108012324619655684915, 1, -128, -4236848945639168214214444425689, 1, -125, 7351435233519569990637234123573, 1, -128, -610529102647679081649021953031, 1, -128, 5547322051837642166681439375, 1, -126, -123858384905308167526197629, 1, -127, -2803007905561206051003887, 1, -127, 78574275159528334702577, 1, -127, 103639741715685460175, 1, -127, -4803621789711245785, 1, -125, 155868255207159755, 1, -128, 5811631127290097, 1, -128, -41380301823603, 1, -128, -154052786853, 1, -126, 5926483075, 1, -128, 48068249, 1, -128, -589079, 1, -128, -2797, 1, -128, 11, 1, -126, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta13Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta13Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta13Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta13Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta13Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta13Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta13El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta13Shift : polyRoundApx 128 d2Delta13Lo d2Delta13Hi d2Delta13Fq.poly = (d2Delta13S,d2Delta13Es) := by decide +kernel
theorem d2Delta13Sites : mergeSites d2Delta13Fq.plogs = [] := by decide +kernel
theorem d2Delta13PData : d2Delta13Pd = [] := by decide +kernel
theorem d2Delta13Plogs : plogsRoundM 16 24 20 128 d2Delta13Lo d2Delta13Hi (mergeSites d2Delta13Fq.plogs) d2Delta13Pd = some (d2Delta13Ap,d2Delta13Ep) := by
  rw [d2Delta13Sites,d2Delta13PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta13Poles : polesRoundM 16 24 12 128 d2Delta13Lo d2Delta13Hi d2Delta13Fq.poles d2Delta13Qd = some (d2Delta13Aq,d2Delta13Eq) := by decide +kernel
theorem d2Delta13Laurent : laurentRoundM 16 30 128 d2Delta13Lo d2Delta13Hi d2Delta13Ts d2Delta13Ld = some (d2Delta13Al,d2Delta13El) := by decide +kernel
theorem d2Delta13Small : chebPolyUB (vecAdd d2Delta13S (vecAdd d2Delta13Ap (vecAdd d2Delta13Aq d2Delta13Al))) d2Delta13Gam+d2Delta13Es+d2Delta13Ep+d2Delta13Eq+d2Delta13El ≤ (d2LitsStandaloneDelta001.q2 (-922145918946138958513) 1 (-77)) := by decide +kernel
theorem d2Delta13Check : chebRoundPieceL d2Delta13Fq d2Delta13Ts 16 24 12 20 30 128 d2Delta13Lo d2Delta13Hi d2Delta13Pd d2Delta13Qd d2Delta13Ld d2Delta13Gam (d2LitsStandaloneDelta001.q2 (-922145918946138958513) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta13Fq d2Delta13Ts 16 24 12 20 30 128 d2Delta13Lo d2Delta13Hi d2Delta13Pd d2Delta13Qd d2Delta13Ld d2Delta13Gam d2Delta13S d2Delta13Ap d2Delta13Aq d2Delta13Al d2Delta13Es d2Delta13Ep d2Delta13Eq d2Delta13El (by decide +kernel) d2Delta13Shift d2Delta13Plogs d2Delta13Poles d2Delta13Laurent]
  exact decide_eq_true d2Delta13Small
theorem d2Delta13Bound : ∀ x ∈ Icc ((d2Delta13Lo : ℚ) : ℝ) ((d2Delta13Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-922145918946138958513) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta13Fq d2Delta13Ts 16 24 12 20 30 128 d2Delta13Lo d2Delta13Hi d2Delta13Pd d2Delta13Qd d2Delta13Ld d2Delta13Gam (d2LitsStandaloneDelta001.q2 (-922145918946138958513) 1 (-77)) d2Delta13Check
  simpa only [d2Delta13Fq, d2Delta13Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta13Shift
#print axioms d2Delta13Sites
#print axioms d2Delta13PData
#print axioms d2Delta13Plogs
#print axioms d2Delta13Poles
#print axioms d2Delta13Laurent
#print axioms d2Delta13Small
#print axioms d2Delta13Check
#print axioms d2Delta13Bound

def d2Delta14Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta14Ts : List LTerm := laurentClean []
def d2Delta14Lo : ℚ := (d2LitsStandaloneDelta001.q2 (28285927) 1 (-31))
def d2Delta14Hi : ℚ := (d2LitsStandaloneDelta001.q2 (14666739) 1 (-30))
def d2Delta14Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta14Qd : List (ℚ × ℚ) := []
def d2Delta14Ld : List LaurentPieceData := []
def d2Delta14Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-4459380529862809756431192745637379377113407985, 1, -159, -8054499266721297582518960891166334860519, 1, -159, 114710477742810615964075783040627141849, 1, -158, -4361832426399522899060891195140628551, 1, -160, 8843837230243124377592073498280627, 1, -159, -12167933791684431345735174357825, 1, -159, -9197951137772014685078789843, 1, -158, 135015937413086446856676485, 1, -160, -16837794096508350649385, 1, -160, -77554916079984964273, 1, -158, 98076041999381235, 1, -159, 55300285638673, 1, -157, -13670581161, 1, -155, -5974386747, 1, -160, -276554975, 1, -156, -3766810507, 1, -160, -2977392405, 1, -160, -1249923067, 1, -159, -1951549443, 1, -160, -202045223, 1, -157, -1244891853, 1, -160, -508589679, 1, -159, -772100715, 1, -160, -38905669, 1, -156, -465196695, 1, -160, -11568813, 1, -155, -68020161, 1, -158, -213810435, 1, -160, -77187229, 1, -159, -119846195, 1, -160, -42460583, 1, -159, -16288823, 1, -158])
def d2Delta14S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-1038280492479661802394848245396848891, 1, -127, -3747621820737533184592362031475, 1, -128, 213631968918384307674644155791, 1, -128, -4062159680921001009969004973, 1, -128, 32946272214831392455765381, 1, -128, -90661692259113189945705, 1, -128, -274119301452263558077, 1, -128, 502983962779981493, 1, -126, -501863826534243, 1, -128, -18490822961915, 1, -128, 23383768277, 1, -128, 105480175, 1, -128, -102771, 1, -127, -209, 1, -127, 1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta14Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta14Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta14Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta14Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta14Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta14Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta14El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta14Shift : polyRoundApx 128 d2Delta14Lo d2Delta14Hi d2Delta14Fq.poly = (d2Delta14S,d2Delta14Es) := by decide +kernel
theorem d2Delta14Sites : mergeSites d2Delta14Fq.plogs = [] := by decide +kernel
theorem d2Delta14PData : d2Delta14Pd = [] := by decide +kernel
theorem d2Delta14Plogs : plogsRoundM 16 24 20 128 d2Delta14Lo d2Delta14Hi (mergeSites d2Delta14Fq.plogs) d2Delta14Pd = some (d2Delta14Ap,d2Delta14Ep) := by
  rw [d2Delta14Sites,d2Delta14PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta14Poles : polesRoundM 16 24 12 128 d2Delta14Lo d2Delta14Hi d2Delta14Fq.poles d2Delta14Qd = some (d2Delta14Aq,d2Delta14Eq) := by decide +kernel
theorem d2Delta14Laurent : laurentRoundM 16 30 128 d2Delta14Lo d2Delta14Hi d2Delta14Ts d2Delta14Ld = some (d2Delta14Al,d2Delta14El) := by decide +kernel
theorem d2Delta14Small : chebPolyUB (vecAdd d2Delta14S (vecAdd d2Delta14Ap (vecAdd d2Delta14Aq d2Delta14Al))) d2Delta14Gam+d2Delta14Es+d2Delta14Ep+d2Delta14Eq+d2Delta14El ≤ (d2LitsStandaloneDelta001.q2 (-7377412528378846420837) 1 (-80)) := by decide +kernel
theorem d2Delta14Check : chebRoundPieceL d2Delta14Fq d2Delta14Ts 16 24 12 20 30 128 d2Delta14Lo d2Delta14Hi d2Delta14Pd d2Delta14Qd d2Delta14Ld d2Delta14Gam (d2LitsStandaloneDelta001.q2 (-7377412528378846420837) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta14Fq d2Delta14Ts 16 24 12 20 30 128 d2Delta14Lo d2Delta14Hi d2Delta14Pd d2Delta14Qd d2Delta14Ld d2Delta14Gam d2Delta14S d2Delta14Ap d2Delta14Aq d2Delta14Al d2Delta14Es d2Delta14Ep d2Delta14Eq d2Delta14El (by decide +kernel) d2Delta14Shift d2Delta14Plogs d2Delta14Poles d2Delta14Laurent]
  exact decide_eq_true d2Delta14Small
theorem d2Delta14Bound : ∀ x ∈ Icc ((d2Delta14Lo : ℚ) : ℝ) ((d2Delta14Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-7377412528378846420837) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta14Fq d2Delta14Ts 16 24 12 20 30 128 d2Delta14Lo d2Delta14Hi d2Delta14Pd d2Delta14Qd d2Delta14Ld d2Delta14Gam (d2LitsStandaloneDelta001.q2 (-7377412528378846420837) 1 (-80)) d2Delta14Check
  simpa only [d2Delta14Fq, d2Delta14Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta14Shift
#print axioms d2Delta14Sites
#print axioms d2Delta14PData
#print axioms d2Delta14Plogs
#print axioms d2Delta14Poles
#print axioms d2Delta14Laurent
#print axioms d2Delta14Small
#print axioms d2Delta14Check
#print axioms d2Delta14Bound

def d2Delta15Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta15Ts : List LTerm := laurentClean []
def d2Delta15Lo : ℚ := (d2LitsStandaloneDelta001.q2 (14666739) 1 (-30))
def d2Delta15Hi : ℚ := (d2LitsStandaloneDelta001.q2 (59714507) 1 (-32))
def d2Delta15Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta15Qd : List (ℚ × ℚ) := []
def d2Delta15Ld : List LaurentPieceData := []
def d2Delta15Gam : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-8918783550999744511141095752790807604828123269, 1, -160, -3365566442487140299723878339325221199079, 1, -159, 52560201574530342470322759910491611961, 1, -159, -518962127193020257209013327133917255, 1, -160, 1082372043179612693444912752210167, 1, -160, -390208397441344081684965061441, 1, -159, -530644853346332281776385107, 1, -160, 1050890824545187956728965, 1, -160, -3068102355719060499, 1, -155, -148497185059902129, 1, -158, 102776656229975, 1, -159, 25053798929, 1, -157, -6772387995, 1, -160, -5512615995, 1, -160, -2289326663, 1, -159, -3761362827, 1, -160, -383120439, 1, -157, -1249492987, 1, -159, -1997767527, 1, -160, -202034471, 1, -157, -1267376327, 1, -160, -508587631, 1, -159, -391079779, 1, -159, -38905669, 1, -156, -58665425, 1, -157, -11568813, 1, -155, -136814079, 1, -159, -213810435, 1, -160, -77451439, 1, -159, -119846195, 1, -160, -21271181, 1, -158, -16288823, 1, -158])
def d2Delta15S : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [-2076566139263814614999097847746692405, 1, -128, -1566851512178497591365754644559, 1, -128, 48948486175440328372934970409, 1, -128, -241658755156366785245430831, 1, -127, 504020241576605092572501, 1, -126, -726826629726679708343, 1, -126, -1976803198102617993, 1, -127, 978723327119771, 1, -124, -2926031679019, 1, -128, -17702311891, 1, -127, 24505147, 1, -128, 24831, 1, -127, -53, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta15Ap : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta15Aq : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta15Al : List ℚ := d2LitsStandaloneDelta001.q2listC (raw_ints% [])
def d2Delta15Es : ℚ := (d2LitsStandaloneDelta001.q2 (61) 1 (-127))
def d2Delta15Ep : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta15Eq : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
def d2Delta15El : ℚ := (d2LitsStandaloneDelta001.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta15Shift : polyRoundApx 128 d2Delta15Lo d2Delta15Hi d2Delta15Fq.poly = (d2Delta15S,d2Delta15Es) := by decide +kernel
theorem d2Delta15Sites : mergeSites d2Delta15Fq.plogs = [] := by decide +kernel
theorem d2Delta15PData : d2Delta15Pd = [] := by decide +kernel
theorem d2Delta15Plogs : plogsRoundM 16 24 20 128 d2Delta15Lo d2Delta15Hi (mergeSites d2Delta15Fq.plogs) d2Delta15Pd = some (d2Delta15Ap,d2Delta15Ep) := by
  rw [d2Delta15Sites,d2Delta15PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta15Poles : polesRoundM 16 24 12 128 d2Delta15Lo d2Delta15Hi d2Delta15Fq.poles d2Delta15Qd = some (d2Delta15Aq,d2Delta15Eq) := by decide +kernel
theorem d2Delta15Laurent : laurentRoundM 16 30 128 d2Delta15Lo d2Delta15Hi d2Delta15Ts d2Delta15Ld = some (d2Delta15Al,d2Delta15El) := by decide +kernel
theorem d2Delta15Small : chebPolyUB (vecAdd d2Delta15S (vecAdd d2Delta15Ap (vecAdd d2Delta15Aq d2Delta15Al))) d2Delta15Gam+d2Delta15Es+d2Delta15Ep+d2Delta15Eq+d2Delta15El ≤ (d2LitsStandaloneDelta001.q2 (-3688719592848741097763) 1 (-79)) := by decide +kernel
theorem d2Delta15Check : chebRoundPieceL d2Delta15Fq d2Delta15Ts 16 24 12 20 30 128 d2Delta15Lo d2Delta15Hi d2Delta15Pd d2Delta15Qd d2Delta15Ld d2Delta15Gam (d2LitsStandaloneDelta001.q2 (-3688719592848741097763) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta15Fq d2Delta15Ts 16 24 12 20 30 128 d2Delta15Lo d2Delta15Hi d2Delta15Pd d2Delta15Qd d2Delta15Ld d2Delta15Gam d2Delta15S d2Delta15Ap d2Delta15Aq d2Delta15Al d2Delta15Es d2Delta15Ep d2Delta15Eq d2Delta15El (by decide +kernel) d2Delta15Shift d2Delta15Plogs d2Delta15Poles d2Delta15Laurent]
  exact decide_eq_true d2Delta15Small
theorem d2Delta15Bound : ∀ x ∈ Icc ((d2Delta15Lo : ℚ) : ℝ) ((d2Delta15Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta001.q2 (-3688719592848741097763) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta15Fq d2Delta15Ts 16 24 12 20 30 128 d2Delta15Lo d2Delta15Hi d2Delta15Pd d2Delta15Qd d2Delta15Ld d2Delta15Gam (d2LitsStandaloneDelta001.q2 (-3688719592848741097763) 1 (-79)) d2Delta15Check
  simpa only [d2Delta15Fq, d2Delta15Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta15Shift
#print axioms d2Delta15Sites
#print axioms d2Delta15PData
#print axioms d2Delta15Plogs
#print axioms d2Delta15Poles
#print axioms d2Delta15Laurent
#print axioms d2Delta15Small
#print axioms d2Delta15Check
#print axioms d2Delta15Bound

end StandaloneDelta001
end CatalanMeasure.GenD.Signed.Data.Cells
