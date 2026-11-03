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
namespace d2LitsStandaloneDelta020
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta020
namespace StandaloneDelta020
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta020.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta020.q2listC (raw_ints% []))⟩
def d2Delta160Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta160Ts : List LTerm := laurentClean []
def d2Delta160Lo : ℚ := (d2LitsStandaloneDelta020.q2 (4270869527) 1 (-32))
def d2Delta160Hi : ℚ := (d2LitsStandaloneDelta020.q2 (1068503045) 1 (-30))
def d2Delta160Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta160Qd : List (ℚ × ℚ) := []
def d2Delta160Ld : List LaurentPieceData := []
def d2Delta160Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-272172614771626026683632571251201220584541, 1, -145, 2616288203353856356036831247382476923, 1, -145, -19047319610661055198485862077312775, 1, -141, -30948628375368203768788666321399707, 1, -146, 763347402109017548044225636444651, 1, -145, 85780126003827320465413582302425, 1, -146, -2326257571984794859267356083, 1, -139, -22994646618512826637898915149, 1, -144, -256770106524210236502493389, 1, -143, 453038309057669880026499, 1, -144, 1035601685450507668521, 1, -136, 58570875119233243541477, 1, -147, 488058968355867062775, 1, -146, 11894425338595575889, 1, -147, 3563646404559817, 1, -142, 447573319443145, 1, -146, 1475684409873, 1, -145, 16651827817, 1, -146, 5094813, 1, -142, 700229, 1, -147, 1331, 1, -146, 9, 1, -147, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta160S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-1038254963878696445936336438664676025, 1, -127, 20316512437171665553899662551139, 1, -128, -4696835736951304338854117660275, 1, -128, -239401372973269777254066209623, 1, -127, 46644294245749031582958765335, 1, -128, 5274903734337560381111348411, 1, -128, -17168617009151659364755351, 1, -127, -22459377007199352205834217, 1, -128, -1008173374140775407657111, 1, -128, 727734310952786473515, 1, -127, 514943265456368626961, 1, -126, 114094390895136710303, 1, -128, 3806726706711700461, 1, -128, 92820328919388095, 1, -128, 890173930868319, 1, -127, 27955643223961, 1, -128, 92184429371, 1, -126, 4161294123, 1, -128, 20372597, 1, -127, 87505, 1, -126, 1331, 1, -127, 9, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta160Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta160Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta160Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta160Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta160Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta160Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta160El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta160Shift : polyRoundApx 128 d2Delta160Lo d2Delta160Hi d2Delta160Fq.poly = (d2Delta160S,d2Delta160Es) := by decide +kernel
theorem d2Delta160Sites : mergeSites d2Delta160Fq.plogs = [] := by decide +kernel
theorem d2Delta160PData : d2Delta160Pd = [] := by decide +kernel
theorem d2Delta160Plogs : plogsRoundM 16 24 20 128 d2Delta160Lo d2Delta160Hi (mergeSites d2Delta160Fq.plogs) d2Delta160Pd = some (d2Delta160Ap,d2Delta160Ep) := by
  rw [d2Delta160Sites,d2Delta160PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta160Poles : polesRoundM 16 24 12 128 d2Delta160Lo d2Delta160Hi d2Delta160Fq.poles d2Delta160Qd = some (d2Delta160Aq,d2Delta160Eq) := by decide +kernel
theorem d2Delta160Laurent : laurentRoundM 16 30 128 d2Delta160Lo d2Delta160Hi d2Delta160Ts d2Delta160Ld = some (d2Delta160Al,d2Delta160El) := by decide +kernel
theorem d2Delta160Small : chebPolyUB (vecAdd d2Delta160S (vecAdd d2Delta160Ap (vecAdd d2Delta160Aq d2Delta160Al))) d2Delta160Gam+d2Delta160Es+d2Delta160Ep+d2Delta160Eq+d2Delta160El ≤ (d2LitsStandaloneDelta020.q2 (-7377173889278915346845) 1 (-80)) := by decide +kernel
theorem d2Delta160Check : chebRoundPieceL d2Delta160Fq d2Delta160Ts 16 24 12 20 30 128 d2Delta160Lo d2Delta160Hi d2Delta160Pd d2Delta160Qd d2Delta160Ld d2Delta160Gam (d2LitsStandaloneDelta020.q2 (-7377173889278915346845) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta160Fq d2Delta160Ts 16 24 12 20 30 128 d2Delta160Lo d2Delta160Hi d2Delta160Pd d2Delta160Qd d2Delta160Ld d2Delta160Gam d2Delta160S d2Delta160Ap d2Delta160Aq d2Delta160Al d2Delta160Es d2Delta160Ep d2Delta160Eq d2Delta160El (by decide +kernel) d2Delta160Shift d2Delta160Plogs d2Delta160Poles d2Delta160Laurent]
  exact decide_eq_true d2Delta160Small
theorem d2Delta160Bound : ∀ x ∈ Icc ((d2Delta160Lo : ℚ) : ℝ) ((d2Delta160Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-7377173889278915346845) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta160Fq d2Delta160Ts 16 24 12 20 30 128 d2Delta160Lo d2Delta160Hi d2Delta160Pd d2Delta160Qd d2Delta160Ld d2Delta160Gam (d2LitsStandaloneDelta020.q2 (-7377173889278915346845) 1 (-80)) d2Delta160Check
  simpa only [d2Delta160Fq, d2Delta160Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta160Shift
#print axioms d2Delta160Sites
#print axioms d2Delta160PData
#print axioms d2Delta160Plogs
#print axioms d2Delta160Poles
#print axioms d2Delta160Laurent
#print axioms d2Delta160Small
#print axioms d2Delta160Check
#print axioms d2Delta160Bound

def d2Delta161Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta161Ts : List LTerm := laurentClean []
def d2Delta161Lo : ℚ := (d2LitsStandaloneDelta020.q2 (1068503045) 1 (-30))
def d2Delta161Hi : ℚ := (d2LitsStandaloneDelta020.q2 (2140148743) 1 (-31))
def d2Delta161Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta161Qd : List (ℚ × ℚ) := []
def d2Delta161Ld : List LaurentPieceData := []
def d2Delta161Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-8709510518080149150148456853933161062557223, 1, -150, -26065404200708155956114736496168259459, 1, -148, -10215343346424429477055000352959129995, 1, -148, 954509291317492437746018160475284981, 1, -148, 189643271424183378746721077613182349, 1, -148, -2452099413021725797848194504037685, 1, -148, -1470237928200123143753141101532365, 1, -148, -71807229691909711011388887912301, 1, -148, 10903852355581435489983343723401, 1, -151, 639284147056387254682748637787, 1, -149, 38091541918785362741396751403, 1, -149, 1425762475111047474766519859, 1, -149, 39170119939557358249024521, 1, -149, 844146616831806286017837, 1, -149, 14824876827143372991677, 1, -149, 217624846939675937173, 1, -149, 5440482703480196671, 1, -150, 29368958040710081, 1, -149, 277030895617641, 1, -149, 2304816088377, 1, -149, 17048286173, 1, -149, 112885223, 1, -149, 673119, 1, -149, 3631, 1, -149, 71, 1, -151, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta161S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-2076499198018872790692327585131230343, 1, -128, -13799994970405314001398276483859, 1, -127, -20956363498192024831496964311947, 1, -128, 3684062717723019066635964542873, 1, -128, 1514366213918335093592478849137, 1, -128, -29615376041750592792697787983, 1, -128, -2823786487427710277846169047, 1, -124, -4556439659039184938231910953, 1, -128, 35814815441207478920627699, 1, -126, 76129830266220777079065455, 1, -128, 2296303774283317820944061, 1, -126, 345412144128750852000829, 1, -127, 19024831258719649634415, 1, -127, 1642354956057318624009, 1, -128, 57739806058790344007, 1, -128, 424074072026522663, 1, -126, 42425901454257717, 1, -128, 916412120799307, 1, -128, 17293129409317, 1, -128, 17987861983, 1, -124, 4258370507, 1, -128, 56400855, 1, -128, 672693, 1, -128, 3631, 1, -127, 71, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta161Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta161Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta161Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta161Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta161Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta161Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta161El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta161Shift : polyRoundApx 128 d2Delta161Lo d2Delta161Hi d2Delta161Fq.poly = (d2Delta161S,d2Delta161Es) := by decide +kernel
theorem d2Delta161Sites : mergeSites d2Delta161Fq.plogs = [] := by decide +kernel
theorem d2Delta161PData : d2Delta161Pd = [] := by decide +kernel
theorem d2Delta161Plogs : plogsRoundM 16 24 20 128 d2Delta161Lo d2Delta161Hi (mergeSites d2Delta161Fq.plogs) d2Delta161Pd = some (d2Delta161Ap,d2Delta161Ep) := by
  rw [d2Delta161Sites,d2Delta161PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta161Poles : polesRoundM 16 24 12 128 d2Delta161Lo d2Delta161Hi d2Delta161Fq.poles d2Delta161Qd = some (d2Delta161Aq,d2Delta161Eq) := by decide +kernel
theorem d2Delta161Laurent : laurentRoundM 16 30 128 d2Delta161Lo d2Delta161Hi d2Delta161Ts d2Delta161Ld = some (d2Delta161Al,d2Delta161El) := by decide +kernel
theorem d2Delta161Small : chebPolyUB (vecAdd d2Delta161S (vecAdd d2Delta161Ap (vecAdd d2Delta161Aq d2Delta161Al))) d2Delta161Gam+d2Delta161Es+d2Delta161Ep+d2Delta161Eq+d2Delta161El ≤ (d2LitsStandaloneDelta020.q2 (-3688557774619768891219) 1 (-79)) := by decide +kernel
theorem d2Delta161Check : chebRoundPieceL d2Delta161Fq d2Delta161Ts 16 24 12 20 30 128 d2Delta161Lo d2Delta161Hi d2Delta161Pd d2Delta161Qd d2Delta161Ld d2Delta161Gam (d2LitsStandaloneDelta020.q2 (-3688557774619768891219) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta161Fq d2Delta161Ts 16 24 12 20 30 128 d2Delta161Lo d2Delta161Hi d2Delta161Pd d2Delta161Qd d2Delta161Ld d2Delta161Gam d2Delta161S d2Delta161Ap d2Delta161Aq d2Delta161Al d2Delta161Es d2Delta161Ep d2Delta161Eq d2Delta161El (by decide +kernel) d2Delta161Shift d2Delta161Plogs d2Delta161Poles d2Delta161Laurent]
  exact decide_eq_true d2Delta161Small
theorem d2Delta161Bound : ∀ x ∈ Icc ((d2Delta161Lo : ℚ) : ℝ) ((d2Delta161Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-3688557774619768891219) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta161Fq d2Delta161Ts 16 24 12 20 30 128 d2Delta161Lo d2Delta161Hi d2Delta161Pd d2Delta161Qd d2Delta161Ld d2Delta161Gam (d2LitsStandaloneDelta020.q2 (-3688557774619768891219) 1 (-79)) d2Delta161Check
  simpa only [d2Delta161Fq, d2Delta161Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta161Shift
#print axioms d2Delta161Sites
#print axioms d2Delta161PData
#print axioms d2Delta161Plogs
#print axioms d2Delta161Poles
#print axioms d2Delta161Laurent
#print axioms d2Delta161Small
#print axioms d2Delta161Check
#print axioms d2Delta161Bound

def d2Delta162Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta162Ts : List LTerm := laurentClean []
def d2Delta162Lo : ℚ := (d2LitsStandaloneDelta020.q2 (2140148743) 1 (-31))
def d2Delta162Hi : ℚ := (d2LitsStandaloneDelta020.q2 (4281345037) 1 (-32))
def d2Delta162Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta162Qd : List (ℚ × ℚ) := []
def d2Delta162Ld : List LaurentPieceData := []
def d2Delta162Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-68044437043737448041940860524903183813741, 1, -143, -71803339533757156619808952001078363, 1, -141, 136426322722602909863585520543609, 1, -140, 81915520632898890560174747716499, 1, -141, 82271247243641956631565576765, 1, -140, -28942791624310883463307467659, 1, -141, -170973917427429587015513797, 1, -140, 1267575453068746508792215, 1, -141, 65832453601210711072711, 1, -141, 796554257060048554445, 1, -141, 2955671122464932225, 1, -140, 31670316190200423, 1, -141, 65694656742459, 1, -140, 439525826257, 1, -141, 609060299, 1, -140, 2852781, 1, -141, 22929, 1, -143, 5, 1, -140, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta162S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-2076551456740981805119916222608129673, 1, -128, -8795072121396464157402617456711, 1, -128, 33226488877389100530804261323, 1, -127, 20034241287397925306527090267, 1, -127, 81345457934536999958111209, 1, -127, -14136544505837870323037813, 1, -126, -1337790185942990360004143, 1, -128, 2461734098008893936455, 1, -126, 64231784446805213937, 1, -124, 24881434754698454721, 1, -128, 92340088546270527, 1, -126, 3958075326400619, 1, -128, 32843065098175, 1, -128, 109870758933, 1, -127, 609014441, 1, -127, 2852611, 1, -127, 22929, 1, -128, 5, 1, -124, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta162Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta162Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta162Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta162Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta162Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta162Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta162El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta162Shift : polyRoundApx 128 d2Delta162Lo d2Delta162Hi d2Delta162Fq.poly = (d2Delta162S,d2Delta162Es) := by decide +kernel
theorem d2Delta162Sites : mergeSites d2Delta162Fq.plogs = [] := by decide +kernel
theorem d2Delta162PData : d2Delta162Pd = [] := by decide +kernel
theorem d2Delta162Plogs : plogsRoundM 16 24 20 128 d2Delta162Lo d2Delta162Hi (mergeSites d2Delta162Fq.plogs) d2Delta162Pd = some (d2Delta162Ap,d2Delta162Ep) := by
  rw [d2Delta162Sites,d2Delta162PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta162Poles : polesRoundM 16 24 12 128 d2Delta162Lo d2Delta162Hi d2Delta162Fq.poles d2Delta162Qd = some (d2Delta162Aq,d2Delta162Eq) := by decide +kernel
theorem d2Delta162Laurent : laurentRoundM 16 30 128 d2Delta162Lo d2Delta162Hi d2Delta162Ts d2Delta162Ld = some (d2Delta162Al,d2Delta162El) := by decide +kernel
theorem d2Delta162Small : chebPolyUB (vecAdd d2Delta162S (vecAdd d2Delta162Ap (vecAdd d2Delta162Aq d2Delta162Al))) d2Delta162Gam+d2Delta162Es+d2Delta162Ep+d2Delta162Eq+d2Delta162El ≤ (d2LitsStandaloneDelta020.q2 (-1844340338290603905569) 1 (-78)) := by decide +kernel
theorem d2Delta162Check : chebRoundPieceL d2Delta162Fq d2Delta162Ts 16 24 12 20 30 128 d2Delta162Lo d2Delta162Hi d2Delta162Pd d2Delta162Qd d2Delta162Ld d2Delta162Gam (d2LitsStandaloneDelta020.q2 (-1844340338290603905569) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta162Fq d2Delta162Ts 16 24 12 20 30 128 d2Delta162Lo d2Delta162Hi d2Delta162Pd d2Delta162Qd d2Delta162Ld d2Delta162Gam d2Delta162S d2Delta162Ap d2Delta162Aq d2Delta162Al d2Delta162Es d2Delta162Ep d2Delta162Eq d2Delta162El (by decide +kernel) d2Delta162Shift d2Delta162Plogs d2Delta162Poles d2Delta162Laurent]
  exact decide_eq_true d2Delta162Small
theorem d2Delta162Bound : ∀ x ∈ Icc ((d2Delta162Lo : ℚ) : ℝ) ((d2Delta162Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-1844340338290603905569) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta162Fq d2Delta162Ts 16 24 12 20 30 128 d2Delta162Lo d2Delta162Hi d2Delta162Pd d2Delta162Qd d2Delta162Ld d2Delta162Gam (d2LitsStandaloneDelta020.q2 (-1844340338290603905569) 1 (-78)) d2Delta162Check
  simpa only [d2Delta162Fq, d2Delta162Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta162Shift
#print axioms d2Delta162Sites
#print axioms d2Delta162PData
#print axioms d2Delta162Plogs
#print axioms d2Delta162Poles
#print axioms d2Delta162Laurent
#print axioms d2Delta162Small
#print axioms d2Delta162Check
#print axioms d2Delta162Bound

def d2Delta163Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta163Ts : List LTerm := laurentClean []
def d2Delta163Lo : ℚ := (d2LitsStandaloneDelta020.q2 (4281345037) 1 (-32))
def d2Delta163Hi : ℚ := (d2LitsStandaloneDelta020.q2 (1070598147) 1 (-30))
def d2Delta163Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta163Qd : List (ℚ × ℚ) := []
def d2Delta163Ld : List LaurentPieceData := []
def d2Delta163Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-34022495142376089282891302651609428695235, 1, -142, -262762517245515113763426745883282509, 1, -143, 1251132398367803579319189156825229, 1, -141, 79488159921964570600045964690025, 1, -141, -246078538156045385474335540561, 1, -140, -36457386407622245138284247755, 1, -141, -272310123478169165418623249, 1, -141, 7763009944507926219788963, 1, -142, 49558961446803022895895, 1, -140, 2125636363786081987803, 1, -142, 7451975819810555309, 1, -141, 38555009508950379, 1, -141, 78052120736721, 1, -140, 512745353511, 1, -141, 1400742615, 1, -141, 25938121, 1, -144, 12903, 1, -142, 89, 1, -144, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta163S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-2076568459815957968301681173448248005, 1, -128, -8048007337065146500258991594719, 1, -128, 305932269115293009364894909103, 1, -128, 19450805948044401465647781653, 1, -127, -479024642173189730620078071, 1, -128, -71258844236925301136146645, 1, -128, -1066807836170498373619351, 1, -128, 30249541444979354051759, 1, -128, 193444163212388336159, 1, -125, 33199815941124965795, 1, -128, 465631417297986527, 1, -128, 2409271506947105, 1, -127, 39021157936947, 1, -128, 256348360429, 1, -128, 1400639391, 1, -128, 810519, 1, -125, 12903, 1, -127, 89, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta163Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta163Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta163Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta163Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta163Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta163Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta163El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta163Shift : polyRoundApx 128 d2Delta163Lo d2Delta163Hi d2Delta163Fq.poly = (d2Delta163S,d2Delta163Es) := by decide +kernel
theorem d2Delta163Sites : mergeSites d2Delta163Fq.plogs = [] := by decide +kernel
theorem d2Delta163PData : d2Delta163Pd = [] := by decide +kernel
theorem d2Delta163Plogs : plogsRoundM 16 24 20 128 d2Delta163Lo d2Delta163Hi (mergeSites d2Delta163Fq.plogs) d2Delta163Pd = some (d2Delta163Ap,d2Delta163Ep) := by
  rw [d2Delta163Sites,d2Delta163PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta163Poles : polesRoundM 16 24 12 128 d2Delta163Lo d2Delta163Hi d2Delta163Fq.poles d2Delta163Qd = some (d2Delta163Aq,d2Delta163Eq) := by decide +kernel
theorem d2Delta163Laurent : laurentRoundM 16 30 128 d2Delta163Lo d2Delta163Hi d2Delta163Ts d2Delta163Ld = some (d2Delta163Al,d2Delta163El) := by decide +kernel
theorem d2Delta163Small : chebPolyUB (vecAdd d2Delta163S (vecAdd d2Delta163Ap (vecAdd d2Delta163Aq d2Delta163Al))) d2Delta163Gam+d2Delta163Es+d2Delta163Ep+d2Delta163Eq+d2Delta163El ≤ (d2LitsStandaloneDelta020.q2 (-7377423563285081140381) 1 (-80)) := by decide +kernel
theorem d2Delta163Check : chebRoundPieceL d2Delta163Fq d2Delta163Ts 16 24 12 20 30 128 d2Delta163Lo d2Delta163Hi d2Delta163Pd d2Delta163Qd d2Delta163Ld d2Delta163Gam (d2LitsStandaloneDelta020.q2 (-7377423563285081140381) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta163Fq d2Delta163Ts 16 24 12 20 30 128 d2Delta163Lo d2Delta163Hi d2Delta163Pd d2Delta163Qd d2Delta163Ld d2Delta163Gam d2Delta163S d2Delta163Ap d2Delta163Aq d2Delta163Al d2Delta163Es d2Delta163Ep d2Delta163Eq d2Delta163El (by decide +kernel) d2Delta163Shift d2Delta163Plogs d2Delta163Poles d2Delta163Laurent]
  exact decide_eq_true d2Delta163Small
theorem d2Delta163Bound : ∀ x ∈ Icc ((d2Delta163Lo : ℚ) : ℝ) ((d2Delta163Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-7377423563285081140381) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta163Fq d2Delta163Ts 16 24 12 20 30 128 d2Delta163Lo d2Delta163Hi d2Delta163Pd d2Delta163Qd d2Delta163Ld d2Delta163Gam (d2LitsStandaloneDelta020.q2 (-7377423563285081140381) 1 (-80)) d2Delta163Check
  simpa only [d2Delta163Fq, d2Delta163Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta163Shift
#print axioms d2Delta163Sites
#print axioms d2Delta163PData
#print axioms d2Delta163Plogs
#print axioms d2Delta163Poles
#print axioms d2Delta163Laurent
#print axioms d2Delta163Small
#print axioms d2Delta163Check
#print axioms d2Delta163Bound

def d2Delta164Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta164Ts : List LTerm := laurentClean []
def d2Delta164Lo : ℚ := (d2LitsStandaloneDelta020.q2 (1070598147) 1 (-30))
def d2Delta164Hi : ℚ := (d2LitsStandaloneDelta020.q2 (4283440139) 1 (-32))
def d2Delta164Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta164Qd : List (ℚ × ℚ) := []
def d2Delta164Ld : List LaurentPieceData := []
def d2Delta164Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-8505683027593266769319075852089809372721, 1, -140, -208230064517693872549882283223622195, 1, -143, 2132648643599529071613022555656473, 1, -141, 16367311559792933374437673338763, 1, -139, -637922939619930391566570800789, 1, -140, -20646369123361937919850846029, 1, -140, -113041141489197953123379453, 1, -141, 15452890422277902239773323, 1, -142, 35793609139184030527835, 1, -139, 2794258231458986409399, 1, -142, 9323027423142914761, 1, -141, 23360901296774935, 1, -140, 92452096510949, 1, -140, 37304537505, 1, -137, 1608166683, 1, -141, 29443195, 1, -144, 3627, 1, -140, 99, 1, -144, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta164S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-2076583030897327860485898582539871651, 1, -128, -6378678025623139622461692265045, 1, -128, 260955933527301903819007016803, 1, -127, 32068270536487795407816327137, 1, -128, -1245278095086256266820347431, 1, -128, -40377720355774603487798515, 1, -127, -55754985691601967246375, 1, -125, 60264633630965541623375, 1, -128, 2235644004171771967663, 1, -128, 43644225459270970721, 1, -128, 582550543540808323, 1, -128, 5839255447622413, 1, -128, 2888776241293, 1, -124, 298408697781, 1, -128, 1608050619, 1, -128, 3680189, 1, -127, 3627, 1, -125, 99, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta164Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta164Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta164Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta164Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta164Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta164Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta164El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta164Shift : polyRoundApx 128 d2Delta164Lo d2Delta164Hi d2Delta164Fq.poly = (d2Delta164S,d2Delta164Es) := by decide +kernel
theorem d2Delta164Sites : mergeSites d2Delta164Fq.plogs = [] := by decide +kernel
theorem d2Delta164PData : d2Delta164Pd = [] := by decide +kernel
theorem d2Delta164Plogs : plogsRoundM 16 24 20 128 d2Delta164Lo d2Delta164Hi (mergeSites d2Delta164Fq.plogs) d2Delta164Pd = some (d2Delta164Ap,d2Delta164Ep) := by
  rw [d2Delta164Sites,d2Delta164PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta164Poles : polesRoundM 16 24 12 128 d2Delta164Lo d2Delta164Hi d2Delta164Fq.poles d2Delta164Qd = some (d2Delta164Aq,d2Delta164Eq) := by decide +kernel
theorem d2Delta164Laurent : laurentRoundM 16 30 128 d2Delta164Lo d2Delta164Hi d2Delta164Ts d2Delta164Ld = some (d2Delta164Al,d2Delta164El) := by decide +kernel
theorem d2Delta164Small : chebPolyUB (vecAdd d2Delta164S (vecAdd d2Delta164Ap (vecAdd d2Delta164Aq d2Delta164Al))) d2Delta164Gam+d2Delta164Es+d2Delta164Ep+d2Delta164Eq+d2Delta164El ≤ (d2LitsStandaloneDelta020.q2 (-3688740241694991253959) 1 (-79)) := by decide +kernel
theorem d2Delta164Check : chebRoundPieceL d2Delta164Fq d2Delta164Ts 16 24 12 20 30 128 d2Delta164Lo d2Delta164Hi d2Delta164Pd d2Delta164Qd d2Delta164Ld d2Delta164Gam (d2LitsStandaloneDelta020.q2 (-3688740241694991253959) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta164Fq d2Delta164Ts 16 24 12 20 30 128 d2Delta164Lo d2Delta164Hi d2Delta164Pd d2Delta164Qd d2Delta164Ld d2Delta164Gam d2Delta164S d2Delta164Ap d2Delta164Aq d2Delta164Al d2Delta164Es d2Delta164Ep d2Delta164Eq d2Delta164El (by decide +kernel) d2Delta164Shift d2Delta164Plogs d2Delta164Poles d2Delta164Laurent]
  exact decide_eq_true d2Delta164Small
theorem d2Delta164Bound : ∀ x ∈ Icc ((d2Delta164Lo : ℚ) : ℝ) ((d2Delta164Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-3688740241694991253959) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta164Fq d2Delta164Ts 16 24 12 20 30 128 d2Delta164Lo d2Delta164Hi d2Delta164Pd d2Delta164Qd d2Delta164Ld d2Delta164Gam (d2LitsStandaloneDelta020.q2 (-3688740241694991253959) 1 (-79)) d2Delta164Check
  simpa only [d2Delta164Fq, d2Delta164Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta164Shift
#print axioms d2Delta164Sites
#print axioms d2Delta164PData
#print axioms d2Delta164Plogs
#print axioms d2Delta164Poles
#print axioms d2Delta164Laurent
#print axioms d2Delta164Small
#print axioms d2Delta164Check
#print axioms d2Delta164Bound

def d2Delta165Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta165Ts : List LTerm := laurentClean []
def d2Delta165Lo : ℚ := (d2LitsStandaloneDelta020.q2 (4283440139) 1 (-32))
def d2Delta165Hi : ℚ := (d2LitsStandaloneDelta020.q2 (535822849) 1 (-29))
def d2Delta165Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta165Qd : List (ℚ × ℚ) := []
def d2Delta165Ld : List LaurentPieceData := []
def d2Delta165Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-272183501745196484737868302306728642642349, 1, -145, -860742587473921585887819747325795991, 1, -146, 209530719620772941463764581151878945, 1, -144, -4740846212949839977350398854389201, 1, -147, -3651786651310941651237146251586839, 1, -145, -470313404616921444052194176089757, 1, -147, 1932926985747059057164276861043, 1, -143, 731988797425314401594582876461, 1, -145, 7246445568023407566681588235, 1, -143, 735706585214306935929957701, 1, -145, 3385809514830633333827839, 1, -143, 1538654828220981850585639, 1, -148, 4379005027270407216253, 1, -146, 164175944049148126323, 1, -148, 161571270545939799, 1, -145, 4341641108345835, 1, -147, 6301334302849, 1, -145, 127799306875, 1, -147, 142753439, 1, -145, 4531215, 1, -148, 4017, 1, -146, 51, 1, -148, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta165S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-129787409051001125953892584822318585, 1, -124, -815217338820185963930485605529, 1, -126, 827289023941540389003015218023, 1, -125, -17916687467148609077499340217, 1, -128, -112841731575179018067949844957, 1, -127, -14975881770535266686895261227, 1, -128, 1831126819571967692209212441, 1, -128, 11068357811874364385855207, 1, -123, 7043571311208577403804343, 1, -126, 1432797399329278380008331, 1, -128, 26400344663923548770331, 1, -127, 1500509103838648119233, 1, -128, 34175643298568580295, 1, -128, 160200903544062187, 1, -126, 10091904279200105, 1, -128, 135608402014907, 1, -128, 787345635299, 1, -127, 1996191643, 1, -125, 142713269, 1, -128, 141567, 1, -125, 4017, 1, -127, 51, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta165Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta165Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta165Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta165Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta165Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta165Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta165El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta165Shift : polyRoundApx 128 d2Delta165Lo d2Delta165Hi d2Delta165Fq.poly = (d2Delta165S,d2Delta165Es) := by decide +kernel
theorem d2Delta165Sites : mergeSites d2Delta165Fq.plogs = [] := by decide +kernel
theorem d2Delta165PData : d2Delta165Pd = [] := by decide +kernel
theorem d2Delta165Plogs : plogsRoundM 16 24 20 128 d2Delta165Lo d2Delta165Hi (mergeSites d2Delta165Fq.plogs) d2Delta165Pd = some (d2Delta165Ap,d2Delta165Ep) := by
  rw [d2Delta165Sites,d2Delta165PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta165Poles : polesRoundM 16 24 12 128 d2Delta165Lo d2Delta165Hi d2Delta165Fq.poles d2Delta165Qd = some (d2Delta165Aq,d2Delta165Eq) := by decide +kernel
theorem d2Delta165Laurent : laurentRoundM 16 30 128 d2Delta165Lo d2Delta165Hi d2Delta165Ts d2Delta165Ld = some (d2Delta165Al,d2Delta165El) := by decide +kernel
theorem d2Delta165Small : chebPolyUB (vecAdd d2Delta165S (vecAdd d2Delta165Ap (vecAdd d2Delta165Aq d2Delta165Al))) d2Delta165Gam+d2Delta165Es+d2Delta165Ep+d2Delta165Eq+d2Delta165El ≤ (d2LitsStandaloneDelta020.q2 (-3688762719613354723189) 1 (-79)) := by decide +kernel
theorem d2Delta165Check : chebRoundPieceL d2Delta165Fq d2Delta165Ts 16 24 12 20 30 128 d2Delta165Lo d2Delta165Hi d2Delta165Pd d2Delta165Qd d2Delta165Ld d2Delta165Gam (d2LitsStandaloneDelta020.q2 (-3688762719613354723189) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta165Fq d2Delta165Ts 16 24 12 20 30 128 d2Delta165Lo d2Delta165Hi d2Delta165Pd d2Delta165Qd d2Delta165Ld d2Delta165Gam d2Delta165S d2Delta165Ap d2Delta165Aq d2Delta165Al d2Delta165Es d2Delta165Ep d2Delta165Eq d2Delta165El (by decide +kernel) d2Delta165Shift d2Delta165Plogs d2Delta165Poles d2Delta165Laurent]
  exact decide_eq_true d2Delta165Small
theorem d2Delta165Bound : ∀ x ∈ Icc ((d2Delta165Lo : ℚ) : ℝ) ((d2Delta165Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-3688762719613354723189) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta165Fq d2Delta165Ts 16 24 12 20 30 128 d2Delta165Lo d2Delta165Hi d2Delta165Pd d2Delta165Qd d2Delta165Ld d2Delta165Gam (d2LitsStandaloneDelta020.q2 (-3688762719613354723189) 1 (-79)) d2Delta165Check
  simpa only [d2Delta165Fq, d2Delta165Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta165Shift
#print axioms d2Delta165Sites
#print axioms d2Delta165PData
#print axioms d2Delta165Plogs
#print axioms d2Delta165Poles
#print axioms d2Delta165Laurent
#print axioms d2Delta165Small
#print axioms d2Delta165Check
#print axioms d2Delta165Bound

def d2Delta166Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta166Ts : List LTerm := laurentClean []
def d2Delta166Lo : ℚ := (d2LitsStandaloneDelta020.q2 (535822849) 1 (-29))
def d2Delta166Hi : ℚ := (d2LitsStandaloneDelta020.q2 (2144338947) 1 (-31))
def d2Delta166Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta166Qd : List (ℚ × ℚ) := []
def d2Delta166Ld : List LaurentPieceData := []
def d2Delta166Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-544364832921136328514941110087128156881265, 1, -146, 592057689330484936204598289195562855, 1, -144, 33695567194166273657333771214212019, 1, -144, -7920897099004678784923539494686167, 1, -144, -1249922786930725240036165335833637, 1, -146, 9058281743140850883747754947385, 1, -143, 796342752868243546035564679301, 1, -143, 27246254608968871557885301223, 1, -143, 1151732451372694393060593647, 1, -144, 8602069581187759244620967, 1, -143, 97196255427657733000401, 1, -143, 866695472705329693657, 1, -143, 100512099351740434759, 1, -147, 151357175017784099, 1, -145, 770847202610973, 1, -145, 3366059903853, 1, -145, 25498728757, 1, -146, 42296973, 1, -145, 123941, 1, -145, 323, 1, -145, 3, 1, -147, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta166S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-1038293779296291404688684894489947367, 1, -127, 9398049654421753565197465767069, 1, -128, 1066888602532616143918134767217, 1, -128, -15279231142684710352213302797, 1, -123, -39308323344284567343294995263, 1, -128, 4329975659193406195024401545, 1, -128, 773182836160317086083335851, 1, -128, 53064207248899276569085427, 1, -128, 1122841020156129993705257, 1, -127, 16782301543575562354083, 1, -126, 1517513846731729277305, 1, -128, 13534431837784313377, 1, -127, 392456785983824693, 1, -128, 2364167018005489, 1, -127, 24082600922261, 1, -127, 420667613051, 1, -128, 99586981, 1, -123, 10572709, 1, -127, 61963, 1, -127, 323, 1, -127, 3, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta166Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta166Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta166Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta166Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta166Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta166Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta166El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta166Shift : polyRoundApx 128 d2Delta166Lo d2Delta166Hi d2Delta166Fq.poly = (d2Delta166S,d2Delta166Es) := by decide +kernel
theorem d2Delta166Sites : mergeSites d2Delta166Fq.plogs = [] := by decide +kernel
theorem d2Delta166PData : d2Delta166Pd = [] := by decide +kernel
theorem d2Delta166Plogs : plogsRoundM 16 24 20 128 d2Delta166Lo d2Delta166Hi (mergeSites d2Delta166Fq.plogs) d2Delta166Pd = some (d2Delta166Ap,d2Delta166Ep) := by
  rw [d2Delta166Sites,d2Delta166PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta166Poles : polesRoundM 16 24 12 128 d2Delta166Lo d2Delta166Hi d2Delta166Fq.poles d2Delta166Qd = some (d2Delta166Aq,d2Delta166Eq) := by decide +kernel
theorem d2Delta166Laurent : laurentRoundM 16 30 128 d2Delta166Lo d2Delta166Hi d2Delta166Ts d2Delta166Ld = some (d2Delta166Al,d2Delta166El) := by decide +kernel
theorem d2Delta166Small : chebPolyUB (vecAdd d2Delta166S (vecAdd d2Delta166Ap (vecAdd d2Delta166Aq d2Delta166Al))) d2Delta166Gam+d2Delta166Es+d2Delta166Ep+d2Delta166Eq+d2Delta166El ≤ (d2LitsStandaloneDelta020.q2 (-7377484811416787352977) 1 (-80)) := by decide +kernel
theorem d2Delta166Check : chebRoundPieceL d2Delta166Fq d2Delta166Ts 16 24 12 20 30 128 d2Delta166Lo d2Delta166Hi d2Delta166Pd d2Delta166Qd d2Delta166Ld d2Delta166Gam (d2LitsStandaloneDelta020.q2 (-7377484811416787352977) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta166Fq d2Delta166Ts 16 24 12 20 30 128 d2Delta166Lo d2Delta166Hi d2Delta166Pd d2Delta166Qd d2Delta166Ld d2Delta166Gam d2Delta166S d2Delta166Ap d2Delta166Aq d2Delta166Al d2Delta166Es d2Delta166Ep d2Delta166Eq d2Delta166El (by decide +kernel) d2Delta166Shift d2Delta166Plogs d2Delta166Poles d2Delta166Laurent]
  exact decide_eq_true d2Delta166Small
theorem d2Delta166Bound : ∀ x ∈ Icc ((d2Delta166Lo : ℚ) : ℝ) ((d2Delta166Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-7377484811416787352977) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta166Fq d2Delta166Ts 16 24 12 20 30 128 d2Delta166Lo d2Delta166Hi d2Delta166Pd d2Delta166Qd d2Delta166Ld d2Delta166Gam (d2LitsStandaloneDelta020.q2 (-7377484811416787352977) 1 (-80)) d2Delta166Check
  simpa only [d2Delta166Fq, d2Delta166Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta166Shift
#print axioms d2Delta166Sites
#print axioms d2Delta166PData
#print axioms d2Delta166Plogs
#print axioms d2Delta166Poles
#print axioms d2Delta166Laurent
#print axioms d2Delta166Small
#print axioms d2Delta166Check
#print axioms d2Delta166Bound

def d2Delta167Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta167Ts : List LTerm := laurentClean []
def d2Delta167Lo : ℚ := (d2LitsStandaloneDelta020.q2 (2144338947) 1 (-31))
def d2Delta167Hi : ℚ := (d2LitsStandaloneDelta020.q2 (8578403339) 1 (-33))
def d2Delta167Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta167Qd : List (ℚ × ℚ) := []
def d2Delta167Ld : List LaurentPieceData := []
def d2Delta167Gam : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-1063206507685236561032584620235353267125, 1, -137, 38942829422667748389063654678727541, 1, -142, -130300537909087881632633586609945, 1, -140, -37230691412484250904458679929781, 1, -142, 5020072646927751273053996807, 1, -138, 12146219346625357077104663885, 1, -142, 42123870488923752341158845, 1, -140, 1245124399732925004046451, 1, -142, 190252967242906354637, 1, -137, 21632646323667768849, 1, -142, 14747887112201975, 1, -140, 128054868410927, 1, -142, 14202043593, 1, -138, 336406649, 1, -142, 105573, 1, -140, 455, 1, -142, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta167S : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [-519143794626545191097019302844019653, 1, -126, 595925632008152132611698227603, 1, -126, -15915585935175334039451987009, 1, -126, -4552173471450775607375125733, 1, -127, 38725737899443033305494715, 1, -128, 11853031308494938649867475, 1, -128, 328997615743671037320625, 1, -128, 303937917858977960199, 1, -124, 11889658297966781743, 1, -126, 21124255607403863, 1, -124, 1843400677779829, 1, -128, 125049311685, 1, -122, 28403348175, 1, -128, 21024989, 1, -126, 105573, 1, -127, 455, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta167Ap : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta167Aq : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta167Al : List ℚ := d2LitsStandaloneDelta020.q2listC (raw_ints% [])
def d2Delta167Es : ℚ := (d2LitsStandaloneDelta020.q2 (61) 1 (-127))
def d2Delta167Ep : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta167Eq : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
def d2Delta167El : ℚ := (d2LitsStandaloneDelta020.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta167Shift : polyRoundApx 128 d2Delta167Lo d2Delta167Hi d2Delta167Fq.poly = (d2Delta167S,d2Delta167Es) := by decide +kernel
theorem d2Delta167Sites : mergeSites d2Delta167Fq.plogs = [] := by decide +kernel
theorem d2Delta167PData : d2Delta167Pd = [] := by decide +kernel
theorem d2Delta167Plogs : plogsRoundM 16 24 20 128 d2Delta167Lo d2Delta167Hi (mergeSites d2Delta167Fq.plogs) d2Delta167Pd = some (d2Delta167Ap,d2Delta167Ep) := by
  rw [d2Delta167Sites,d2Delta167PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta167Poles : polesRoundM 16 24 12 128 d2Delta167Lo d2Delta167Hi d2Delta167Fq.poles d2Delta167Qd = some (d2Delta167Aq,d2Delta167Eq) := by decide +kernel
theorem d2Delta167Laurent : laurentRoundM 16 30 128 d2Delta167Lo d2Delta167Hi d2Delta167Ts d2Delta167Ld = some (d2Delta167Al,d2Delta167El) := by decide +kernel
theorem d2Delta167Small : chebPolyUB (vecAdd d2Delta167S (vecAdd d2Delta167Ap (vecAdd d2Delta167Aq d2Delta167Al))) d2Delta167Gam+d2Delta167Es+d2Delta167Ep+d2Delta167Eq+d2Delta167El ≤ (d2LitsStandaloneDelta020.q2 (-7377468589280621374437) 1 (-80)) := by decide +kernel
theorem d2Delta167Check : chebRoundPieceL d2Delta167Fq d2Delta167Ts 16 24 12 20 30 128 d2Delta167Lo d2Delta167Hi d2Delta167Pd d2Delta167Qd d2Delta167Ld d2Delta167Gam (d2LitsStandaloneDelta020.q2 (-7377468589280621374437) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta167Fq d2Delta167Ts 16 24 12 20 30 128 d2Delta167Lo d2Delta167Hi d2Delta167Pd d2Delta167Qd d2Delta167Ld d2Delta167Gam d2Delta167S d2Delta167Ap d2Delta167Aq d2Delta167Al d2Delta167Es d2Delta167Ep d2Delta167Eq d2Delta167El (by decide +kernel) d2Delta167Shift d2Delta167Plogs d2Delta167Poles d2Delta167Laurent]
  exact decide_eq_true d2Delta167Small
theorem d2Delta167Bound : ∀ x ∈ Icc ((d2Delta167Lo : ℚ) : ℝ) ((d2Delta167Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta020.q2 (-7377468589280621374437) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta167Fq d2Delta167Ts 16 24 12 20 30 128 d2Delta167Lo d2Delta167Hi d2Delta167Pd d2Delta167Qd d2Delta167Ld d2Delta167Gam (d2LitsStandaloneDelta020.q2 (-7377468589280621374437) 1 (-80)) d2Delta167Check
  simpa only [d2Delta167Fq, d2Delta167Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta167Shift
#print axioms d2Delta167Sites
#print axioms d2Delta167PData
#print axioms d2Delta167Plogs
#print axioms d2Delta167Poles
#print axioms d2Delta167Laurent
#print axioms d2Delta167Small
#print axioms d2Delta167Check
#print axioms d2Delta167Bound

end StandaloneDelta020
end CatalanMeasure.GenD.Signed.Data.Cells
