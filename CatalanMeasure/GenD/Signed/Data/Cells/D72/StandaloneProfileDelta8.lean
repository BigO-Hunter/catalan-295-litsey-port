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
set_option profiler true
set_option profiler.threshold 0
namespace decay2LitsStandaloneProfileDelta8
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end decay2LitsStandaloneProfileDelta8
def ceDeltaRawFq : FieldQ := ⟨decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% []))⟩
def ceDelta0Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta0Ts : List LTerm := laurentClean []
def ceDelta0Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (1) 1 (-10))
def ceDelta0Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (1571839) 1 (-29))
def ceDelta0Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta0Qd : List (ℚ × ℚ) := []
def ceDelta0Ld : List LaurentPieceData := []
def ceDelta0Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-4456679874713452401921326765657375892205114013, 1, -159, -284553030620882133154671837272107929598547, 1, -158, 44264120349345855809840100816424228063675, 1, -160, -780365116258430997698167528995574729611, 1, -160, 656871447873834354785543248487808779, 1, -157, 4863945369671033814069448308350549, 1, -158, -218367145159795597050339551891473, 1, -159, 349716286806983379281245536003, 1, -159, 8238329175316823304075478423, 1, -159, -30434790083737023173225183, 1, -159, -48922029527768144223899, 1, -157, 2103630638659368208225, 1, -160, 6416939323899494785, 1, -160, -47139517692141753, 1, -160, -36443198979015, 1, -159, 191377558217, 1, -158, -2422050493, 1, -160, -1265221875, 1, -159, -1914895631, 1, -160, -1625939317, 1, -160, -1216782691, 1, -160, -1021057635, 1, -160, -376181187, 1, -159, -623894229, 1, -160, -226182139, 1, -159, -185327589, 1, -159, -264302269, 1, -160, -213940165, 1, -160, -74977931, 1, -159, -119878831, 1, -160, -82559751, 1, -160, -65162425, 1, -160])
def ceDelta0S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-2075313592397571964175537975656390325, 1, -128, -132232779853598030990638815511405, 1, -127, 10301148642818826231155348764727, 1, -127, -726862238135134973255838404299, 1, -128, 9793028828288109756495624647, 1, -128, 72460188742832037911971739, 1, -128, -3254906216899180782445069, 1, -128, 2607630537459910796393, 1, -126, 491159333572563450881, 1, -128, -1814744566940642405, 1, -127, -23332431620728675, 1, -127, 501690750495759, 1, -128, 765080419993, 1, -126, -44966748229, 1, -128, -69513527, 1, -127, 1467667, 1, -127, 3911, 1, -128, -147, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def ceDelta0Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta0Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta0Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta0Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta0Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta0Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta0El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta0Shift : polyRoundApx 128 ceDelta0Lo ceDelta0Hi ceDelta0Fq.poly = (ceDelta0S,ceDelta0Es) := by decide +kernel
theorem ceDelta0Sites : mergeSites ceDelta0Fq.plogs = [] := by decide +kernel
theorem ceDelta0PData : ceDelta0Pd = [] := by decide +kernel
theorem ceDelta0Plogs : plogsRoundM 16 24 20 128 ceDelta0Lo ceDelta0Hi (mergeSites ceDelta0Fq.plogs) ceDelta0Pd = some (ceDelta0Ap,ceDelta0Ep) := by
  rw [ceDelta0Sites,ceDelta0PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta0Poles : polesRoundM 16 24 12 128 ceDelta0Lo ceDelta0Hi ceDelta0Fq.poles ceDelta0Qd = some (ceDelta0Aq,ceDelta0Eq) := by decide +kernel
theorem ceDelta0Laurent : laurentRoundM 16 30 128 ceDelta0Lo ceDelta0Hi ceDelta0Ts ceDelta0Ld = some (ceDelta0Al,ceDelta0El) := by decide +kernel
theorem ceDelta0Small : chebPolyUB (vecAdd ceDelta0S (vecAdd ceDelta0Ap (vecAdd ceDelta0Aq ceDelta0Al))) ceDelta0Gam+ceDelta0Es+ceDelta0Ep+ceDelta0Eq+ceDelta0El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-3685989803073705846221) 1 (-79)) := by decide +kernel
theorem ceDelta0Check : chebRoundPieceL ceDelta0Fq ceDelta0Ts 16 24 12 20 30 128 ceDelta0Lo ceDelta0Hi ceDelta0Pd ceDelta0Qd ceDelta0Ld ceDelta0Gam (decay2LitsStandaloneProfileDelta8.q2 (-3685989803073705846221) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta0Fq ceDelta0Ts 16 24 12 20 30 128 ceDelta0Lo ceDelta0Hi ceDelta0Pd ceDelta0Qd ceDelta0Ld ceDelta0Gam ceDelta0S ceDelta0Ap ceDelta0Aq ceDelta0Al ceDelta0Es ceDelta0Ep ceDelta0Eq ceDelta0El (by decide +kernel) ceDelta0Shift ceDelta0Plogs ceDelta0Poles ceDelta0Laurent]
  exact decide_eq_true ceDelta0Small
theorem ceDelta0Bound : ∀ x ∈ Icc ((ceDelta0Lo : ℚ) : ℝ) ((ceDelta0Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-3685989803073705846221) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta0Fq ceDelta0Ts 16 24 12 20 30 128 ceDelta0Lo ceDelta0Hi ceDelta0Pd ceDelta0Qd ceDelta0Ld ceDelta0Gam (decay2LitsStandaloneProfileDelta8.q2 (-3685989803073705846221) 1 (-79)) ceDelta0Check
  simpa only [ceDelta0Fq, ceDelta0Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta0Shift
#print axioms ceDelta0Sites
#print axioms ceDelta0PData
#print axioms ceDelta0Plogs
#print axioms ceDelta0Poles
#print axioms ceDelta0Laurent
#print axioms ceDelta0Small
#print axioms ceDelta0Check
#print axioms ceDelta0Bound

def ceDelta1Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta1Ts : List LTerm := laurentClean []
def ceDelta1Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (84853681) 1 (-31))
def ceDelta1Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (5368827) 1 (-27))
def ceDelta1Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta1Qd : List (ℚ × ℚ) := []
def ceDelta1Ld : List LaurentPieceData := []
def ceDelta1Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-278712562021143838649408257696948365646287469, 1, -155, -22922340972953579931208503121199236205, 1, -154, 7405353109539485496508720243133778409, 1, -158, 11949147843718961107376718776839505, 1, -157, -736686607288257919594969686299673, 1, -159, 196499569310332034116461867333, 1, -158, 10180130696451233429323214231, 1, -159, -6338942526633816466710999, 1, -157, -16288785742544084832803, 1, -160, 174161953214490471025, 1, -160, -21041197377650905, 1, -158, -37145243221543, 1, -157, 64406685981, 1, -158, -158046255, 1, -155, -4503917801, 1, -160, -1821168121, 1, -159, -3022707245, 1, -160, -2405273705, 1, -160, -1975756223, 1, -160, -1546500885, 1, -160, -1256828081, 1, -160, -967171661, 1, -160, -777522443, 1, -160, -73484153, 1, -157, -116864741, 1, -158, -347044705, 1, -160, -272945067, 1, -160, -99422715, 1, -159, -154675803, 1, -160, -1726659, 1, -154, -21254147, 1, -158, -7440875, 1, -157])
def ceDelta1S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-2076570413610778904639617640008326379, 1, -128, -341636267930020578696468895599, 1, -128, 13796289504626235553986203873, 1, -128, 89024428323282575570423007, 1, -128, -2744599015397289321897641, 1, -128, 2929394180794117033929, 1, -128, 75848369673798271383, 1, -127, -377842096118065565, 1, -127, -485418560518735, 1, -128, 2595264046525, 1, -126, -5016800777, 1, -127, -70848073, 1, -128, 125965, 1, -128, 305, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta1Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta1Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta1Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta1Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta1Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta1Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta1El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta1Shift : polyRoundApx 128 ceDelta1Lo ceDelta1Hi ceDelta1Fq.poly = (ceDelta1S,ceDelta1Es) := by decide +kernel
theorem ceDelta1Sites : mergeSites ceDelta1Fq.plogs = [] := by decide +kernel
theorem ceDelta1PData : ceDelta1Pd = [] := by decide +kernel
theorem ceDelta1Plogs : plogsRoundM 16 24 20 128 ceDelta1Lo ceDelta1Hi (mergeSites ceDelta1Fq.plogs) ceDelta1Pd = some (ceDelta1Ap,ceDelta1Ep) := by
  rw [ceDelta1Sites,ceDelta1PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta1Poles : polesRoundM 16 24 12 128 ceDelta1Lo ceDelta1Hi ceDelta1Fq.poles ceDelta1Qd = some (ceDelta1Aq,ceDelta1Eq) := by decide +kernel
theorem ceDelta1Laurent : laurentRoundM 16 30 128 ceDelta1Lo ceDelta1Hi ceDelta1Ts ceDelta1Ld = some (ceDelta1Al,ceDelta1El) := by decide +kernel
theorem ceDelta1Small : chebPolyUB (vecAdd ceDelta1S (vecAdd ceDelta1Ap (vecAdd ceDelta1Aq ceDelta1Al))) ceDelta1Gam+ceDelta1Es+ceDelta1Ep+ceDelta1Eq+ceDelta1El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-3688729425421386968615) 1 (-79)) := by decide +kernel
theorem ceDelta1Check : chebRoundPieceL ceDelta1Fq ceDelta1Ts 16 24 12 20 30 128 ceDelta1Lo ceDelta1Hi ceDelta1Pd ceDelta1Qd ceDelta1Ld ceDelta1Gam (decay2LitsStandaloneProfileDelta8.q2 (-3688729425421386968615) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta1Fq ceDelta1Ts 16 24 12 20 30 128 ceDelta1Lo ceDelta1Hi ceDelta1Pd ceDelta1Qd ceDelta1Ld ceDelta1Gam ceDelta1S ceDelta1Ap ceDelta1Aq ceDelta1Al ceDelta1Es ceDelta1Ep ceDelta1Eq ceDelta1El (by decide +kernel) ceDelta1Shift ceDelta1Plogs ceDelta1Poles ceDelta1Laurent]
  exact decide_eq_true ceDelta1Small
theorem ceDelta1Bound : ∀ x ∈ Icc ((ceDelta1Lo : ℚ) : ℝ) ((ceDelta1Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-3688729425421386968615) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta1Fq ceDelta1Ts 16 24 12 20 30 128 ceDelta1Lo ceDelta1Hi ceDelta1Pd ceDelta1Qd ceDelta1Ld ceDelta1Gam (decay2LitsStandaloneProfileDelta8.q2 (-3688729425421386968615) 1 (-79)) ceDelta1Check
  simpa only [ceDelta1Fq, ceDelta1Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta1Shift
#print axioms ceDelta1Sites
#print axioms ceDelta1PData
#print axioms ceDelta1Plogs
#print axioms ceDelta1Poles
#print axioms ceDelta1Laurent
#print axioms ceDelta1Small
#print axioms ceDelta1Check
#print axioms ceDelta1Bound

def ceDelta2Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta2Ts : List LTerm := laurentClean []
def ceDelta2Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (64424899) 1 (-29))
def ceDelta2Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (32736225) 1 (-28))
def ceDelta2Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta2Qd : List (ℚ × ℚ) := []
def ceDelta2Ld : List LaurentPieceData := []
def ceDelta2Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-1114849927146930933722413987661286253299437127, 1, -157, -40840286136972183801865419415633494373, 1, -154, 84752365932927161727620346780448276995, 1, -159, 1648505008750586667909320865225074229, 1, -160, -77884847170233341342436642536537843, 1, -160, -320785675978319394441785480228735, 1, -160, 13685462771005812576835781114393, 1, -160, 24612735374125574929186231181, 1, -160, -610594899833233793312534719, 1, -159, -41614833911205551532839, 1, -156, 63927555335002192998981, 1, -160, -15490369513950555639, 1, -160, -268158450395629313, 1, -157, 1664205662667191, 1, -160, 49151155554629, 1, -160, -60106839713, 1, -160, -3739657181, 1, -160, -2466300117, 1, -160, -238741199, 1, -157, -1587382853, 1, -160, -1211930319, 1, -160, -993236127, 1, -160, -747989429, 1, -160, -604138827, 1, -160, -112173705, 1, -158, -178525361, 1, -159, -130704223, 1, -159, -51235353, 1, -158, -73899287, 1, -159, -28547325, 1, -158, -40516833, 1, -159, -61729031, 1, -160])
def ceDelta2S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-1038284924202374865939828268374912023, 1, -127, -609719527860439046031011629855, 1, -128, 79076920842398344973895014435, 1, -128, 1536784024656515355031176777, 1, -128, -145224825244121202410631255, 1, -128, -1195661660665100297880051, 1, -128, 51018724318995570637101, 1, -127, 366847622817350743217, 1, -128, -36413347455101940325, 1, -128, -39676835556357007, 1, -128, 952978466919569, 1, -125, -3698351222359, 1, -128, -1023271493189, 1, -128, 1587922011, 1, -128, 93781455, 1, -128, -215125, 1, -128, -1545, 1, -126, 17, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta2Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta2Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta2Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta2Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta2Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta2Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta2El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta2Shift : polyRoundApx 128 ceDelta2Lo ceDelta2Hi ceDelta2Fq.poly = (ceDelta2S,ceDelta2Es) := by decide +kernel
theorem ceDelta2Sites : mergeSites ceDelta2Fq.plogs = [] := by decide +kernel
theorem ceDelta2PData : ceDelta2Pd = [] := by decide +kernel
theorem ceDelta2Plogs : plogsRoundM 16 24 20 128 ceDelta2Lo ceDelta2Hi (mergeSites ceDelta2Fq.plogs) ceDelta2Pd = some (ceDelta2Ap,ceDelta2Ep) := by
  rw [ceDelta2Sites,ceDelta2PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta2Poles : polesRoundM 16 24 12 128 ceDelta2Lo ceDelta2Hi ceDelta2Fq.poles ceDelta2Qd = some (ceDelta2Aq,ceDelta2Eq) := by decide +kernel
theorem ceDelta2Laurent : laurentRoundM 16 30 128 ceDelta2Lo ceDelta2Hi ceDelta2Ts ceDelta2Ld = some (ceDelta2Al,ceDelta2El) := by decide +kernel
theorem ceDelta2Small : chebPolyUB (vecAdd ceDelta2S (vecAdd ceDelta2Ap (vecAdd ceDelta2Aq ceDelta2Al))) ceDelta2Gam+ceDelta2Es+ceDelta2Ep+ceDelta2Eq+ceDelta2El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-3688727830715343089299) 1 (-79)) := by decide +kernel
theorem ceDelta2Check : chebRoundPieceL ceDelta2Fq ceDelta2Ts 16 24 12 20 30 128 ceDelta2Lo ceDelta2Hi ceDelta2Pd ceDelta2Qd ceDelta2Ld ceDelta2Gam (decay2LitsStandaloneProfileDelta8.q2 (-3688727830715343089299) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta2Fq ceDelta2Ts 16 24 12 20 30 128 ceDelta2Lo ceDelta2Hi ceDelta2Pd ceDelta2Qd ceDelta2Ld ceDelta2Gam ceDelta2S ceDelta2Ap ceDelta2Aq ceDelta2Al ceDelta2Es ceDelta2Ep ceDelta2Eq ceDelta2El (by decide +kernel) ceDelta2Shift ceDelta2Plogs ceDelta2Poles ceDelta2Laurent]
  exact decide_eq_true ceDelta2Small
theorem ceDelta2Bound : ∀ x ∈ Icc ((ceDelta2Lo : ℚ) : ℝ) ((ceDelta2Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-3688727830715343089299) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta2Fq ceDelta2Ts 16 24 12 20 30 128 ceDelta2Lo ceDelta2Hi ceDelta2Pd ceDelta2Qd ceDelta2Ld ceDelta2Gam (decay2LitsStandaloneProfileDelta8.q2 (-3688727830715343089299) 1 (-79)) ceDelta2Check
  simpa only [ceDelta2Fq, ceDelta2Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta2Shift
#print axioms ceDelta2Sites
#print axioms ceDelta2PData
#print axioms ceDelta2Plogs
#print axioms ceDelta2Poles
#print axioms ceDelta2Laurent
#print axioms ceDelta2Small
#print axioms ceDelta2Check
#print axioms ceDelta2Bound

def ceDelta3Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta3Ts : List LTerm := laurentClean []
def ceDelta3Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (22031339) 1 (-25))
def ceDelta3Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (11539445) 1 (-24))
def ceDelta3Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta3Qd : List (ℚ × ℚ) := []
def ceDelta3Ld : List LaurentPieceData := []
def ceDelta3Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-4459399017145843962239387308955938861614346579, 1, -159, 382853179563392030240237108217032300121, 1, -155, -2718962394038836193772148014443996578163, 1, -158, -42701188461920941800202846988770602468557, 1, -160, 727576645178617430292148128793728169353, 1, -158, 4513627837391335424375757143344891528767, 1, -160, -74423334041794563345197474922754779085, 1, -159, -99833823186689385640895716640761557801, 1, -159, 2132262336555235771434909750555134653, 1, -160, 4944802253649303746151602561738814375, 1, -160, 33568384483990541845889157163125311, 1, -160, -19406538641200394336710587052646989, 1, -158, -1688238703097722508228719740201589, 1, -160, 826717969510372693420838136343593, 1, -160, 29566434444532765308320376443129, 1, -160, -1549454577368494187579566171021, 1, -158, -39181246429793604767982761035, 1, -157, 16537128191333857282495746485, 1, -159, 285949305223036199311561725, 1, -157, -122305000643118912364806025, 1, -160, -12150566277465460119443897, 1, -160, 67948027773581587340013, 1, -158, 48228835924104811548089, 1, -160, -603976758751084501, 1, -154, -143963135712425302657, 1, -160, -1217507480314455819, 1, -159, 317098018456256129, 1, -160, 5620320875448755, 1, -159, -476281895260981, 1, -160, -30697570550579, 1, -160, 163125832347, 1, -159, 29142574305, 1, -159])
def ceDelta3S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-2076566241959083625090125369733222531, 1, -128, 38269452702303003887447546470631, 1, -128, -347643954649427851454200727447, 1, -123, -63532371362696740380129445167407, 1, -128, 3580162534558548644790784657765, 1, -127, 22541512049621843969963335229767, 1, -128, -612929032040107099778058636609, 1, -127, -3691289006114196510815070846723, 1, -128, 50633956326733612200722782695, 1, -128, 43616907898730042035143126661, 1, -125, 6701611528786773283225219927, 1, -128, -10603204210004674545902094931, 1, -127, -15914772758305871846725021, 1, -122, 880912030116394653864388947, 1, -128, 66567158120418569639913175, 1, -128, -25859565382202338990572081, 1, -128, -2721765330867866685880981, 1, -128, 16903616458534472324247, 1, -123, 4846395833750467240307, 1, -124, -7813546496696430749687, 1, -128, -1617250992839948970655, 1, -128, 1037542288863230571, 1, -122, 3160400144513002423, 1, -125, 6336190408020239, 1, -126, -297608262950546885, 1, -128, -10743354684856545, 1, -128, 2582530202736721, 1, -128, 189945596597643, 1, -128, -15181743516769, 1, -128, -1016978709729, 1, -127, 38542523463, 1, -128, 15221006687, 1, -128, 4678289, 1, -122, -19910487, 1, -126, -282605, 1, -124, 252767, 1, -128, 3905, 1, -125, -39, 1, -128, -137, 1, -128, -5, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta3Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta3Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta3Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta3Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta3Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta3Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta3El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta3Shift : polyRoundApx 128 ceDelta3Lo ceDelta3Hi ceDelta3Fq.poly = (ceDelta3S,ceDelta3Es) := by decide +kernel
theorem ceDelta3Sites : mergeSites ceDelta3Fq.plogs = [] := by decide +kernel
theorem ceDelta3PData : ceDelta3Pd = [] := by decide +kernel
theorem ceDelta3Plogs : plogsRoundM 16 24 20 128 ceDelta3Lo ceDelta3Hi (mergeSites ceDelta3Fq.plogs) ceDelta3Pd = some (ceDelta3Ap,ceDelta3Ep) := by
  rw [ceDelta3Sites,ceDelta3PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta3Poles : polesRoundM 16 24 12 128 ceDelta3Lo ceDelta3Hi ceDelta3Fq.poles ceDelta3Qd = some (ceDelta3Aq,ceDelta3Eq) := by decide +kernel
theorem ceDelta3Laurent : laurentRoundM 16 30 128 ceDelta3Lo ceDelta3Hi ceDelta3Ts ceDelta3Ld = some (ceDelta3Al,ceDelta3El) := by decide +kernel
theorem ceDelta3Small : chebPolyUB (vecAdd ceDelta3S (vecAdd ceDelta3Ap (vecAdd ceDelta3Aq ceDelta3Al))) ceDelta3Gam+ceDelta3Es+ceDelta3Ep+ceDelta3Eq+ceDelta3El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-461087245884294322201) 1 (-76)) := by decide +kernel
theorem ceDelta3Check : chebRoundPieceL ceDelta3Fq ceDelta3Ts 16 24 12 20 30 128 ceDelta3Lo ceDelta3Hi ceDelta3Pd ceDelta3Qd ceDelta3Ld ceDelta3Gam (decay2LitsStandaloneProfileDelta8.q2 (-461087245884294322201) 1 (-76)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta3Fq ceDelta3Ts 16 24 12 20 30 128 ceDelta3Lo ceDelta3Hi ceDelta3Pd ceDelta3Qd ceDelta3Ld ceDelta3Gam ceDelta3S ceDelta3Ap ceDelta3Aq ceDelta3Al ceDelta3Es ceDelta3Ep ceDelta3Eq ceDelta3El (by decide +kernel) ceDelta3Shift ceDelta3Plogs ceDelta3Poles ceDelta3Laurent]
  exact decide_eq_true ceDelta3Small
theorem ceDelta3Bound : ∀ x ∈ Icc ((ceDelta3Lo : ℚ) : ℝ) ((ceDelta3Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-461087245884294322201) 1 (-76)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta3Fq ceDelta3Ts 16 24 12 20 30 128 ceDelta3Lo ceDelta3Hi ceDelta3Pd ceDelta3Qd ceDelta3Ld ceDelta3Gam (decay2LitsStandaloneProfileDelta8.q2 (-461087245884294322201) 1 (-76)) ceDelta3Check
  simpa only [ceDelta3Fq, ceDelta3Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta3Shift
#print axioms ceDelta3Sites
#print axioms ceDelta3PData
#print axioms ceDelta3Plogs
#print axioms ceDelta3Poles
#print axioms ceDelta3Laurent
#print axioms ceDelta3Small
#print axioms ceDelta3Check
#print axioms ceDelta3Bound

def ceDelta4Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta4Ts : List LTerm := laurentClean []
def ceDelta4Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (2133863437) 1 (-31))
def ceDelta4Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (533727747) 1 (-29))
def ceDelta4Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta4Qd : List (ℚ × ℚ) := []
def ceDelta4Ld : List LaurentPieceData := []
def ceDelta4Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-34022619698425086896658584496029575175253, 1, -142, 1424578351585519947280948481577892053, 1, -144, -3517585399816701497368871143423919, 1, -143, -3085217905333368321768812061497147, 1, -144, -974686028593443425269898087511, 1, -140, 1045787211120317901723619288525, 1, -143, 8374022372061038233428585297, 1, -142, -167364244001049627892854471, 1, -143, -904756236254992923850639, 1, -140, -70885573124989197580063, 1, -143, 117516432446085783473, 1, -142, 14719858208895355117, 1, -143, 26689783421504919, 1, -140, 7944841618621783, 1, -145, 27697317818043, 1, -144, 308585377487, 1, -145, 177911185, 1, -142, 5563679, 1, -145, 9371, 1, -144, 55, 1, -145, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta4S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-2076575802217987594250245681830766059, 1, -128, 10939365123866687067706876368553, 1, -127, -106391741903208857201834046239, 1, -127, -23618167567357256467758118811, 1, -125, -1928252263168776172016662701, 1, -128, 511209397355851197977985587, 1, -128, 8206033860098970977018145, 1, -127, -325635989216753208107165, 1, -128, -14141384163301583110995, 1, -127, -555057519397067875875, 1, -128, 3632370498518744459, 1, -128, 229594444002985391, 1, -127, 6666388223446289, 1, -127, 124065835937511, 1, -127, 3460741595911, 1, -128, 38561350413, 1, -128, 355738031, 1, -128, 2781317, 1, -128, 9371, 1, -127, 55, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta4Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta4Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta4Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta4Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta4Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta4Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta4El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta4Shift : polyRoundApx 128 ceDelta4Lo ceDelta4Hi ceDelta4Fq.poly = (ceDelta4S,ceDelta4Es) := by decide +kernel
theorem ceDelta4Sites : mergeSites ceDelta4Fq.plogs = [] := by decide +kernel
theorem ceDelta4PData : ceDelta4Pd = [] := by decide +kernel
theorem ceDelta4Plogs : plogsRoundM 16 24 20 128 ceDelta4Lo ceDelta4Hi (mergeSites ceDelta4Fq.plogs) ceDelta4Pd = some (ceDelta4Ap,ceDelta4Ep) := by
  rw [ceDelta4Sites,ceDelta4PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta4Poles : polesRoundM 16 24 12 128 ceDelta4Lo ceDelta4Hi ceDelta4Fq.poles ceDelta4Qd = some (ceDelta4Aq,ceDelta4Eq) := by decide +kernel
theorem ceDelta4Laurent : laurentRoundM 16 30 128 ceDelta4Lo ceDelta4Hi ceDelta4Ts ceDelta4Ld = some (ceDelta4Al,ceDelta4El) := by decide +kernel
theorem ceDelta4Small : chebPolyUB (vecAdd ceDelta4S (vecAdd ceDelta4Ap (vecAdd ceDelta4Aq ceDelta4Al))) ceDelta4Gam+ceDelta4Es+ceDelta4Ep+ceDelta4Eq+ceDelta4El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-7377401862000940515285) 1 (-80)) := by decide +kernel
theorem ceDelta4Check : chebRoundPieceL ceDelta4Fq ceDelta4Ts 16 24 12 20 30 128 ceDelta4Lo ceDelta4Hi ceDelta4Pd ceDelta4Qd ceDelta4Ld ceDelta4Gam (decay2LitsStandaloneProfileDelta8.q2 (-7377401862000940515285) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta4Fq ceDelta4Ts 16 24 12 20 30 128 ceDelta4Lo ceDelta4Hi ceDelta4Pd ceDelta4Qd ceDelta4Ld ceDelta4Gam ceDelta4S ceDelta4Ap ceDelta4Aq ceDelta4Al ceDelta4Es ceDelta4Ep ceDelta4Eq ceDelta4El (by decide +kernel) ceDelta4Shift ceDelta4Plogs ceDelta4Poles ceDelta4Laurent]
  exact decide_eq_true ceDelta4Small
theorem ceDelta4Bound : ∀ x ∈ Icc ((ceDelta4Lo : ℚ) : ℝ) ((ceDelta4Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-7377401862000940515285) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta4Fq ceDelta4Ts 16 24 12 20 30 128 ceDelta4Lo ceDelta4Hi ceDelta4Pd ceDelta4Qd ceDelta4Ld ceDelta4Gam (decay2LitsStandaloneProfileDelta8.q2 (-7377401862000940515285) 1 (-80)) ceDelta4Check
  simpa only [ceDelta4Fq, ceDelta4Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta4Shift
#print axioms ceDelta4Sites
#print axioms ceDelta4PData
#print axioms ceDelta4Plogs
#print axioms ceDelta4Poles
#print axioms ceDelta4Laurent
#print axioms ceDelta4Small
#print axioms ceDelta4Check
#print axioms ceDelta4Bound

def ceDelta5Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta5Ts : List LTerm := laurentClean []
def ceDelta5Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (549754242049) 1 (-39))
def ceDelta5Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (1048575) 1 (-20))
def ceDelta5Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta5Qd : List (ℚ × ℚ) := []
def ceDelta5Ld : List LaurentPieceData := []
def ceDelta5Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-519127088030728256756228750180003679, 1, -126, 22693069828565367264379987769413, 1, -134, 6147959806774368886528275285, 1, -132, 12610101345543002476908337, 1, -134, 54717931707870669361, 1, -128, 592348305869516307, 1, -134, 16704050344571, 1, -132, 671521237, 1, -131, 5053, 1, -128, 15, 1, -134, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta5S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-2076508352507160460230382392260504043, 1, -128, 88644656243219892097126169675, 1, -126, 768494538103361239907155469, 1, -128, 197032787246899192807889, 1, -126, 437743403550815129655, 1, -128, 37021766766520465, 1, -126, 16704049697787, 1, -127, 5372169761, 1, -128, 5053, 1, -121, 15, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta5Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta5Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta5Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta5Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta5Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta5Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta5El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta5Shift : polyRoundApx 128 ceDelta5Lo ceDelta5Hi ceDelta5Fq.poly = (ceDelta5S,ceDelta5Es) := by decide +kernel
theorem ceDelta5Sites : mergeSites ceDelta5Fq.plogs = [] := by decide +kernel
theorem ceDelta5PData : ceDelta5Pd = [] := by decide +kernel
theorem ceDelta5Plogs : plogsRoundM 16 24 20 128 ceDelta5Lo ceDelta5Hi (mergeSites ceDelta5Fq.plogs) ceDelta5Pd = some (ceDelta5Ap,ceDelta5Ep) := by
  rw [ceDelta5Sites,ceDelta5PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta5Poles : polesRoundM 16 24 12 128 ceDelta5Lo ceDelta5Hi ceDelta5Fq.poles ceDelta5Qd = some (ceDelta5Aq,ceDelta5Eq) := by decide +kernel
theorem ceDelta5Laurent : laurentRoundM 16 30 128 ceDelta5Lo ceDelta5Hi ceDelta5Ts ceDelta5Ld = some (ceDelta5Al,ceDelta5El) := by decide +kernel
theorem ceDelta5Small : chebPolyUB (vecAdd ceDelta5S (vecAdd ceDelta5Ap (vecAdd ceDelta5Aq ceDelta5Al))) ceDelta5Gam+ceDelta5Es+ceDelta5Ep+ceDelta5Eq+ceDelta5El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-7377238365646307656955) 1 (-80)) := by decide +kernel
theorem ceDelta5Check : chebRoundPieceL ceDelta5Fq ceDelta5Ts 16 24 12 20 30 128 ceDelta5Lo ceDelta5Hi ceDelta5Pd ceDelta5Qd ceDelta5Ld ceDelta5Gam (decay2LitsStandaloneProfileDelta8.q2 (-7377238365646307656955) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta5Fq ceDelta5Ts 16 24 12 20 30 128 ceDelta5Lo ceDelta5Hi ceDelta5Pd ceDelta5Qd ceDelta5Ld ceDelta5Gam ceDelta5S ceDelta5Ap ceDelta5Aq ceDelta5Al ceDelta5Es ceDelta5Ep ceDelta5Eq ceDelta5El (by decide +kernel) ceDelta5Shift ceDelta5Plogs ceDelta5Poles ceDelta5Laurent]
  exact decide_eq_true ceDelta5Small
theorem ceDelta5Bound : ∀ x ∈ Icc ((ceDelta5Lo : ℚ) : ℝ) ((ceDelta5Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-7377238365646307656955) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta5Fq ceDelta5Ts 16 24 12 20 30 128 ceDelta5Lo ceDelta5Hi ceDelta5Pd ceDelta5Qd ceDelta5Ld ceDelta5Gam (decay2LitsStandaloneProfileDelta8.q2 (-7377238365646307656955) 1 (-80)) ceDelta5Check
  simpa only [ceDelta5Fq, ceDelta5Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta5Shift
#print axioms ceDelta5Sites
#print axioms ceDelta5PData
#print axioms ceDelta5Plogs
#print axioms ceDelta5Poles
#print axioms ceDelta5Laurent
#print axioms ceDelta5Small
#print axioms ceDelta5Check
#print axioms ceDelta5Bound

def ceDelta6Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta6Ts : List LTerm := laurentClean []
def ceDelta6Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta6Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (1) 1 (-10))
def ceDelta6Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta6Qd : List (ℚ × ℚ) := []
def ceDelta6Ld : List LaurentPieceData := []
def ceDelta6Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-2227869188001040753948661415259668319927103227, 1, -158, -712543811319191866063033871796282579326213, 1, -160, 6456712904743581956495176464086290992023, 1, -159, -52751426477345163867114965794312168165, 1, -159, 307794202576971306800790888169471125, 1, -160, 430606480916841866351930221577899, 1, -159, -7029367359615823808724039478415, 1, -160, 1124042610738857747145719555, 1, -159, 70692793969829157260669315, 1, -160, -47426157233287959065771, 1, -159, -450397633466686150967, 1, -160, 454240469667116287, 1, -159, 2022607744280799, 1, -160, -2683641188587, 1, -159, -2745055509, 1, -158, -3792179451, 1, -160, -2929742299, 1, -160, -631522141, 1, -158, -59731107, 1, -155, -814564245, 1, -159, -606907643, 1, -159, -511387441, 1, -159, -187489097, 1, -158, -312355983, 1, -159, -112637477, 1, -158, -185499977, 1, -159, -263024305, 1, -160, -214068699, 1, -160, -149111373, 1, -160, -3747533, 1, -155, -82034699, 1, -160, -65174581, 1, -160])
def ceDelta6S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-1037433937322601125452613281598025537, 1, -127, -165828340326966420598710814036879, 1, -128, 93948580393126894307040526245, 1, -122, -49130599474545315575229235399, 1, -127, 573389940327047186408704533, 1, -128, 3208209658697437286709571, 1, -128, -52377081794528112916691, 1, -128, 8377950386263104927, 1, -126, 2106943668585607277, 1, -128, -5654234177202023, 1, -128, -53694475333177, 1, -128, 216615355281, 1, -128, 120562709, 1, -125, -2556805, 1, -127, -12605, 1, -128, 43, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def ceDelta6Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta6Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta6Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta6Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta6Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta6Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta6El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta6Shift : polyRoundApx 128 ceDelta6Lo ceDelta6Hi ceDelta6Fq.poly = (ceDelta6S,ceDelta6Es) := by decide +kernel
theorem ceDelta6Sites : mergeSites ceDelta6Fq.plogs = [] := by decide +kernel
theorem ceDelta6PData : ceDelta6Pd = [] := by decide +kernel
theorem ceDelta6Plogs : plogsRoundM 16 24 20 128 ceDelta6Lo ceDelta6Hi (mergeSites ceDelta6Fq.plogs) ceDelta6Pd = some (ceDelta6Ap,ceDelta6Ep) := by
  rw [ceDelta6Sites,ceDelta6PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta6Poles : polesRoundM 16 24 12 128 ceDelta6Lo ceDelta6Hi ceDelta6Fq.poles ceDelta6Qd = some (ceDelta6Aq,ceDelta6Eq) := by decide +kernel
theorem ceDelta6Laurent : laurentRoundM 16 30 128 ceDelta6Lo ceDelta6Hi ceDelta6Ts ceDelta6Ld = some (ceDelta6Al,ceDelta6El) := by decide +kernel
theorem ceDelta6Small : chebPolyUB (vecAdd ceDelta6S (vecAdd ceDelta6Ap (vecAdd ceDelta6Aq ceDelta6Al))) ceDelta6Gam+ceDelta6Es+ceDelta6Ep+ceDelta6Eq+ceDelta6El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-7370800626787845804691) 1 (-80)) := by decide +kernel
theorem ceDelta6Check : chebRoundPieceL ceDelta6Fq ceDelta6Ts 16 24 12 20 30 128 ceDelta6Lo ceDelta6Hi ceDelta6Pd ceDelta6Qd ceDelta6Ld ceDelta6Gam (decay2LitsStandaloneProfileDelta8.q2 (-7370800626787845804691) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta6Fq ceDelta6Ts 16 24 12 20 30 128 ceDelta6Lo ceDelta6Hi ceDelta6Pd ceDelta6Qd ceDelta6Ld ceDelta6Gam ceDelta6S ceDelta6Ap ceDelta6Aq ceDelta6Al ceDelta6Es ceDelta6Ep ceDelta6Eq ceDelta6El (by decide +kernel) ceDelta6Shift ceDelta6Plogs ceDelta6Poles ceDelta6Laurent]
  exact decide_eq_true ceDelta6Small
theorem ceDelta6Bound : ∀ x ∈ Icc ((ceDelta6Lo : ℚ) : ℝ) ((ceDelta6Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-7370800626787845804691) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta6Fq ceDelta6Ts 16 24 12 20 30 128 ceDelta6Lo ceDelta6Hi ceDelta6Pd ceDelta6Qd ceDelta6Ld ceDelta6Gam (decay2LitsStandaloneProfileDelta8.q2 (-7370800626787845804691) 1 (-80)) ceDelta6Check
  simpa only [ceDelta6Fq, ceDelta6Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta6Shift
#print axioms ceDelta6Sites
#print axioms ceDelta6PData
#print axioms ceDelta6Plogs
#print axioms ceDelta6Poles
#print axioms ceDelta6Laurent
#print axioms ceDelta6Small
#print axioms ceDelta6Check
#print axioms ceDelta6Bound

def ceDelta7Fq : FieldQ := fieldClean ceDeltaRawFq
def ceDelta7Ts : List LTerm := laurentClean []
def ceDelta7Lo : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (1048575) 1 (-20))
def ceDelta7Hi : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (1) 1 (0))
def ceDelta7Pd : List (ℚ × (List ℚ × List ℚ)) := []
def ceDelta7Qd : List (ℚ × ℚ) := []
def ceDelta7Ld : List LaurentPieceData := []
def ceDelta7Gam : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-265793000785427159756120326681631925905, 1, -135, 5715832732887693478349011007351, 1, -133, 386779954413030281681643483, 1, -130, 793085337408272001534037, 1, -133, 110143928886673819495, 1, -133, 9319717814892111, 1, -133, 65745142357, 1, -130, 21159749, 1, -133, 2549, 1, -135, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta7S : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [-1038253909366422335377974930674194501, 1, -127, 178619698550991495378810398361, 1, -128, 193389949670533215025506837, 1, -128, 49567830675605201456873, 1, -127, 1720998839545421861, 1, -124, 2329929416693467, 1, -127, 262980566879, 1, -127, 21159749, 1, -127, 2549, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def ceDelta7Ap : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta7Aq : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta7Al : List ℚ := decay2LitsStandaloneProfileDelta8.q2listC (raw_ints% [])
def ceDelta7Es : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (61) 1 (-127))
def ceDelta7Ep : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta7Eq : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
def ceDelta7El : ℚ := (decay2LitsStandaloneProfileDelta8.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem ceDelta7Shift : polyRoundApx 128 ceDelta7Lo ceDelta7Hi ceDelta7Fq.poly = (ceDelta7S,ceDelta7Es) := by decide +kernel
theorem ceDelta7Sites : mergeSites ceDelta7Fq.plogs = [] := by decide +kernel
theorem ceDelta7PData : ceDelta7Pd = [] := by decide +kernel
theorem ceDelta7Plogs : plogsRoundM 16 24 20 128 ceDelta7Lo ceDelta7Hi (mergeSites ceDelta7Fq.plogs) ceDelta7Pd = some (ceDelta7Ap,ceDelta7Ep) := by
  rw [ceDelta7Sites,ceDelta7PData]
  simp only [plogsRoundM]
  decide +kernel
theorem ceDelta7Poles : polesRoundM 16 24 12 128 ceDelta7Lo ceDelta7Hi ceDelta7Fq.poles ceDelta7Qd = some (ceDelta7Aq,ceDelta7Eq) := by decide +kernel
theorem ceDelta7Laurent : laurentRoundM 16 30 128 ceDelta7Lo ceDelta7Hi ceDelta7Ts ceDelta7Ld = some (ceDelta7Al,ceDelta7El) := by decide +kernel
theorem ceDelta7Small : chebPolyUB (vecAdd ceDelta7S (vecAdd ceDelta7Ap (vecAdd ceDelta7Aq ceDelta7Al))) ceDelta7Gam+ceDelta7Es+ceDelta7Ep+ceDelta7Eq+ceDelta7El ≤ (decay2LitsStandaloneProfileDelta8.q2 (-7377237096476310565023) 1 (-80)) := by decide +kernel
theorem ceDelta7Check : chebRoundPieceL ceDelta7Fq ceDelta7Ts 16 24 12 20 30 128 ceDelta7Lo ceDelta7Hi ceDelta7Pd ceDelta7Qd ceDelta7Ld ceDelta7Gam (decay2LitsStandaloneProfileDelta8.q2 (-7377237096476310565023) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts ceDelta7Fq ceDelta7Ts 16 24 12 20 30 128 ceDelta7Lo ceDelta7Hi ceDelta7Pd ceDelta7Qd ceDelta7Ld ceDelta7Gam ceDelta7S ceDelta7Ap ceDelta7Aq ceDelta7Al ceDelta7Es ceDelta7Ep ceDelta7Eq ceDelta7El (by decide +kernel) ceDelta7Shift ceDelta7Plogs ceDelta7Poles ceDelta7Laurent]
  exact decide_eq_true ceDelta7Small
theorem ceDelta7Bound : ∀ x ∈ Icc ((ceDelta7Lo : ℚ) : ℝ) ((ceDelta7Hi : ℚ) : ℝ), fieldTower ceDeltaRawFq (poleF ceDeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((decay2LitsStandaloneProfileDelta8.q2 (-7377237096476310565023) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound ceDelta7Fq ceDelta7Ts 16 24 12 20 30 128 ceDelta7Lo ceDelta7Hi ceDelta7Pd ceDelta7Qd ceDelta7Ld ceDelta7Gam (decay2LitsStandaloneProfileDelta8.q2 (-7377237096476310565023) 1 (-80)) ceDelta7Check
  simpa only [ceDelta7Fq, ceDelta7Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms ceDelta7Shift
#print axioms ceDelta7Sites
#print axioms ceDelta7PData
#print axioms ceDelta7Plogs
#print axioms ceDelta7Poles
#print axioms ceDelta7Laurent
#print axioms ceDelta7Small
#print axioms ceDelta7Check
#print axioms ceDelta7Bound

end CatalanMeasure.GenD.Signed.Data.Cells
