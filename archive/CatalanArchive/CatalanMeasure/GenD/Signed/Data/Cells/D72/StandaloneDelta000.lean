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
namespace d2LitsStandaloneDelta000
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta000
namespace StandaloneDelta000
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta000.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta000.q2listC (raw_ints% []))⟩
def d2Delta0Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta0Ts : List LTerm := laurentClean []
def d2Delta0Lo : ℚ := (d2LitsStandaloneDelta000.q2 (1) 1 (-10))
def d2Delta0Hi : ℚ := (d2LitsStandaloneDelta000.q2 (1571839) 1 (-29))
def d2Delta0Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta0Qd : List (ℚ × ℚ) := []
def d2Delta0Ld : List LaurentPieceData := []
def d2Delta0Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-4456679874713452401921326765657375892205114013, 1, -159, -284553030620882133154671837272107929598547, 1, -158, 44264120349345855809840100816424228063675, 1, -160, -780365116258430997698167528995574729611, 1, -160, 656871447873834354785543248487808779, 1, -157, 4863945369671033814069448308350549, 1, -158, -218367145159795597050339551891473, 1, -159, 349716286806983379281245536003, 1, -159, 8238329175316823304075478423, 1, -159, -30434790083737023173225183, 1, -159, -48922029527768144223899, 1, -157, 2103630638659368208225, 1, -160, 6416939323899494785, 1, -160, -47139517692141753, 1, -160, -36443198979015, 1, -159, 191377558217, 1, -158, -2422050493, 1, -160, -1265221875, 1, -159, -1914895631, 1, -160, -1625939317, 1, -160, -1216782691, 1, -160, -1021057635, 1, -160, -376181187, 1, -159, -623894229, 1, -160, -226182139, 1, -159, -185327589, 1, -159, -264302269, 1, -160, -213940165, 1, -160, -74977931, 1, -159, -119878831, 1, -160, -82559751, 1, -160, -65162425, 1, -160])
def d2Delta0S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-2075313592397571964175537975656390325, 1, -128, -132232779853598030990638815511405, 1, -127, 10301148642818826231155348764727, 1, -127, -726862238135134973255838404299, 1, -128, 9793028828288109756495624647, 1, -128, 72460188742832037911971739, 1, -128, -3254906216899180782445069, 1, -128, 2607630537459910796393, 1, -126, 491159333572563450881, 1, -128, -1814744566940642405, 1, -127, -23332431620728675, 1, -127, 501690750495759, 1, -128, 765080419993, 1, -126, -44966748229, 1, -128, -69513527, 1, -127, 1467667, 1, -127, 3911, 1, -128, -147, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta0Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta0Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta0Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta0Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta0Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta0Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta0El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta0Shift : polyRoundApx 128 d2Delta0Lo d2Delta0Hi d2Delta0Fq.poly = (d2Delta0S,d2Delta0Es) := by decide +kernel
theorem d2Delta0Sites : mergeSites d2Delta0Fq.plogs = [] := by decide +kernel
theorem d2Delta0PData : d2Delta0Pd = [] := by decide +kernel
theorem d2Delta0Plogs : plogsRoundM 16 24 20 128 d2Delta0Lo d2Delta0Hi (mergeSites d2Delta0Fq.plogs) d2Delta0Pd = some (d2Delta0Ap,d2Delta0Ep) := by
  rw [d2Delta0Sites,d2Delta0PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta0Poles : polesRoundM 16 24 12 128 d2Delta0Lo d2Delta0Hi d2Delta0Fq.poles d2Delta0Qd = some (d2Delta0Aq,d2Delta0Eq) := by decide +kernel
theorem d2Delta0Laurent : laurentRoundM 16 30 128 d2Delta0Lo d2Delta0Hi d2Delta0Ts d2Delta0Ld = some (d2Delta0Al,d2Delta0El) := by decide +kernel
theorem d2Delta0Small : chebPolyUB (vecAdd d2Delta0S (vecAdd d2Delta0Ap (vecAdd d2Delta0Aq d2Delta0Al))) d2Delta0Gam+d2Delta0Es+d2Delta0Ep+d2Delta0Eq+d2Delta0El ≤ (d2LitsStandaloneDelta000.q2 (-3685989803073705846221) 1 (-79)) := by decide +kernel
theorem d2Delta0Check : chebRoundPieceL d2Delta0Fq d2Delta0Ts 16 24 12 20 30 128 d2Delta0Lo d2Delta0Hi d2Delta0Pd d2Delta0Qd d2Delta0Ld d2Delta0Gam (d2LitsStandaloneDelta000.q2 (-3685989803073705846221) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta0Fq d2Delta0Ts 16 24 12 20 30 128 d2Delta0Lo d2Delta0Hi d2Delta0Pd d2Delta0Qd d2Delta0Ld d2Delta0Gam d2Delta0S d2Delta0Ap d2Delta0Aq d2Delta0Al d2Delta0Es d2Delta0Ep d2Delta0Eq d2Delta0El (by decide +kernel) d2Delta0Shift d2Delta0Plogs d2Delta0Poles d2Delta0Laurent]
  exact decide_eq_true d2Delta0Small
theorem d2Delta0Bound : ∀ x ∈ Icc ((d2Delta0Lo : ℚ) : ℝ) ((d2Delta0Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-3685989803073705846221) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta0Fq d2Delta0Ts 16 24 12 20 30 128 d2Delta0Lo d2Delta0Hi d2Delta0Pd d2Delta0Qd d2Delta0Ld d2Delta0Gam (d2LitsStandaloneDelta000.q2 (-3685989803073705846221) 1 (-79)) d2Delta0Check
  simpa only [d2Delta0Fq, d2Delta0Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta0Shift
#print axioms d2Delta0Sites
#print axioms d2Delta0PData
#print axioms d2Delta0Plogs
#print axioms d2Delta0Poles
#print axioms d2Delta0Laurent
#print axioms d2Delta0Small
#print axioms d2Delta0Check
#print axioms d2Delta0Bound

def d2Delta1Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta1Ts : List LTerm := laurentClean []
def d2Delta1Lo : ℚ := (d2LitsStandaloneDelta000.q2 (1571839) 1 (-29))
def d2Delta1Hi : ℚ := (d2LitsStandaloneDelta000.q2 (1309695) 1 (-28))
def d2Delta1Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta1Qd : List (ℚ × ℚ) := []
def d2Delta1Ld : List LaurentPieceData := []
def d2Delta1Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-8915310688441983208666913949000396497536180953, 1, -160, -410050711452710906240995091080663209630447, 1, -159, 35415232991699618159914604821766948651077, 1, -160, -693734443859813713070203618437835711737, 1, -160, 1385289060239550203954006937026051775, 1, -158, 9266619241458155593523776198816187, 1, -160, -410118529107792511724712236274363, 1, -160, 1188789449650550540043050506191, 1, -160, 14026629800617235568831832831, 1, -160, -74591649425801770655259931, 1, -160, -292921927780407498432209, 1, -160, 2351384740220166668789, 1, -160, 1941097965629021813, 1, -159, -12478984331616571, 1, -158, -26161136586775, 1, -160, 777483122263, 1, -160, -768605619, 1, -158, -315653331, 1, -157, -479592507, 1, -158, -811547357, 1, -159, -1219823869, 1, -160, -509826669, 1, -159, -754778149, 1, -160, -311644227, 1, -159, -454141741, 1, -160, -370427029, 1, -160, -132760837, 1, -159, -106932713, 1, -159, -150739125, 1, -160, -119857675, 1, -160, -83032079, 1, -160, -16289325, 1, -158])
def d2Delta1S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-2075765770425416653689658858079981929, 1, -128, -95230081729715266445449806138019, 1, -127, 1030073753658350032827610399509, 1, -124, -161533420977818507218497444893, 1, -126, 10325791747644711448356150875, 1, -128, 34489839155804371584592035, 1, -128, -3056457284084705528306221, 1, -128, 17724348276318588299629, 1, -128, 418113447115990907731, 1, -128, -4447550648611467703, 1, -128, -8731142167618035, 1, -126, 560768536963537, 1, -128, 925674943439, 1, -127, -47614719477, 1, -128, -24942939, 1, -127, 2980965, 1, -128, -1043, 1, -128, -9, 1, -124, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta1Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta1Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta1Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta1Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta1Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta1Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta1El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta1Shift : polyRoundApx 128 d2Delta1Lo d2Delta1Hi d2Delta1Fq.poly = (d2Delta1S,d2Delta1Es) := by decide +kernel
theorem d2Delta1Sites : mergeSites d2Delta1Fq.plogs = [] := by decide +kernel
theorem d2Delta1PData : d2Delta1Pd = [] := by decide +kernel
theorem d2Delta1Plogs : plogsRoundM 16 24 20 128 d2Delta1Lo d2Delta1Hi (mergeSites d2Delta1Fq.plogs) d2Delta1Pd = some (d2Delta1Ap,d2Delta1Ep) := by
  rw [d2Delta1Sites,d2Delta1PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta1Poles : polesRoundM 16 24 12 128 d2Delta1Lo d2Delta1Hi d2Delta1Fq.poles d2Delta1Qd = some (d2Delta1Aq,d2Delta1Eq) := by decide +kernel
theorem d2Delta1Laurent : laurentRoundM 16 30 128 d2Delta1Lo d2Delta1Hi d2Delta1Ts d2Delta1Ld = some (d2Delta1Al,d2Delta1El) := by decide +kernel
theorem d2Delta1Small : chebPolyUB (vecAdd d2Delta1S (vecAdd d2Delta1Ap (vecAdd d2Delta1Aq d2Delta1Al))) d2Delta1Gam+d2Delta1Es+d2Delta1Ep+d2Delta1Eq+d2Delta1El ≤ (d2LitsStandaloneDelta000.q2 (-7373863911139295599495) 1 (-80)) := by decide +kernel
theorem d2Delta1Check : chebRoundPieceL d2Delta1Fq d2Delta1Ts 16 24 12 20 30 128 d2Delta1Lo d2Delta1Hi d2Delta1Pd d2Delta1Qd d2Delta1Ld d2Delta1Gam (d2LitsStandaloneDelta000.q2 (-7373863911139295599495) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta1Fq d2Delta1Ts 16 24 12 20 30 128 d2Delta1Lo d2Delta1Hi d2Delta1Pd d2Delta1Qd d2Delta1Ld d2Delta1Gam d2Delta1S d2Delta1Ap d2Delta1Aq d2Delta1Al d2Delta1Es d2Delta1Ep d2Delta1Eq d2Delta1El (by decide +kernel) d2Delta1Shift d2Delta1Plogs d2Delta1Poles d2Delta1Laurent]
  exact decide_eq_true d2Delta1Small
theorem d2Delta1Bound : ∀ x ∈ Icc ((d2Delta1Lo : ℚ) : ℝ) ((d2Delta1Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-7373863911139295599495) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta1Fq d2Delta1Ts 16 24 12 20 30 128 d2Delta1Lo d2Delta1Hi d2Delta1Pd d2Delta1Qd d2Delta1Ld d2Delta1Gam (d2LitsStandaloneDelta000.q2 (-7373863911139295599495) 1 (-80)) d2Delta1Check
  simpa only [d2Delta1Fq, d2Delta1Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta1Shift
#print axioms d2Delta1Sites
#print axioms d2Delta1PData
#print axioms d2Delta1Plogs
#print axioms d2Delta1Poles
#print axioms d2Delta1Laurent
#print axioms d2Delta1Small
#print axioms d2Delta1Check
#print axioms d2Delta1Bound

def d2Delta2Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta2Ts : List LTerm := laurentClean []
def d2Delta2Lo : ℚ := (d2LitsStandaloneDelta000.q2 (1309695) 1 (-28))
def d2Delta2Hi : ℚ := (d2LitsStandaloneDelta000.q2 (6286331) 1 (-30))
def d2Delta2Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta2Qd : List (ℚ × ℚ) := []
def d2Delta2Ld : List LaurentPieceData := []
def d2Delta2Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-1114551954561731826704394137408153328392201395, 1, -157, -156065494372231231971350312723216046291763, 1, -159, 3682003597085545383636785987709247999125, 1, -159, -39164963869943702836699172680926869631, 1, -159, 351733685121788808870026478540271533, 1, -160, 66312844509588096875498569116155, 1, -160, -2983334073247064615399402723009, 1, -159, 5862982690378027251468186971, 1, -159, 46509057598697049894339349, 1, -160, -160576953807405192954683, 1, -160, -208424300645429912089, 1, -160, 299856250833984549, 1, -158, 234806138303393, 1, -159, -6144341415007, 1, -160, -4088072335, 1, -160, -942214449, 1, -158, -96925559, 1, -155, -2511189255, 1, -160, -2027561599, 1, -160, -1620686587, 1, -160, -1289141279, 1, -160, -1018585217, 1, -160, -199164347, 1, -158, -622881233, 1, -160, -239104633, 1, -159, -370294121, 1, -160, -69667621, 1, -158, -213828585, 1, -160, -78781897, 1, -159, -119849107, 1, -160, -86394901, 1, -160, -65155657, 1, -160])
def d2Delta2S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-1038008253107465469847605075199911075, 1, -127, -72618946114033614839569436487719, 1, -128, 1714238944866193026178219639055, 1, -127, -18237684653127012054602336977, 1, -126, 327610863429363208714587739, 1, -127, 15420550111740058020483, 1, -124, -22228957065380446339819, 1, -127, 87376018063098037393, 1, -127, 1386140044542036529, 1, -128, -9571918718906909, 1, -128, -12423392297199, 1, -127, 285984234163, 1, -128, 111964119, 1, -127, -5854707, 1, -128, 1011, 1, -128, 11, 1, -125, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta2Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta2Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta2Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta2Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta2Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta2Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta2El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta2Shift : polyRoundApx 128 d2Delta2Lo d2Delta2Hi d2Delta2Fq.poly = (d2Delta2S,d2Delta2Es) := by decide +kernel
theorem d2Delta2Sites : mergeSites d2Delta2Fq.plogs = [] := by decide +kernel
theorem d2Delta2PData : d2Delta2Pd = [] := by decide +kernel
theorem d2Delta2Plogs : plogsRoundM 16 24 20 128 d2Delta2Lo d2Delta2Hi (mergeSites d2Delta2Fq.plogs) d2Delta2Pd = some (d2Delta2Ap,d2Delta2Ep) := by
  rw [d2Delta2Sites,d2Delta2PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta2Poles : polesRoundM 16 24 12 128 d2Delta2Lo d2Delta2Hi d2Delta2Fq.poles d2Delta2Qd = some (d2Delta2Aq,d2Delta2Eq) := by decide +kernel
theorem d2Delta2Laurent : laurentRoundM 16 30 128 d2Delta2Lo d2Delta2Hi d2Delta2Ts d2Delta2Ld = some (d2Delta2Al,d2Delta2El) := by decide +kernel
theorem d2Delta2Small : chebPolyUB (vecAdd d2Delta2S (vecAdd d2Delta2Ap (vecAdd d2Delta2Aq d2Delta2Al))) d2Delta2Gam+d2Delta2Es+d2Delta2Ep+d2Delta2Eq+d2Delta2El ≤ (d2LitsStandaloneDelta000.q2 (-7375221802821927963011) 1 (-80)) := by decide +kernel
theorem d2Delta2Check : chebRoundPieceL d2Delta2Fq d2Delta2Ts 16 24 12 20 30 128 d2Delta2Lo d2Delta2Hi d2Delta2Pd d2Delta2Qd d2Delta2Ld d2Delta2Gam (d2LitsStandaloneDelta000.q2 (-7375221802821927963011) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta2Fq d2Delta2Ts 16 24 12 20 30 128 d2Delta2Lo d2Delta2Hi d2Delta2Pd d2Delta2Qd d2Delta2Ld d2Delta2Gam d2Delta2S d2Delta2Ap d2Delta2Aq d2Delta2Al d2Delta2Es d2Delta2Ep d2Delta2Eq d2Delta2El (by decide +kernel) d2Delta2Shift d2Delta2Plogs d2Delta2Poles d2Delta2Laurent]
  exact decide_eq_true d2Delta2Small
theorem d2Delta2Bound : ∀ x ∈ Icc ((d2Delta2Lo : ℚ) : ℝ) ((d2Delta2Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-7375221802821927963011) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta2Fq d2Delta2Ts 16 24 12 20 30 128 d2Delta2Lo d2Delta2Hi d2Delta2Pd d2Delta2Qd d2Delta2Ld d2Delta2Gam (d2LitsStandaloneDelta000.q2 (-7375221802821927963011) 1 (-80)) d2Delta2Check
  simpa only [d2Delta2Fq, d2Delta2Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta2Shift
#print axioms d2Delta2Sites
#print axioms d2Delta2PData
#print axioms d2Delta2Plogs
#print axioms d2Delta2Poles
#print axioms d2Delta2Laurent
#print axioms d2Delta2Small
#print axioms d2Delta2Check
#print axioms d2Delta2Bound

def d2Delta3Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta3Ts : List LTerm := laurentClean []
def d2Delta3Lo : ℚ := (d2LitsStandaloneDelta000.q2 (6286331) 1 (-30))
def d2Delta3Hi : ℚ := (d2LitsStandaloneDelta000.q2 (3666941) 1 (-29))
def d2Delta3Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta3Qd : List (ℚ × ℚ) := []
def d2Delta3Ld : List LaurentPieceData := []
def d2Delta3Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-8916983895383224370486025666967290245026622301, 1, -160, -1003449395890932346918811512691445128199, 1, -152, 3228916685242185670926753246628093796733, 1, -159, -36349622335073436888418346084532843307, 1, -159, 175827691219959742757364242494098241, 1, -159, -9098060785248045447782572048715, 1, -157, -5618384972539815630843932253453, 1, -160, 13120257440859457877208059979, 1, -160, 1268468516187761720069651, 1, -155, -83926466554545252125599, 1, -159, -155266155101274507537, 1, -160, 607163051094208457, 1, -159, 151844663219745, 1, -160, -1518937750145, 1, -158, -2483797453, 1, -160, -1857972537, 1, -159, -2945936251, 1, -160, -2489418621, 1, -160, -962945979, 1, -159, -1612911361, 1, -160, -613053051, 1, -159, -127021527, 1, -157, -47473617, 1, -156, -311118883, 1, -159, -457530305, 1, -160, -185074411, 1, -159, -133872875, 1, -159, -213801341, 1, -160, -152101427, 1, -160, -119844979, 1, -160, -83812691, 1, -160, -16288793, 1, -158])
def d2Delta3S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-129759287707055538397862755625961419, 1, -124, -29879732520561958070912261835397, 1, -127, 1503253983889822254723673552219, 1, -127, -33853054309276316328069479025, 1, -127, 655071984159913543783835727, 1, -128, -271485494882587633832933, 1, -128, -20931324757316306728541, 1, -127, 195529582659732333161, 1, -128, 1209752118222679665, 1, -128, -2501402662558319, 1, -126, -18509385246979, 1, -128, 289536720681, 1, -128, 72395485, 1, -128, -5789397, 1, -128, 3639, 1, -128, 43, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta3Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta3Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta3Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta3Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta3Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta3Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta3El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta3Shift : polyRoundApx 128 d2Delta3Lo d2Delta3Hi d2Delta3Fq.poly = (d2Delta3S,d2Delta3Es) := by decide +kernel
theorem d2Delta3Sites : mergeSites d2Delta3Fq.plogs = [] := by decide +kernel
theorem d2Delta3PData : d2Delta3Pd = [] := by decide +kernel
theorem d2Delta3Plogs : plogsRoundM 16 24 20 128 d2Delta3Lo d2Delta3Hi (mergeSites d2Delta3Fq.plogs) d2Delta3Pd = some (d2Delta3Ap,d2Delta3Ep) := by
  rw [d2Delta3Sites,d2Delta3PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta3Poles : polesRoundM 16 24 12 128 d2Delta3Lo d2Delta3Hi d2Delta3Fq.poles d2Delta3Qd = some (d2Delta3Aq,d2Delta3Eq) := by decide +kernel
theorem d2Delta3Laurent : laurentRoundM 16 30 128 d2Delta3Lo d2Delta3Hi d2Delta3Ts d2Delta3Ld = some (d2Delta3Al,d2Delta3El) := by decide +kernel
theorem d2Delta3Small : chebPolyUB (vecAdd d2Delta3S (vecAdd d2Delta3Ap (vecAdd d2Delta3Aq d2Delta3Al))) d2Delta3Gam+d2Delta3Es+d2Delta3Ep+d2Delta3Eq+d2Delta3El ≤ (d2LitsStandaloneDelta000.q2 (-921967288726607073627) 1 (-77)) := by decide +kernel
theorem d2Delta3Check : chebRoundPieceL d2Delta3Fq d2Delta3Ts 16 24 12 20 30 128 d2Delta3Lo d2Delta3Hi d2Delta3Pd d2Delta3Qd d2Delta3Ld d2Delta3Gam (d2LitsStandaloneDelta000.q2 (-921967288726607073627) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta3Fq d2Delta3Ts 16 24 12 20 30 128 d2Delta3Lo d2Delta3Hi d2Delta3Pd d2Delta3Qd d2Delta3Ld d2Delta3Gam d2Delta3S d2Delta3Ap d2Delta3Aq d2Delta3Al d2Delta3Es d2Delta3Ep d2Delta3Eq d2Delta3El (by decide +kernel) d2Delta3Shift d2Delta3Plogs d2Delta3Poles d2Delta3Laurent]
  exact decide_eq_true d2Delta3Small
theorem d2Delta3Bound : ∀ x ∈ Icc ((d2Delta3Lo : ℚ) : ℝ) ((d2Delta3Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-921967288726607073627) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta3Fq d2Delta3Ts 16 24 12 20 30 128 d2Delta3Lo d2Delta3Hi d2Delta3Pd d2Delta3Qd d2Delta3Ld d2Delta3Gam (d2LitsStandaloneDelta000.q2 (-921967288726607073627) 1 (-77)) d2Delta3Check
  simpa only [d2Delta3Fq, d2Delta3Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta3Shift
#print axioms d2Delta3Sites
#print axioms d2Delta3PData
#print axioms d2Delta3Plogs
#print axioms d2Delta3Poles
#print axioms d2Delta3Laurent
#print axioms d2Delta3Small
#print axioms d2Delta3Check
#print axioms d2Delta3Bound

def d2Delta4Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta4Ts : List LTerm := laurentClean []
def d2Delta4Lo : ℚ := (d2LitsStandaloneDelta000.q2 (3666941) 1 (-29))
def d2Delta4Hi : ℚ := (d2LitsStandaloneDelta000.q2 (8381433) 1 (-30))
def d2Delta4Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta4Qd : List (ℚ × ℚ) := []
def d2Delta4Ld : List LaurentPieceData := []
def d2Delta4Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-4458724346981473082934228507848210565029643003, 1, -159, -26076806183141566817747100502117882605357, 1, -157, 2809564964410959285630254729002189162313, 1, -159, -67091602969284596426067968314140937395, 1, -160, 348881771788034143474851932209754707, 1, -160, -101538082909545219414668163414763, 1, -159, -2616874679862311554447023846309, 1, -159, 14321391849531203988035460849, 1, -160, 17224691646075252092570729, 1, -159, -5406060858424847862523, 1, -155, -101786313112318833951, 1, -160, 303522918935522383, 1, -158, -160380951043789, 1, -160, -5931650941231, 1, -160, -1163813295, 1, -160, -3762888499, 1, -160, -1475210851, 1, -159, -1253535243, 1, -159, -482473869, 1, -158, -404698829, 1, -158, -19208039, 1, -154, -508926673, 1, -159, -95240523, 1, -157, -155660889, 1, -158, -229555189, 1, -159, -92557495, 1, -158, -67182729, 1, -158, -213814431, 1, -160, -152671999, 1, -160, -119846615, 1, -160, -84120247, 1, -160, -65155321, 1, -160])
def d2Delta4S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-519064156847539589636446030521160869, 1, -126, -48524973837590255110537725267575, 1, -128, 2615961411330136938247678618931, 1, -128, -62482978578611114244197771197, 1, -128, 324950716433287827628972709, 1, -127, -94611393396261718624415, 1, -125, -19498262399261680650427, 1, -127, 53357142390606510719, 1, -126, 1026701961357016687, 1, -128, -10312038830715787, 1, -128, -379176394491, 1, -123, 289480382135, 1, -128, -76494129, 1, -128, -2825929, 1, -127, 6165, 1, -128, 41, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta4Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta4Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta4Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta4Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta4Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta4Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta4El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta4Shift : polyRoundApx 128 d2Delta4Lo d2Delta4Hi d2Delta4Fq.poly = (d2Delta4S,d2Delta4Es) := by decide +kernel
theorem d2Delta4Sites : mergeSites d2Delta4Fq.plogs = [] := by decide +kernel
theorem d2Delta4PData : d2Delta4Pd = [] := by decide +kernel
theorem d2Delta4Plogs : plogsRoundM 16 24 20 128 d2Delta4Lo d2Delta4Hi (mergeSites d2Delta4Fq.plogs) d2Delta4Pd = some (d2Delta4Ap,d2Delta4Ep) := by
  rw [d2Delta4Sites,d2Delta4PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta4Poles : polesRoundM 16 24 12 128 d2Delta4Lo d2Delta4Hi d2Delta4Fq.poles d2Delta4Qd = some (d2Delta4Aq,d2Delta4Eq) := by decide +kernel
theorem d2Delta4Laurent : laurentRoundM 16 30 128 d2Delta4Lo d2Delta4Hi d2Delta4Ts d2Delta4Ld = some (d2Delta4Al,d2Delta4El) := by decide +kernel
theorem d2Delta4Small : chebPolyUB (vecAdd d2Delta4S (vecAdd d2Delta4Ap (vecAdd d2Delta4Aq d2Delta4Al))) d2Delta4Gam+d2Delta4Es+d2Delta4Ep+d2Delta4Eq+d2Delta4El ≤ (d2LitsStandaloneDelta000.q2 (-7376163407433400112089) 1 (-80)) := by decide +kernel
theorem d2Delta4Check : chebRoundPieceL d2Delta4Fq d2Delta4Ts 16 24 12 20 30 128 d2Delta4Lo d2Delta4Hi d2Delta4Pd d2Delta4Qd d2Delta4Ld d2Delta4Gam (d2LitsStandaloneDelta000.q2 (-7376163407433400112089) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta4Fq d2Delta4Ts 16 24 12 20 30 128 d2Delta4Lo d2Delta4Hi d2Delta4Pd d2Delta4Qd d2Delta4Ld d2Delta4Gam d2Delta4S d2Delta4Ap d2Delta4Aq d2Delta4Al d2Delta4Es d2Delta4Ep d2Delta4Eq d2Delta4El (by decide +kernel) d2Delta4Shift d2Delta4Plogs d2Delta4Poles d2Delta4Laurent]
  exact decide_eq_true d2Delta4Small
theorem d2Delta4Bound : ∀ x ∈ Icc ((d2Delta4Lo : ℚ) : ℝ) ((d2Delta4Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-7376163407433400112089) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta4Fq d2Delta4Ts 16 24 12 20 30 128 d2Delta4Lo d2Delta4Hi d2Delta4Pd d2Delta4Qd d2Delta4Ld d2Delta4Gam (d2LitsStandaloneDelta000.q2 (-7376163407433400112089) 1 (-80)) d2Delta4Check
  simpa only [d2Delta4Fq, d2Delta4Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta4Shift
#print axioms d2Delta4Sites
#print axioms d2Delta4PData
#print axioms d2Delta4Plogs
#print axioms d2Delta4Poles
#print axioms d2Delta4Laurent
#print axioms d2Delta4Small
#print axioms d2Delta4Check
#print axioms d2Delta4Bound

def d2Delta5Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta5Ts : List LTerm := laurentClean []
def d2Delta5Lo : ℚ := (d2LitsStandaloneDelta000.q2 (8381433) 1 (-30))
def d2Delta5Hi : ℚ := (d2LitsStandaloneDelta000.q2 (17810417) 1 (-31))
def d2Delta5Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta5Qd : List (ℚ × ℚ) := []
def d2Delta5Ld : List LaurentPieceData := []
def d2Delta5Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-8917741286081895615726930398945581031720788339, 1, -160, -44131954083492471206364200224510877285473, 1, -159, 39320659409661148722590801849992654213, 1, -155, -7865633593176649408521005964161746179, 1, -160, 10786414785240477085619713121429729, 1, -159, -4603204712722094849091358750259, 1, -159, -76951500321747808728883268553, 1, -160, 117914155949608124281107033, 1, -160, 58092241191436385723869, 1, -159, -42836377872110741831, 1, -157, -60408956424258555, 1, -160, 147001059554563, 1, -158, -25393265747, 1, -158, -6182806175, 1, -160, -4609383375, 1, -160, -3745817207, 1, -160, -1546322371, 1, -159, -1246593165, 1, -159, -2019557827, 1, -160, -403630817, 1, -158, -1282730365, 1, -160, -508372889, 1, -159, -395985305, 1, -159, -155601555, 1, -158, -475053379, 1, -160, -92547265, 1, -158, -276702417, 1, -160, -213808975, 1, -160, -156423293, 1, -160, -119846087, 1, -160, -85779473, 1, -160, -8144411, 1, -157])
def d2Delta5S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-1038161868266927057220785885745356831, 1, -127, -10272524239523136638326065015723, 1, -127, 585883301262887880884698627795, 1, -128, -3662699628378596959409756339, 1, -127, 40183386359003516521652823, 1, -128, -34299622601973041341733, 1, -128, -17916883760998298953, 1, -123, 1757103803674690025, 1, -128, 3462585403538697, 1, -128, -10213181112537, 1, -127, -450073245, 1, -124, 70097589, 1, -127, -11311, 1, -126, -21, 1, -123, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta5Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta5Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta5Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta5Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta5Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta5Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta5El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta5Shift : polyRoundApx 128 d2Delta5Lo d2Delta5Hi d2Delta5Fq.poly = (d2Delta5S,d2Delta5Es) := by decide +kernel
theorem d2Delta5Sites : mergeSites d2Delta5Fq.plogs = [] := by decide +kernel
theorem d2Delta5PData : d2Delta5Pd = [] := by decide +kernel
theorem d2Delta5Plogs : plogsRoundM 16 24 20 128 d2Delta5Lo d2Delta5Hi (mergeSites d2Delta5Fq.plogs) d2Delta5Pd = some (d2Delta5Ap,d2Delta5Ep) := by
  rw [d2Delta5Sites,d2Delta5PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta5Poles : polesRoundM 16 24 12 128 d2Delta5Lo d2Delta5Hi d2Delta5Fq.poles d2Delta5Qd = some (d2Delta5Aq,d2Delta5Eq) := by decide +kernel
theorem d2Delta5Laurent : laurentRoundM 16 30 128 d2Delta5Lo d2Delta5Hi d2Delta5Ts d2Delta5Ld = some (d2Delta5Al,d2Delta5El) := by decide +kernel
theorem d2Delta5Small : chebPolyUB (vecAdd d2Delta5S (vecAdd d2Delta5Ap (vecAdd d2Delta5Aq d2Delta5Al))) d2Delta5Gam+d2Delta5Es+d2Delta5Ep+d2Delta5Eq+d2Delta5El ≤ (d2LitsStandaloneDelta000.q2 (-7376508642083683048963) 1 (-80)) := by decide +kernel
theorem d2Delta5Check : chebRoundPieceL d2Delta5Fq d2Delta5Ts 16 24 12 20 30 128 d2Delta5Lo d2Delta5Hi d2Delta5Pd d2Delta5Qd d2Delta5Ld d2Delta5Gam (d2LitsStandaloneDelta000.q2 (-7376508642083683048963) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta5Fq d2Delta5Ts 16 24 12 20 30 128 d2Delta5Lo d2Delta5Hi d2Delta5Pd d2Delta5Qd d2Delta5Ld d2Delta5Gam d2Delta5S d2Delta5Ap d2Delta5Aq d2Delta5Al d2Delta5Es d2Delta5Ep d2Delta5Eq d2Delta5El (by decide +kernel) d2Delta5Shift d2Delta5Plogs d2Delta5Poles d2Delta5Laurent]
  exact decide_eq_true d2Delta5Small
theorem d2Delta5Bound : ∀ x ∈ Icc ((d2Delta5Lo : ℚ) : ℝ) ((d2Delta5Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-7376508642083683048963) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta5Fq d2Delta5Ts 16 24 12 20 30 128 d2Delta5Lo d2Delta5Hi d2Delta5Pd d2Delta5Qd d2Delta5Ld d2Delta5Gam (d2LitsStandaloneDelta000.q2 (-7376508642083683048963) 1 (-80)) d2Delta5Check
  simpa only [d2Delta5Fq, d2Delta5Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta5Shift
#print axioms d2Delta5Sites
#print axioms d2Delta5PData
#print axioms d2Delta5Plogs
#print axioms d2Delta5Poles
#print axioms d2Delta5Laurent
#print axioms d2Delta5Small
#print axioms d2Delta5Check
#print axioms d2Delta5Bound

def d2Delta6Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta6Ts : List LTerm := laurentClean []
def d2Delta6Lo : ℚ := (d2LitsStandaloneDelta000.q2 (17810417) 1 (-31))
def d2Delta6Hi : ℚ := (d2LitsStandaloneDelta000.q2 (36668385) 1 (-32))
def d2Delta6Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta6Qd : List (ℚ × ℚ) := []
def d2Delta6Ld : List LaurentPieceData := []
def d2Delta6Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-8917869051173869443605167430322355065181479283, 1, -160, -20226753234218831269272985556587376196705, 1, -159, 9285690037360580202428189810659995013, 1, -155, -950948893241314639734528223794988291, 1, -160, 669524830938212458910367554447585, 1, -159, -165151703147857441940955264563, 1, -159, -1163241460822620034300513225, 1, -160, 942138232568832258847321, 1, -160, 208809183570767848925, 1, -159, -84037514269321543, 1, -157, -40112258515963, 1, -160, 69349389571, 1, -158, -1680243795, 1, -158, -5479211679, 1, -160, -4609383375, 1, -160, -3745817207, 1, -160, -1546322371, 1, -159, -1246593165, 1, -159, -2019557827, 1, -160, -403630817, 1, -158, -1282730365, 1, -160, -508372889, 1, -159, -395985305, 1, -159, -155601555, 1, -158, -475053379, 1, -160, -92547265, 1, -158, -276702417, 1, -160, -213808975, 1, -160, -156423293, 1, -160, -119846087, 1, -160, -85779473, 1, -160, -8144411, 1, -157])
def d2Delta6S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-259544157548650737977546395404077513, 1, -125, -9418151719358158814972038528383, 1, -128, 138365069863582905823705873333, 1, -128, -885638633473863085485181067, 1, -128, 2494187357525419859009025, 1, -128, -76906290203680980611, 1, -124, -4333424574773612797, 1, -127, 7019521916526003, 1, -127, 12446009164479, 1, -128, -40072395837, 1, -128, -4780583, 1, -128, 67999, 1, -128, -15, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta6Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta6Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta6Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta6Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta6Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta6Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta6El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta6Shift : polyRoundApx 128 d2Delta6Lo d2Delta6Hi d2Delta6Fq.poly = (d2Delta6S,d2Delta6Es) := by decide +kernel
theorem d2Delta6Sites : mergeSites d2Delta6Fq.plogs = [] := by decide +kernel
theorem d2Delta6PData : d2Delta6Pd = [] := by decide +kernel
theorem d2Delta6Plogs : plogsRoundM 16 24 20 128 d2Delta6Lo d2Delta6Hi (mergeSites d2Delta6Fq.plogs) d2Delta6Pd = some (d2Delta6Ap,d2Delta6Ep) := by
  rw [d2Delta6Sites,d2Delta6PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta6Poles : polesRoundM 16 24 12 128 d2Delta6Lo d2Delta6Hi d2Delta6Fq.poles d2Delta6Qd = some (d2Delta6Aq,d2Delta6Eq) := by decide +kernel
theorem d2Delta6Laurent : laurentRoundM 16 30 128 d2Delta6Lo d2Delta6Hi d2Delta6Ts d2Delta6Ld = some (d2Delta6Al,d2Delta6El) := by decide +kernel
theorem d2Delta6Small : chebPolyUB (vecAdd d2Delta6S (vecAdd d2Delta6Ap (vecAdd d2Delta6Aq d2Delta6Al))) d2Delta6Gam+d2Delta6Es+d2Delta6Ep+d2Delta6Eq+d2Delta6El ≤ (d2LitsStandaloneDelta000.q2 (-3688327337741772707043) 1 (-79)) := by decide +kernel
theorem d2Delta6Check : chebRoundPieceL d2Delta6Fq d2Delta6Ts 16 24 12 20 30 128 d2Delta6Lo d2Delta6Hi d2Delta6Pd d2Delta6Qd d2Delta6Ld d2Delta6Gam (d2LitsStandaloneDelta000.q2 (-3688327337741772707043) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta6Fq d2Delta6Ts 16 24 12 20 30 128 d2Delta6Lo d2Delta6Hi d2Delta6Pd d2Delta6Qd d2Delta6Ld d2Delta6Gam d2Delta6S d2Delta6Ap d2Delta6Aq d2Delta6Al d2Delta6Es d2Delta6Ep d2Delta6Eq d2Delta6El (by decide +kernel) d2Delta6Shift d2Delta6Plogs d2Delta6Poles d2Delta6Laurent]
  exact decide_eq_true d2Delta6Small
theorem d2Delta6Bound : ∀ x ∈ Icc ((d2Delta6Lo : ℚ) : ℝ) ((d2Delta6Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-3688327337741772707043) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta6Fq d2Delta6Ts 16 24 12 20 30 128 d2Delta6Lo d2Delta6Hi d2Delta6Pd d2Delta6Qd d2Delta6Ld d2Delta6Gam (d2LitsStandaloneDelta000.q2 (-3688327337741772707043) 1 (-79)) d2Delta6Check
  simpa only [d2Delta6Fq, d2Delta6Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta6Shift
#print axioms d2Delta6Sites
#print axioms d2Delta6PData
#print axioms d2Delta6Plogs
#print axioms d2Delta6Poles
#print axioms d2Delta6Laurent
#print axioms d2Delta6Small
#print axioms d2Delta6Check
#print axioms d2Delta6Bound

def d2Delta7Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta7Ts : List LTerm := laurentClean []
def d2Delta7Lo : ℚ := (d2LitsStandaloneDelta000.q2 (36668385) 1 (-32))
def d2Delta7Hi : ℚ := (d2LitsStandaloneDelta000.q2 (74384321) 1 (-33))
def d2Delta7Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta7Qd : List (ℚ × ℚ) := []
def d2Delta7Ld : List LaurentPieceData := []
def d2Delta7Gam : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-1114741078475065763043897430642666931718549795, 1, -157, -9673516387068143494209532629231774629543, 1, -159, 72162938055550387693115309932079738331, 1, -160, -116863669278334509094662832327358967, 1, -160, 41685754090823417883861243334447, 1, -159, -5485438311852844799606083161, 1, -159, -17864925912862710316294137, 1, -160, 7437091172513895965221, 1, -160, 1560357533658560889, 1, -160, -328794075615689, 1, -158, -39053743849, 1, -160, -981239505, 1, -157, -6392741311, 1, -160, -5559851979, 1, -160, -1100216703, 1, -158, -3777372107, 1, -160, -2955213371, 1, -160, -1251852315, 1, -159, -967022487, 1, -159, -202183549, 1, -157, -616269019, 1, -159, -508712711, 1, -159, -382102321, 1, -159, -38908255, 1, -156, -230295969, 1, -159, -5784485, 1, -154, -134809631, 1, -159, -213810835, 1, -160, -76582521, 1, -159, -119846211, 1, -160, -84373953, 1, -160, -16288823, 1, -158])
def d2Delta7S : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [-1038183539635895377534385836211458941, 1, -127, -4504500465277420920336143989605, 1, -128, 33603331339246070360574290739, 1, -128, -13604715283011001447488617, 1, -125, 155291734954777211130277, 1, -128, -40869894189310844063, 1, -128, -16638020422052697, 1, -125, 55410735376337, 1, -127, 46502287569, 1, -128, -9798755, 1, -125, -3575, 1, -128, 33, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0])
def d2Delta7Ap : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta7Aq : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta7Al : List ℚ := d2LitsStandaloneDelta000.q2listC (raw_ints% [])
def d2Delta7Es : ℚ := (d2LitsStandaloneDelta000.q2 (61) 1 (-127))
def d2Delta7Ep : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta7Eq : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
def d2Delta7El : ℚ := (d2LitsStandaloneDelta000.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta7Shift : polyRoundApx 128 d2Delta7Lo d2Delta7Hi d2Delta7Fq.poly = (d2Delta7S,d2Delta7Es) := by decide +kernel
theorem d2Delta7Sites : mergeSites d2Delta7Fq.plogs = [] := by decide +kernel
theorem d2Delta7PData : d2Delta7Pd = [] := by decide +kernel
theorem d2Delta7Plogs : plogsRoundM 16 24 20 128 d2Delta7Lo d2Delta7Hi (mergeSites d2Delta7Fq.plogs) d2Delta7Pd = some (d2Delta7Ap,d2Delta7Ep) := by
  rw [d2Delta7Sites,d2Delta7PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta7Poles : polesRoundM 16 24 12 128 d2Delta7Lo d2Delta7Hi d2Delta7Fq.poles d2Delta7Qd = some (d2Delta7Aq,d2Delta7Eq) := by decide +kernel
theorem d2Delta7Laurent : laurentRoundM 16 30 128 d2Delta7Lo d2Delta7Hi d2Delta7Ts d2Delta7Ld = some (d2Delta7Al,d2Delta7El) := by decide +kernel
theorem d2Delta7Small : chebPolyUB (vecAdd d2Delta7S (vecAdd d2Delta7Ap (vecAdd d2Delta7Aq d2Delta7Al))) d2Delta7Gam+d2Delta7Es+d2Delta7Ep+d2Delta7Eq+d2Delta7El ≤ (d2LitsStandaloneDelta000.q2 (-1844180400442319974681) 1 (-78)) := by decide +kernel
theorem d2Delta7Check : chebRoundPieceL d2Delta7Fq d2Delta7Ts 16 24 12 20 30 128 d2Delta7Lo d2Delta7Hi d2Delta7Pd d2Delta7Qd d2Delta7Ld d2Delta7Gam (d2LitsStandaloneDelta000.q2 (-1844180400442319974681) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta7Fq d2Delta7Ts 16 24 12 20 30 128 d2Delta7Lo d2Delta7Hi d2Delta7Pd d2Delta7Qd d2Delta7Ld d2Delta7Gam d2Delta7S d2Delta7Ap d2Delta7Aq d2Delta7Al d2Delta7Es d2Delta7Ep d2Delta7Eq d2Delta7El (by decide +kernel) d2Delta7Shift d2Delta7Plogs d2Delta7Poles d2Delta7Laurent]
  exact decide_eq_true d2Delta7Small
theorem d2Delta7Bound : ∀ x ∈ Icc ((d2Delta7Lo : ℚ) : ℝ) ((d2Delta7Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta000.q2 (-1844180400442319974681) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta7Fq d2Delta7Ts 16 24 12 20 30 128 d2Delta7Lo d2Delta7Hi d2Delta7Pd d2Delta7Qd d2Delta7Ld d2Delta7Gam (d2LitsStandaloneDelta000.q2 (-1844180400442319974681) 1 (-78)) d2Delta7Check
  simpa only [d2Delta7Fq, d2Delta7Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta7Shift
#print axioms d2Delta7Sites
#print axioms d2Delta7PData
#print axioms d2Delta7Plogs
#print axioms d2Delta7Poles
#print axioms d2Delta7Laurent
#print axioms d2Delta7Small
#print axioms d2Delta7Check
#print axioms d2Delta7Bound

end StandaloneDelta000
end CatalanMeasure.GenD.Signed.Data.Cells
