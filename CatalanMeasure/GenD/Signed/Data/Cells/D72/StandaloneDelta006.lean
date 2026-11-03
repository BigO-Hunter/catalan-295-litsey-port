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
namespace d2LitsStandaloneDelta006
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta006
namespace StandaloneDelta006
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta006.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta006.q2listC (raw_ints% []))⟩
def d2Delta48Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta48Ts : List LTerm := laurentClean []
def d2Delta48Lo : ℚ := (d2LitsStandaloneDelta006.q2 (30903267) 1 (-29))
def d2Delta48Hi : ℚ := (d2LitsStandaloneDelta006.q2 (62854085) 1 (-30))
def d2Delta48Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta48Qd : List (ℚ × ℚ) := []
def d2Delta48Ld : List LaurentPieceData := []
def d2Delta48Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-8918687114759436473615677370561296972251481299, 1, -160, 2669618860127061560320903393647519466835, 1, -160, -87806821687541547942049612671672702007, 1, -160, -525074487975798726883965257072414145, 1, -160, 12117465040468210170813584593495575, 1, -160, 6963819525695778455681360634071, 1, -159, -624799852075112045053586701535, 1, -160, 852548314044114921061981349, 1, -160, 12962401014822705878206177, 1, -160, -38031946124529834379253, 1, -160, -23842524171569955015, 1, -158, 447962138956869537, 1, -160, 148274505278639, 1, -159, -2904521863875, 1, -160, -4464655139, 1, -160, -1883279893, 1, -159, -1563494971, 1, -159, -2489989335, 1, -160, -1026484727, 1, -159, -399106197, 1, -158, -1311980967, 1, -160, -497693655, 1, -159, -815516053, 1, -160, -603213365, 1, -160, -246347469, 1, -159, -355061855, 1, -160, -289102627, 1, -160, -101431003, 1, -159, -82322347, 1, -159, -28106987, 1, -158, -90941595, 1, -160, -7550203, 1, -157])
def d2Delta48S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-2076543641029972745157044065846970705, 1, -128, 621935854019414641188594582435, 1, -128, -40910810777502828398366239303, 1, -128, -489078568512795777087095743, 1, -128, 5644380160995502805109303, 1, -126, 51862262883395735665771, 1, -128, -4655894299009570663163, 1, -128, 12709060628265474903, 1, -128, 96584519235815549, 1, -126, -2267174356971377, 1, -128, -2842356423497, 1, -126, 106811483933, 1, -128, 70703809, 1, -127, -2764821, 1, -128, 167, 1, -127, 47, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta48Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta48Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta48Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta48Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta48Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta48Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta48El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta48Shift : polyRoundApx 128 d2Delta48Lo d2Delta48Hi d2Delta48Fq.poly = (d2Delta48S,d2Delta48Es) := by decide +kernel
theorem d2Delta48Sites : mergeSites d2Delta48Fq.plogs = [] := by decide +kernel
theorem d2Delta48PData : d2Delta48Pd = [] := by decide +kernel
theorem d2Delta48Plogs : plogsRoundM 16 24 20 128 d2Delta48Lo d2Delta48Hi (mergeSites d2Delta48Fq.plogs) d2Delta48Pd = some (d2Delta48Ap,d2Delta48Ep) := by
  rw [d2Delta48Sites,d2Delta48PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta48Poles : polesRoundM 16 24 12 128 d2Delta48Lo d2Delta48Hi d2Delta48Fq.poles d2Delta48Qd = some (d2Delta48Aq,d2Delta48Eq) := by decide +kernel
theorem d2Delta48Laurent : laurentRoundM 16 30 128 d2Delta48Lo d2Delta48Hi d2Delta48Ts d2Delta48Ld = some (d2Delta48Al,d2Delta48El) := by decide +kernel
theorem d2Delta48Small : chebPolyUB (vecAdd d2Delta48S (vecAdd d2Delta48Ap (vecAdd d2Delta48Aq d2Delta48Al))) d2Delta48Gam+d2Delta48Es+d2Delta48Ep+d2Delta48Eq+d2Delta48El ≤ (d2LitsStandaloneDelta006.q2 (-3688681394711037166591) 1 (-79)) := by decide +kernel
theorem d2Delta48Check : chebRoundPieceL d2Delta48Fq d2Delta48Ts 16 24 12 20 30 128 d2Delta48Lo d2Delta48Hi d2Delta48Pd d2Delta48Qd d2Delta48Ld d2Delta48Gam (d2LitsStandaloneDelta006.q2 (-3688681394711037166591) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta48Fq d2Delta48Ts 16 24 12 20 30 128 d2Delta48Lo d2Delta48Hi d2Delta48Pd d2Delta48Qd d2Delta48Ld d2Delta48Gam d2Delta48S d2Delta48Ap d2Delta48Aq d2Delta48Al d2Delta48Es d2Delta48Ep d2Delta48Eq d2Delta48El (by decide +kernel) d2Delta48Shift d2Delta48Plogs d2Delta48Poles d2Delta48Laurent]
  exact decide_eq_true d2Delta48Small
theorem d2Delta48Bound : ∀ x ∈ Icc ((d2Delta48Lo : ℚ) : ℝ) ((d2Delta48Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-3688681394711037166591) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta48Fq d2Delta48Ts 16 24 12 20 30 128 d2Delta48Lo d2Delta48Hi d2Delta48Pd d2Delta48Qd d2Delta48Ld d2Delta48Gam (d2LitsStandaloneDelta006.q2 (-3688681394711037166591) 1 (-79)) d2Delta48Check
  simpa only [d2Delta48Fq, d2Delta48Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta48Shift
#print axioms d2Delta48Sites
#print axioms d2Delta48PData
#print axioms d2Delta48Plogs
#print axioms d2Delta48Poles
#print axioms d2Delta48Laurent
#print axioms d2Delta48Small
#print axioms d2Delta48Check
#print axioms d2Delta48Bound

def d2Delta49Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta49Ts : List LTerm := laurentClean []
def d2Delta49Lo : ℚ := (d2LitsStandaloneDelta006.q2 (62854085) 1 (-30))
def d2Delta49Hi : ℚ := (d2LitsStandaloneDelta006.q2 (15975409) 1 (-28))
def d2Delta49Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta49Qd : List (ℚ × ℚ) := []
def d2Delta49Ld : List LaurentPieceData := []
def d2Delta49Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-8918682495591918843316491084513636122161923283, 1, -160, 1945272582064648010551828458745220188789, 1, -160, -92937861641530474499762706358987707447, 1, -160, -41221552624716216186652780657477303, 1, -157, 12248236216709118835699802685679127, 1, -160, -367759790733022058567218822675, 1, -159, -595332197253328323931790900447, 1, -160, 622370635315746817928418357, 1, -159, 11529368874738685453469409, 1, -160, -20724445088862893030937, 1, -159, -18849931895558078663, 1, -158, 28661714087001631, 1, -156, 73211159471279, 1, -159, -179616973877, 1, -156, -3725409059, 1, -160, -3763239023, 1, -160, -1563494971, 1, -159, -2488985081, 1, -160, -1026484727, 1, -159, -798543613, 1, -159, -1311980967, 1, -160, -498381125, 1, -159, -815516053, 1, -160, -604632769, 1, -160, -246347469, 1, -159, -89050245, 1, -158, -289102627, 1, -160, -101823263, 1, -159, -82322347, 1, -159, -28227727, 1, -158, -90941595, 1, -160, -30336547, 1, -159])
def d2Delta49S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-2076542564351532694470505409015410891, 1, -128, 113287352470292810494464995911, 1, -126, -43300380904493647647115728239, 1, -128, -307121058900096564091578351, 1, -128, 11410385780487010536874447, 1, -127, -2772487288399827202307, 1, -128, -2218128870589036860807, 1, -127, 1159603084271203365, 1, -124, 171812219618579771, 1, -127, -308855882480179, 1, -125, -8988557416287, 1, -128, 109344654641, 1, -128, 34908349, 1, -127, -2735593, 1, -128, 109, 1, -124, 23, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta49Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta49Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta49Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta49Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta49Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta49Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta49El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta49Shift : polyRoundApx 128 d2Delta49Lo d2Delta49Hi d2Delta49Fq.poly = (d2Delta49S,d2Delta49Es) := by decide +kernel
theorem d2Delta49Sites : mergeSites d2Delta49Fq.plogs = [] := by decide +kernel
theorem d2Delta49PData : d2Delta49Pd = [] := by decide +kernel
theorem d2Delta49Plogs : plogsRoundM 16 24 20 128 d2Delta49Lo d2Delta49Hi (mergeSites d2Delta49Fq.plogs) d2Delta49Pd = some (d2Delta49Ap,d2Delta49Ep) := by
  rw [d2Delta49Sites,d2Delta49PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta49Poles : polesRoundM 16 24 12 128 d2Delta49Lo d2Delta49Hi d2Delta49Fq.poles d2Delta49Qd = some (d2Delta49Aq,d2Delta49Eq) := by decide +kernel
theorem d2Delta49Laurent : laurentRoundM 16 30 128 d2Delta49Lo d2Delta49Hi d2Delta49Ts d2Delta49Ld = some (d2Delta49Al,d2Delta49El) := by decide +kernel
theorem d2Delta49Small : chebPolyUB (vecAdd d2Delta49S (vecAdd d2Delta49Ap (vecAdd d2Delta49Aq d2Delta49Al))) d2Delta49Gam+d2Delta49Es+d2Delta49Ep+d2Delta49Eq+d2Delta49El ≤ (d2LitsStandaloneDelta006.q2 (-922169945452326459879) 1 (-77)) := by decide +kernel
theorem d2Delta49Check : chebRoundPieceL d2Delta49Fq d2Delta49Ts 16 24 12 20 30 128 d2Delta49Lo d2Delta49Hi d2Delta49Pd d2Delta49Qd d2Delta49Ld d2Delta49Gam (d2LitsStandaloneDelta006.q2 (-922169945452326459879) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta49Fq d2Delta49Ts 16 24 12 20 30 128 d2Delta49Lo d2Delta49Hi d2Delta49Pd d2Delta49Qd d2Delta49Ld d2Delta49Gam d2Delta49S d2Delta49Ap d2Delta49Aq d2Delta49Al d2Delta49Es d2Delta49Ep d2Delta49Eq d2Delta49El (by decide +kernel) d2Delta49Shift d2Delta49Plogs d2Delta49Poles d2Delta49Laurent]
  exact decide_eq_true d2Delta49Small
theorem d2Delta49Bound : ∀ x ∈ Icc ((d2Delta49Lo : ℚ) : ℝ) ((d2Delta49Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-922169945452326459879) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta49Fq d2Delta49Ts 16 24 12 20 30 128 d2Delta49Lo d2Delta49Hi d2Delta49Pd d2Delta49Qd d2Delta49Ld d2Delta49Gam (d2LitsStandaloneDelta006.q2 (-922169945452326459879) 1 (-77)) d2Delta49Check
  simpa only [d2Delta49Fq, d2Delta49Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta49Shift
#print axioms d2Delta49Sites
#print axioms d2Delta49PData
#print axioms d2Delta49Plogs
#print axioms d2Delta49Poles
#print axioms d2Delta49Laurent
#print axioms d2Delta49Small
#print axioms d2Delta49Check
#print axioms d2Delta49Bound

def d2Delta50Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta50Ts : List LTerm := laurentClean []
def d2Delta50Lo : ℚ := (d2LitsStandaloneDelta006.q2 (15975409) 1 (-28))
def d2Delta50Hi : ℚ := (d2LitsStandaloneDelta006.q2 (64949187) 1 (-30))
def d2Delta50Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta50Qd : List (ℚ × ℚ) := []
def d2Delta50Ld : List LaurentPieceData := []
def d2Delta50Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-557417459920825908234614214008436552303634737, 1, -156, 594633016573565695305145055217235550267, 1, -159, -11965283249744435303927873480894873165, 1, -157, -67341027855453284348500208553999543, 1, -159, 12093678708389200913967067822433699, 1, -160, -3641241909587162256301622097497, 1, -158, -555542526704245061084725064351, 1, -160, 794631998997533619152489657, 1, -159, 2496949706034967648744915, 1, -158, -11014945744352729265081, 1, -158, -55119627348055560963, 1, -160, 462061958948732749, 1, -160, -1048957514885, 1, -160, -2802571044429, 1, -160, -686386973, 1, -158, -1853303161, 1, -159, -2917300207, 1, -160, -1233169413, 1, -159, -237161339, 1, -157, -1590298913, 1, -160, -1200449927, 1, -160, -249010717, 1, -158, -738428423, 1, -160, -605651045, 1, -160, -441303185, 1, -160, -357361819, 1, -160, -256065071, 1, -160, -204516371, 1, -160, -36042679, 1, -158, -113465553, 1, -160, -2459815, 1, -155, -30497105, 1, -159])
def d2Delta50S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-64891932292076339214235786011043839, 1, -123, 276991633344045997141869971607, 1, -128, -44596682168930576058319439079, 1, -128, -62682297370255475220246335, 1, -127, 22532441026173827887304723, 1, -128, -54300180360616498314883, 1, -128, -4139709703803248850639, 1, -128, 2960973524252002585, 1, -125, 297676027427811409, 1, -128, -656617668879777, 1, -126, -6570770109067, 1, -128, 110172827313, 1, -128, -507971, 1, -128, -1333851, 1, -127, 3093, 1, -128, 43, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta50Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta50Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta50Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta50Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta50Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta50Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta50El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta50Shift : polyRoundApx 128 d2Delta50Lo d2Delta50Hi d2Delta50Fq.poly = (d2Delta50S,d2Delta50Es) := by decide +kernel
theorem d2Delta50Sites : mergeSites d2Delta50Fq.plogs = [] := by decide +kernel
theorem d2Delta50PData : d2Delta50Pd = [] := by decide +kernel
theorem d2Delta50Plogs : plogsRoundM 16 24 20 128 d2Delta50Lo d2Delta50Hi (mergeSites d2Delta50Fq.plogs) d2Delta50Pd = some (d2Delta50Ap,d2Delta50Ep) := by
  rw [d2Delta50Sites,d2Delta50PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta50Poles : polesRoundM 16 24 12 128 d2Delta50Lo d2Delta50Hi d2Delta50Fq.poles d2Delta50Qd = some (d2Delta50Aq,d2Delta50Eq) := by decide +kernel
theorem d2Delta50Laurent : laurentRoundM 16 30 128 d2Delta50Lo d2Delta50Hi d2Delta50Ts d2Delta50Ld = some (d2Delta50Al,d2Delta50El) := by decide +kernel
theorem d2Delta50Small : chebPolyUB (vecAdd d2Delta50S (vecAdd d2Delta50Ap (vecAdd d2Delta50Aq d2Delta50Al))) d2Delta50Gam+d2Delta50Es+d2Delta50Ep+d2Delta50Eq+d2Delta50El ≤ (d2LitsStandaloneDelta006.q2 (-1844339398020538372215) 1 (-78)) := by decide +kernel
theorem d2Delta50Check : chebRoundPieceL d2Delta50Fq d2Delta50Ts 16 24 12 20 30 128 d2Delta50Lo d2Delta50Hi d2Delta50Pd d2Delta50Qd d2Delta50Ld d2Delta50Gam (d2LitsStandaloneDelta006.q2 (-1844339398020538372215) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta50Fq d2Delta50Ts 16 24 12 20 30 128 d2Delta50Lo d2Delta50Hi d2Delta50Pd d2Delta50Qd d2Delta50Ld d2Delta50Gam d2Delta50S d2Delta50Ap d2Delta50Aq d2Delta50Al d2Delta50Es d2Delta50Ep d2Delta50Eq d2Delta50El (by decide +kernel) d2Delta50Shift d2Delta50Plogs d2Delta50Poles d2Delta50Laurent]
  exact decide_eq_true d2Delta50Small
theorem d2Delta50Bound : ∀ x ∈ Icc ((d2Delta50Lo : ℚ) : ℝ) ((d2Delta50Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-1844339398020538372215) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta50Fq d2Delta50Ts 16 24 12 20 30 128 d2Delta50Lo d2Delta50Hi d2Delta50Pd d2Delta50Qd d2Delta50Ld d2Delta50Gam (d2LitsStandaloneDelta006.q2 (-1844339398020538372215) 1 (-78)) d2Delta50Check
  simpa only [d2Delta50Fq, d2Delta50Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta50Shift
#print axioms d2Delta50Sites
#print axioms d2Delta50PData
#print axioms d2Delta50Plogs
#print axioms d2Delta50Poles
#print axioms d2Delta50Laurent
#print axioms d2Delta50Small
#print axioms d2Delta50Check
#print axioms d2Delta50Bound

def d2Delta51Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta51Ts : List LTerm := laurentClean []
def d2Delta51Lo : ℚ := (d2LitsStandaloneDelta006.q2 (64949187) 1 (-30))
def d2Delta51Hi : ℚ := (d2LitsStandaloneDelta006.q2 (1063935) 1 (-24))
def d2Delta51Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta51Qd : List (ℚ × ℚ) := []
def d2Delta51Ld : List LaurentPieceData := []
def d2Delta51Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-557417401654665506214972775980825404354619697, 1, -156, -506622308555902139716157247458174262297, 1, -159, -105826209724769118675069488541061348941, 1, -157, 6371397296357175073463420607012908935, 1, -160, 889980821555385030649232164425967011, 1, -160, -9407139122585391046239511253844921, 1, -160, -328163605441680671935529718592159, 1, -160, 579782708110567836946251953085, 1, -157, 10980679118520059601537283539, 1, -158, -460696998713066561933243375, 1, -159, -879330175332372720521987, 1, -160, 79379459923106609918443, 1, -160, -148584646860622099589, 1, -160, -1012668435295216041, 1, -158, 3469266364928227, 1, -158, 140631225466729, 1, -160, -649206593519, 1, -160, -6052170425, 1, -160, -234621819, 1, -157, -1598064579, 1, -160, -1200449927, 1, -160, -500012275, 1, -159, -738428423, 1, -160, -608041977, 1, -160, -441303185, 1, -160, -358918471, 1, -160, -256065071, 1, -160, -205527199, 1, -160, -36042679, 1, -158, -114094581, 1, -160, -2459815, 1, -155, -15341105, 1, -158])
def d2Delta51S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-259567680156750757951586060463424197, 1, -125, -240375724894137541997081144657, 1, -128, -197946223257949786758781428429, 1, -127, 2988846020437589182519875715, 1, -127, 830693805298130494490442121, 1, -127, -549458889173720325376193, 1, -122, -305953452301569180316339, 1, -125, 34619552673321834975087, 1, -127, 327315194527417575381, 1, -126, -54971422840223201909, 1, -128, -26152911508328199, 1, -126, 18938095889187739, 1, -128, -70943352249627, 1, -128, -241564731899, 1, -124, 26488138577, 1, -128, 134177829, 1, -126, -4933587, 1, -128, -54463, 1, -128, 155, 1, -126, 1, 1, -126, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta51Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta51Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta51Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta51Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta51Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta51Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta51El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta51Shift : polyRoundApx 128 d2Delta51Lo d2Delta51Hi d2Delta51Fq.poly = (d2Delta51S,d2Delta51Es) := by decide +kernel
theorem d2Delta51Sites : mergeSites d2Delta51Fq.plogs = [] := by decide +kernel
theorem d2Delta51PData : d2Delta51Pd = [] := by decide +kernel
theorem d2Delta51Plogs : plogsRoundM 16 24 20 128 d2Delta51Lo d2Delta51Hi (mergeSites d2Delta51Fq.plogs) d2Delta51Pd = some (d2Delta51Ap,d2Delta51Ep) := by
  rw [d2Delta51Sites,d2Delta51PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta51Poles : polesRoundM 16 24 12 128 d2Delta51Lo d2Delta51Hi d2Delta51Fq.poles d2Delta51Qd = some (d2Delta51Aq,d2Delta51Eq) := by decide +kernel
theorem d2Delta51Laurent : laurentRoundM 16 30 128 d2Delta51Lo d2Delta51Hi d2Delta51Ts d2Delta51Ld = some (d2Delta51Al,d2Delta51El) := by decide +kernel
theorem d2Delta51Small : chebPolyUB (vecAdd d2Delta51S (vecAdd d2Delta51Ap (vecAdd d2Delta51Aq d2Delta51Al))) d2Delta51Gam+d2Delta51Es+d2Delta51Ep+d2Delta51Eq+d2Delta51El ≤ (d2LitsStandaloneDelta006.q2 (-7377356339524829560497) 1 (-80)) := by decide +kernel
theorem d2Delta51Check : chebRoundPieceL d2Delta51Fq d2Delta51Ts 16 24 12 20 30 128 d2Delta51Lo d2Delta51Hi d2Delta51Pd d2Delta51Qd d2Delta51Ld d2Delta51Gam (d2LitsStandaloneDelta006.q2 (-7377356339524829560497) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta51Fq d2Delta51Ts 16 24 12 20 30 128 d2Delta51Lo d2Delta51Hi d2Delta51Pd d2Delta51Qd d2Delta51Ld d2Delta51Gam d2Delta51S d2Delta51Ap d2Delta51Aq d2Delta51Al d2Delta51Es d2Delta51Ep d2Delta51Eq d2Delta51El (by decide +kernel) d2Delta51Shift d2Delta51Plogs d2Delta51Poles d2Delta51Laurent]
  exact decide_eq_true d2Delta51Small
theorem d2Delta51Bound : ∀ x ∈ Icc ((d2Delta51Lo : ℚ) : ℝ) ((d2Delta51Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-7377356339524829560497) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta51Fq d2Delta51Ts 16 24 12 20 30 128 d2Delta51Lo d2Delta51Hi d2Delta51Pd d2Delta51Qd d2Delta51Ld d2Delta51Gam (d2LitsStandaloneDelta006.q2 (-7377356339524829560497) 1 (-80)) d2Delta51Check
  simpa only [d2Delta51Fq, d2Delta51Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta51Shift
#print axioms d2Delta51Sites
#print axioms d2Delta51PData
#print axioms d2Delta51Plogs
#print axioms d2Delta51Poles
#print axioms d2Delta51Laurent
#print axioms d2Delta51Small
#print axioms d2Delta51Check
#print axioms d2Delta51Bound

def d2Delta52Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta52Ts : List LTerm := laurentClean []
def d2Delta52Lo : ℚ := (d2LitsStandaloneDelta006.q2 (1063935) 1 (-24))
def d2Delta52Hi : ℚ := (d2LitsStandaloneDelta006.q2 (35093471) 1 (-29))
def d2Delta52Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta52Qd : List (ℚ × ℚ) := []
def d2Delta52Ld : List LaurentPieceData := []
def d2Delta52Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-557417760960487553776720712671047063768746289, 1, -156, -4225355656160583725043595976587134364859, 1, -160, -40520427231702903845594383409146658381, 1, -157, 5039108045442685197350849279105542239, 1, -160, 135440580774353930914269950244169123, 1, -160, -1953193299385916870766215587672433, 1, -160, -18370101442200502626559963640479, 1, -160, 79668121612229576521171611349, 1, -158, 159071554858833988571313619, 1, -158, -23520101545448487104141433, 1, -160, 32657064966180174687485, 1, -160, 202778751107284543711, 1, -158, -2373989822626624645, 1, -160, -522537387515363, 1, -155, 17102627836131, 1, -158, 227913857947, 1, -160, -4153702383, 1, -160, -1242052769, 1, -159, -237161339, 1, -157, -799956113, 1, -159, -1200449927, 1, -160, -501218767, 1, -159, -738428423, 1, -160, -152527439, 1, -158, -441303185, 1, -160, -360459615, 1, -160, -256065071, 1, -160, -103294013, 1, -159, -36042679, 1, -158, -114779335, 1, -160, -2459815, 1, -155, -61780807, 1, -160])
def d2Delta52S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-2076542901589750325142464355232305289, 1, -128, -987314327735064505878561633219, 1, -128, -75601354594764623160429769421, 1, -127, 2351067249691147695189027489, 1, -127, 126241533185447026142942409, 1, -127, -7284524447829499560235853, 1, -128, -136905838464891944255149, 1, -128, 2375872455943347123581, 1, -127, 18953070657725812677, 1, -128, -1402439170923137659, 1, -128, 3896422161145827, 1, -128, 193436718170391, 1, -128, -566231668745, 1, -127, -7974942225, 1, -127, 130528757, 1, -128, 110481, 1, -125, -4717, 1, -127, -35, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta52Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta52Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta52Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta52Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta52Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta52Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta52El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta52Shift : polyRoundApx 128 d2Delta52Lo d2Delta52Hi d2Delta52Fq.poly = (d2Delta52S,d2Delta52Es) := by decide +kernel
theorem d2Delta52Sites : mergeSites d2Delta52Fq.plogs = [] := by decide +kernel
theorem d2Delta52PData : d2Delta52Pd = [] := by decide +kernel
theorem d2Delta52Plogs : plogsRoundM 16 24 20 128 d2Delta52Lo d2Delta52Hi (mergeSites d2Delta52Fq.plogs) d2Delta52Pd = some (d2Delta52Ap,d2Delta52Ep) := by
  rw [d2Delta52Sites,d2Delta52PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta52Poles : polesRoundM 16 24 12 128 d2Delta52Lo d2Delta52Hi d2Delta52Fq.poles d2Delta52Qd = some (d2Delta52Aq,d2Delta52Eq) := by decide +kernel
theorem d2Delta52Laurent : laurentRoundM 16 30 128 d2Delta52Lo d2Delta52Hi d2Delta52Ts d2Delta52Ld = some (d2Delta52Al,d2Delta52El) := by decide +kernel
theorem d2Delta52Small : chebPolyUB (vecAdd d2Delta52S (vecAdd d2Delta52Ap (vecAdd d2Delta52Aq d2Delta52Al))) d2Delta52Gam+d2Delta52Es+d2Delta52Ep+d2Delta52Eq+d2Delta52El ≤ (d2LitsStandaloneDelta006.q2 (-1844339717947960035749) 1 (-78)) := by decide +kernel
theorem d2Delta52Check : chebRoundPieceL d2Delta52Fq d2Delta52Ts 16 24 12 20 30 128 d2Delta52Lo d2Delta52Hi d2Delta52Pd d2Delta52Qd d2Delta52Ld d2Delta52Gam (d2LitsStandaloneDelta006.q2 (-1844339717947960035749) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta52Fq d2Delta52Ts 16 24 12 20 30 128 d2Delta52Lo d2Delta52Hi d2Delta52Pd d2Delta52Qd d2Delta52Ld d2Delta52Gam d2Delta52S d2Delta52Ap d2Delta52Aq d2Delta52Al d2Delta52Es d2Delta52Ep d2Delta52Eq d2Delta52El (by decide +kernel) d2Delta52Shift d2Delta52Plogs d2Delta52Poles d2Delta52Laurent]
  exact decide_eq_true d2Delta52Small
theorem d2Delta52Bound : ∀ x ∈ Icc ((d2Delta52Lo : ℚ) : ℝ) ((d2Delta52Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-1844339717947960035749) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta52Fq d2Delta52Ts 16 24 12 20 30 128 d2Delta52Lo d2Delta52Hi d2Delta52Pd d2Delta52Qd d2Delta52Ld d2Delta52Gam (d2LitsStandaloneDelta006.q2 (-1844339717947960035749) 1 (-78)) d2Delta52Check
  simpa only [d2Delta52Fq, d2Delta52Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta52Shift
#print axioms d2Delta52Sites
#print axioms d2Delta52PData
#print axioms d2Delta52Plogs
#print axioms d2Delta52Poles
#print axioms d2Delta52Laurent
#print axioms d2Delta52Small
#print axioms d2Delta52Check
#print axioms d2Delta52Bound

def d2Delta53Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta53Ts : List LTerm := laurentClean []
def d2Delta53Lo : ℚ := (d2LitsStandaloneDelta006.q2 (35093471) 1 (-29))
def d2Delta53Hi : ℚ := (d2LitsStandaloneDelta006.q2 (71234493) 1 (-30))
def d2Delta53Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta53Qd : List (ℚ × ℚ) := []
def d2Delta53Ld : List LaurentPieceData := []
def d2Delta53Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-557418229229090383714471312208911863768279345, 1, -156, -1508426559981499615235004048684639456461, 1, -159, -8512197350360336664274494537391242829, 1, -157, 202740863414520404212061552742957927, 1, -158, 6501604612092714192789363520578979, 1, -160, -34759588511457452813953025171665, 1, -159, -180797561411268668981381640863, 1, -160, 2551570908882804625686778271, 1, -160, 17160630235809173288403, 1, -158, -21640551465481320627301, 1, -159, 56559048774744665341, 1, -160, 43624636776844889, 1, -157, -724671814005893, 1, -160, -104466493179, 1, -156, 90476771, 1, -158, -3523108833, 1, -160, -2917300207, 1, -160, -2325129821, 1, -160, -237161339, 1, -157, -372831521, 1, -158, -1200449927, 1, -160, -232641329, 1, -158, -738428423, 1, -160, -564579387, 1, -160, -441303185, 1, -160, -83210553, 1, -158, -256065071, 1, -160, -95276057, 1, -159, -36042679, 1, -158, -3308453, 1, -155, -2459815, 1, -155, -28523993, 1, -159])
def d2Delta53S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-1038272352838116412882125583678018929, 1, -127, -351491193046993573171904540657, 1, -127, -31722517147897842218502386799, 1, -128, 377796164372231516995733333, 1, -127, 12112202865688510602597461, 1, -128, -32380707183803309442553, 1, -125, -673525439842746941765, 1, -127, 2376698380490127599, 1, -124, 2028849462344769, 1, -128, -1289991796236597, 1, -127, 6743400708827, 1, -128, 20803139415, 1, -126, -172789491, 1, -127, -1589135, 1, -128, 2255, 1, -126, 19, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta53Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta53Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta53Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta53Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta53Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta53Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta53El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta53Shift : polyRoundApx 128 d2Delta53Lo d2Delta53Hi d2Delta53Fq.poly = (d2Delta53S,d2Delta53Es) := by decide +kernel
theorem d2Delta53Sites : mergeSites d2Delta53Fq.plogs = [] := by decide +kernel
theorem d2Delta53PData : d2Delta53Pd = [] := by decide +kernel
theorem d2Delta53Plogs : plogsRoundM 16 24 20 128 d2Delta53Lo d2Delta53Hi (mergeSites d2Delta53Fq.plogs) d2Delta53Pd = some (d2Delta53Ap,d2Delta53Ep) := by
  rw [d2Delta53Sites,d2Delta53PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta53Poles : polesRoundM 16 24 12 128 d2Delta53Lo d2Delta53Hi d2Delta53Fq.poles d2Delta53Qd = some (d2Delta53Aq,d2Delta53Eq) := by decide +kernel
theorem d2Delta53Laurent : laurentRoundM 16 30 128 d2Delta53Lo d2Delta53Hi d2Delta53Ts d2Delta53Ld = some (d2Delta53Al,d2Delta53El) := by decide +kernel
theorem d2Delta53Small : chebPolyUB (vecAdd d2Delta53S (vecAdd d2Delta53Ap (vecAdd d2Delta53Aq d2Delta53Al))) d2Delta53Gam+d2Delta53Es+d2Delta53Ep+d2Delta53Eq+d2Delta53El ≤ (d2LitsStandaloneDelta006.q2 (-1844341571085857514865) 1 (-78)) := by decide +kernel
theorem d2Delta53Check : chebRoundPieceL d2Delta53Fq d2Delta53Ts 16 24 12 20 30 128 d2Delta53Lo d2Delta53Hi d2Delta53Pd d2Delta53Qd d2Delta53Ld d2Delta53Gam (d2LitsStandaloneDelta006.q2 (-1844341571085857514865) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta53Fq d2Delta53Ts 16 24 12 20 30 128 d2Delta53Lo d2Delta53Hi d2Delta53Pd d2Delta53Qd d2Delta53Ld d2Delta53Gam d2Delta53S d2Delta53Ap d2Delta53Aq d2Delta53Al d2Delta53Es d2Delta53Ep d2Delta53Eq d2Delta53El (by decide +kernel) d2Delta53Shift d2Delta53Plogs d2Delta53Poles d2Delta53Laurent]
  exact decide_eq_true d2Delta53Small
theorem d2Delta53Bound : ∀ x ∈ Icc ((d2Delta53Lo : ℚ) : ℝ) ((d2Delta53Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-1844341571085857514865) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta53Fq d2Delta53Ts 16 24 12 20 30 128 d2Delta53Lo d2Delta53Hi d2Delta53Pd d2Delta53Qd d2Delta53Ld d2Delta53Gam (d2LitsStandaloneDelta006.q2 (-1844341571085857514865) 1 (-78)) d2Delta53Check
  simpa only [d2Delta53Fq, d2Delta53Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta53Shift
#print axioms d2Delta53Sites
#print axioms d2Delta53PData
#print axioms d2Delta53Plogs
#print axioms d2Delta53Poles
#print axioms d2Delta53Laurent
#print axioms d2Delta53Small
#print axioms d2Delta53Check
#print axioms d2Delta53Bound

def d2Delta54Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta54Ts : List LTerm := laurentClean []
def d2Delta54Lo : ℚ := (d2LitsStandaloneDelta006.q2 (71234493) 1 (-30))
def d2Delta54Hi : ℚ := (d2LitsStandaloneDelta006.q2 (18070511) 1 (-28))
def d2Delta54Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta54Qd : List (ℚ × ℚ) := []
def d2Delta54Ld : List LaurentPieceData := []
def d2Delta54Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-557418638384871663780956069986163950686300465, 1, -156, -1760523074235005078113222276793585844897, 1, -159, -7223555414958124819721864914808110669, 1, -157, 451827288124905028018261349035466017, 1, -159, 5073611852336867021321797190952355, 1, -160, -18250541454920102037896842651163, 1, -158, -109553777530298510492554965663, 1, -160, 1264651800544958126091218381, 1, -159, -361287333726735245429293, 1, -158, -40722160323461809370375, 1, -160, 71120329078486199549, 1, -160, 156122921328613381, 1, -159, -804289446245509, 1, -160, -349740959423, 1, -158, 158503139, 1, -158, -3749348617, 1, -160, -2917300207, 1, -160, -310786499, 1, -157, -237161339, 1, -157, -801560097, 1, -159, -1200449927, 1, -160, -1005083801, 1, -160, -738428423, 1, -160, -38263897, 1, -156, -441303185, 1, -160, -362042739, 1, -160, -256065071, 1, -160, -103850815, 1, -159, -36042679, 1, -158, -57758549, 1, -159, -2459815, 1, -155, -62242311, 1, -160])
def d2Delta54S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-1038273116150455267567377233079158691, 1, -127, -410219360751483377128269282049, 1, -127, -6729822926343793472176313909, 1, -126, 841933882320654164365921551, 1, -128, 4725781405433552352097839, 1, -127, -272020220921972429315413, 1, -128, -816153093027455030451, 1, -128, 37695022140024038077, 1, -128, -43090003181402095, 1, -128, -2427434630297537, 1, -128, 2119838621305, 1, -126, 9306191375, 1, -125, -95886361, 1, -126, -83059, 1, -124, 9539, 1, -128, 7, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta54Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta54Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta54Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta54Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta54Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta54Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta54El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta54Shift : polyRoundApx 128 d2Delta54Lo d2Delta54Hi d2Delta54Fq.poly = (d2Delta54S,d2Delta54Es) := by decide +kernel
theorem d2Delta54Sites : mergeSites d2Delta54Fq.plogs = [] := by decide +kernel
theorem d2Delta54PData : d2Delta54Pd = [] := by decide +kernel
theorem d2Delta54Plogs : plogsRoundM 16 24 20 128 d2Delta54Lo d2Delta54Hi (mergeSites d2Delta54Fq.plogs) d2Delta54Pd = some (d2Delta54Ap,d2Delta54Ep) := by
  rw [d2Delta54Sites,d2Delta54PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta54Poles : polesRoundM 16 24 12 128 d2Delta54Lo d2Delta54Hi d2Delta54Fq.poles d2Delta54Qd = some (d2Delta54Aq,d2Delta54Eq) := by decide +kernel
theorem d2Delta54Laurent : laurentRoundM 16 30 128 d2Delta54Lo d2Delta54Hi d2Delta54Ts d2Delta54Ld = some (d2Delta54Al,d2Delta54El) := by decide +kernel
theorem d2Delta54Small : chebPolyUB (vecAdd d2Delta54S (vecAdd d2Delta54Ap (vecAdd d2Delta54Aq d2Delta54Al))) d2Delta54Gam+d2Delta54Es+d2Delta54Ep+d2Delta54Eq+d2Delta54El ≤ (d2LitsStandaloneDelta006.q2 (-3688685645434215802971) 1 (-79)) := by decide +kernel
theorem d2Delta54Check : chebRoundPieceL d2Delta54Fq d2Delta54Ts 16 24 12 20 30 128 d2Delta54Lo d2Delta54Hi d2Delta54Pd d2Delta54Qd d2Delta54Ld d2Delta54Gam (d2LitsStandaloneDelta006.q2 (-3688685645434215802971) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta54Fq d2Delta54Ts 16 24 12 20 30 128 d2Delta54Lo d2Delta54Hi d2Delta54Pd d2Delta54Qd d2Delta54Ld d2Delta54Gam d2Delta54S d2Delta54Ap d2Delta54Aq d2Delta54Al d2Delta54Es d2Delta54Ep d2Delta54Eq d2Delta54El (by decide +kernel) d2Delta54Shift d2Delta54Plogs d2Delta54Poles d2Delta54Laurent]
  exact decide_eq_true d2Delta54Small
theorem d2Delta54Bound : ∀ x ∈ Icc ((d2Delta54Lo : ℚ) : ℝ) ((d2Delta54Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-3688685645434215802971) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta54Fq d2Delta54Ts 16 24 12 20 30 128 d2Delta54Lo d2Delta54Hi d2Delta54Pd d2Delta54Qd d2Delta54Ld d2Delta54Gam (d2LitsStandaloneDelta006.q2 (-3688685645434215802971) 1 (-79)) d2Delta54Check
  simpa only [d2Delta54Fq, d2Delta54Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta54Shift
#print axioms d2Delta54Sites
#print axioms d2Delta54PData
#print axioms d2Delta54Plogs
#print axioms d2Delta54Poles
#print axioms d2Delta54Laurent
#print axioms d2Delta54Small
#print axioms d2Delta54Check
#print axioms d2Delta54Bound

def d2Delta55Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta55Ts : List LTerm := laurentClean []
def d2Delta55Lo : ℚ := (d2LitsStandaloneDelta006.q2 (18070511) 1 (-28))
def d2Delta55Hi : ℚ := (d2LitsStandaloneDelta006.q2 (9559031) 1 (-27))
def d2Delta55Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta55Qd : List (ℚ × ℚ) := []
def d2Delta55Ld : List LaurentPieceData := []
def d2Delta55Gam : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-8918718645024005898062490642168168436471080037, 1, -160, -8685502484355512587807168917104484315095, 1, -159, -113194350029336338116684911686356596485, 1, -158, 65709633449240208178333517970713351307, 1, -160, 173022634081544683861536448624622957, 1, -159, -75935471407777064172230866557328047, 1, -160, 61053259589398592660489732617489, 1, -158, 18614456411061351327419019978159, 1, -159, -2420605709946826019887867007, 1, -153, -1050039939203806881368635671, 1, -157, 52241477604672909275416615, 1, -159, 866535534558613846281035, 1, -160, -15727405483177665982789, 1, -160, -44585343884904479581, 1, -160, 1429004882510490763, 1, -160, 537788435726669, 1, -160, -22436255080697, 1, -158, 88792048383, 1, -160, 2136280051, 1, -160, -1496449919, 1, -160, -10269957, 1, -153, -463984693, 1, -159, -102212867, 1, -157, -140617779, 1, -158, -247265179, 1, -159, -331244355, 1, -160, -145275141, 1, -159, -94707545, 1, -159, -41430993, 1, -158, -105107837, 1, -160, -22926271, 1, -158, -14141133, 1, -158])
def d2Delta55S : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [-2076550897187740783098720935944874055, 1, -128, -4090488377747541956701849098861, 1, -128, -211484440747946201581665523789, 1, -128, 30775476369595086266141282809, 1, -127, 641818694689361228545145387, 1, -128, -8870416864856395638771489, 1, -123, 1838023940249546240676555, 1, -128, 69485146239892491845265, 1, -125, -9265041649500535233755, 1, -128, -501266378325567223491, 1, -128, 1559731276931088137, 1, -125, 206736372087013117, 1, -128, -7508955424803147, 1, -128, -21263790088253, 1, -127, 2728350302523, 1, -128, 1022800051, 1, -127, -342626065, 1, -127, 174079, 1, -125, 128011, 1, -128, -493, 1, -128, -19, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta55Ap : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta55Aq : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta55Al : List ℚ := d2LitsStandaloneDelta006.q2listC (raw_ints% [])
def d2Delta55Es : ℚ := (d2LitsStandaloneDelta006.q2 (61) 1 (-127))
def d2Delta55Ep : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta55Eq : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
def d2Delta55El : ℚ := (d2LitsStandaloneDelta006.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta55Shift : polyRoundApx 128 d2Delta55Lo d2Delta55Hi d2Delta55Fq.poly = (d2Delta55S,d2Delta55Es) := by decide +kernel
theorem d2Delta55Sites : mergeSites d2Delta55Fq.plogs = [] := by decide +kernel
theorem d2Delta55PData : d2Delta55Pd = [] := by decide +kernel
theorem d2Delta55Plogs : plogsRoundM 16 24 20 128 d2Delta55Lo d2Delta55Hi (mergeSites d2Delta55Fq.plogs) d2Delta55Pd = some (d2Delta55Ap,d2Delta55Ep) := by
  rw [d2Delta55Sites,d2Delta55PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta55Poles : polesRoundM 16 24 12 128 d2Delta55Lo d2Delta55Hi d2Delta55Fq.poles d2Delta55Qd = some (d2Delta55Aq,d2Delta55Eq) := by decide +kernel
theorem d2Delta55Laurent : laurentRoundM 16 30 128 d2Delta55Lo d2Delta55Hi d2Delta55Ts d2Delta55Ld = some (d2Delta55Al,d2Delta55El) := by decide +kernel
theorem d2Delta55Small : chebPolyUB (vecAdd d2Delta55S (vecAdd d2Delta55Ap (vecAdd d2Delta55Aq d2Delta55Al))) d2Delta55Gam+d2Delta55Es+d2Delta55Ep+d2Delta55Eq+d2Delta55El ≤ (d2LitsStandaloneDelta006.q2 (-922172044223603266095) 1 (-77)) := by decide +kernel
theorem d2Delta55Check : chebRoundPieceL d2Delta55Fq d2Delta55Ts 16 24 12 20 30 128 d2Delta55Lo d2Delta55Hi d2Delta55Pd d2Delta55Qd d2Delta55Ld d2Delta55Gam (d2LitsStandaloneDelta006.q2 (-922172044223603266095) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta55Fq d2Delta55Ts 16 24 12 20 30 128 d2Delta55Lo d2Delta55Hi d2Delta55Pd d2Delta55Qd d2Delta55Ld d2Delta55Gam d2Delta55S d2Delta55Ap d2Delta55Aq d2Delta55Al d2Delta55Es d2Delta55Ep d2Delta55Eq d2Delta55El (by decide +kernel) d2Delta55Shift d2Delta55Plogs d2Delta55Poles d2Delta55Laurent]
  exact decide_eq_true d2Delta55Small
theorem d2Delta55Bound : ∀ x ∈ Icc ((d2Delta55Lo : ℚ) : ℝ) ((d2Delta55Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta006.q2 (-922172044223603266095) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta55Fq d2Delta55Ts 16 24 12 20 30 128 d2Delta55Lo d2Delta55Hi d2Delta55Pd d2Delta55Qd d2Delta55Ld d2Delta55Gam (d2LitsStandaloneDelta006.q2 (-922172044223603266095) 1 (-77)) d2Delta55Check
  simpa only [d2Delta55Fq, d2Delta55Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta55Shift
#print axioms d2Delta55Sites
#print axioms d2Delta55PData
#print axioms d2Delta55Plogs
#print axioms d2Delta55Poles
#print axioms d2Delta55Laurent
#print axioms d2Delta55Small
#print axioms d2Delta55Check
#print axioms d2Delta55Bound

end StandaloneDelta006
end CatalanMeasure.GenD.Signed.Data.Cells
