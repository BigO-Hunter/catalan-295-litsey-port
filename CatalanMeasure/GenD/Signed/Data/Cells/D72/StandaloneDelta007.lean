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
namespace d2LitsStandaloneDelta007
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta007
namespace StandaloneDelta007
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta007.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta007.q2listC (raw_ints% []))⟩
def d2Delta56Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta56Ts : List LTerm := laurentClean []
def d2Delta56Lo : ℚ := (d2LitsStandaloneDelta007.q2 (9559031) 1 (-27))
def d2Delta56Hi : ℚ := (d2LitsStandaloneDelta007.q2 (77519799) 1 (-30))
def d2Delta56Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta56Qd : List (ℚ × ℚ) := []
def d2Delta56Ld : List LaurentPieceData := []
def d2Delta56Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-8918741049748439066265952200103968182173892625, 1, -160, -4645274972688727295928140625123986715247, 1, -160, 2662980110127059692496166258433660387, 1, -160, 506861809812364017456236875490453321, 1, -159, -2206977761123741579064436773660701, 1, -160, -66306185505808516942346893192209, 1, -160, 25474316728137966509046874389, 1, -157, 1794296520643522931582048505, 1, -160, -7151234975743861326159621, 1, -160, -21170899018857060000161, 1, -160, 58110237512833769645, 1, -159, 90857415964580527, 1, -160, -488297311523861, 1, -159, 34846844471, 1, -159, 338085297, 1, -159, -939357571, 1, -158, -3035903363, 1, -160, -2489180499, 1, -160, -2004736075, 1, -160, -803004313, 1, -159, -161101771, 1, -157, -1007647203, 1, -160, -805707253, 1, -160, -307162467, 1, -159, -30582093, 1, -156, -363652991, 1, -160, -288447039, 1, -160, -13053767, 1, -156, -41234701, 1, -158, -116303547, 1, -160, -91434093, 1, -160, -31373619, 1, -159])
def d2Delta56S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-2076556219815655229137237372454285257, 1, -128, -541135258401172384067794543107, 1, -127, 311039604181049129681772043, 1, -126, 944412477009970227698072337, 1, -128, -4113094269032036592491777, 1, -128, -61764145412551510259271, 1, -126, 759406938302277358201, 1, -127, 6684985245512453753, 1, -126, -106579024094805725, 1, -127, -630971743035887, 1, -127, 13855957328069, 1, -128, 21661864731, 1, -128, -465707959, 1, -128, 17941, 1, -126, 4919, 1, -127, -11, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta56Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta56Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta56Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta56Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta56Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta56Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta56El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta56Shift : polyRoundApx 128 d2Delta56Lo d2Delta56Hi d2Delta56Fq.poly = (d2Delta56S,d2Delta56Es) := by decide +kernel
theorem d2Delta56Sites : mergeSites d2Delta56Fq.plogs = [] := by decide +kernel
theorem d2Delta56PData : d2Delta56Pd = [] := by decide +kernel
theorem d2Delta56Plogs : plogsRoundM 16 24 20 128 d2Delta56Lo d2Delta56Hi (mergeSites d2Delta56Fq.plogs) d2Delta56Pd = some (d2Delta56Ap,d2Delta56Ep) := by
  rw [d2Delta56Sites,d2Delta56PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta56Poles : polesRoundM 16 24 12 128 d2Delta56Lo d2Delta56Hi d2Delta56Fq.poles d2Delta56Qd = some (d2Delta56Aq,d2Delta56Eq) := by decide +kernel
theorem d2Delta56Laurent : laurentRoundM 16 30 128 d2Delta56Lo d2Delta56Hi d2Delta56Ts d2Delta56Ld = some (d2Delta56Al,d2Delta56El) := by decide +kernel
theorem d2Delta56Small : chebPolyUB (vecAdd d2Delta56S (vecAdd d2Delta56Ap (vecAdd d2Delta56Aq d2Delta56Al))) d2Delta56Gam+d2Delta56Es+d2Delta56Ep+d2Delta56Eq+d2Delta56El ≤ (d2LitsStandaloneDelta007.q2 (-3688702919604085441333) 1 (-79)) := by decide +kernel
theorem d2Delta56Check : chebRoundPieceL d2Delta56Fq d2Delta56Ts 16 24 12 20 30 128 d2Delta56Lo d2Delta56Hi d2Delta56Pd d2Delta56Qd d2Delta56Ld d2Delta56Gam (d2LitsStandaloneDelta007.q2 (-3688702919604085441333) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta56Fq d2Delta56Ts 16 24 12 20 30 128 d2Delta56Lo d2Delta56Hi d2Delta56Pd d2Delta56Qd d2Delta56Ld d2Delta56Gam d2Delta56S d2Delta56Ap d2Delta56Aq d2Delta56Al d2Delta56Es d2Delta56Ep d2Delta56Eq d2Delta56El (by decide +kernel) d2Delta56Shift d2Delta56Plogs d2Delta56Poles d2Delta56Laurent]
  exact decide_eq_true d2Delta56Small
theorem d2Delta56Bound : ∀ x ∈ Icc ((d2Delta56Lo : ℚ) : ℝ) ((d2Delta56Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-3688702919604085441333) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta56Fq d2Delta56Ts 16 24 12 20 30 128 d2Delta56Lo d2Delta56Hi d2Delta56Pd d2Delta56Qd d2Delta56Ld d2Delta56Gam (d2LitsStandaloneDelta007.q2 (-3688702919604085441333) 1 (-79)) d2Delta56Check
  simpa only [d2Delta56Fq, d2Delta56Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta56Shift
#print axioms d2Delta56Sites
#print axioms d2Delta56PData
#print axioms d2Delta56Plogs
#print axioms d2Delta56Poles
#print axioms d2Delta56Laurent
#print axioms d2Delta56Small
#print axioms d2Delta56Check
#print axioms d2Delta56Bound

def d2Delta57Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta57Ts : List LTerm := laurentClean []
def d2Delta57Lo : ℚ := (d2LitsStandaloneDelta007.q2 (77519799) 1 (-30))
def d2Delta57Hi : ℚ := (d2LitsStandaloneDelta007.q2 (39283675) 1 (-29))
def d2Delta57Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta57Qd : List (ℚ × ℚ) := []
def d2Delta57Ld : List LaurentPieceData := []
def d2Delta57Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-8918750280962086538281204952454605859069411033, 1, -160, -4576011671985700245768907068720363942511, 1, -160, 7286468980244586676196532314829109611, 1, -159, 484042670803812546682756914959804233, 1, -159, -435032228985936967921008516227799, 1, -157, -60838763901362604479486894074897, 1, -160, 250722944238754886566152088019, 1, -160, 1554166780282742834336110841, 1, -160, -7828870604818959124508319, 1, -160, -16455897967052435513761, 1, -160, 7449351968690141333, 1, -156, 44194446097996463, 1, -160, -965262401127445, 1, -160, 176642106935, 1, -159, 367876565, 1, -160, -939619715, 1, -158, -192974041, 1, -156, -2489180499, 1, -160, -1012867033, 1, -159, -803004313, 1, -159, -1295445387, 1, -160, -1007647203, 1, -160, -806728557, 1, -160, -307162467, 1, -159, -122180305, 1, -158, -363652991, 1, -160, -71930089, 1, -158, -13053767, 1, -156, -41112437, 1, -158, -116303547, 1, -160, -22793339, 1, -158, -31373619, 1, -159])
def d2Delta57S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-129784898243648131135458811028239737, 1, -124, -33316000424494428032103846237, 1, -123, 6792536586731898781663345355, 1, -128, 225470763907292976443652213, 1, -126, -1621321926888218127188607, 1, -126, -56670646661089017705233, 1, -126, 1868498171682198726011, 1, -128, 23161096651985440005, 1, -128, -116677024264020951, 1, -127, -245219231884365, 1, -126, 7104946074435, 1, -127, 2633916691, 1, -126, -460302905, 1, -128, 42779, 1, -125, 9457, 1, -128, -15, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta57Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta57Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta57Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta57Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta57Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta57Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta57El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta57Shift : polyRoundApx 128 d2Delta57Lo d2Delta57Hi d2Delta57Fq.poly = (d2Delta57S,d2Delta57Es) := by decide +kernel
theorem d2Delta57Sites : mergeSites d2Delta57Fq.plogs = [] := by decide +kernel
theorem d2Delta57PData : d2Delta57Pd = [] := by decide +kernel
theorem d2Delta57Plogs : plogsRoundM 16 24 20 128 d2Delta57Lo d2Delta57Hi (mergeSites d2Delta57Fq.plogs) d2Delta57Pd = some (d2Delta57Ap,d2Delta57Ep) := by
  rw [d2Delta57Sites,d2Delta57PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta57Poles : polesRoundM 16 24 12 128 d2Delta57Lo d2Delta57Hi d2Delta57Fq.poles d2Delta57Qd = some (d2Delta57Aq,d2Delta57Eq) := by decide +kernel
theorem d2Delta57Laurent : laurentRoundM 16 30 128 d2Delta57Lo d2Delta57Hi d2Delta57Ts d2Delta57Ld = some (d2Delta57Al,d2Delta57El) := by decide +kernel
theorem d2Delta57Small : chebPolyUB (vecAdd d2Delta57S (vecAdd d2Delta57Ap (vecAdd d2Delta57Aq d2Delta57Al))) d2Delta57Gam+d2Delta57Es+d2Delta57Ep+d2Delta57Eq+d2Delta57El ≤ (d2LitsStandaloneDelta007.q2 (-7377413522567406029369) 1 (-80)) := by decide +kernel
theorem d2Delta57Check : chebRoundPieceL d2Delta57Fq d2Delta57Ts 16 24 12 20 30 128 d2Delta57Lo d2Delta57Hi d2Delta57Pd d2Delta57Qd d2Delta57Ld d2Delta57Gam (d2LitsStandaloneDelta007.q2 (-7377413522567406029369) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta57Fq d2Delta57Ts 16 24 12 20 30 128 d2Delta57Lo d2Delta57Hi d2Delta57Pd d2Delta57Qd d2Delta57Ld d2Delta57Gam d2Delta57S d2Delta57Ap d2Delta57Aq d2Delta57Al d2Delta57Es d2Delta57Ep d2Delta57Eq d2Delta57El (by decide +kernel) d2Delta57Shift d2Delta57Plogs d2Delta57Poles d2Delta57Laurent]
  exact decide_eq_true d2Delta57Small
theorem d2Delta57Bound : ∀ x ∈ Icc ((d2Delta57Lo : ℚ) : ℝ) ((d2Delta57Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-7377413522567406029369) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta57Fq d2Delta57Ts 16 24 12 20 30 128 d2Delta57Lo d2Delta57Hi d2Delta57Pd d2Delta57Qd d2Delta57Ld d2Delta57Gam (d2LitsStandaloneDelta007.q2 (-7377413522567406029369) 1 (-80)) d2Delta57Check
  simpa only [d2Delta57Fq, d2Delta57Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta57Shift
#print axioms d2Delta57Sites
#print axioms d2Delta57PData
#print axioms d2Delta57Plogs
#print axioms d2Delta57Poles
#print axioms d2Delta57Laurent
#print axioms d2Delta57Small
#print axioms d2Delta57Check
#print axioms d2Delta57Bound

def d2Delta58Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta58Ts : List LTerm := laurentClean []
def d2Delta58Lo : ℚ := (d2LitsStandaloneDelta007.q2 (39283675) 1 (-29))
def d2Delta58Hi : ℚ := (d2LitsStandaloneDelta007.q2 (20165613) 1 (-28))
def d2Delta58Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta58Qd : List (ℚ × ℚ) := []
def d2Delta58Ld : List LaurentPieceData := []
def d2Delta58Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-8918763543313868357882013740868692664803583835, 1, -160, -268269839840172179940564390769463638807, 1, -155, 62113994237129656435328564945386494425, 1, -159, 6904458699728304826321764922314214039, 1, -160, -82454657889394951260863318216296823, 1, -160, -202843937588296646926379225384105, 1, -157, 9844331960477041795920578627639, 1, -159, 74234472248925345043877965407, 1, -159, -1090540578031532638210178849, 1, -159, -1185706315575931598455579, 1, -158, 61341903874110327748523, 1, -159, -48914772204176066747, 1, -160, -1886743917963368331, 1, -159, 3105430477737283, 1, -159, 37117361438637, 1, -159, -92334831007, 1, -159, -4095193207, 1, -160, -2316319335, 1, -160, -2011462265, 1, -160, -742782707, 1, -159, -160798085, 1, -157, -925439931, 1, -160, -50074703, 1, -156, -140094103, 1, -158, -242725841, 1, -159, -82405981, 1, -158, -285862317, 1, -160, -94118297, 1, -159, -163445231, 1, -160, -3259335, 1, -155, -90661861, 1, -160, -28019329, 1, -159])
def d2Delta58S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-1038280742664860000470169629030238521, 1, -127, -2003590661515836487714451546903, 1, -128, 7250228916451599622989589083, 1, -125, 804729589254053045192257027, 1, -125, -76901943889147027993485835, 1, -127, -3024546264429339476929599, 1, -127, 73411005975896536431985, 1, -127, 553248926147790514865, 1, -126, -65037852463855781405, 1, -128, -282662319901790241, 1, -128, 3657612065046093, 1, -126, -1460180573503, 1, -125, -899917432375, 1, -127, 5925735207, 1, -128, 70815797, 1, -127, -345609, 1, -127, -3925, 1, -127, 3, 1, -124, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta58Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta58Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta58Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta58Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta58Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta58Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta58El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta58Shift : polyRoundApx 128 d2Delta58Lo d2Delta58Hi d2Delta58Fq.poly = (d2Delta58S,d2Delta58Es) := by decide +kernel
theorem d2Delta58Sites : mergeSites d2Delta58Fq.plogs = [] := by decide +kernel
theorem d2Delta58PData : d2Delta58Pd = [] := by decide +kernel
theorem d2Delta58Plogs : plogsRoundM 16 24 20 128 d2Delta58Lo d2Delta58Hi (mergeSites d2Delta58Fq.plogs) d2Delta58Pd = some (d2Delta58Ap,d2Delta58Ep) := by
  rw [d2Delta58Sites,d2Delta58PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta58Poles : polesRoundM 16 24 12 128 d2Delta58Lo d2Delta58Hi d2Delta58Fq.poles d2Delta58Qd = some (d2Delta58Aq,d2Delta58Eq) := by decide +kernel
theorem d2Delta58Laurent : laurentRoundM 16 30 128 d2Delta58Lo d2Delta58Hi d2Delta58Ts d2Delta58Ld = some (d2Delta58Al,d2Delta58El) := by decide +kernel
theorem d2Delta58Small : chebPolyUB (vecAdd d2Delta58S (vecAdd d2Delta58Ap (vecAdd d2Delta58Aq d2Delta58Al))) d2Delta58Gam+d2Delta58Es+d2Delta58Ep+d2Delta58Eq+d2Delta58El ≤ (d2LitsStandaloneDelta007.q2 (-7377421081390661256909) 1 (-80)) := by decide +kernel
theorem d2Delta58Check : chebRoundPieceL d2Delta58Fq d2Delta58Ts 16 24 12 20 30 128 d2Delta58Lo d2Delta58Hi d2Delta58Pd d2Delta58Qd d2Delta58Ld d2Delta58Gam (d2LitsStandaloneDelta007.q2 (-7377421081390661256909) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta58Fq d2Delta58Ts 16 24 12 20 30 128 d2Delta58Lo d2Delta58Hi d2Delta58Pd d2Delta58Qd d2Delta58Ld d2Delta58Gam d2Delta58S d2Delta58Ap d2Delta58Aq d2Delta58Al d2Delta58Es d2Delta58Ep d2Delta58Eq d2Delta58El (by decide +kernel) d2Delta58Shift d2Delta58Plogs d2Delta58Poles d2Delta58Laurent]
  exact decide_eq_true d2Delta58Small
theorem d2Delta58Bound : ∀ x ∈ Icc ((d2Delta58Lo : ℚ) : ℝ) ((d2Delta58Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-7377421081390661256909) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta58Fq d2Delta58Ts 16 24 12 20 30 128 d2Delta58Lo d2Delta58Hi d2Delta58Pd d2Delta58Qd d2Delta58Ld d2Delta58Gam (d2LitsStandaloneDelta007.q2 (-7377421081390661256909) 1 (-80)) d2Delta58Check
  simpa only [d2Delta58Fq, d2Delta58Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta58Shift
#print axioms d2Delta58Sites
#print axioms d2Delta58PData
#print axioms d2Delta58Plogs
#print axioms d2Delta58Poles
#print axioms d2Delta58Laurent
#print axioms d2Delta58Small
#print axioms d2Delta58Check
#print axioms d2Delta58Bound

def d2Delta59Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta59Ts : List LTerm := laurentClean []
def d2Delta59Lo : ℚ := (d2LitsStandaloneDelta007.q2 (20165613) 1 (-28))
def d2Delta59Hi : ℚ := (d2LitsStandaloneDelta007.q2 (41378777) 1 (-29))
def d2Delta59Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta59Qd : List (ℚ × ℚ) := []
def d2Delta59Ld : List LaurentPieceData := []
def d2Delta59Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-4459389736869290356876187149650986543329392951, 1, -159, -227628686294806260896992844248833850135, 1, -155, 99090755649124543230681388724264729139, 1, -159, 5352487793865773924274577807165901463, 1, -160, -54944493851475984810571988309340803, 1, -159, -138543607093903807328780541461673, 1, -157, 5712428627588015884401235784221, 1, -158, 38441125062011970060278672991, 1, -159, -2264485218003507541292634041, 1, -160, 17368432668639945178341, 1, -158, 29169845082572461346337, 1, -158, -220625780176225880251, 1, -160, -3348177946959374355, 1, -160, 5014517643087171, 1, -159, 61536819778353, 1, -160, -121553466783, 1, -159, -3835500849, 1, -160, -2315663975, 1, -160, -2002410573, 1, -160, -742782707, 1, -159, -640932745, 1, -159, -925439931, 1, -160, -798536631, 1, -160, -140094103, 1, -158, -483777241, 1, -160, -82405981, 1, -158, -284824737, 1, -160, -94118297, 1, -159, -162835981, 1, -160, -3259335, 1, -155, -90326771, 1, -160, -28019329, 1, -159])
def d2Delta59S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-64892662863931064578963014232296769, 1, -123, -1699705833359122404317945578925, 1, -128, 23122559410138773743705939415, 1, -126, 311878429172731439213505261, 1, -124, -6404363741490102993544501, 1, -123, -4130926097219131468045877, 1, -128, 42594660960602419788631, 1, -126, 1145625340213610283199, 1, -128, -67521697062890038013, 1, -128, 4285649431344713, 1, -128, 13914056206291317, 1, -128, -52632374586897, 1, -128, -798473263087, 1, -127, 2391966507, 1, -126, 14675611, 1, -125, -914181, 1, -128, -3015, 1, -127, 29, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta59Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta59Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta59Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta59Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta59Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta59Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta59El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta59Shift : polyRoundApx 128 d2Delta59Lo d2Delta59Hi d2Delta59Fq.poly = (d2Delta59S,d2Delta59Es) := by decide +kernel
theorem d2Delta59Sites : mergeSites d2Delta59Fq.plogs = [] := by decide +kernel
theorem d2Delta59PData : d2Delta59Pd = [] := by decide +kernel
theorem d2Delta59Plogs : plogsRoundM 16 24 20 128 d2Delta59Lo d2Delta59Hi (mergeSites d2Delta59Fq.plogs) d2Delta59Pd = some (d2Delta59Ap,d2Delta59Ep) := by
  rw [d2Delta59Sites,d2Delta59PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta59Poles : polesRoundM 16 24 12 128 d2Delta59Lo d2Delta59Hi d2Delta59Fq.poles d2Delta59Qd = some (d2Delta59Aq,d2Delta59Eq) := by decide +kernel
theorem d2Delta59Laurent : laurentRoundM 16 30 128 d2Delta59Lo d2Delta59Hi d2Delta59Ts d2Delta59Ld = some (d2Delta59Al,d2Delta59El) := by decide +kernel
theorem d2Delta59Small : chebPolyUB (vecAdd d2Delta59S (vecAdd d2Delta59Ap (vecAdd d2Delta59Aq d2Delta59Al))) d2Delta59Gam+d2Delta59Es+d2Delta59Ep+d2Delta59Eq+d2Delta59El ≤ (d2LitsStandaloneDelta007.q2 (-7377435274580079895003) 1 (-80)) := by decide +kernel
theorem d2Delta59Check : chebRoundPieceL d2Delta59Fq d2Delta59Ts 16 24 12 20 30 128 d2Delta59Lo d2Delta59Hi d2Delta59Pd d2Delta59Qd d2Delta59Ld d2Delta59Gam (d2LitsStandaloneDelta007.q2 (-7377435274580079895003) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta59Fq d2Delta59Ts 16 24 12 20 30 128 d2Delta59Lo d2Delta59Hi d2Delta59Pd d2Delta59Qd d2Delta59Ld d2Delta59Gam d2Delta59S d2Delta59Ap d2Delta59Aq d2Delta59Al d2Delta59Es d2Delta59Ep d2Delta59Eq d2Delta59El (by decide +kernel) d2Delta59Shift d2Delta59Plogs d2Delta59Poles d2Delta59Laurent]
  exact decide_eq_true d2Delta59Small
theorem d2Delta59Bound : ∀ x ∈ Icc ((d2Delta59Lo : ℚ) : ℝ) ((d2Delta59Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-7377435274580079895003) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta59Fq d2Delta59Ts 16 24 12 20 30 128 d2Delta59Lo d2Delta59Hi d2Delta59Pd d2Delta59Qd d2Delta59Ld d2Delta59Gam (d2LitsStandaloneDelta007.q2 (-7377435274580079895003) 1 (-80)) d2Delta59Check
  simpa only [d2Delta59Fq, d2Delta59Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta59Shift
#print axioms d2Delta59Sites
#print axioms d2Delta59PData
#print axioms d2Delta59Plogs
#print axioms d2Delta59Poles
#print axioms d2Delta59Laurent
#print axioms d2Delta59Small
#print axioms d2Delta59Check
#print axioms d2Delta59Bound

def d2Delta60Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta60Ts : List LTerm := laurentClean []
def d2Delta60Lo : ℚ := (d2LitsStandaloneDelta007.q2 (41378777) 1 (-29))
def d2Delta60Hi : ℚ := (d2LitsStandaloneDelta007.q2 (5303291) 1 (-26))
def d2Delta60Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta60Qd : List (ℚ × ℚ) := []
def d2Delta60Ld : List LaurentPieceData := []
def d2Delta60Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-1114849034401667773692667426556915237471344297, 1, -157, -5473124332585060342613516926498849381773, 1, -160, 251228674873400345549683893165413753041, 1, -160, 3447309143637939761623922288036505343, 1, -160, -31609964420776809644008397798567593, 1, -158, -542277656872056169596374637869215, 1, -160, 23994602610955492479239890194195, 1, -160, 1334441358177831958065925367, 1, -158, -2180730781577533198561408839, 1, -160, 4497178336957890490237155, 1, -160, 51817709233178861283531, 1, -159, -367472835817831907289, 1, -160, -686100125906350705, 1, -158, 13046882119459233, 1, -160, 22908171595533, 1, -159, -142633426675, 1, -159, -3559578429, 1, -160, -2487753955, 1, -160, -499881561, 1, -158, -1608767697, 1, -160, -639456919, 1, -159, -1010141501, 1, -160, -398081867, 1, -159, -308204879, 1, -159, -241041915, 1, -159, -365281507, 1, -160, -283711599, 1, -160, -210056907, 1, -160, -81077147, 1, -159, -58567099, 1, -159, -2810513, 1, -155, -63293493, 1, -160])
def d2Delta60S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-1038284102288130777586279154749141747, 1, -127, -1276719610076766088968332051609, 1, -128, 117223081314214764438999441489, 1, -128, 1606541036868505430467650839, 1, -127, -235780829412062954485275655, 1, -128, -1010140217427112661359117, 1, -127, 178903729355001042745561, 1, -128, 78935543549634366349, 1, -128, -65021731971783829297, 1, -128, 268293701784427541, 1, -128, 12358230924692105, 1, -128, -43826397739285, 1, -127, -654469023397, 1, -127, 12446509153, 1, -128, 43706039, 1, -127, -1074147, 1, -128, -3933, 1, -128, 1, 1, -122, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta60Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta60Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta60Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta60Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta60Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta60Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta60El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta60Shift : polyRoundApx 128 d2Delta60Lo d2Delta60Hi d2Delta60Fq.poly = (d2Delta60S,d2Delta60Es) := by decide +kernel
theorem d2Delta60Sites : mergeSites d2Delta60Fq.plogs = [] := by decide +kernel
theorem d2Delta60PData : d2Delta60Pd = [] := by decide +kernel
theorem d2Delta60Plogs : plogsRoundM 16 24 20 128 d2Delta60Lo d2Delta60Hi (mergeSites d2Delta60Fq.plogs) d2Delta60Pd = some (d2Delta60Ap,d2Delta60Ep) := by
  rw [d2Delta60Sites,d2Delta60PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta60Poles : polesRoundM 16 24 12 128 d2Delta60Lo d2Delta60Hi d2Delta60Fq.poles d2Delta60Qd = some (d2Delta60Aq,d2Delta60Eq) := by decide +kernel
theorem d2Delta60Laurent : laurentRoundM 16 30 128 d2Delta60Lo d2Delta60Hi d2Delta60Ts d2Delta60Ld = some (d2Delta60Al,d2Delta60El) := by decide +kernel
theorem d2Delta60Small : chebPolyUB (vecAdd d2Delta60S (vecAdd d2Delta60Ap (vecAdd d2Delta60Aq d2Delta60Al))) d2Delta60Gam+d2Delta60Es+d2Delta60Ep+d2Delta60Eq+d2Delta60El ≤ (d2LitsStandaloneDelta007.q2 (-7377447319413752294595) 1 (-80)) := by decide +kernel
theorem d2Delta60Check : chebRoundPieceL d2Delta60Fq d2Delta60Ts 16 24 12 20 30 128 d2Delta60Lo d2Delta60Hi d2Delta60Pd d2Delta60Qd d2Delta60Ld d2Delta60Gam (d2LitsStandaloneDelta007.q2 (-7377447319413752294595) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta60Fq d2Delta60Ts 16 24 12 20 30 128 d2Delta60Lo d2Delta60Hi d2Delta60Pd d2Delta60Qd d2Delta60Ld d2Delta60Gam d2Delta60S d2Delta60Ap d2Delta60Aq d2Delta60Al d2Delta60Es d2Delta60Ep d2Delta60Eq d2Delta60El (by decide +kernel) d2Delta60Shift d2Delta60Plogs d2Delta60Poles d2Delta60Laurent]
  exact decide_eq_true d2Delta60Small
theorem d2Delta60Bound : ∀ x ∈ Icc ((d2Delta60Lo : ℚ) : ℝ) ((d2Delta60Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-7377447319413752294595) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta60Fq d2Delta60Ts 16 24 12 20 30 128 d2Delta60Lo d2Delta60Hi d2Delta60Pd d2Delta60Qd d2Delta60Ld d2Delta60Gam (d2LitsStandaloneDelta007.q2 (-7377447319413752294595) 1 (-80)) d2Delta60Check
  simpa only [d2Delta60Fq, d2Delta60Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta60Shift
#print axioms d2Delta60Sites
#print axioms d2Delta60PData
#print axioms d2Delta60Plogs
#print axioms d2Delta60Poles
#print axioms d2Delta60Laurent
#print axioms d2Delta60Small
#print axioms d2Delta60Check
#print axioms d2Delta60Bound

def d2Delta61Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta61Ts : List LTerm := laurentClean []
def d2Delta61Lo : ℚ := (d2LitsStandaloneDelta007.q2 (5303291) 1 (-26))
def d2Delta61Hi : ℚ := (d2LitsStandaloneDelta007.q2 (85900207) 1 (-30))
def d2Delta61Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta61Qd : List (ℚ × ℚ) := []
def d2Delta61Ld : List LaurentPieceData := []
def d2Delta61Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-8918799508641160226352298241731519644384475353, 1, -160, -1946172455869636833666335190399882583437, 1, -160, 17231286078942566610799901958774946715, 1, -158, 236877186077831231172316367610013439, 1, -160, -4107775064742231555332046747382897, 1, -159, -3513208614215877478468132796575, 1, -160, 368459044707800317074102309731, 1, -160, -88407262292014932450456329, 1, -158, -7889716167728784322086725, 1, -160, 14477547286628050632931, 1, -160, 43946914346268805887, 1, -159, -223064243986218969, 1, -160, -537586887293617, 1, -160, 1789126255009, 1, -160, -1261103371, 1, -159, -1883201267, 1, -159, -1521017829, 1, -159, -2491948259, 1, -160, -998121455, 1, -159, -1608767697, 1, -160, -159484039, 1, -157, -1010141501, 1, -160, -396875215, 1, -159, -308204879, 1, -159, -480329825, 1, -160, -365281507, 1, -160, -141262555, 1, -159, -210056907, 1, -160, -80701829, 1, -159, -58567099, 1, -159, -89491123, 1, -160, -63293493, 1, -160])
def d2Delta61S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-1038284923133268074681864080473804347, 1, -127, -453294046454000720939292526829, 1, -128, 32111075628803039119529467471, 1, -128, 220625425846931788622939173, 1, -128, -15306772741584904519884785, 1, -128, -13078498914691612304681, 1, -128, 1372852047955566500915, 1, -127, -2635712600564553015, 1, -127, -235158060045407625, 1, -128, 431537661251141, 1, -127, 2619632477151, 1, -126, -26594110405, 1, -127, -256351603, 1, -128, 855819, 1, -127, 951, 1, -126, -9, 1, -126, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta61Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta61Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta61Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta61Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta61Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta61Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta61El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta61Shift : polyRoundApx 128 d2Delta61Lo d2Delta61Hi d2Delta61Fq.poly = (d2Delta61S,d2Delta61Es) := by decide +kernel
theorem d2Delta61Sites : mergeSites d2Delta61Fq.plogs = [] := by decide +kernel
theorem d2Delta61PData : d2Delta61Pd = [] := by decide +kernel
theorem d2Delta61Plogs : plogsRoundM 16 24 20 128 d2Delta61Lo d2Delta61Hi (mergeSites d2Delta61Fq.plogs) d2Delta61Pd = some (d2Delta61Ap,d2Delta61Ep) := by
  rw [d2Delta61Sites,d2Delta61PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta61Poles : polesRoundM 16 24 12 128 d2Delta61Lo d2Delta61Hi d2Delta61Fq.poles d2Delta61Qd = some (d2Delta61Aq,d2Delta61Eq) := by decide +kernel
theorem d2Delta61Laurent : laurentRoundM 16 30 128 d2Delta61Lo d2Delta61Hi d2Delta61Ts d2Delta61Ld = some (d2Delta61Al,d2Delta61El) := by decide +kernel
theorem d2Delta61Small : chebPolyUB (vecAdd d2Delta61S (vecAdd d2Delta61Ap (vecAdd d2Delta61Aq d2Delta61Al))) d2Delta61Gam+d2Delta61Es+d2Delta61Ep+d2Delta61Eq+d2Delta61El ≤ (d2LitsStandaloneDelta007.q2 (-7377456373743030713023) 1 (-80)) := by decide +kernel
theorem d2Delta61Check : chebRoundPieceL d2Delta61Fq d2Delta61Ts 16 24 12 20 30 128 d2Delta61Lo d2Delta61Hi d2Delta61Pd d2Delta61Qd d2Delta61Ld d2Delta61Gam (d2LitsStandaloneDelta007.q2 (-7377456373743030713023) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta61Fq d2Delta61Ts 16 24 12 20 30 128 d2Delta61Lo d2Delta61Hi d2Delta61Pd d2Delta61Qd d2Delta61Ld d2Delta61Gam d2Delta61S d2Delta61Ap d2Delta61Aq d2Delta61Al d2Delta61Es d2Delta61Ep d2Delta61Eq d2Delta61El (by decide +kernel) d2Delta61Shift d2Delta61Plogs d2Delta61Poles d2Delta61Laurent]
  exact decide_eq_true d2Delta61Small
theorem d2Delta61Bound : ∀ x ∈ Icc ((d2Delta61Lo : ℚ) : ℝ) ((d2Delta61Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-7377456373743030713023) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta61Fq d2Delta61Ts 16 24 12 20 30 128 d2Delta61Lo d2Delta61Hi d2Delta61Pd d2Delta61Qd d2Delta61Ld d2Delta61Gam (d2LitsStandaloneDelta007.q2 (-7377456373743030713023) 1 (-80)) d2Delta61Check
  simpa only [d2Delta61Fq, d2Delta61Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta61Shift
#print axioms d2Delta61Sites
#print axioms d2Delta61PData
#print axioms d2Delta61Plogs
#print axioms d2Delta61Poles
#print axioms d2Delta61Laurent
#print axioms d2Delta61Small
#print axioms d2Delta61Check
#print axioms d2Delta61Bound

def d2Delta62Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta62Ts : List LTerm := laurentClean []
def d2Delta62Lo : ℚ := (d2LitsStandaloneDelta007.q2 (85900207) 1 (-30))
def d2Delta62Hi : ℚ := (d2LitsStandaloneDelta007.q2 (22260715) 1 (-28))
def d2Delta62Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta62Qd : List (ℚ × ℚ) := []
def d2Delta62Ld : List LaurentPieceData := []
def d2Delta62Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-2229701118289957022755935041106608977588114227, 1, -158, -2446664905663581575009506860604358764709, 1, -160, 640837542537215131228643341552755065301, 1, -160, -162042118035325076304666306988772589, 1, -158, -647583414735550277791971292984714673, 1, -160, 3264265457970257667889747300594731, 1, -160, 61015575621097849752163735819237, 1, -158, -1790357782232376210923435550257, 1, -160, -43360200899208940702039203025, 1, -160, 406361635713664261762220603, 1, -160, 3910869614658283501814211, 1, -160, -46977590339227779131749, 1, -160, -181429754455951658579, 1, -160, 3115604557813395589, 1, -160, 4156234381381425, 1, -160, -135897756245433, 1, -160, -662016981, 1, -158, 30306447, 1, -154, -529950511, 1, -158, -370742167, 1, -158, -677226215, 1, -159, -922981809, 1, -160, -210715751, 1, -158, -558303297, 1, -160, -127406261, 1, -158, -327989301, 1, -160, -37399135, 1, -157, -187023485, 1, -160, -170443913, 1, -160, -12930959, 1, -157, -47080961, 1, -159, -55472621, 1, -160])
def d2Delta62S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-2076571135466265992410718000614612151, 1, -128, -4446890791557426520127512653, 1, -121, 4681569942118517679932022503, 1, -122, -309438852888315901738914355, 1, -127, -302236832655052254924826125, 1, -126, 3051766136500882094561097, 1, -126, 14226494880413109087773, 1, -121, -6683234514496734678987, 1, -126, -646700253984854723649, 1, -127, 24251853928510378975, 1, -128, 466471563785301605, 1, -128, -11209989888883155, 1, -128, -43270097192759, 1, -127, 743304129389, 1, -126, 7927378773, 1, -128, -518671447, 1, -128, 4823, 1, -128, 4061, 1, -124, -107, 1, -128, -7, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta62Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta62Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta62Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta62Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta62Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta62Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta62El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta62Shift : polyRoundApx 128 d2Delta62Lo d2Delta62Hi d2Delta62Fq.poly = (d2Delta62S,d2Delta62Es) := by decide +kernel
theorem d2Delta62Sites : mergeSites d2Delta62Fq.plogs = [] := by decide +kernel
theorem d2Delta62PData : d2Delta62Pd = [] := by decide +kernel
theorem d2Delta62Plogs : plogsRoundM 16 24 20 128 d2Delta62Lo d2Delta62Hi (mergeSites d2Delta62Fq.plogs) d2Delta62Pd = some (d2Delta62Ap,d2Delta62Ep) := by
  rw [d2Delta62Sites,d2Delta62PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta62Poles : polesRoundM 16 24 12 128 d2Delta62Lo d2Delta62Hi d2Delta62Fq.poles d2Delta62Qd = some (d2Delta62Aq,d2Delta62Eq) := by decide +kernel
theorem d2Delta62Laurent : laurentRoundM 16 30 128 d2Delta62Lo d2Delta62Hi d2Delta62Ts d2Delta62Ld = some (d2Delta62Al,d2Delta62El) := by decide +kernel
theorem d2Delta62Small : chebPolyUB (vecAdd d2Delta62S (vecAdd d2Delta62Ap (vecAdd d2Delta62Aq d2Delta62Al))) d2Delta62Gam+d2Delta62Es+d2Delta62Ep+d2Delta62Eq+d2Delta62El ≤ (d2LitsStandaloneDelta007.q2 (-7377459592352139135499) 1 (-80)) := by decide +kernel
theorem d2Delta62Check : chebRoundPieceL d2Delta62Fq d2Delta62Ts 16 24 12 20 30 128 d2Delta62Lo d2Delta62Hi d2Delta62Pd d2Delta62Qd d2Delta62Ld d2Delta62Gam (d2LitsStandaloneDelta007.q2 (-7377459592352139135499) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta62Fq d2Delta62Ts 16 24 12 20 30 128 d2Delta62Lo d2Delta62Hi d2Delta62Pd d2Delta62Qd d2Delta62Ld d2Delta62Gam d2Delta62S d2Delta62Ap d2Delta62Aq d2Delta62Al d2Delta62Es d2Delta62Ep d2Delta62Eq d2Delta62El (by decide +kernel) d2Delta62Shift d2Delta62Plogs d2Delta62Poles d2Delta62Laurent]
  exact decide_eq_true d2Delta62Small
theorem d2Delta62Bound : ∀ x ∈ Icc ((d2Delta62Lo : ℚ) : ℝ) ((d2Delta62Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-7377459592352139135499) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta62Fq d2Delta62Ts 16 24 12 20 30 128 d2Delta62Lo d2Delta62Hi d2Delta62Pd d2Delta62Qd d2Delta62Ld d2Delta62Gam (d2LitsStandaloneDelta007.q2 (-7377459592352139135499) 1 (-80)) d2Delta62Check
  simpa only [d2Delta62Fq, d2Delta62Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta62Shift
#print axioms d2Delta62Sites
#print axioms d2Delta62PData
#print axioms d2Delta62Plogs
#print axioms d2Delta62Poles
#print axioms d2Delta62Laurent
#print axioms d2Delta62Small
#print axioms d2Delta62Check
#print axioms d2Delta62Bound

def d2Delta63Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta63Ts : List LTerm := laurentClean []
def d2Delta63Lo : ℚ := (d2LitsStandaloneDelta007.q2 (22260715) 1 (-28))
def d2Delta63Hi : ℚ := (d2LitsStandaloneDelta007.q2 (92185513) 1 (-30))
def d2Delta63Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta63Qd : List (ℚ × ℚ) := []
def d2Delta63Ld : List LaurentPieceData := []
def d2Delta63Gam : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-8918804384240640577901591480769745954180363013, 1, -160, 2479714594153579188408886039095477458779, 1, -160, 143505970933434785509519352000013322021, 1, -158, -2547161385484169609158490731972766957, 1, -158, -528533038124912427480159176792382423, 1, -160, 8377904063966520890176535373755435, 1, -160, 176897329093098222489399405988085, 1, -160, -2917800679939320764233424070193, 1, -160, -13216279010368858644687753511, 1, -159, 519476148509614890930504251, 1, -160, 427526371234806554858071, 1, -158, -51748574089048556038501, 1, -160, -4326215653323243161, 1, -158, 3122640395136430213, 1, -160, -953684191558039, 1, -158, -126879762800057, 1, -160, 136200368841, 1, -159, 22263695, 1, -154, -984854539, 1, -159, -370738071, 1, -158, -620539159, 1, -159, -922981809, 1, -160, -381917831, 1, -159, -558303297, 1, -160, -228192949, 1, -159, -327989301, 1, -160, -264533331, 1, -160, -187023485, 1, -160, -4645085, 1, -155, -12930959, 1, -157, -40457975, 1, -159, -55472621, 1, -160])
def d2Delta63S : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [-1038285549589576464324375520003203611, 1, -127, 584479989653683656479693460771, 1, -128, 134142955854806190175869390611, 1, -127, -9527966312182285918497414247, 1, -128, -986447466232140589652949201, 1, -128, 15643132289065633841789033, 1, -127, 1319563756979205608341475, 1, -128, -43548319379990640537431, 1, -128, -788261294640553439579, 1, -128, 30997132410473516017, 1, -128, 203885179693600449, 1, -128, -6173751334519529, 1, -127, -4113060881311, 1, -127, 372474669131, 1, -125, -7284431893, 1, -128, -242118571, 1, -127, 262831, 1, -125, 57117, 1, -128, -81, 1, -126, -3, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta63Ap : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta63Aq : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta63Al : List ℚ := d2LitsStandaloneDelta007.q2listC (raw_ints% [])
def d2Delta63Es : ℚ := (d2LitsStandaloneDelta007.q2 (61) 1 (-127))
def d2Delta63Ep : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta63Eq : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
def d2Delta63El : ℚ := (d2LitsStandaloneDelta007.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta63Shift : polyRoundApx 128 d2Delta63Lo d2Delta63Hi d2Delta63Fq.poly = (d2Delta63S,d2Delta63Es) := by decide +kernel
theorem d2Delta63Sites : mergeSites d2Delta63Fq.plogs = [] := by decide +kernel
theorem d2Delta63PData : d2Delta63Pd = [] := by decide +kernel
theorem d2Delta63Plogs : plogsRoundM 16 24 20 128 d2Delta63Lo d2Delta63Hi (mergeSites d2Delta63Fq.plogs) d2Delta63Pd = some (d2Delta63Ap,d2Delta63Ep) := by
  rw [d2Delta63Sites,d2Delta63PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta63Poles : polesRoundM 16 24 12 128 d2Delta63Lo d2Delta63Hi d2Delta63Fq.poles d2Delta63Qd = some (d2Delta63Aq,d2Delta63Eq) := by decide +kernel
theorem d2Delta63Laurent : laurentRoundM 16 30 128 d2Delta63Lo d2Delta63Hi d2Delta63Ts d2Delta63Ld = some (d2Delta63Al,d2Delta63El) := by decide +kernel
theorem d2Delta63Small : chebPolyUB (vecAdd d2Delta63S (vecAdd d2Delta63Ap (vecAdd d2Delta63Aq d2Delta63Al))) d2Delta63Gam+d2Delta63Es+d2Delta63Ep+d2Delta63Eq+d2Delta63El ≤ (d2LitsStandaloneDelta007.q2 (-7377459538931416019771) 1 (-80)) := by decide +kernel
theorem d2Delta63Check : chebRoundPieceL d2Delta63Fq d2Delta63Ts 16 24 12 20 30 128 d2Delta63Lo d2Delta63Hi d2Delta63Pd d2Delta63Qd d2Delta63Ld d2Delta63Gam (d2LitsStandaloneDelta007.q2 (-7377459538931416019771) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta63Fq d2Delta63Ts 16 24 12 20 30 128 d2Delta63Lo d2Delta63Hi d2Delta63Pd d2Delta63Qd d2Delta63Ld d2Delta63Gam d2Delta63S d2Delta63Ap d2Delta63Aq d2Delta63Al d2Delta63Es d2Delta63Ep d2Delta63Eq d2Delta63El (by decide +kernel) d2Delta63Shift d2Delta63Plogs d2Delta63Poles d2Delta63Laurent]
  exact decide_eq_true d2Delta63Small
theorem d2Delta63Bound : ∀ x ∈ Icc ((d2Delta63Lo : ℚ) : ℝ) ((d2Delta63Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta007.q2 (-7377459538931416019771) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta63Fq d2Delta63Ts 16 24 12 20 30 128 d2Delta63Lo d2Delta63Hi d2Delta63Pd d2Delta63Qd d2Delta63Ld d2Delta63Gam (d2LitsStandaloneDelta007.q2 (-7377459538931416019771) 1 (-80)) d2Delta63Check
  simpa only [d2Delta63Fq, d2Delta63Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta63Shift
#print axioms d2Delta63Sites
#print axioms d2Delta63PData
#print axioms d2Delta63Plogs
#print axioms d2Delta63Poles
#print axioms d2Delta63Laurent
#print axioms d2Delta63Small
#print axioms d2Delta63Check
#print axioms d2Delta63Bound

end StandaloneDelta007
end CatalanMeasure.GenD.Signed.Data.Cells
