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
namespace d2LitsStandaloneDelta016
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta016
namespace StandaloneDelta016
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta016.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta016.q2listC (raw_ints% []))⟩
def d2Delta128Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta128Ts : List LTerm := laurentClean []
def d2Delta128Lo : ℚ := (d2LitsStandaloneDelta016.q2 (57680841) 1 (-26))
def d2Delta128Hi : ℚ := (d2LitsStandaloneDelta016.q2 (7341049) 1 (-23))
def d2Delta128Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta128Qd : List (ℚ × ℚ) := []
def d2Delta128Ld : List LaurentPieceData := []
def d2Delta128Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-4459425396535299249867854943465571618945501493, 1, -159, 7548818207198700601779540803473984926373, 1, -160, -55198050679965888895781482262110271377321, 1, -160, -10510909733098823744421362203729124604191, 1, -160, 5622849042163478268601475883149937059313, 1, -160, 178518471022083916289780403812461906223, 1, -158, -171706063500995252884751963139658403815, 1, -160, -2606268725078618348864504308117156963, 1, -157, 2440657607731480542652331537065400827, 1, -160, 336260620082171995337757760571327489, 1, -160, -8636015206528319739667023260485257, 1, -159, -826603576243503237047399133661641, 1, -158, 39140845767755312412409838453201, 1, -160, 2591839621011300779019923063709, 1, -157, 163589769820137096786127028283, 1, -159, -82956165192581371531645435201, 1, -160, -3377893891242910655338046721, 1, -160, 96727078345603626601496337, 1, -159, 15078760719381557546161179, 1, -160, -63685329764525189642277, 1, -159, -19683480420255762780663, 1, -159, -744070135383988901465, 1, -160, 7205050927240204447, 1, -157, 88118447404043085, 1, -155, -20242684535681499, 1, -160, -4723181155124489, 1, -160, -95498359718877, 1, -160, 3464887712775, 1, -160, 50498883933, 1, -158, 769857595, 1, -159, -40747713, 1, -158, -730567, 1, -157])
def d2Delta128S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-2076567569283499480447624670023759255, 1, -128, 9965368281695596230811428886487, 1, -128, -36914965666566988926057749044099, 1, -128, -13395634312789099234860874894945, 1, -128, 12484874988651276841355268071331, 1, -128, 1619313598704790706338661078703, 1, -127, -1429320355655978290343788690025, 1, -128, -358004119608996229243832498977, 1, -128, 77945606511248135122200608883, 1, -128, 22292252076010842458767715041, 1, -128, -131989413160399342445600647, 1, -124, -854377127426736497969075853, 1, -128, 4077042129377687867230989, 1, -126, 20982897733218884592221479, 1, -128, 731073730532750353440643, 1, -128, -41133653888501462366267, 1, -125, -27893590967846197664243, 1, -128, 373325041689142748385, 1, -125, 60570437302922741677, 1, -125, -6780293787165143021, 1, -128, -4960932282468109571, 1, -128, -49452640014199545, 1, -126, 28367751313554973, 1, -128, 717526339772133, 1, -126, -34547851782371, 1, -128, -4703253595309, 1, -126, -790781929183, 1, -128, 53401976275, 1, -128, 3232354881, 1, -127, 107457083, 1, -128, -20285715, 1, -128, -1463075, 1, -128, -6035, 1, -128, 2223, 1, -127, 251, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta128Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta128Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta128Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta128Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta128Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta128Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta128El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta128Shift : polyRoundApx 128 d2Delta128Lo d2Delta128Hi d2Delta128Fq.poly = (d2Delta128S,d2Delta128Es) := by decide +kernel
theorem d2Delta128Sites : mergeSites d2Delta128Fq.plogs = [] := by decide +kernel
theorem d2Delta128PData : d2Delta128Pd = [] := by decide +kernel
theorem d2Delta128Plogs : plogsRoundM 16 24 20 128 d2Delta128Lo d2Delta128Hi (mergeSites d2Delta128Fq.plogs) d2Delta128Pd = some (d2Delta128Ap,d2Delta128Ep) := by
  rw [d2Delta128Sites,d2Delta128PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta128Poles : polesRoundM 16 24 12 128 d2Delta128Lo d2Delta128Hi d2Delta128Fq.poles d2Delta128Qd = some (d2Delta128Aq,d2Delta128Eq) := by decide +kernel
theorem d2Delta128Laurent : laurentRoundM 16 30 128 d2Delta128Lo d2Delta128Hi d2Delta128Ts d2Delta128Ld = some (d2Delta128Al,d2Delta128El) := by decide +kernel
theorem d2Delta128Small : chebPolyUB (vecAdd d2Delta128S (vecAdd d2Delta128Ap (vecAdd d2Delta128Aq d2Delta128Al))) d2Delta128Gam+d2Delta128Es+d2Delta128Ep+d2Delta128Eq+d2Delta128El ≤ (d2LitsStandaloneDelta016.q2 (-7377434461494361769893) 1 (-80)) := by decide +kernel
theorem d2Delta128Check : chebRoundPieceL d2Delta128Fq d2Delta128Ts 16 24 12 20 30 128 d2Delta128Lo d2Delta128Hi d2Delta128Pd d2Delta128Qd d2Delta128Ld d2Delta128Gam (d2LitsStandaloneDelta016.q2 (-7377434461494361769893) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta128Fq d2Delta128Ts 16 24 12 20 30 128 d2Delta128Lo d2Delta128Hi d2Delta128Pd d2Delta128Qd d2Delta128Ld d2Delta128Gam d2Delta128S d2Delta128Ap d2Delta128Aq d2Delta128Al d2Delta128Es d2Delta128Ep d2Delta128Eq d2Delta128El (by decide +kernel) d2Delta128Shift d2Delta128Plogs d2Delta128Poles d2Delta128Laurent]
  exact decide_eq_true d2Delta128Small
theorem d2Delta128Bound : ∀ x ∈ Icc ((d2Delta128Lo : ℚ) : ℝ) ((d2Delta128Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-7377434461494361769893) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta128Fq d2Delta128Ts 16 24 12 20 30 128 d2Delta128Lo d2Delta128Hi d2Delta128Pd d2Delta128Qd d2Delta128Ld d2Delta128Gam (d2LitsStandaloneDelta016.q2 (-7377434461494361769893) 1 (-80)) d2Delta128Check
  simpa only [d2Delta128Fq, d2Delta128Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta128Shift
#print axioms d2Delta128Sites
#print axioms d2Delta128PData
#print axioms d2Delta128Plogs
#print axioms d2Delta128Poles
#print axioms d2Delta128Laurent
#print axioms d2Delta128Small
#print axioms d2Delta128Check
#print axioms d2Delta128Bound

def d2Delta129Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta129Ts : List LTerm := laurentClean []
def d2Delta129Lo : ℚ := (d2LitsStandaloneDelta016.q2 (7341049) 1 (-23))
def d2Delta129Hi : ℚ := (d2LitsStandaloneDelta016.q2 (59775943) 1 (-26))
def d2Delta129Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta129Qd : List (ℚ × ℚ) := []
def d2Delta129Ld : List LaurentPieceData := []
def d2Delta129Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-8918872712547925216883927734317383939507522017, 1, -160, 119983297060205603114799312111337329755945, 1, -160, 21284685678654711735520385018167169743331, 1, -158, -3269001870852484934988742279137294535463, 1, -158, -8181542672273276461331327429212549612937, 1, -160, 226584968487472323285327193328185000447, 1, -159, 312935730279565174939093292663416259243, 1, -160, -2678851435578957867911921339195562459, 1, -160, -6096812131773841624862296022356749125, 1, -160, -135631384099907665716865189080287827, 1, -160, 16995186527904740668643735235622903, 1, -158, 3266619880025089487584239587155331, 1, -160, -446167197992698087712107684078957, 1, -160, -34879962037861292802797671449315, 1, -160, 1536443960614519173291025240247, 1, -160, 217394856826698119857424533051, 1, -160, -245297004560079063690752327, 1, -160, -415685796715981264910709071, 1, -159, -11842623625791649349910897, 1, -159, 1790284230837317613062849, 1, -160, 3644543175097676463761, 1, -155, -877896496134725860039, 1, -160, -281990854983591584243, 1, -160, -3241013034260165, 1, -149, 158159827538796633, 1, -159, 20528419328632387, 1, -160, 63680323749415, 1, -159, -12635673688699, 1, -159, -923560966645, 1, -160, 187561305, 1, -156, 282969783, 1, -158, 30790057, 1, -160])
def d2Delta129S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-2076608676448064616490484875636589977, 1, -128, 18800453292598135551932314908605, 1, -127, 28121424751893585062521936461027, 1, -127, -14319186357859926299439957467543, 1, -128, -4742545766131982210868459110059, 1, -126, 871721448373692117976457554275, 1, -127, 1356527119949701371066468410433, 1, -127, -19504095090952401329342704219, 1, -128, -101343324691046595367524290399, 1, -127, -2591192217185432015875232615, 1, -126, 4378146771433910377264033571, 1, -127, 111460551327417845297037019, 1, -125, -223011839197172988453857699, 1, -128, -36469470173364140313686379, 1, -128, 1465870709150213805235341, 1, -127, 884251027421547768418097, 1, -128, 767448388541902152291, 1, -127, -3301788586757264863947, 1, -126, -795812092259429829205, 1, -128, 110300123467997795667, 1, -128, 3750873610480442923, 1, -126, -175666239840943591, 1, -128, -141377952751670233, 1, -128, -1747803020458929, 1, -126, 610705759475345, 1, -128, 41429227262493, 1, -127, 300155304811, 1, -126, -396013192215, 1, -128, -29925038315, 1, -128, 126769543, 1, -128, 35543521, 1, -126, 7989797, 1, -128, -76361, 1, -128, -16889, 1, -127, -1769, 1, -128, 1, 1, -127, 5, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta129Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta129Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta129Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta129Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta129Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta129Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta129El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta129Shift : polyRoundApx 128 d2Delta129Lo d2Delta129Hi d2Delta129Fq.poly = (d2Delta129S,d2Delta129Es) := by decide +kernel
theorem d2Delta129Sites : mergeSites d2Delta129Fq.plogs = [] := by decide +kernel
theorem d2Delta129PData : d2Delta129Pd = [] := by decide +kernel
theorem d2Delta129Plogs : plogsRoundM 16 24 20 128 d2Delta129Lo d2Delta129Hi (mergeSites d2Delta129Fq.plogs) d2Delta129Pd = some (d2Delta129Ap,d2Delta129Ep) := by
  rw [d2Delta129Sites,d2Delta129PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta129Poles : polesRoundM 16 24 12 128 d2Delta129Lo d2Delta129Hi d2Delta129Fq.poles d2Delta129Qd = some (d2Delta129Aq,d2Delta129Eq) := by decide +kernel
theorem d2Delta129Laurent : laurentRoundM 16 30 128 d2Delta129Lo d2Delta129Hi d2Delta129Ts d2Delta129Ld = some (d2Delta129Al,d2Delta129El) := by decide +kernel
theorem d2Delta129Small : chebPolyUB (vecAdd d2Delta129S (vecAdd d2Delta129Ap (vecAdd d2Delta129Aq d2Delta129Al))) d2Delta129Gam+d2Delta129Es+d2Delta129Ep+d2Delta129Eq+d2Delta129El ≤ (d2LitsStandaloneDelta016.q2 (-7377330695701668737483) 1 (-80)) := by decide +kernel
theorem d2Delta129Check : chebRoundPieceL d2Delta129Fq d2Delta129Ts 16 24 12 20 30 128 d2Delta129Lo d2Delta129Hi d2Delta129Pd d2Delta129Qd d2Delta129Ld d2Delta129Gam (d2LitsStandaloneDelta016.q2 (-7377330695701668737483) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta129Fq d2Delta129Ts 16 24 12 20 30 128 d2Delta129Lo d2Delta129Hi d2Delta129Pd d2Delta129Qd d2Delta129Ld d2Delta129Gam d2Delta129S d2Delta129Ap d2Delta129Aq d2Delta129Al d2Delta129Es d2Delta129Ep d2Delta129Eq d2Delta129El (by decide +kernel) d2Delta129Shift d2Delta129Plogs d2Delta129Poles d2Delta129Laurent]
  exact decide_eq_true d2Delta129Small
theorem d2Delta129Bound : ∀ x ∈ Icc ((d2Delta129Lo : ℚ) : ℝ) ((d2Delta129Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-7377330695701668737483) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta129Fq d2Delta129Ts 16 24 12 20 30 128 d2Delta129Lo d2Delta129Hi d2Delta129Pd d2Delta129Qd d2Delta129Ld d2Delta129Gam (d2LitsStandaloneDelta016.q2 (-7377330695701668737483) 1 (-80)) d2Delta129Check
  simpa only [d2Delta129Fq, d2Delta129Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta129Shift
#print axioms d2Delta129Sites
#print axioms d2Delta129PData
#print axioms d2Delta129Plogs
#print axioms d2Delta129Poles
#print axioms d2Delta129Laurent
#print axioms d2Delta129Small
#print axioms d2Delta129Check
#print axioms d2Delta129Bound

def d2Delta130Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta130Ts : List LTerm := laurentClean []
def d2Delta130Lo : ℚ := (d2LitsStandaloneDelta016.q2 (59775943) 1 (-26))
def d2Delta130Hi : ℚ := (d2LitsStandaloneDelta016.q2 (242246425) 1 (-28))
def d2Delta130Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta130Qd : List (ℚ × ℚ) := []
def d2Delta130Ld : List LaurentPieceData := []
def d2Delta130Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-8918701088006454393072720648954826126749179007, 1, -160, -65478144390587675545815973453652226932973, 1, -160, -20806306661167162531956939273327920836681, 1, -159, 13845173512183207999962506990257546655075, 1, -160, 652743568601715555734115168667429980659, 1, -158, -220014643607292383831810834967147934823, 1, -159, -69732941175142616800197371855051877341, 1, -160, 5397860328462611989756461507374782403, 1, -160, 964351485126945153101620928346784979, 1, -160, -13146428076804270800073524496150645, 1, -159, -3870717441029111671525937549794197, 1, -159, -8253113402123192453851233085695, 1, -158, 37764339233772283878697803814317, 1, -160, 269103172456536064801439627313, 1, -158, -108901847212127620561443231781, 1, -160, -6065503790940581221669665409, 1, -160, 143075762022226118521954345, 1, -160, 18060237710590483317954269, 1, -160, 152780942220019243302127, 1, -160, -30189401709550860844807, 1, -160, -1022603335010409829445, 1, -160, 20119755906025359879, 1, -160, 120289622048872425, 1, -156, 11836129534708449, 1, -159, -803838377003409, 1, -159, -8244505509625, 1, -157, -128836525155, 1, -160, 27799612767, 1, -159, 382571181, 1, -158, -872663, 1, -158, -1227939, 1, -160, -16171, 1, -158])
def d2Delta130S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-32445884403255279479162020583359231, 1, -122, -25437174514865781955592838579157, 1, -128, -6135056192874173562171732753249, 1, -126, 15014481604143837457676910592353, 1, -128, 5679298210055998425902804446981, 1, -128, -1782631413855551697135570931555, 1, -128, -289540607467665998743200305025, 1, -127, 41968172905524010270843679237, 1, -127, 31108500713330738790670779249, 1, -128, -1541260919394878254603889703, 1, -128, -244469718844361416487443945, 1, -126, -354347742012949327944365, 1, -123, 18741492850171608948099393, 1, -128, 278845918135764150024245, 1, -126, -212039201112513957142077, 1, -128, -24326841975157723311901, 1, -128, 1069257306765578808223, 1, -128, 284387321027716083179, 1, -128, 1324750518099548315, 1, -126, -934031859216056223, 1, -127, -130047624455000847, 1, -128, 4774665378003047, 1, -128, 958581889687943, 1, -128, 12372648219101, 1, -127, -3132397510383, 1, -128, -263509332173, 1, -128, -84065363, 1, -124, 435031047, 1, -127, 48929699, 1, -128, -152763, 1, -128, -36685, 1, -126, -7125, 1, -128, -1, 1, -126, 1, 1, -124, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta130Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta130Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta130Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta130Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta130Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta130Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta130El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta130Shift : polyRoundApx 128 d2Delta130Lo d2Delta130Hi d2Delta130Fq.poly = (d2Delta130S,d2Delta130Es) := by decide +kernel
theorem d2Delta130Sites : mergeSites d2Delta130Fq.plogs = [] := by decide +kernel
theorem d2Delta130PData : d2Delta130Pd = [] := by decide +kernel
theorem d2Delta130Plogs : plogsRoundM 16 24 20 128 d2Delta130Lo d2Delta130Hi (mergeSites d2Delta130Fq.plogs) d2Delta130Pd = some (d2Delta130Ap,d2Delta130Ep) := by
  rw [d2Delta130Sites,d2Delta130PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta130Poles : polesRoundM 16 24 12 128 d2Delta130Lo d2Delta130Hi d2Delta130Fq.poles d2Delta130Qd = some (d2Delta130Aq,d2Delta130Eq) := by decide +kernel
theorem d2Delta130Laurent : laurentRoundM 16 30 128 d2Delta130Lo d2Delta130Hi d2Delta130Ts d2Delta130Ld = some (d2Delta130Al,d2Delta130El) := by decide +kernel
theorem d2Delta130Small : chebPolyUB (vecAdd d2Delta130S (vecAdd d2Delta130Ap (vecAdd d2Delta130Aq d2Delta130Al))) d2Delta130Gam+d2Delta130Es+d2Delta130Ep+d2Delta130Eq+d2Delta130El ≤ (d2LitsStandaloneDelta016.q2 (-7377274006593220575481) 1 (-80)) := by decide +kernel
theorem d2Delta130Check : chebRoundPieceL d2Delta130Fq d2Delta130Ts 16 24 12 20 30 128 d2Delta130Lo d2Delta130Hi d2Delta130Pd d2Delta130Qd d2Delta130Ld d2Delta130Gam (d2LitsStandaloneDelta016.q2 (-7377274006593220575481) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta130Fq d2Delta130Ts 16 24 12 20 30 128 d2Delta130Lo d2Delta130Hi d2Delta130Pd d2Delta130Qd d2Delta130Ld d2Delta130Gam d2Delta130S d2Delta130Ap d2Delta130Aq d2Delta130Al d2Delta130Es d2Delta130Ep d2Delta130Eq d2Delta130El (by decide +kernel) d2Delta130Shift d2Delta130Plogs d2Delta130Poles d2Delta130Laurent]
  exact decide_eq_true d2Delta130Small
theorem d2Delta130Bound : ∀ x ∈ Icc ((d2Delta130Lo : ℚ) : ℝ) ((d2Delta130Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-7377274006593220575481) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta130Fq d2Delta130Ts 16 24 12 20 30 128 d2Delta130Lo d2Delta130Hi d2Delta130Pd d2Delta130Qd d2Delta130Ld d2Delta130Gam (d2LitsStandaloneDelta016.q2 (-7377274006593220575481) 1 (-80)) d2Delta130Check
  simpa only [d2Delta130Fq, d2Delta130Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta130Shift
#print axioms d2Delta130Sites
#print axioms d2Delta130PData
#print axioms d2Delta130Plogs
#print axioms d2Delta130Poles
#print axioms d2Delta130Laurent
#print axioms d2Delta130Small
#print axioms d2Delta130Check
#print axioms d2Delta130Bound

def d2Delta131Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta131Ts : List LTerm := laurentClean []
def d2Delta131Lo : ℚ := (d2LitsStandaloneDelta016.q2 (242246425) 1 (-28))
def d2Delta131Hi : ℚ := (d2LitsStandaloneDelta016.q2 (30411747) 1 (-25))
def d2Delta131Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta131Qd : List (ℚ × ℚ) := []
def d2Delta131Ld : List LaurentPieceData := []
def d2Delta131Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-8918793409222559113178370277066201088371351619, 1, -160, 7491338096160517013853599778131253063603, 1, -160, 8781523599871148243702261283288232672981, 1, -160, 44596745077998375611022883226519177657, 1, -160, -31671935495429847399566583128690809509, 1, -159, -6016257779615146940713626952982015, 1, -153, 80095129369237382075282391297698521, 1, -159, 1415707179797618222003567201903803, 1, -159, -199187275080214195547611233391919, 1, -160, -4813954618523641539451493755151, 1, -160, 130473338567885799042612358969, 1, -160, 2283950625095602434358531973, 1, -159, -36357089698991132556936781, 1, -160, -162677506026835614295469, 1, -156, -7868570185271148515755, 1, -160, 889681487253865118967, 1, -160, 10587465107958369521, 1, -160, -156291505096711525, 1, -160, -4086330625108467, 1, -160, -2206529468141, 1, -160, 803177671505, 1, -160, 7746401539, 1, -160, -69689091, 1, -160, -1796957, 1, -158, -629323, 1, -158, -1562513, 1, -160, -325687, 1, -159, -99689, 1, -158, -149859, 1, -160, -89875, 1, -160, -15069, 1, -159, -17667, 1, -160])
def d2Delta131S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-2076570469478708587519254427223889085, 1, -128, 428040371781167265469520145825, 1, -126, 4207875573273178428593891920371, 1, -128, 45156976699918983941082171231, 1, -128, -29946213036903657336383898541, 1, -126, -2943095659036394861733217055, 1, -128, 602708487121909558505273589, 1, -127, 42839964408584605106967185, 1, -128, -5975185933391512867616703, 1, -128, -144969551613645202059231, 1, -127, 15605570558586047242931, 1, -128, 1097158983196169185291, 1, -128, -17283356851130406897, 1, -128, -311875810138835871, 1, -125, -1916532975296285, 1, -125, 1701999855145619, 1, -127, 81338162775065, 1, -128, -1192078493199, 1, -127, -62597768937, 1, -127, -18080999, 1, -125, 24552775, 1, -126, 1905101, 1, -128, -14855, 1, -127, -1689, 1, -128, -15, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta131Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta131Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta131Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta131Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta131Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta131Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta131El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta131Shift : polyRoundApx 128 d2Delta131Lo d2Delta131Hi d2Delta131Fq.poly = (d2Delta131S,d2Delta131Es) := by decide +kernel
theorem d2Delta131Sites : mergeSites d2Delta131Fq.plogs = [] := by decide +kernel
theorem d2Delta131PData : d2Delta131Pd = [] := by decide +kernel
theorem d2Delta131Plogs : plogsRoundM 16 24 20 128 d2Delta131Lo d2Delta131Hi (mergeSites d2Delta131Fq.plogs) d2Delta131Pd = some (d2Delta131Ap,d2Delta131Ep) := by
  rw [d2Delta131Sites,d2Delta131PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta131Poles : polesRoundM 16 24 12 128 d2Delta131Lo d2Delta131Hi d2Delta131Fq.poles d2Delta131Qd = some (d2Delta131Aq,d2Delta131Eq) := by decide +kernel
theorem d2Delta131Laurent : laurentRoundM 16 30 128 d2Delta131Lo d2Delta131Hi d2Delta131Ts d2Delta131Ld = some (d2Delta131Al,d2Delta131El) := by decide +kernel
theorem d2Delta131Small : chebPolyUB (vecAdd d2Delta131S (vecAdd d2Delta131Ap (vecAdd d2Delta131Aq d2Delta131Al))) d2Delta131Gam+d2Delta131Es+d2Delta131Ep+d2Delta131Eq+d2Delta131El ≤ (d2LitsStandaloneDelta016.q2 (-3688719722410259272509) 1 (-79)) := by decide +kernel
theorem d2Delta131Check : chebRoundPieceL d2Delta131Fq d2Delta131Ts 16 24 12 20 30 128 d2Delta131Lo d2Delta131Hi d2Delta131Pd d2Delta131Qd d2Delta131Ld d2Delta131Gam (d2LitsStandaloneDelta016.q2 (-3688719722410259272509) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta131Fq d2Delta131Ts 16 24 12 20 30 128 d2Delta131Lo d2Delta131Hi d2Delta131Pd d2Delta131Qd d2Delta131Ld d2Delta131Gam d2Delta131S d2Delta131Ap d2Delta131Aq d2Delta131Al d2Delta131Es d2Delta131Ep d2Delta131Eq d2Delta131El (by decide +kernel) d2Delta131Shift d2Delta131Plogs d2Delta131Poles d2Delta131Laurent]
  exact decide_eq_true d2Delta131Small
theorem d2Delta131Bound : ∀ x ∈ Icc ((d2Delta131Lo : ℚ) : ℝ) ((d2Delta131Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-3688719722410259272509) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta131Fq d2Delta131Ts 16 24 12 20 30 128 d2Delta131Lo d2Delta131Hi d2Delta131Pd d2Delta131Qd d2Delta131Ld d2Delta131Gam (d2LitsStandaloneDelta016.q2 (-3688719722410259272509) 1 (-79)) d2Delta131Check
  simpa only [d2Delta131Fq, d2Delta131Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta131Shift
#print axioms d2Delta131Sites
#print axioms d2Delta131PData
#print axioms d2Delta131Plogs
#print axioms d2Delta131Poles
#print axioms d2Delta131Laurent
#print axioms d2Delta131Small
#print axioms d2Delta131Check
#print axioms d2Delta131Bound

def d2Delta132Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta132Ts : List LTerm := laurentClean []
def d2Delta132Lo : ℚ := (d2LitsStandaloneDelta016.q2 (30411747) 1 (-25))
def d2Delta132Hi : ℚ := (d2LitsStandaloneDelta016.q2 (244341527) 1 (-28))
def d2Delta132Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta132Qd : List (ℚ × ℚ) := []
def d2Delta132Ld : List LaurentPieceData := []
def d2Delta132Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-8918718511697585705825022494271044557798247683, 1, -160, 31458299106064232625660802161246956120509, 1, -159, 3442893999174273534953985667702542612845, 1, -160, -870858780305040815569735825322959401425, 1, -160, -19060010956454808113503275710891082493, 1, -159, 797584714790656874762215424715369935, 1, -158, 66701467660088739271412321383478141, 1, -159, -620690356014527961503081008214683, 1, -157, -238327733060394017474555809496079, 1, -160, 3433139004787532857856199935099, 1, -160, 246351818946040156664436683249, 1, -160, -257791338061028491389666057, 1, -160, -153553257719311695241962461, 1, -160, -81252784819675846000921, 1, -156, 55925818761318080036413, 1, -160, 512863225864702673437, 1, -159, -9042786796169905231, 1, -160, -388353728051781209, 1, -160, -1328286134515323, 1, -160, 38996547041337, 1, -159, 1023687825569, 1, -160, -4951196113, 1, -160, -231194267, 1, -160, -5338933, 1, -160, -614675, 1, -158, -1053987, 1, -160, -323947, 1, -159, -31063, 1, -157, -149619, 1, -160, -25607, 1, -159, -15065, 1, -159, -9063, 1, -160])
def d2Delta132S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-519137945541020500390257202463879369, 1, -126, 3815230508154514681136155533007, 1, -126, 1674787389418039794706658456323, 1, -128, -825971453384456969499926735643, 1, -128, -72503869260133975817419614907, 1, -128, 750923117963948111888804697, 1, -124, 504099565419319541289882949, 1, -127, -74452642183143234719258959, 1, -128, -1794096491308205348516617, 1, -126, 102397499208804810202121, 1, -127, 29587598742015822547103, 1, -128, -57410781777061006017, 1, -128, -36796846128516677139, 1, -127, -1254536361564941205, 1, -128, 106945654319060383, 1, -128, 492258226754907, 1, -125, -17201811533923, 1, -126, -5948433364065, 1, -128, -1286322517, 1, -123, 148957277, 1, -123, 62781913, 1, -127, -299449, 1, -126, -108983, 1, -128, -337, 1, -126, 9, 1, -126, 1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta132Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta132Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta132Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta132Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta132Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta132Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta132El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta132Shift : polyRoundApx 128 d2Delta132Lo d2Delta132Hi d2Delta132Fq.poly = (d2Delta132S,d2Delta132Es) := by decide +kernel
theorem d2Delta132Sites : mergeSites d2Delta132Fq.plogs = [] := by decide +kernel
theorem d2Delta132PData : d2Delta132Pd = [] := by decide +kernel
theorem d2Delta132Plogs : plogsRoundM 16 24 20 128 d2Delta132Lo d2Delta132Hi (mergeSites d2Delta132Fq.plogs) d2Delta132Pd = some (d2Delta132Ap,d2Delta132Ep) := by
  rw [d2Delta132Sites,d2Delta132PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta132Poles : polesRoundM 16 24 12 128 d2Delta132Lo d2Delta132Hi d2Delta132Fq.poles d2Delta132Qd = some (d2Delta132Aq,d2Delta132Eq) := by decide +kernel
theorem d2Delta132Laurent : laurentRoundM 16 30 128 d2Delta132Lo d2Delta132Hi d2Delta132Ts d2Delta132Ld = some (d2Delta132Al,d2Delta132El) := by decide +kernel
theorem d2Delta132Small : chebPolyUB (vecAdd d2Delta132S (vecAdd d2Delta132Ap (vecAdd d2Delta132Aq d2Delta132Al))) d2Delta132Gam+d2Delta132Es+d2Delta132Ep+d2Delta132Eq+d2Delta132El ≤ (d2LitsStandaloneDelta016.q2 (-461083462235333465813) 1 (-76)) := by decide +kernel
theorem d2Delta132Check : chebRoundPieceL d2Delta132Fq d2Delta132Ts 16 24 12 20 30 128 d2Delta132Lo d2Delta132Hi d2Delta132Pd d2Delta132Qd d2Delta132Ld d2Delta132Gam (d2LitsStandaloneDelta016.q2 (-461083462235333465813) 1 (-76)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta132Fq d2Delta132Ts 16 24 12 20 30 128 d2Delta132Lo d2Delta132Hi d2Delta132Pd d2Delta132Qd d2Delta132Ld d2Delta132Gam d2Delta132S d2Delta132Ap d2Delta132Aq d2Delta132Al d2Delta132Es d2Delta132Ep d2Delta132Eq d2Delta132El (by decide +kernel) d2Delta132Shift d2Delta132Plogs d2Delta132Poles d2Delta132Laurent]
  exact decide_eq_true d2Delta132Small
theorem d2Delta132Bound : ∀ x ∈ Icc ((d2Delta132Lo : ℚ) : ℝ) ((d2Delta132Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-461083462235333465813) 1 (-76)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta132Fq d2Delta132Ts 16 24 12 20 30 128 d2Delta132Lo d2Delta132Hi d2Delta132Pd d2Delta132Qd d2Delta132Ld d2Delta132Gam (d2LitsStandaloneDelta016.q2 (-461083462235333465813) 1 (-76)) d2Delta132Check
  simpa only [d2Delta132Fq, d2Delta132Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta132Shift
#print axioms d2Delta132Sites
#print axioms d2Delta132PData
#print axioms d2Delta132Plogs
#print axioms d2Delta132Poles
#print axioms d2Delta132Laurent
#print axioms d2Delta132Small
#print axioms d2Delta132Check
#print axioms d2Delta132Bound

def d2Delta133Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta133Ts : List LTerm := laurentClean []
def d2Delta133Lo : ℚ := (d2LitsStandaloneDelta016.q2 (244341527) 1 (-28))
def d2Delta133Hi : ℚ := (d2LitsStandaloneDelta016.q2 (246436629) 1 (-28))
def d2Delta133Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta133Qd : List (ℚ × ℚ) := []
def d2Delta133Ld : List LaurentPieceData := []
def d2Delta133Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-2229653065134212998157394173224280976819043811, 1, -158, 75955816756229091659362532079361228395, 1, -158, -11071165444958182044146064821995134984641, 1, -158, -679027593844941091217452747929559689707, 1, -158, 1157535455184615689951525665633850398707, 1, -160, 17836711972509366392474779369902740829, 1, -158, -12015562603897472728598346342191550219, 1, -160, -819044843373729684201793868689869619, 1, -160, 59008768898841536546079424077590891, 1, -160, 2550279754109428011637735842772157, 1, -159, -127802151327809988623836995672581, 1, -160, -2325759464943898313326309101421, 1, -157, -35353472460540935967245537533, 1, -160, 40491255985351352560081223481, 1, -160, 881955567808457558298419149, 1, -160, -48485466253886925649145383, 1, -160, -2244361573584732452718793, 1, -160, 15333463524100592385257, 1, -160, 352056849396628356553, 1, -157, 42356272151734214707, 1, -160, -411799035666364549, 1, -158, -67967401969168141, 1, -160, -98147220040431, 1, -159, 10278241964339, 1, -158, 968093027395, 1, -160, -714495609, 1, -158, -554928601, 1, -160, -10433497, 1, -160, -6937, 1, -157, -26903, 1, -159, -15651, 1, -160, -1275, 1, -157])
def d2Delta133S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-64891114061646788006879384120139679, 1, -123, 2052324837247732479898051979205, 1, -128, -11414264095492276398451502496399, 1, -127, -2872632151886905008149741377747, 1, -128, 1146286160133602302682773269365, 1, -127, 143832186154933419689476510897, 1, -127, -46536704935091387193049013877, 1, -127, -12901051115257303951967752685, 1, -128, 898311952168239680448936283, 1, -127, 316373802453125489442179553, 1, -128, -15176439932932595921112551, 1, -128, -71290256243534912836101, 1, -122, -11428786645795253901921, 1, -127, 39310774129985500338213, 1, -128, 875708476440131429995, 1, -127, -46481735308176217211, 1, -126, -17512035807474262449, 1, -128, 221493447801435221, 1, -128, 86955450933540483, 1, -128, 1336457778017741, 1, -127, -200516674157979, 1, -128, -8412324555107, 1, -127, -107272747667, 1, -128, 40215908315, 1, -128, 1918989963, 1, -128, -5041015, 1, -127, -4338747, 1, -128, -80355, 1, -127, 899, 1, -128, 297, 1, -128, 5, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta133Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta133Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta133Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta133Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta133Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta133Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta133El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta133Shift : polyRoundApx 128 d2Delta133Lo d2Delta133Hi d2Delta133Fq.poly = (d2Delta133S,d2Delta133Es) := by decide +kernel
theorem d2Delta133Sites : mergeSites d2Delta133Fq.plogs = [] := by decide +kernel
theorem d2Delta133PData : d2Delta133Pd = [] := by decide +kernel
theorem d2Delta133Plogs : plogsRoundM 16 24 20 128 d2Delta133Lo d2Delta133Hi (mergeSites d2Delta133Fq.plogs) d2Delta133Pd = some (d2Delta133Ap,d2Delta133Ep) := by
  rw [d2Delta133Sites,d2Delta133PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta133Poles : polesRoundM 16 24 12 128 d2Delta133Lo d2Delta133Hi d2Delta133Fq.poles d2Delta133Qd = some (d2Delta133Aq,d2Delta133Eq) := by decide +kernel
theorem d2Delta133Laurent : laurentRoundM 16 30 128 d2Delta133Lo d2Delta133Hi d2Delta133Ts d2Delta133Ld = some (d2Delta133Al,d2Delta133El) := by decide +kernel
theorem d2Delta133Small : chebPolyUB (vecAdd d2Delta133S (vecAdd d2Delta133Ap (vecAdd d2Delta133Aq d2Delta133Al))) d2Delta133Gam+d2Delta133Es+d2Delta133Ep+d2Delta133Eq+d2Delta133El ≤ (d2LitsStandaloneDelta016.q2 (-57634867157596033717) 1 (-73)) := by decide +kernel
theorem d2Delta133Check : chebRoundPieceL d2Delta133Fq d2Delta133Ts 16 24 12 20 30 128 d2Delta133Lo d2Delta133Hi d2Delta133Pd d2Delta133Qd d2Delta133Ld d2Delta133Gam (d2LitsStandaloneDelta016.q2 (-57634867157596033717) 1 (-73)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta133Fq d2Delta133Ts 16 24 12 20 30 128 d2Delta133Lo d2Delta133Hi d2Delta133Pd d2Delta133Qd d2Delta133Ld d2Delta133Gam d2Delta133S d2Delta133Ap d2Delta133Aq d2Delta133Al d2Delta133Es d2Delta133Ep d2Delta133Eq d2Delta133El (by decide +kernel) d2Delta133Shift d2Delta133Plogs d2Delta133Poles d2Delta133Laurent]
  exact decide_eq_true d2Delta133Small
theorem d2Delta133Bound : ∀ x ∈ Icc ((d2Delta133Lo : ℚ) : ℝ) ((d2Delta133Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-57634867157596033717) 1 (-73)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta133Fq d2Delta133Ts 16 24 12 20 30 128 d2Delta133Lo d2Delta133Hi d2Delta133Pd d2Delta133Qd d2Delta133Ld d2Delta133Gam (d2LitsStandaloneDelta016.q2 (-57634867157596033717) 1 (-73)) d2Delta133Check
  simpa only [d2Delta133Fq, d2Delta133Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta133Shift
#print axioms d2Delta133Sites
#print axioms d2Delta133PData
#print axioms d2Delta133Plogs
#print axioms d2Delta133Poles
#print axioms d2Delta133Laurent
#print axioms d2Delta133Small
#print axioms d2Delta133Check
#print axioms d2Delta133Bound

def d2Delta134Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta134Ts : List LTerm := laurentClean []
def d2Delta134Lo : ℚ := (d2LitsStandaloneDelta016.q2 (246436629) 1 (-28))
def d2Delta134Hi : ℚ := (d2LitsStandaloneDelta016.q2 (61871045) 1 (-26))
def d2Delta134Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta134Qd : List (ℚ × ℚ) := []
def d2Delta134Ld : List LaurentPieceData := []
def d2Delta134Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-8918763660898465487460123353442772383991733845, 1, -160, -54481172216291099483595858223968808244287, 1, -159, -1781827373797233885828735998256961125255, 1, -160, 1287954152034657994108587346996932789383, 1, -160, 10772245277425462116757221943650064371, 1, -159, -5544351508467754180910275249607821685, 1, -160, -116657738667850918994731404728180471, 1, -160, 11021692649993370443826939503153789, 1, -160, 151948862350267730047249003026253, 1, -159, -11012572880470484031850978427449, 1, -160, -213729405426256006998750834889, 1, -159, 1177236773169321713246930357, 1, -158, 348757787613903035591610295, 1, -160, 121698026212279144497611, 1, -157, -165463870839930383955281, 1, -160, -2221962501364415088011, 1, -160, 38833718751737118173, 1, -160, 585105547780336911, 1, -159, 1284898796183665, 1, -160, -296529668285553, 1, -160, -1787514837039, 1, -159, 12117601795, 1, -159, 240118623, 1, -158, 1528165, 1, -159, -1188433, 1, -160, -409905, 1, -159, -245453, 1, -160, -173359, 1, -160, -23453, 1, -159, -31341, 1, -160, -235, 1, -155, -37, 1, -153])
def d2Delta134S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-1038280531928134042673631069938223471, 1, -127, -6568967707993113629422434621671, 1, -126, -435174472799356354280126618667, 1, -127, 1225462689912120130783397442501, 1, -128, 20722426800937014397105734715, 1, -127, -20942840944589575936435895015, 1, -128, -887393360088614566987347889, 1, -128, 20714500633458325716716091, 1, -125, 9184812918383853337893151, 1, -128, -659484112464288634756855, 1, -128, -51457483612267319668351, 1, -128, 279908776496645458005, 1, -126, 20925898540181910787, 1, -125, 480200338174105243, 1, -127, -316782062559117923, 1, -128, -267255447572179, 1, -123, 9253020700741, 1, -123, 8971021522205, 1, -127, 20700087121, 1, -127, -18129720829, 1, -128, -438996811, 1, -128, 2941833, 1, -127, 472097, 1, -128, 6293, 1, -128, -167, 1, -128, -1, 1, -125, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta134Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta134Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta134Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta134Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta134Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta134Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta134El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta134Shift : polyRoundApx 128 d2Delta134Lo d2Delta134Hi d2Delta134Fq.poly = (d2Delta134S,d2Delta134Es) := by decide +kernel
theorem d2Delta134Sites : mergeSites d2Delta134Fq.plogs = [] := by decide +kernel
theorem d2Delta134PData : d2Delta134Pd = [] := by decide +kernel
theorem d2Delta134Plogs : plogsRoundM 16 24 20 128 d2Delta134Lo d2Delta134Hi (mergeSites d2Delta134Fq.plogs) d2Delta134Pd = some (d2Delta134Ap,d2Delta134Ep) := by
  rw [d2Delta134Sites,d2Delta134PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta134Poles : polesRoundM 16 24 12 128 d2Delta134Lo d2Delta134Hi d2Delta134Fq.poles d2Delta134Qd = some (d2Delta134Aq,d2Delta134Eq) := by decide +kernel
theorem d2Delta134Laurent : laurentRoundM 16 30 128 d2Delta134Lo d2Delta134Hi d2Delta134Ts d2Delta134Ld = some (d2Delta134Al,d2Delta134El) := by decide +kernel
theorem d2Delta134Small : chebPolyUB (vecAdd d2Delta134S (vecAdd d2Delta134Ap (vecAdd d2Delta134Aq d2Delta134Al))) d2Delta134Gam+d2Delta134Es+d2Delta134Ep+d2Delta134Eq+d2Delta134El ≤ (d2LitsStandaloneDelta016.q2 (-1844333923730465154003) 1 (-78)) := by decide +kernel
theorem d2Delta134Check : chebRoundPieceL d2Delta134Fq d2Delta134Ts 16 24 12 20 30 128 d2Delta134Lo d2Delta134Hi d2Delta134Pd d2Delta134Qd d2Delta134Ld d2Delta134Gam (d2LitsStandaloneDelta016.q2 (-1844333923730465154003) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta134Fq d2Delta134Ts 16 24 12 20 30 128 d2Delta134Lo d2Delta134Hi d2Delta134Pd d2Delta134Qd d2Delta134Ld d2Delta134Gam d2Delta134S d2Delta134Ap d2Delta134Aq d2Delta134Al d2Delta134Es d2Delta134Ep d2Delta134Eq d2Delta134El (by decide +kernel) d2Delta134Shift d2Delta134Plogs d2Delta134Poles d2Delta134Laurent]
  exact decide_eq_true d2Delta134Small
theorem d2Delta134Bound : ∀ x ∈ Icc ((d2Delta134Lo : ℚ) : ℝ) ((d2Delta134Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-1844333923730465154003) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta134Fq d2Delta134Ts 16 24 12 20 30 128 d2Delta134Lo d2Delta134Hi d2Delta134Pd d2Delta134Qd d2Delta134Ld d2Delta134Gam (d2LitsStandaloneDelta016.q2 (-1844333923730465154003) 1 (-78)) d2Delta134Check
  simpa only [d2Delta134Fq, d2Delta134Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta134Shift
#print axioms d2Delta134Sites
#print axioms d2Delta134PData
#print axioms d2Delta134Plogs
#print axioms d2Delta134Poles
#print axioms d2Delta134Laurent
#print axioms d2Delta134Small
#print axioms d2Delta134Check
#print axioms d2Delta134Bound

def d2Delta135Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta135Ts : List LTerm := laurentClean []
def d2Delta135Lo : ℚ := (d2LitsStandaloneDelta016.q2 (61871045) 1 (-26))
def d2Delta135Hi : ℚ := (d2LitsStandaloneDelta016.q2 (124789641) 1 (-27))
def d2Delta135Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta135Qd : List (ℚ × ℚ) := []
def d2Delta135Ld : List LaurentPieceData := []
def d2Delta135Gam : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-8918948647480835025310290759210068074616327299, 1, -160, -26233942508985949930425436408302396466229, 1, -160, 25041205370869742047616321587404419993407, 1, -159, -436898576690938403902752902358801620237, 1, -159, -208752863185080828109978727933211004807, 1, -157, -4213024244646442233091727033585175323, 1, -160, 22576522398367445674331047811133702101, 1, -160, 256472630353468518186437748988570423, 1, -159, -37835654872964150344858838674550189, 1, -158, -6258114378516763230514134938976729, 1, -160, 265381614511302878815833535947133, 1, -159, 8731486768603277993096874483677, 1, -158, -791368871039302603359148859161, 1, -160, -107394040865390800462820462853, 1, -160, -795140340816213491752752943, 1, -160, 45854628660363496279333609, 1, -158, 705132862112587297020885, 1, -157, -65718193114071306698925, 1, -159, -10354647408336511021421, 1, -160, -96491387814060755973, 1, -160, 8320431608475183075, 1, -160, 36056814896279433, 1, -157, -3891829019287, 1, -156, -13854214678033, 1, -156, -5288619560787, 1, -160, 14291688973, 1, -160, 3453089031, 1, -160, 75565593, 1, -160, 43891, 1, -160, -45965, 1, -160, -2297, 1, -158, -1779, 1, -160])
def d2Delta135S : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [-519154152288269182731014154023303035, 1, -126, -5503479273873893727639495200343, 1, -128, 26527850816347602982874010346327, 1, -128, -49206493675693624321185562057, 1, -124, -3368659901168425601088815244615, 1, -128, -3713797345236429907047839873, 1, -125, 177367988698595897217037723207, 1, -128, 8505908667159032967529911061, 1, -128, -4669809787871182594248982309, 1, -128, -396331010562891569141550407, 1, -128, 64396432716244228896328977, 1, -128, 8663805770486022130034141, 1, -128, -92940874476404615707019, 1, -126, -105057615754811534051589, 1, -128, -1691440355428830518563, 1, -128, 708152736157787805547, 1, -128, 44470680714838302369, 1, -128, -988374643327059829, 1, -127, -321077300605207311, 1, -128, -6262203396576689, 1, -128, 253920345703049, 1, -126, 35834549284527, 1, -127, 16037566619, 1, -127, -216797003357, 1, -128, -5252313683, 1, -127, 47802109, 1, -128, 842361, 1, -123, 1196761, 1, -128, 239, 1, -124, -2037, 1, -128, -53, 1, -127, -1, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta135Ap : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta135Aq : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta135Al : List ℚ := d2LitsStandaloneDelta016.q2listC (raw_ints% [])
def d2Delta135Es : ℚ := (d2LitsStandaloneDelta016.q2 (61) 1 (-127))
def d2Delta135Ep : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta135Eq : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
def d2Delta135El : ℚ := (d2LitsStandaloneDelta016.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta135Shift : polyRoundApx 128 d2Delta135Lo d2Delta135Hi d2Delta135Fq.poly = (d2Delta135S,d2Delta135Es) := by decide +kernel
theorem d2Delta135Sites : mergeSites d2Delta135Fq.plogs = [] := by decide +kernel
theorem d2Delta135PData : d2Delta135Pd = [] := by decide +kernel
theorem d2Delta135Plogs : plogsRoundM 16 24 20 128 d2Delta135Lo d2Delta135Hi (mergeSites d2Delta135Fq.plogs) d2Delta135Pd = some (d2Delta135Ap,d2Delta135Ep) := by
  rw [d2Delta135Sites,d2Delta135PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta135Poles : polesRoundM 16 24 12 128 d2Delta135Lo d2Delta135Hi d2Delta135Fq.poles d2Delta135Qd = some (d2Delta135Aq,d2Delta135Eq) := by decide +kernel
theorem d2Delta135Laurent : laurentRoundM 16 30 128 d2Delta135Lo d2Delta135Hi d2Delta135Ts d2Delta135Ld = some (d2Delta135Al,d2Delta135El) := by decide +kernel
theorem d2Delta135Small : chebPolyUB (vecAdd d2Delta135S (vecAdd d2Delta135Ap (vecAdd d2Delta135Aq d2Delta135Al))) d2Delta135Gam+d2Delta135Es+d2Delta135Ep+d2Delta135Eq+d2Delta135El ≤ (d2LitsStandaloneDelta016.q2 (-1844379037807701406083) 1 (-78)) := by decide +kernel
theorem d2Delta135Check : chebRoundPieceL d2Delta135Fq d2Delta135Ts 16 24 12 20 30 128 d2Delta135Lo d2Delta135Hi d2Delta135Pd d2Delta135Qd d2Delta135Ld d2Delta135Gam (d2LitsStandaloneDelta016.q2 (-1844379037807701406083) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta135Fq d2Delta135Ts 16 24 12 20 30 128 d2Delta135Lo d2Delta135Hi d2Delta135Pd d2Delta135Qd d2Delta135Ld d2Delta135Gam d2Delta135S d2Delta135Ap d2Delta135Aq d2Delta135Al d2Delta135Es d2Delta135Ep d2Delta135Eq d2Delta135El (by decide +kernel) d2Delta135Shift d2Delta135Plogs d2Delta135Poles d2Delta135Laurent]
  exact decide_eq_true d2Delta135Small
theorem d2Delta135Bound : ∀ x ∈ Icc ((d2Delta135Lo : ℚ) : ℝ) ((d2Delta135Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta016.q2 (-1844379037807701406083) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta135Fq d2Delta135Ts 16 24 12 20 30 128 d2Delta135Lo d2Delta135Hi d2Delta135Pd d2Delta135Qd d2Delta135Ld d2Delta135Gam (d2LitsStandaloneDelta016.q2 (-1844379037807701406083) 1 (-78)) d2Delta135Check
  simpa only [d2Delta135Fq, d2Delta135Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta135Shift
#print axioms d2Delta135Sites
#print axioms d2Delta135PData
#print axioms d2Delta135Plogs
#print axioms d2Delta135Poles
#print axioms d2Delta135Laurent
#print axioms d2Delta135Small
#print axioms d2Delta135Check
#print axioms d2Delta135Bound

end StandaloneDelta016
end CatalanMeasure.GenD.Signed.Data.Cells
