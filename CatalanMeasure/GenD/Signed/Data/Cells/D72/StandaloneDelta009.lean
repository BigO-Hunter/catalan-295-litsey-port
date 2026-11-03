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
namespace d2LitsStandaloneDelta009
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta009
namespace StandaloneDelta009
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta009.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta009.q2listC (raw_ints% []))⟩
def d2Delta72Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta72Ts : List LTerm := laurentClean []
def d2Delta72Lo : ℚ := (d2LitsStandaloneDelta009.q2 (106851227) 1 (-30))
def d2Delta72Hi : ℚ := (d2LitsStandaloneDelta009.q2 (53949389) 1 (-29))
def d2Delta72Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta72Qd : List (ℚ × ℚ) := []
def d2Delta72Ld : List LaurentPieceData := []
def d2Delta72Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-4459363999939426362783079363408849162651737511, 1, -159, 1266447223552243815652998401865010284819, 1, -160, -25637172842699879040498578196392568249, 1, -159, -117829609594701720747447032057272585, 1, -159, 3019320604087450211715885186077083, 1, -159, 2169401120099727951789342232337, 1, -158, -133928744791651423658797874699, 1, -159, -34581606758104017103858401, 1, -160, 1484375061686446060491447, 1, -158, -1767050386359586320533, 1, -159, -37529037733046467831, 1, -159, 79646723068632589, 1, -160, 292893580820511, 1, -159, -410776297625, 1, -159, -891400967, 1, -157, -904846491, 1, -158, -2753377547, 1, -160, -1193609769, 1, -159, -1793325393, 1, -160, -1529148605, 1, -160, -1135135749, 1, -160, -475921015, 1, -159, -697659541, 1, -160, -71916869, 1, -157, -416077741, 1, -160, -337460791, 1, -160, -120341189, 1, -159, -191954947, 1, -160, -33746541, 1, -158, -105826365, 1, -160, -9171835, 1, -157, -28257735, 1, -159])
def d2Delta72S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-1038276584422968808921845465291856765, 1, -127, 73758084594625774038231801759, 1, -126, -23887726786101640114950676041, 1, -128, -109757579721436790779028199, 1, -127, 11250839516271200293140995, 1, -128, 32327497214896100481033, 1, -128, -249505967099568866571, 1, -125, -257416042287395477, 1, -127, 44243416630728809, 1, -126, -210701044786041, 1, -128, -559278616367, 1, -124, 18991790243, 1, -128, 279348087, 1, -128, -389229, 1, -127, -5757, 1, -128, 19, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta72Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta72Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta72Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta72Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta72Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta72Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta72El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta72Shift : polyRoundApx 128 d2Delta72Lo d2Delta72Hi d2Delta72Fq.poly = (d2Delta72S,d2Delta72Es) := by decide +kernel
theorem d2Delta72Sites : mergeSites d2Delta72Fq.plogs = [] := by decide +kernel
theorem d2Delta72PData : d2Delta72Pd = [] := by decide +kernel
theorem d2Delta72Plogs : plogsRoundM 16 24 20 128 d2Delta72Lo d2Delta72Hi (mergeSites d2Delta72Fq.plogs) d2Delta72Pd = some (d2Delta72Ap,d2Delta72Ep) := by
  rw [d2Delta72Sites,d2Delta72PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta72Poles : polesRoundM 16 24 12 128 d2Delta72Lo d2Delta72Hi d2Delta72Fq.poles d2Delta72Qd = some (d2Delta72Aq,d2Delta72Eq) := by decide +kernel
theorem d2Delta72Laurent : laurentRoundM 16 30 128 d2Delta72Lo d2Delta72Hi d2Delta72Ts d2Delta72Ld = some (d2Delta72Al,d2Delta72El) := by decide +kernel
theorem d2Delta72Small : chebPolyUB (vecAdd d2Delta72S (vecAdd d2Delta72Ap (vecAdd d2Delta72Aq d2Delta72Al))) d2Delta72Gam+d2Delta72Es+d2Delta72Ep+d2Delta72Eq+d2Delta72El ≤ (d2LitsStandaloneDelta009.q2 (-7377397799939958731881) 1 (-80)) := by decide +kernel
theorem d2Delta72Check : chebRoundPieceL d2Delta72Fq d2Delta72Ts 16 24 12 20 30 128 d2Delta72Lo d2Delta72Hi d2Delta72Pd d2Delta72Qd d2Delta72Ld d2Delta72Gam (d2LitsStandaloneDelta009.q2 (-7377397799939958731881) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta72Fq d2Delta72Ts 16 24 12 20 30 128 d2Delta72Lo d2Delta72Hi d2Delta72Pd d2Delta72Qd d2Delta72Ld d2Delta72Gam d2Delta72S d2Delta72Ap d2Delta72Aq d2Delta72Al d2Delta72Es d2Delta72Ep d2Delta72Eq d2Delta72El (by decide +kernel) d2Delta72Shift d2Delta72Plogs d2Delta72Poles d2Delta72Laurent]
  exact decide_eq_true d2Delta72Small
theorem d2Delta72Bound : ∀ x ∈ Icc ((d2Delta72Lo : ℚ) : ℝ) ((d2Delta72Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-7377397799939958731881) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta72Fq d2Delta72Ts 16 24 12 20 30 128 d2Delta72Lo d2Delta72Hi d2Delta72Pd d2Delta72Qd d2Delta72Ld d2Delta72Gam (d2LitsStandaloneDelta009.q2 (-7377397799939958731881) 1 (-80)) d2Delta72Check
  simpa only [d2Delta72Fq, d2Delta72Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta72Shift
#print axioms d2Delta72Sites
#print axioms d2Delta72PData
#print axioms d2Delta72Plogs
#print axioms d2Delta72Poles
#print axioms d2Delta72Laurent
#print axioms d2Delta72Small
#print axioms d2Delta72Check
#print axioms d2Delta72Bound

def d2Delta73Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta73Ts : List LTerm := laurentClean []
def d2Delta73Lo : ℚ := (d2LitsStandaloneDelta009.q2 (53949389) 1 (-29))
def d2Delta73Hi : ℚ := (d2LitsStandaloneDelta009.q2 (13749235) 1 (-27))
def d2Delta73Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta73Qd : List (ℚ × ℚ) := []
def d2Delta73Ld : List LaurentPieceData := []
def d2Delta73Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-4459362654309717789371589514324672406426535801, 1, -159, 1260626932403859119085358198185253811025, 1, -160, -216497927891316800592848094374752473065, 1, -160, -710298559063281661161415255804099935, 1, -160, 49198944892245139082904936121925973, 1, -159, -29277405916929739060071925179245, 1, -160, -16849568422064179131407866351647, 1, -160, 31195416487429564353178313165, 1, -160, 180039187382666923327289003, 1, -157, -2009312342262498429601315, 1, -159, -2190252344355806636815, 1, -155, 244250109295887847931, 1, -160, 524958122489284545, 1, -158, -2148864723376641, 1, -158, -20667760113817, 1, -159, 191655231669, 1, -160, -573314881, 1, -158, -1121333519, 1, -159, -1851983933, 1, -160, -1429832067, 1, -160, -582010963, 1, -159, -221998921, 1, -158, -710817751, 1, -160, -536131055, 1, -160, -421644833, 1, -160, -78619799, 1, -158, -242875379, 1, -160, -179100835, 1, -160, -135790757, 1, -160, -49485419, 1, -159, -36824587, 1, -159, -26515757, 1, -159])
def d2Delta73S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-2076552503747654367851345451599937063, 1, -128, 73502170939208898559394090089, 1, -126, -100998054779887818054098804659, 1, -128, -661380342372966942729650943, 1, -128, 183468714365358033606388197, 1, -128, -1716886318406151319385, 1, -122, -125624935205090708167211, 1, -128, 232693514659524538883, 1, -127, 42945578492020484709, 1, -128, -119844436481161939, 1, -127, -8358153842930339, 1, -128, 29130204649039, 1, -127, 1001554104119, 1, -128, -8200054395, 1, -128, -78850433, 1, -128, 186083, 1, -126, 4347, 1, -128, -3, 1, -124, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta73Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta73Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta73Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta73Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta73Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta73Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta73El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta73Shift : polyRoundApx 128 d2Delta73Lo d2Delta73Hi d2Delta73Fq.poly = (d2Delta73S,d2Delta73Es) := by decide +kernel
theorem d2Delta73Sites : mergeSites d2Delta73Fq.plogs = [] := by decide +kernel
theorem d2Delta73PData : d2Delta73Pd = [] := by decide +kernel
theorem d2Delta73Plogs : plogsRoundM 16 24 20 128 d2Delta73Lo d2Delta73Hi (mergeSites d2Delta73Fq.plogs) d2Delta73Pd = some (d2Delta73Ap,d2Delta73Ep) := by
  rw [d2Delta73Sites,d2Delta73PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta73Poles : polesRoundM 16 24 12 128 d2Delta73Lo d2Delta73Hi d2Delta73Fq.poles d2Delta73Qd = some (d2Delta73Aq,d2Delta73Eq) := by decide +kernel
theorem d2Delta73Laurent : laurentRoundM 16 30 128 d2Delta73Lo d2Delta73Hi d2Delta73Ts d2Delta73Ld = some (d2Delta73Al,d2Delta73El) := by decide +kernel
theorem d2Delta73Small : chebPolyUB (vecAdd d2Delta73S (vecAdd d2Delta73Ap (vecAdd d2Delta73Aq d2Delta73Al))) d2Delta73Gam+d2Delta73Es+d2Delta73Ep+d2Delta73Eq+d2Delta73El ≤ (d2LitsStandaloneDelta009.q2 (-7377395441457992554827) 1 (-80)) := by decide +kernel
theorem d2Delta73Check : chebRoundPieceL d2Delta73Fq d2Delta73Ts 16 24 12 20 30 128 d2Delta73Lo d2Delta73Hi d2Delta73Pd d2Delta73Qd d2Delta73Ld d2Delta73Gam (d2LitsStandaloneDelta009.q2 (-7377395441457992554827) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta73Fq d2Delta73Ts 16 24 12 20 30 128 d2Delta73Lo d2Delta73Hi d2Delta73Pd d2Delta73Qd d2Delta73Ld d2Delta73Gam d2Delta73S d2Delta73Ap d2Delta73Aq d2Delta73Al d2Delta73Es d2Delta73Ep d2Delta73Eq d2Delta73El (by decide +kernel) d2Delta73Shift d2Delta73Plogs d2Delta73Poles d2Delta73Laurent]
  exact decide_eq_true d2Delta73Small
theorem d2Delta73Bound : ∀ x ∈ Icc ((d2Delta73Lo : ℚ) : ℝ) ((d2Delta73Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-7377395441457992554827) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta73Fq d2Delta73Ts 16 24 12 20 30 128 d2Delta73Lo d2Delta73Hi d2Delta73Pd d2Delta73Qd d2Delta73Ld d2Delta73Gam (d2LitsStandaloneDelta009.q2 (-7377395441457992554827) 1 (-80)) d2Delta73Check
  simpa only [d2Delta73Fq, d2Delta73Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta73Shift
#print axioms d2Delta73Sites
#print axioms d2Delta73PData
#print axioms d2Delta73Plogs
#print axioms d2Delta73Poles
#print axioms d2Delta73Laurent
#print axioms d2Delta73Small
#print axioms d2Delta73Check
#print axioms d2Delta73Bound

def d2Delta74Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta74Ts : List LTerm := laurentClean []
def d2Delta74Lo : ℚ := (d2LitsStandaloneDelta009.q2 (13749235) 1 (-27))
def d2Delta74Hi : ℚ := (d2LitsStandaloneDelta009.q2 (28546021) 1 (-28))
def d2Delta74Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta74Qd : List (ℚ × ℚ) := []
def d2Delta74Ld : List LaurentPieceData := []
def d2Delta74Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-8918726052047529103313069108336117438405660637, 1, -160, -1313726536190659286873236415253742724293, 1, -159, -829458511022103850140347511573116005763, 1, -160, 3120997719095337273379565915449024873, 1, -158, 708251023202334012771595990945782371, 1, -159, -18996119269081166753395692093932525, 1, -160, -905733903424950263133954463201673, 1, -160, 5965623528095109134683665340181, 1, -159, 286275472564179775448602435939, 1, -160, -3910052803754445223998850783, 1, -160, -3168754916043205997199587, 1, -156, 5887579135352224949273, 1, -153, 2689952359604431377811, 1, -159, -92245039308929924703, 1, -160, -356824588521257921, 1, -160, 1913238858451219, 1, -158, 15004742268957, 1, -160, -460039529679, 1, -160, -2364926421, 1, -160, -47238573, 1, -155, -1272072737, 1, -160, -477274483, 1, -159, -783094257, 1, -160, -144359997, 1, -158, -117026069, 1, -158, -21186531, 1, -156, -271547829, 1, -160, -48246793, 1, -158, -152780117, 1, -160, -53241559, 1, -159, -83317191, 1, -160, -14227205, 1, -158])
def d2Delta74S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-2076552533817386723723017603411398451, 1, -128, -310246845376763514515109753891, 1, -127, -194444478348486265978365538513, 1, -127, 11715235773034936427564671395, 1, -128, 2648573700096901326422110361, 1, -128, -71077583834323924405994969, 1, -128, -6765320020250014443682313, 1, -128, 178314308891644612801667, 1, -128, 8546792386190432142899, 1, -128, -233551771236036280559, 1, -128, -3025809824114921601, 1, -127, 89980364299377333, 1, -127, 2567721283149291, 1, -128, -44040626603837, 1, -127, -681046976699, 1, -128, 7305853121, 1, -126, 114549667, 1, -128, -6989177, 1, -128, -5453, 1, -127, 1265, 1, -128, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta74Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta74Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta74Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta74Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta74Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta74Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta74El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta74Shift : polyRoundApx 128 d2Delta74Lo d2Delta74Hi d2Delta74Fq.poly = (d2Delta74S,d2Delta74Es) := by decide +kernel
theorem d2Delta74Sites : mergeSites d2Delta74Fq.plogs = [] := by decide +kernel
theorem d2Delta74PData : d2Delta74Pd = [] := by decide +kernel
theorem d2Delta74Plogs : plogsRoundM 16 24 20 128 d2Delta74Lo d2Delta74Hi (mergeSites d2Delta74Fq.plogs) d2Delta74Pd = some (d2Delta74Ap,d2Delta74Ep) := by
  rw [d2Delta74Sites,d2Delta74PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta74Poles : polesRoundM 16 24 12 128 d2Delta74Lo d2Delta74Hi d2Delta74Fq.poles d2Delta74Qd = some (d2Delta74Aq,d2Delta74Eq) := by decide +kernel
theorem d2Delta74Laurent : laurentRoundM 16 30 128 d2Delta74Lo d2Delta74Hi d2Delta74Ts d2Delta74Ld = some (d2Delta74Al,d2Delta74El) := by decide +kernel
theorem d2Delta74Small : chebPolyUB (vecAdd d2Delta74S (vecAdd d2Delta74Ap (vecAdd d2Delta74Aq d2Delta74Al))) d2Delta74Gam+d2Delta74Es+d2Delta74Ep+d2Delta74Eq+d2Delta74El ≤ (d2LitsStandaloneDelta009.q2 (-7377394407920389419713) 1 (-80)) := by decide +kernel
theorem d2Delta74Check : chebRoundPieceL d2Delta74Fq d2Delta74Ts 16 24 12 20 30 128 d2Delta74Lo d2Delta74Hi d2Delta74Pd d2Delta74Qd d2Delta74Ld d2Delta74Gam (d2LitsStandaloneDelta009.q2 (-7377394407920389419713) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta74Fq d2Delta74Ts 16 24 12 20 30 128 d2Delta74Lo d2Delta74Hi d2Delta74Pd d2Delta74Qd d2Delta74Ld d2Delta74Gam d2Delta74S d2Delta74Ap d2Delta74Aq d2Delta74Al d2Delta74Es d2Delta74Ep d2Delta74Eq d2Delta74El (by decide +kernel) d2Delta74Shift d2Delta74Plogs d2Delta74Poles d2Delta74Laurent]
  exact decide_eq_true d2Delta74Small
theorem d2Delta74Bound : ∀ x ∈ Icc ((d2Delta74Lo : ℚ) : ℝ) ((d2Delta74Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-7377394407920389419713) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta74Fq d2Delta74Ts 16 24 12 20 30 128 d2Delta74Lo d2Delta74Hi d2Delta74Pd d2Delta74Qd d2Delta74Ld d2Delta74Gam (d2LitsStandaloneDelta009.q2 (-7377394407920389419713) 1 (-80)) d2Delta74Check
  simpa only [d2Delta74Fq, d2Delta74Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta74Shift
#print axioms d2Delta74Sites
#print axioms d2Delta74PData
#print axioms d2Delta74Plogs
#print axioms d2Delta74Poles
#print axioms d2Delta74Laurent
#print axioms d2Delta74Small
#print axioms d2Delta74Check
#print axioms d2Delta74Bound

def d2Delta75Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta75Ts : List LTerm := laurentClean []
def d2Delta75Lo : ℚ := (d2LitsStandaloneDelta009.q2 (28546021) 1 (-28))
def d2Delta75Hi : ℚ := (d2LitsStandaloneDelta009.q2 (58139593) 1 (-29))
def d2Delta75Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta75Qd : List (ℚ × ℚ) := []
def d2Delta75Ld : List LaurentPieceData := []
def d2Delta75Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-4459366457317809535577675477124947978814110443, 1, -159, -224093472213428014305643173574371438581, 1, -156, -162574580859064146751060620957259618603, 1, -160, 857236471395129797853135756681031347, 1, -158, 16016856595861995779431951784753703, 1, -158, -1023164540889540612128152887798891, 1, -160, -4639024694726717620120909816039, 1, -159, 34033182710225852710119426139, 1, -158, 320152764583428558520518913, 1, -159, -9841294754994422450154381, 1, -160, -22840860226307199817475, 1, -160, 430104743654876760671, 1, -160, 387218854738600533, 1, -160, -6100436551085455, 1, -159, -142240339853, 1, -159, 234919246633, 1, -160, -191880641, 1, -156, -2422258083, 1, -160, -480568881, 1, -158, -97518073, 1, -156, -610942769, 1, -159, -979622419, 1, -160, -188821405, 1, -158, -74782571, 1, -157, -453587051, 1, -160, -355147683, 1, -160, -132206613, 1, -159, -204795375, 1, -160, -18685329, 1, -157, -57318407, 1, -159, -81885619, 1, -160, -62246389, 1, -160])
def d2Delta75S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-1038277143612150278293764963306254287, 1, -127, -418604760180147356171861601507, 1, -127, -37912031187975756653250185427, 1, -127, 3198220966792163594292459867, 1, -128, 29859648778586355380556523, 1, -126, -1907567932742658270082181, 1, -127, -34582512949259007768347, 1, -127, 31716497945648274487, 1, -122, 19089399536818186849, 1, -128, -9169826936253079, 1, -122, -1361698321947693, 1, -127, 51291391422269, 1, -127, 184642204863, 1, -128, -5819533683, 1, -127, -530365, 1, -128, 113787, 1, -125, -967, 1, -128, -13, 1, -126, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta75Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta75Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta75Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta75Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta75Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta75Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta75El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta75Shift : polyRoundApx 128 d2Delta75Lo d2Delta75Hi d2Delta75Fq.poly = (d2Delta75S,d2Delta75Es) := by decide +kernel
theorem d2Delta75Sites : mergeSites d2Delta75Fq.plogs = [] := by decide +kernel
theorem d2Delta75PData : d2Delta75Pd = [] := by decide +kernel
theorem d2Delta75Plogs : plogsRoundM 16 24 20 128 d2Delta75Lo d2Delta75Hi (mergeSites d2Delta75Fq.plogs) d2Delta75Pd = some (d2Delta75Ap,d2Delta75Ep) := by
  rw [d2Delta75Sites,d2Delta75PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta75Poles : polesRoundM 16 24 12 128 d2Delta75Lo d2Delta75Hi d2Delta75Fq.poles d2Delta75Qd = some (d2Delta75Aq,d2Delta75Eq) := by decide +kernel
theorem d2Delta75Laurent : laurentRoundM 16 30 128 d2Delta75Lo d2Delta75Hi d2Delta75Ts d2Delta75Ld = some (d2Delta75Al,d2Delta75El) := by decide +kernel
theorem d2Delta75Small : chebPolyUB (vecAdd d2Delta75S (vecAdd d2Delta75Ap (vecAdd d2Delta75Aq d2Delta75Al))) d2Delta75Gam+d2Delta75Es+d2Delta75Ep+d2Delta75Eq+d2Delta75El ≤ (d2LitsStandaloneDelta009.q2 (-7377399852303983031407) 1 (-80)) := by decide +kernel
theorem d2Delta75Check : chebRoundPieceL d2Delta75Fq d2Delta75Ts 16 24 12 20 30 128 d2Delta75Lo d2Delta75Hi d2Delta75Pd d2Delta75Qd d2Delta75Ld d2Delta75Gam (d2LitsStandaloneDelta009.q2 (-7377399852303983031407) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta75Fq d2Delta75Ts 16 24 12 20 30 128 d2Delta75Lo d2Delta75Hi d2Delta75Pd d2Delta75Qd d2Delta75Ld d2Delta75Gam d2Delta75S d2Delta75Ap d2Delta75Aq d2Delta75Al d2Delta75Es d2Delta75Ep d2Delta75Eq d2Delta75El (by decide +kernel) d2Delta75Shift d2Delta75Plogs d2Delta75Poles d2Delta75Laurent]
  exact decide_eq_true d2Delta75Small
theorem d2Delta75Bound : ∀ x ∈ Icc ((d2Delta75Lo : ℚ) : ℝ) ((d2Delta75Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-7377399852303983031407) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta75Fq d2Delta75Ts 16 24 12 20 30 128 d2Delta75Lo d2Delta75Hi d2Delta75Pd d2Delta75Qd d2Delta75Ld d2Delta75Gam (d2LitsStandaloneDelta009.q2 (-7377399852303983031407) 1 (-80)) d2Delta75Check
  simpa only [d2Delta75Fq, d2Delta75Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta75Shift
#print axioms d2Delta75Sites
#print axioms d2Delta75PData
#print axioms d2Delta75Plogs
#print axioms d2Delta75Poles
#print axioms d2Delta75Laurent
#print axioms d2Delta75Small
#print axioms d2Delta75Check
#print axioms d2Delta75Bound

def d2Delta76Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta76Ts : List LTerm := laurentClean []
def d2Delta76Lo : ℚ := (d2LitsStandaloneDelta009.q2 (58139593) 1 (-29))
def d2Delta76Hi : ℚ := (d2LitsStandaloneDelta009.q2 (7398393) 1 (-26))
def d2Delta76Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta76Qd : List (ℚ × ℚ) := []
def d2Delta76Ld : List LaurentPieceData := []
def d2Delta76Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-4459370622346595612462423794446175671674244851, 1, -159, -294106480307445621182929316649195799719, 1, -156, -3624612633621436057143495868012756397, 1, -155, 4279553197093630455088834982219410831, 1, -160, 20848354812456456225645107702535201, 1, -159, -599057263853937741243471893596701, 1, -159, -1308444672010782558165479784029, 1, -158, 150814842134694419253083398945, 1, -160, 274167526822818474196699481, 1, -160, -2593305748199331496671183, 1, -158, -3730634037231432119821, 1, -160, 433541380804252696339, 1, -160, -60188417025268783, 1, -158, -5911179065060839, 1, -159, 13641644481167, 1, -160, 219394202277, 1, -160, -1542318105, 1, -159, -2579696777, 1, -160, -1770429267, 1, -160, -834524183, 1, -159, -1114725217, 1, -160, -262878523, 1, -158, -341285925, 1, -159, -643791961, 1, -160, -406161513, 1, -160, -382765085, 1, -160, -29336139, 1, -157, -110415643, 1, -159, -131584165, 1, -160, -61772827, 1, -159, -71532907, 1, -160, -33489605, 1, -159])
def d2Delta76S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-2076556237569052028786652150448149139, 1, -128, -549311323107551623646688298273, 1, -127, -54088625229327274278233455661, 1, -128, 498903202993234183390027475, 1, -125, 77724676170532059127665631, 1, -128, -1116814568371720599964629, 1, -126, -9752758143102630341601, 1, -126, 281088464370546375031, 1, -125, 8171940450657222355, 1, -128, -618576569348607157, 1, -128, -111095426751129, 1, -126, 103400967476285, 1, -128, -114891404609, 1, -128, -11277868099, 1, -128, 26037853, 1, -128, 212973, 1, -126, -2657, 1, -128, -3, 1, -124, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta76Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta76Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta76Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta76Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta76Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta76Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta76El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta76Shift : polyRoundApx 128 d2Delta76Lo d2Delta76Hi d2Delta76Fq.poly = (d2Delta76S,d2Delta76Es) := by decide +kernel
theorem d2Delta76Sites : mergeSites d2Delta76Fq.plogs = [] := by decide +kernel
theorem d2Delta76PData : d2Delta76Pd = [] := by decide +kernel
theorem d2Delta76Plogs : plogsRoundM 16 24 20 128 d2Delta76Lo d2Delta76Hi (mergeSites d2Delta76Fq.plogs) d2Delta76Pd = some (d2Delta76Ap,d2Delta76Ep) := by
  rw [d2Delta76Sites,d2Delta76PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta76Poles : polesRoundM 16 24 12 128 d2Delta76Lo d2Delta76Hi d2Delta76Fq.poles d2Delta76Qd = some (d2Delta76Aq,d2Delta76Eq) := by decide +kernel
theorem d2Delta76Laurent : laurentRoundM 16 30 128 d2Delta76Lo d2Delta76Hi d2Delta76Ts d2Delta76Ld = some (d2Delta76Al,d2Delta76El) := by decide +kernel
theorem d2Delta76Small : chebPolyUB (vecAdd d2Delta76S (vecAdd d2Delta76Ap (vecAdd d2Delta76Aq d2Delta76Al))) d2Delta76Gam+d2Delta76Es+d2Delta76Ep+d2Delta76Eq+d2Delta76El ≤ (d2LitsStandaloneDelta009.q2 (-7377405854002262608857) 1 (-80)) := by decide +kernel
theorem d2Delta76Check : chebRoundPieceL d2Delta76Fq d2Delta76Ts 16 24 12 20 30 128 d2Delta76Lo d2Delta76Hi d2Delta76Pd d2Delta76Qd d2Delta76Ld d2Delta76Gam (d2LitsStandaloneDelta009.q2 (-7377405854002262608857) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta76Fq d2Delta76Ts 16 24 12 20 30 128 d2Delta76Lo d2Delta76Hi d2Delta76Pd d2Delta76Qd d2Delta76Ld d2Delta76Gam d2Delta76S d2Delta76Ap d2Delta76Aq d2Delta76Al d2Delta76Es d2Delta76Ep d2Delta76Eq d2Delta76El (by decide +kernel) d2Delta76Shift d2Delta76Plogs d2Delta76Poles d2Delta76Laurent]
  exact decide_eq_true d2Delta76Small
theorem d2Delta76Bound : ∀ x ∈ Icc ((d2Delta76Lo : ℚ) : ℝ) ((d2Delta76Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-7377405854002262608857) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta76Fq d2Delta76Ts 16 24 12 20 30 128 d2Delta76Lo d2Delta76Hi d2Delta76Pd d2Delta76Qd d2Delta76Ld d2Delta76Gam (d2LitsStandaloneDelta009.q2 (-7377405854002262608857) 1 (-80)) d2Delta76Check
  simpa only [d2Delta76Fq, d2Delta76Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta76Shift
#print axioms d2Delta76Sites
#print axioms d2Delta76PData
#print axioms d2Delta76Plogs
#print axioms d2Delta76Poles
#print axioms d2Delta76Laurent
#print axioms d2Delta76Small
#print axioms d2Delta76Check
#print axioms d2Delta76Bound

def d2Delta77Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta77Ts : List LTerm := laurentClean []
def d2Delta77Lo : ℚ := (d2LitsStandaloneDelta009.q2 (7398393) 1 (-26))
def d2Delta77Hi : ℚ := (d2LitsStandaloneDelta009.q2 (15844337) 1 (-27))
def d2Delta77Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta77Qd : List (ℚ × ℚ) := []
def d2Delta77Ld : List LaurentPieceData := []
def d2Delta77Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-8918767855362231694783616091316048466706031431, 1, -160, -21713298187885357088091661159104896479879, 1, -160, 378961913346531835594554264472150770213, 1, -160, 18437889134528391071659819752631620891, 1, -156, -5182081670542918419163554526321455347, 1, -160, -301782379667146193615966742696026571, 1, -158, 21127493399390194894028450629841913, 1, -160, 1107636593195029330812166073679549, 1, -159, -39416149986630782366304743370083, 1, -160, -2213274713676018482112056871905, 1, -160, 5099750328091213683783905483, 1, -157, 1336912627141368955734164447, 1, -160, -26028076599451823280607723, 1, -160, -261753720994916956955813, 1, -159, 2744027211888557811321, 1, -158, 8792790623975781221, 1, -156, -810202830709556451, 1, -158, -6821205643431197, 1, -158, 176295054550255, 1, -158, 3967637705527, 1, -160, -119053951087, 1, -160, -1415728615, 1, -160, -706419143, 1, -160, -296902169, 1, -159, -107134559, 1, -158, -172243, 1, -149, -246727113, 1, -160, -101711023, 1, -159, -137728219, 1, -160, -113824083, 1, -160, -74505473, 1, -160, -7720699, 1, -157])
def d2Delta77S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-2076562549808852761572177664234719167, 1, -128, -1315747390081090432562893497811, 1, -126, 93104555073330509832687254105, 1, -127, 140198019352846734920567020319, 1, -127, -9889969595846205745321859557, 1, -128, -4554898636148081273607344027, 1, -128, 79886069326657208187419703, 1, -127, 16653921937191759903955467, 1, -127, -1186893517855927361785695, 1, -128, -132800031857019884604069, 1, -128, 1225208814322293382991, 1, -126, 320370411294100611463, 1, -128, -12484588409897146607, 1, -128, -501271210931827793, 1, -128, 10517174837701115, 1, -127, 269220534647847, 1, -127, -12411211599747, 1, -127, -417485332169, 1, -128, 21592493437, 1, -128, 242830159, 1, -128, -14430835, 1, -128, -27201, 1, -126, 1913, 1, -126, 19, 1, -127, -1, 1, -126, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta77Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta77Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta77Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta77Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta77Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta77Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta77El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta77Shift : polyRoundApx 128 d2Delta77Lo d2Delta77Hi d2Delta77Fq.poly = (d2Delta77S,d2Delta77Es) := by decide +kernel
theorem d2Delta77Sites : mergeSites d2Delta77Fq.plogs = [] := by decide +kernel
theorem d2Delta77PData : d2Delta77Pd = [] := by decide +kernel
theorem d2Delta77Plogs : plogsRoundM 16 24 20 128 d2Delta77Lo d2Delta77Hi (mergeSites d2Delta77Fq.plogs) d2Delta77Pd = some (d2Delta77Ap,d2Delta77Ep) := by
  rw [d2Delta77Sites,d2Delta77PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta77Poles : polesRoundM 16 24 12 128 d2Delta77Lo d2Delta77Hi d2Delta77Fq.poles d2Delta77Qd = some (d2Delta77Aq,d2Delta77Eq) := by decide +kernel
theorem d2Delta77Laurent : laurentRoundM 16 30 128 d2Delta77Lo d2Delta77Hi d2Delta77Ts d2Delta77Ld = some (d2Delta77Al,d2Delta77El) := by decide +kernel
theorem d2Delta77Small : chebPolyUB (vecAdd d2Delta77S (vecAdd d2Delta77Ap (vecAdd d2Delta77Aq d2Delta77Al))) d2Delta77Gam+d2Delta77Es+d2Delta77Ep+d2Delta77Eq+d2Delta77El ≤ (d2LitsStandaloneDelta009.q2 (-461088333387483430755) 1 (-76)) := by decide +kernel
theorem d2Delta77Check : chebRoundPieceL d2Delta77Fq d2Delta77Ts 16 24 12 20 30 128 d2Delta77Lo d2Delta77Hi d2Delta77Pd d2Delta77Qd d2Delta77Ld d2Delta77Gam (d2LitsStandaloneDelta009.q2 (-461088333387483430755) 1 (-76)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta77Fq d2Delta77Ts 16 24 12 20 30 128 d2Delta77Lo d2Delta77Hi d2Delta77Pd d2Delta77Qd d2Delta77Ld d2Delta77Gam d2Delta77S d2Delta77Ap d2Delta77Aq d2Delta77Al d2Delta77Es d2Delta77Ep d2Delta77Eq d2Delta77El (by decide +kernel) d2Delta77Shift d2Delta77Plogs d2Delta77Poles d2Delta77Laurent]
  exact decide_eq_true d2Delta77Small
theorem d2Delta77Bound : ∀ x ∈ Icc ((d2Delta77Lo : ℚ) : ℝ) ((d2Delta77Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-461088333387483430755) 1 (-76)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta77Fq d2Delta77Ts 16 24 12 20 30 128 d2Delta77Lo d2Delta77Hi d2Delta77Pd d2Delta77Qd d2Delta77Ld d2Delta77Gam (d2LitsStandaloneDelta009.q2 (-461088333387483430755) 1 (-76)) d2Delta77Check
  simpa only [d2Delta77Fq, d2Delta77Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta77Shift
#print axioms d2Delta77Sites
#print axioms d2Delta77PData
#print axioms d2Delta77Plogs
#print axioms d2Delta77Poles
#print axioms d2Delta77Laurent
#print axioms d2Delta77Small
#print axioms d2Delta77Check
#print axioms d2Delta77Bound

def d2Delta78Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta78Ts : List LTerm := laurentClean []
def d2Delta78Lo : ℚ := (d2LitsStandaloneDelta009.q2 (15844337) 1 (-27))
def d2Delta78Hi : ℚ := (d2LitsStandaloneDelta009.q2 (64424899) 1 (-29))
def d2Delta78Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta78Qd : List (ℚ × ℚ) := []
def d2Delta78Ld : List LaurentPieceData := []
def d2Delta78Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-4459396455392247692421648751088464428161532693, 1, -159, -1935052650932231217447038916655106741387, 1, -159, 142514421867561086499317234225377728367, 1, -160, 2825804313912852606845735248816386181, 1, -160, -34131553804560092266596210530303457, 1, -159, -636590873383701372996733918377907, 1, -160, 6228166999224829110900685888293, 1, -159, 490736377420471240591673059, 1, -153, -1151305142985554586337539851, 1, -160, -3206059047196368614793919, 1, -160, 31163029365621041098501, 1, -159, 5524712944723418755, 1, -156, -1079488929505019349, 1, -159, -1153531889698463, 1, -160, 12734259821219, 1, -158, -6563955429, 1, -160, -1983452595, 1, -159, -2629253729, 1, -160, -1014991275, 1, -159, -850630113, 1, -159, -1290510437, 1, -160, -267553813, 1, -158, -797102003, 1, -160, -40888485, 1, -156, -59748755, 1, -157, -97096173, 1, -158, -278076415, 1, -160, -223787463, 1, -160, -156838829, 1, -160, -62538261, 1, -159, -5356529, 1, -156, -16941229, 1, -158])
def d2Delta78S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-129785520451946545181255643647293501, 1, -124, -903053651144797113000883603405, 1, -128, 16622662826374405273391964561, 1, -126, 2634700525342995379551719161, 1, -128, -127289199535418808148869691, 1, -128, -2373124136583026669246457, 1, -128, 46437779893157701004653, 1, -127, 58527211407965932387, 1, -124, -34330145125638527609, 1, -128, -191153971651387089, 1, -128, 7432934092079469, 1, -128, 21078682596239, 1, -128, -1029820978741, 1, -128, -550025425, 1, -127, 24297453, 1, -126, -1247, 1, -125, -6577, 1, -128, 5, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta78Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta78Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta78Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta78Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta78Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta78Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta78El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta78Shift : polyRoundApx 128 d2Delta78Lo d2Delta78Hi d2Delta78Fq.poly = (d2Delta78S,d2Delta78Es) := by decide +kernel
theorem d2Delta78Sites : mergeSites d2Delta78Fq.plogs = [] := by decide +kernel
theorem d2Delta78PData : d2Delta78Pd = [] := by decide +kernel
theorem d2Delta78Plogs : plogsRoundM 16 24 20 128 d2Delta78Lo d2Delta78Hi (mergeSites d2Delta78Fq.plogs) d2Delta78Pd = some (d2Delta78Ap,d2Delta78Ep) := by
  rw [d2Delta78Sites,d2Delta78PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta78Poles : polesRoundM 16 24 12 128 d2Delta78Lo d2Delta78Hi d2Delta78Fq.poles d2Delta78Qd = some (d2Delta78Aq,d2Delta78Eq) := by decide +kernel
theorem d2Delta78Laurent : laurentRoundM 16 30 128 d2Delta78Lo d2Delta78Hi d2Delta78Ts d2Delta78Ld = some (d2Delta78Al,d2Delta78El) := by decide +kernel
theorem d2Delta78Small : chebPolyUB (vecAdd d2Delta78S (vecAdd d2Delta78Ap (vecAdd d2Delta78Aq d2Delta78Al))) d2Delta78Gam+d2Delta78Es+d2Delta78Ep+d2Delta78Eq+d2Delta78El ≤ (d2LitsStandaloneDelta009.q2 (-1844362315405156296239) 1 (-78)) := by decide +kernel
theorem d2Delta78Check : chebRoundPieceL d2Delta78Fq d2Delta78Ts 16 24 12 20 30 128 d2Delta78Lo d2Delta78Hi d2Delta78Pd d2Delta78Qd d2Delta78Ld d2Delta78Gam (d2LitsStandaloneDelta009.q2 (-1844362315405156296239) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta78Fq d2Delta78Ts 16 24 12 20 30 128 d2Delta78Lo d2Delta78Hi d2Delta78Pd d2Delta78Qd d2Delta78Ld d2Delta78Gam d2Delta78S d2Delta78Ap d2Delta78Aq d2Delta78Al d2Delta78Es d2Delta78Ep d2Delta78Eq d2Delta78El (by decide +kernel) d2Delta78Shift d2Delta78Plogs d2Delta78Poles d2Delta78Laurent]
  exact decide_eq_true d2Delta78Small
theorem d2Delta78Bound : ∀ x ∈ Icc ((d2Delta78Lo : ℚ) : ℝ) ((d2Delta78Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-1844362315405156296239) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta78Fq d2Delta78Ts 16 24 12 20 30 128 d2Delta78Lo d2Delta78Hi d2Delta78Pd d2Delta78Qd d2Delta78Ld d2Delta78Gam (d2LitsStandaloneDelta009.q2 (-1844362315405156296239) 1 (-78)) d2Delta78Check
  simpa only [d2Delta78Fq, d2Delta78Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta78Shift
#print axioms d2Delta78Sites
#print axioms d2Delta78PData
#print axioms d2Delta78Plogs
#print axioms d2Delta78Poles
#print axioms d2Delta78Laurent
#print axioms d2Delta78Small
#print axioms d2Delta78Check
#print axioms d2Delta78Bound

def d2Delta79Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta79Ts : List LTerm := laurentClean []
def d2Delta79Lo : ℚ := (d2LitsStandaloneDelta009.q2 (64424899) 1 (-29))
def d2Delta79Hi : ℚ := (d2LitsStandaloneDelta009.q2 (32736225) 1 (-28))
def d2Delta79Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta79Qd : List (ℚ × ℚ) := []
def d2Delta79Ld : List LaurentPieceData := []
def d2Delta79Gam : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-1114849927146930933722413987661286253299437127, 1, -157, -40840286136972183801865419415633494373, 1, -154, 84752365932927161727620346780448276995, 1, -159, 1648505008750586667909320865225074229, 1, -160, -77884847170233341342436642536537843, 1, -160, -320785675978319394441785480228735, 1, -160, 13685462771005812576835781114393, 1, -160, 24612735374125574929186231181, 1, -160, -610594899833233793312534719, 1, -159, -41614833911205551532839, 1, -156, 63927555335002192998981, 1, -160, -15490369513950555639, 1, -160, -268158450395629313, 1, -157, 1664205662667191, 1, -160, 49151155554629, 1, -160, -60106839713, 1, -160, -3739657181, 1, -160, -2466300117, 1, -160, -238741199, 1, -157, -1587382853, 1, -160, -1211930319, 1, -160, -993236127, 1, -160, -747989429, 1, -160, -604138827, 1, -160, -112173705, 1, -158, -178525361, 1, -159, -130704223, 1, -159, -51235353, 1, -158, -73899287, 1, -159, -28547325, 1, -158, -40516833, 1, -159, -61729031, 1, -160])
def d2Delta79S : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [-1038284924202374865939828268374912023, 1, -127, -609719527860439046031011629855, 1, -128, 79076920842398344973895014435, 1, -128, 1536784024656515355031176777, 1, -128, -145224825244121202410631255, 1, -128, -1195661660665100297880051, 1, -128, 51018724318995570637101, 1, -127, 366847622817350743217, 1, -128, -36413347455101940325, 1, -128, -39676835556357007, 1, -128, 952978466919569, 1, -125, -3698351222359, 1, -128, -1023271493189, 1, -128, 1587922011, 1, -128, 93781455, 1, -128, -215125, 1, -128, -1545, 1, -126, 17, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta79Ap : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta79Aq : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta79Al : List ℚ := d2LitsStandaloneDelta009.q2listC (raw_ints% [])
def d2Delta79Es : ℚ := (d2LitsStandaloneDelta009.q2 (61) 1 (-127))
def d2Delta79Ep : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta79Eq : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
def d2Delta79El : ℚ := (d2LitsStandaloneDelta009.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta79Shift : polyRoundApx 128 d2Delta79Lo d2Delta79Hi d2Delta79Fq.poly = (d2Delta79S,d2Delta79Es) := by decide +kernel
theorem d2Delta79Sites : mergeSites d2Delta79Fq.plogs = [] := by decide +kernel
theorem d2Delta79PData : d2Delta79Pd = [] := by decide +kernel
theorem d2Delta79Plogs : plogsRoundM 16 24 20 128 d2Delta79Lo d2Delta79Hi (mergeSites d2Delta79Fq.plogs) d2Delta79Pd = some (d2Delta79Ap,d2Delta79Ep) := by
  rw [d2Delta79Sites,d2Delta79PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta79Poles : polesRoundM 16 24 12 128 d2Delta79Lo d2Delta79Hi d2Delta79Fq.poles d2Delta79Qd = some (d2Delta79Aq,d2Delta79Eq) := by decide +kernel
theorem d2Delta79Laurent : laurentRoundM 16 30 128 d2Delta79Lo d2Delta79Hi d2Delta79Ts d2Delta79Ld = some (d2Delta79Al,d2Delta79El) := by decide +kernel
theorem d2Delta79Small : chebPolyUB (vecAdd d2Delta79S (vecAdd d2Delta79Ap (vecAdd d2Delta79Aq d2Delta79Al))) d2Delta79Gam+d2Delta79Es+d2Delta79Ep+d2Delta79Eq+d2Delta79El ≤ (d2LitsStandaloneDelta009.q2 (-3688727830715343089299) 1 (-79)) := by decide +kernel
theorem d2Delta79Check : chebRoundPieceL d2Delta79Fq d2Delta79Ts 16 24 12 20 30 128 d2Delta79Lo d2Delta79Hi d2Delta79Pd d2Delta79Qd d2Delta79Ld d2Delta79Gam (d2LitsStandaloneDelta009.q2 (-3688727830715343089299) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta79Fq d2Delta79Ts 16 24 12 20 30 128 d2Delta79Lo d2Delta79Hi d2Delta79Pd d2Delta79Qd d2Delta79Ld d2Delta79Gam d2Delta79S d2Delta79Ap d2Delta79Aq d2Delta79Al d2Delta79Es d2Delta79Ep d2Delta79Eq d2Delta79El (by decide +kernel) d2Delta79Shift d2Delta79Plogs d2Delta79Poles d2Delta79Laurent]
  exact decide_eq_true d2Delta79Small
theorem d2Delta79Bound : ∀ x ∈ Icc ((d2Delta79Lo : ℚ) : ℝ) ((d2Delta79Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta009.q2 (-3688727830715343089299) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta79Fq d2Delta79Ts 16 24 12 20 30 128 d2Delta79Lo d2Delta79Hi d2Delta79Pd d2Delta79Qd d2Delta79Ld d2Delta79Gam (d2LitsStandaloneDelta009.q2 (-3688727830715343089299) 1 (-79)) d2Delta79Check
  simpa only [d2Delta79Fq, d2Delta79Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta79Shift
#print axioms d2Delta79Sites
#print axioms d2Delta79PData
#print axioms d2Delta79Plogs
#print axioms d2Delta79Poles
#print axioms d2Delta79Laurent
#print axioms d2Delta79Small
#print axioms d2Delta79Check
#print axioms d2Delta79Bound

end StandaloneDelta009
end CatalanMeasure.GenD.Signed.Data.Cells
