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
namespace d2LitsStandaloneDelta004
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta004
namespace StandaloneDelta004
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta004.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta004.q2listC (raw_ints% []))⟩
def d2Delta32Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta32Ts : List LTerm := laurentClean []
def d2Delta32Lo : ℚ := (d2LitsStandaloneDelta004.q2 (16237553) 1 (-29))
def d2Delta32Hi : ℚ := (d2LitsStandaloneDelta004.q2 (1080319) 1 (-25))
def d2Delta32Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta32Qd : List (ℚ × ℚ) := []
def d2Delta32Ld : List LaurentPieceData := []
def d2Delta32Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278709745491698923680121503834114879341191789, 1, -155, -9285609941794817467988732789288782667569, 1, -160, -109718752743924323329388851425541092887, 1, -158, 23471819010837341232607329888678743865, 1, -160, 37727060335290171163801619837529063, 1, -159, -1552219847097084107317211122715237, 1, -157, 77354827964708197235387138272663, 1, -159, -164098247987089641250542535169, 1, -160, -8218415131773570238285517347, 1, -160, 36616500006436719759408329, 1, -160, 49935883188476333653799, 1, -158, -1496112519221767692965, 1, -160, -646672423929771747, 1, -158, 35304175048500945, 1, -160, 9924243598103, 1, -160, -145315634293, 1, -158, -2722159149, 1, -160, -297674041, 1, -157, -1975756223, 1, -160, -1539681939, 1, -160, -1256828081, 1, -160, -964693585, 1, -160, -777522443, 1, -160, -293537737, 1, -159, -116864741, 1, -158, -86704923, 1, -158, -272945067, 1, -160, -99395219, 1, -159, -154675803, 1, -160, -13811837, 1, -157, -21254147, 1, -158, -465039, 1, -153])
def d2Delta32S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-1038274659866473541975784902122821861, 1, -127, -2178383871557236666368196106925, 1, -128, -102253499194042900146334035049, 1, -127, 5479414366708876445901259077, 1, -126, 69407465268591195575254947, 1, -127, -5781934177633400991418689, 1, -125, 1153166668428360980627269, 1, -128, -612541520303510611211, 1, -126, -122493694823748430993, 1, -127, 272936817549755211, 1, -125, 23814985012363493, 1, -128, -356810456645733, 1, -128, -1233496027177, 1, -128, 33676954323, 1, -128, 9464205, 1, -127, -137753, 1, -124, 2293, 1, -128, 107, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta32Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta32Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta32Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta32Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta32Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta32Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta32El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta32Shift : polyRoundApx 128 d2Delta32Lo d2Delta32Hi d2Delta32Fq.poly = (d2Delta32S,d2Delta32Es) := by decide +kernel
theorem d2Delta32Sites : mergeSites d2Delta32Fq.plogs = [] := by decide +kernel
theorem d2Delta32PData : d2Delta32Pd = [] := by decide +kernel
theorem d2Delta32Plogs : plogsRoundM 16 24 20 128 d2Delta32Lo d2Delta32Hi (mergeSites d2Delta32Fq.plogs) d2Delta32Pd = some (d2Delta32Ap,d2Delta32Ep) := by
  rw [d2Delta32Sites,d2Delta32PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta32Poles : polesRoundM 16 24 12 128 d2Delta32Lo d2Delta32Hi d2Delta32Fq.poles d2Delta32Qd = some (d2Delta32Aq,d2Delta32Eq) := by decide +kernel
theorem d2Delta32Laurent : laurentRoundM 16 30 128 d2Delta32Lo d2Delta32Hi d2Delta32Ts d2Delta32Ld = some (d2Delta32Al,d2Delta32El) := by decide +kernel
theorem d2Delta32Small : chebPolyUB (vecAdd d2Delta32S (vecAdd d2Delta32Ap (vecAdd d2Delta32Aq d2Delta32Al))) d2Delta32Gam+d2Delta32Es+d2Delta32Ep+d2Delta32Eq+d2Delta32El ≤ (d2LitsStandaloneDelta004.q2 (-7377377472616635038931) 1 (-80)) := by decide +kernel
theorem d2Delta32Check : chebRoundPieceL d2Delta32Fq d2Delta32Ts 16 24 12 20 30 128 d2Delta32Lo d2Delta32Hi d2Delta32Pd d2Delta32Qd d2Delta32Ld d2Delta32Gam (d2LitsStandaloneDelta004.q2 (-7377377472616635038931) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta32Fq d2Delta32Ts 16 24 12 20 30 128 d2Delta32Lo d2Delta32Hi d2Delta32Pd d2Delta32Qd d2Delta32Ld d2Delta32Gam d2Delta32S d2Delta32Ap d2Delta32Aq d2Delta32Al d2Delta32Es d2Delta32Ep d2Delta32Eq d2Delta32El (by decide +kernel) d2Delta32Shift d2Delta32Plogs d2Delta32Poles d2Delta32Laurent]
  exact decide_eq_true d2Delta32Small
theorem d2Delta32Bound : ∀ x ∈ Icc ((d2Delta32Lo : ℚ) : ℝ) ((d2Delta32Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-7377377472616635038931) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta32Fq d2Delta32Ts 16 24 12 20 30 128 d2Delta32Lo d2Delta32Hi d2Delta32Pd d2Delta32Qd d2Delta32Ld d2Delta32Gam (d2LitsStandaloneDelta004.q2 (-7377377472616635038931) 1 (-80)) d2Delta32Check
  simpa only [d2Delta32Fq, d2Delta32Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta32Shift
#print axioms d2Delta32Sites
#print axioms d2Delta32PData
#print axioms d2Delta32Plogs
#print axioms d2Delta32Poles
#print axioms d2Delta32Laurent
#print axioms d2Delta32Small
#print axioms d2Delta32Check
#print axioms d2Delta32Bound

def d2Delta33Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta33Ts : List LTerm := laurentClean []
def d2Delta33Lo : ℚ := (d2LitsStandaloneDelta004.q2 (1080319) 1 (-25))
def d2Delta33Hi : ℚ := (d2LitsStandaloneDelta004.q2 (70187967) 1 (-31))
def d2Delta33Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta33Qd : List (ℚ × ℚ) := []
def d2Delta33Ld : List LaurentPieceData := []
def d2Delta33Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278710134873391843384048896614305556088541805, 1, -155, -2775991342213419288818343112773384330921, 1, -160, -4089731110737674883673326609728140823, 1, -158, 367938423472382161462731763843144511, 1, -160, -129350037297201824160599013544985, 1, -159, -9886432630974023799953427057513, 1, -160, 18372232663395390701425880471, 1, -159, -19544401796298391703999721, 1, -160, -112057340606332427211299, 1, -160, 19599867976467885149, 1, -157, 37600690277187367, 1, -158, -92800784569425, 1, -158, -23057659619, 1, -158, -1195332207, 1, -158, -4503917801, 1, -160, -3611772601, 1, -160, -3022707245, 1, -160, -2393070425, 1, -160, -1975756223, 1, -160, -1542090065, 1, -160, -1256828081, 1, -160, -482880853, 1, -159, -777522443, 1, -160, -587482695, 1, -160, -116864741, 1, -158, -43369075, 1, -157, -272945067, 1, -160, -12426705, 1, -156, -154675803, 1, -160, -3453227, 1, -155, -21254147, 1, -158, -29763317, 1, -159])
def d2Delta33S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-519138079811229445165840265393174669, 1, -126, -646592864514296589873051653053, 1, -128, -3808617897320152506645120557, 1, -127, 171357698441441497972618651, 1, -127, -241138547312020068321009, 1, -127, -36829321890800631217427, 1, -128, 136887139792664865171, 1, -127, -291255310224376085, 1, -128, -13045366462163, 1, -120, 2336547181121, 1, -126, 8964764991, 1, -127, -44250771, 1, -127, -10215, 1, -126, 501, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta33Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta33Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta33Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta33Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta33Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta33Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta33El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta33Shift : polyRoundApx 128 d2Delta33Lo d2Delta33Hi d2Delta33Fq.poly = (d2Delta33S,d2Delta33Es) := by decide +kernel
theorem d2Delta33Sites : mergeSites d2Delta33Fq.plogs = [] := by decide +kernel
theorem d2Delta33PData : d2Delta33Pd = [] := by decide +kernel
theorem d2Delta33Plogs : plogsRoundM 16 24 20 128 d2Delta33Lo d2Delta33Hi (mergeSites d2Delta33Fq.plogs) d2Delta33Pd = some (d2Delta33Ap,d2Delta33Ep) := by
  rw [d2Delta33Sites,d2Delta33PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta33Poles : polesRoundM 16 24 12 128 d2Delta33Lo d2Delta33Hi d2Delta33Fq.poles d2Delta33Qd = some (d2Delta33Aq,d2Delta33Eq) := by decide +kernel
theorem d2Delta33Laurent : laurentRoundM 16 30 128 d2Delta33Lo d2Delta33Hi d2Delta33Ts d2Delta33Ld = some (d2Delta33Al,d2Delta33El) := by decide +kernel
theorem d2Delta33Small : chebPolyUB (vecAdd d2Delta33S (vecAdd d2Delta33Ap (vecAdd d2Delta33Aq d2Delta33Al))) d2Delta33Gam+d2Delta33Es+d2Delta33Ep+d2Delta33Eq+d2Delta33El ≤ (d2LitsStandaloneDelta004.q2 (-7377393532775317446209) 1 (-80)) := by decide +kernel
theorem d2Delta33Check : chebRoundPieceL d2Delta33Fq d2Delta33Ts 16 24 12 20 30 128 d2Delta33Lo d2Delta33Hi d2Delta33Pd d2Delta33Qd d2Delta33Ld d2Delta33Gam (d2LitsStandaloneDelta004.q2 (-7377393532775317446209) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta33Fq d2Delta33Ts 16 24 12 20 30 128 d2Delta33Lo d2Delta33Hi d2Delta33Pd d2Delta33Qd d2Delta33Ld d2Delta33Gam d2Delta33S d2Delta33Ap d2Delta33Aq d2Delta33Al d2Delta33Es d2Delta33Ep d2Delta33Eq d2Delta33El (by decide +kernel) d2Delta33Shift d2Delta33Plogs d2Delta33Poles d2Delta33Laurent]
  exact decide_eq_true d2Delta33Small
theorem d2Delta33Bound : ∀ x ∈ Icc ((d2Delta33Lo : ℚ) : ℝ) ((d2Delta33Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-7377393532775317446209) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta33Fq d2Delta33Ts 16 24 12 20 30 128 d2Delta33Lo d2Delta33Hi d2Delta33Pd d2Delta33Qd d2Delta33Ld d2Delta33Gam (d2LitsStandaloneDelta004.q2 (-7377393532775317446209) 1 (-80)) d2Delta33Check
  simpa only [d2Delta33Fq, d2Delta33Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta33Shift
#print axioms d2Delta33Sites
#print axioms d2Delta33PData
#print axioms d2Delta33Plogs
#print axioms d2Delta33Poles
#print axioms d2Delta33Laurent
#print axioms d2Delta33Small
#print axioms d2Delta33Check
#print axioms d2Delta33Bound

def d2Delta34Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta34Ts : List LTerm := laurentClean []
def d2Delta34Lo : ℚ := (d2LitsStandaloneDelta004.q2 (70187967) 1 (-31))
def d2Delta34Hi : ℚ := (d2LitsStandaloneDelta004.q2 (35617759) 1 (-30))
def d2Delta34Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta34Qd : List (ℚ × ℚ) := []
def d2Delta34Ld : List LaurentPieceData := []
def d2Delta34Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278710312027510624961387573143306901245055597, 1, -155, -2889286776882250505195795588230525542057, 1, -160, -2993717232787386936032635105192572439, 1, -158, 362265114555192177704545838895536959, 1, -160, -223828227042282590266734294815769, 1, -159, -9011532324998099236853359627113, 1, -160, 18073938538292092117668294039, 1, -159, -23038791409720478123644137, 1, -160, -106308235098056901956131, 1, -160, 20310911161528233053, 1, -157, 33497327300247335, 1, -158, -93665297470545, 1, -158, -16241391331, 1, -158, -1196118639, 1, -158, -4503917801, 1, -160, -3611772601, 1, -160, -3022707245, 1, -160, -2393070425, 1, -160, -1975756223, 1, -160, -1542090065, 1, -160, -1256828081, 1, -160, -482880853, 1, -159, -777522443, 1, -160, -587482695, 1, -160, -116864741, 1, -158, -43369075, 1, -157, -272945067, 1, -160, -12426705, 1, -156, -154675803, 1, -160, -3453227, 1, -155, -21254147, 1, -158, -29763317, 1, -159])
def d2Delta34S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-2076553640166744301146111112690783467, 1, -128, -84120943714032660754081666289, 1, -125, -5575398905203032707348207275, 1, -128, 2636153453890213959860255, 1, -121, -104278638836274875111855, 1, -125, -16784986572472463425231, 1, -127, 269329008066315958613, 1, -128, -343326535996929239, 1, -128, -3168272226881495, 1, -128, 9685242803471, 1, -128, 7986427519, 1, -127, -22331499, 1, -126, -27859, 1, -128, 249, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta34Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta34Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta34Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta34Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta34Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta34Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta34El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta34Shift : polyRoundApx 128 d2Delta34Lo d2Delta34Hi d2Delta34Fq.poly = (d2Delta34S,d2Delta34Es) := by decide +kernel
theorem d2Delta34Sites : mergeSites d2Delta34Fq.plogs = [] := by decide +kernel
theorem d2Delta34PData : d2Delta34Pd = [] := by decide +kernel
theorem d2Delta34Plogs : plogsRoundM 16 24 20 128 d2Delta34Lo d2Delta34Hi (mergeSites d2Delta34Fq.plogs) d2Delta34Pd = some (d2Delta34Ap,d2Delta34Ep) := by
  rw [d2Delta34Sites,d2Delta34PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta34Poles : polesRoundM 16 24 12 128 d2Delta34Lo d2Delta34Hi d2Delta34Fq.poles d2Delta34Qd = some (d2Delta34Aq,d2Delta34Eq) := by decide +kernel
theorem d2Delta34Laurent : laurentRoundM 16 30 128 d2Delta34Lo d2Delta34Hi d2Delta34Ts d2Delta34Ld = some (d2Delta34Al,d2Delta34El) := by decide +kernel
theorem d2Delta34Small : chebPolyUB (vecAdd d2Delta34S (vecAdd d2Delta34Ap (vecAdd d2Delta34Aq d2Delta34Al))) d2Delta34Gam+d2Delta34Es+d2Delta34Ep+d2Delta34Eq+d2Delta34El ≤ (d2LitsStandaloneDelta004.q2 (-7377398131920953076567) 1 (-80)) := by decide +kernel
theorem d2Delta34Check : chebRoundPieceL d2Delta34Fq d2Delta34Ts 16 24 12 20 30 128 d2Delta34Lo d2Delta34Hi d2Delta34Pd d2Delta34Qd d2Delta34Ld d2Delta34Gam (d2LitsStandaloneDelta004.q2 (-7377398131920953076567) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta34Fq d2Delta34Ts 16 24 12 20 30 128 d2Delta34Lo d2Delta34Hi d2Delta34Pd d2Delta34Qd d2Delta34Ld d2Delta34Gam d2Delta34S d2Delta34Ap d2Delta34Aq d2Delta34Al d2Delta34Es d2Delta34Ep d2Delta34Eq d2Delta34El (by decide +kernel) d2Delta34Shift d2Delta34Plogs d2Delta34Poles d2Delta34Laurent]
  exact decide_eq_true d2Delta34Small
theorem d2Delta34Bound : ∀ x ∈ Icc ((d2Delta34Lo : ℚ) : ℝ) ((d2Delta34Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-7377398131920953076567) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta34Fq d2Delta34Ts 16 24 12 20 30 128 d2Delta34Lo d2Delta34Hi d2Delta34Pd d2Delta34Qd d2Delta34Ld d2Delta34Gam (d2LitsStandaloneDelta004.q2 (-7377398131920953076567) 1 (-80)) d2Delta34Check
  simpa only [d2Delta34Fq, d2Delta34Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta34Shift
#print axioms d2Delta34Sites
#print axioms d2Delta34PData
#print axioms d2Delta34Plogs
#print axioms d2Delta34Poles
#print axioms d2Delta34Laurent
#print axioms d2Delta34Small
#print axioms d2Delta34Check
#print axioms d2Delta34Bound

def d2Delta35Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta35Ts : List LTerm := laurentClean []
def d2Delta35Lo : ℚ := (d2LitsStandaloneDelta004.q2 (35617759) 1 (-30))
def d2Delta35Hi : ℚ := (d2LitsStandaloneDelta004.q2 (18332655) 1 (-29))
def d2Delta35Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta35Qd : List (ℚ × ℚ) := []
def d2Delta35Ld : List LaurentPieceData := []
def d2Delta35Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278710588844956955566244115983305657858445933, 1, -155, -2991184302313183538905939663085795716563, 1, -159, -5578174885097053057751597347595220503, 1, -158, 696635213093373333362142664913714621, 1, -158, -5584288234150804650663910393205785, 1, -159, -30917905365396654170088416527731, 1, -157, 1122359861541364550268264869271, 1, -159, -893539202759586998727799369, 1, -158, -24915710448633279828890147, 1, -160, 86922283779114138926861, 1, -160, 27943661509035425575, 1, -158, -193218377147425915, 1, -158, -18398448187107, 1, -158, 1052143642821, 1, -158, -6452172009, 1, -160, -1817652773, 1, -159, -3022707245, 1, -160, -2397189193, 1, -160, -1975756223, 1, -160, -1543981337, 1, -160, -1256828081, 1, -160, -966493577, 1, -160, -777522443, 1, -160, -146930093, 1, -158, -116864741, 1, -158, -347016741, 1, -160, -272945067, 1, -160, -99420717, 1, -159, -154675803, 1, -160, -27626439, 1, -158, -21254147, 1, -158, -59526971, 1, -160])
def d2Delta35S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-2076555700212971740156537851950426801, 1, -128, -697412698515071800641257750145, 1, -127, -5184673944404079552668202839, 1, -127, 1298160068014313529271959623, 1, -127, -20828182408511458688648439, 1, -128, -460666085553420318033447, 1, -127, 16725950335550598945309, 1, -128, -26635372233386721617, 1, -127, -742579346867413031, 1, -128, 5181478599401887, 1, -128, 13324681394387, 1, -128, -92140231493, 1, -127, -17538065, 1, -127, 2009455, 1, -127, -3717, 1, -128, -31, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta35Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta35Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta35Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta35Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta35Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta35Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta35El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta35Shift : polyRoundApx 128 d2Delta35Lo d2Delta35Hi d2Delta35Fq.poly = (d2Delta35S,d2Delta35Es) := by decide +kernel
theorem d2Delta35Sites : mergeSites d2Delta35Fq.plogs = [] := by decide +kernel
theorem d2Delta35PData : d2Delta35Pd = [] := by decide +kernel
theorem d2Delta35Plogs : plogsRoundM 16 24 20 128 d2Delta35Lo d2Delta35Hi (mergeSites d2Delta35Fq.plogs) d2Delta35Pd = some (d2Delta35Ap,d2Delta35Ep) := by
  rw [d2Delta35Sites,d2Delta35PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta35Poles : polesRoundM 16 24 12 128 d2Delta35Lo d2Delta35Hi d2Delta35Fq.poles d2Delta35Qd = some (d2Delta35Aq,d2Delta35Eq) := by decide +kernel
theorem d2Delta35Laurent : laurentRoundM 16 30 128 d2Delta35Lo d2Delta35Hi d2Delta35Ts d2Delta35Ld = some (d2Delta35Al,d2Delta35El) := by decide +kernel
theorem d2Delta35Small : chebPolyUB (vecAdd d2Delta35S (vecAdd d2Delta35Ap (vecAdd d2Delta35Aq d2Delta35Al))) d2Delta35Gam+d2Delta35Es+d2Delta35Ep+d2Delta35Eq+d2Delta35El ≤ (d2LitsStandaloneDelta004.q2 (-7377402890114792346191) 1 (-80)) := by decide +kernel
theorem d2Delta35Check : chebRoundPieceL d2Delta35Fq d2Delta35Ts 16 24 12 20 30 128 d2Delta35Lo d2Delta35Hi d2Delta35Pd d2Delta35Qd d2Delta35Ld d2Delta35Gam (d2LitsStandaloneDelta004.q2 (-7377402890114792346191) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta35Fq d2Delta35Ts 16 24 12 20 30 128 d2Delta35Lo d2Delta35Hi d2Delta35Pd d2Delta35Qd d2Delta35Ld d2Delta35Gam d2Delta35S d2Delta35Ap d2Delta35Aq d2Delta35Al d2Delta35Es d2Delta35Ep d2Delta35Eq d2Delta35El (by decide +kernel) d2Delta35Shift d2Delta35Plogs d2Delta35Poles d2Delta35Laurent]
  exact decide_eq_true d2Delta35Small
theorem d2Delta35Bound : ∀ x ∈ Icc ((d2Delta35Lo : ℚ) : ℝ) ((d2Delta35Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-7377402890114792346191) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta35Fq d2Delta35Ts 16 24 12 20 30 128 d2Delta35Lo d2Delta35Hi d2Delta35Pd d2Delta35Qd d2Delta35Ld d2Delta35Gam (d2LitsStandaloneDelta004.q2 (-7377402890114792346191) 1 (-80)) d2Delta35Check
  simpa only [d2Delta35Fq, d2Delta35Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta35Shift
#print axioms d2Delta35Sites
#print axioms d2Delta35PData
#print axioms d2Delta35Plogs
#print axioms d2Delta35Poles
#print axioms d2Delta35Laurent
#print axioms d2Delta35Small
#print axioms d2Delta35Check
#print axioms d2Delta35Bound

def d2Delta36Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta36Ts : List LTerm := laurentClean []
def d2Delta36Lo : ℚ := (d2LitsStandaloneDelta004.q2 (18332655) 1 (-29))
def d2Delta36Hi : ℚ := (d2LitsStandaloneDelta004.q2 (20427757) 1 (-29))
def d2Delta36Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta36Qd : List (ℚ × ℚ) := []
def d2Delta36Ld : List LaurentPieceData := []
def d2Delta36Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278711491762914117524755695494360253149961837, 1, -155, -347080044841539709099645917867519851097, 1, -154, 204873130575046336390773560503383378409, 1, -158, 17015610090477426523542574617396189617, 1, -157, -2577489265490182225451276396731208729, 1, -159, -31232081058727189591548069996862251, 1, -158, 3953188634992660166895198767574423, 1, -159, -10713014302895079157395750452447, 1, -157, -1095305134118816527482098586147, 1, -160, 24573069329958191407933932337, 1, -160, 7218163324248660846018343, 1, -158, -392703960349663943612287, 1, -157, 1881182273973834283293, 1, -158, 7919975415165040853, 1, -155, -1123080180801524969, 1, -160, -7237938703684665, 1, -159, 86974245152211, 1, -160, 615283504919, 1, -160, -6627009983, 1, -160, -1567442581, 1, -160, -1256647857, 1, -160, -967301517, 1, -160, -777522443, 1, -160, -73486289, 1, -157, -116864741, 1, -158, -347046177, 1, -160, -272945067, 1, -160, -99422747, 1, -159, -154675803, 1, -160, -1726659, 1, -154, -21254147, 1, -158, -7440875, 1, -157])
def d2Delta36S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-64892582021047274353345542014077163, 1, -123, -5267123122117757102334102910741, 1, -128, 97810245508460835849157758599, 1, -126, 127356799086581113771545866583, 1, -128, -4845148606361636051328448721, 1, -127, -231578446401512164767230419, 1, -127, 1842887308625047178486129, 1, -123, -1280388389802982392503673, 1, -128, -32651229324356050639921, 1, -128, 733364932417847768487, 1, -127, 3431113963132890465, 1, -128, -93726149072401981, 1, -125, 1797786060940241, 1, -127, 120952808816807, 1, -127, -134047560769, 1, -124, -27630572491, 1, -127, 332111439, 1, -127, 9431093, 1, -128, -17757, 1, -125, -309, 1, -126, 11, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta36Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta36Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta36Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta36Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta36Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta36Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta36El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta36Shift : polyRoundApx 128 d2Delta36Lo d2Delta36Hi d2Delta36Fq.poly = (d2Delta36S,d2Delta36Es) := by decide +kernel
theorem d2Delta36Sites : mergeSites d2Delta36Fq.plogs = [] := by decide +kernel
theorem d2Delta36PData : d2Delta36Pd = [] := by decide +kernel
theorem d2Delta36Plogs : plogsRoundM 16 24 20 128 d2Delta36Lo d2Delta36Hi (mergeSites d2Delta36Fq.plogs) d2Delta36Pd = some (d2Delta36Ap,d2Delta36Ep) := by
  rw [d2Delta36Sites,d2Delta36PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta36Poles : polesRoundM 16 24 12 128 d2Delta36Lo d2Delta36Hi d2Delta36Fq.poles d2Delta36Qd = some (d2Delta36Aq,d2Delta36Eq) := by decide +kernel
theorem d2Delta36Laurent : laurentRoundM 16 30 128 d2Delta36Lo d2Delta36Hi d2Delta36Ts d2Delta36Ld = some (d2Delta36Al,d2Delta36El) := by decide +kernel
theorem d2Delta36Small : chebPolyUB (vecAdd d2Delta36S (vecAdd d2Delta36Ap (vecAdd d2Delta36Aq d2Delta36Al))) d2Delta36Gam+d2Delta36Es+d2Delta36Ep+d2Delta36Eq+d2Delta36El ≤ (d2LitsStandaloneDelta004.q2 (-7377412590317674247539) 1 (-80)) := by decide +kernel
theorem d2Delta36Check : chebRoundPieceL d2Delta36Fq d2Delta36Ts 16 24 12 20 30 128 d2Delta36Lo d2Delta36Hi d2Delta36Pd d2Delta36Qd d2Delta36Ld d2Delta36Gam (d2LitsStandaloneDelta004.q2 (-7377412590317674247539) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta36Fq d2Delta36Ts 16 24 12 20 30 128 d2Delta36Lo d2Delta36Hi d2Delta36Pd d2Delta36Qd d2Delta36Ld d2Delta36Gam d2Delta36S d2Delta36Ap d2Delta36Aq d2Delta36Al d2Delta36Es d2Delta36Ep d2Delta36Eq d2Delta36El (by decide +kernel) d2Delta36Shift d2Delta36Plogs d2Delta36Poles d2Delta36Laurent]
  exact decide_eq_true d2Delta36Small
theorem d2Delta36Bound : ∀ x ∈ Icc ((d2Delta36Lo : ℚ) : ℝ) ((d2Delta36Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-7377412590317674247539) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta36Fq d2Delta36Ts 16 24 12 20 30 128 d2Delta36Lo d2Delta36Hi d2Delta36Pd d2Delta36Qd d2Delta36Ld d2Delta36Gam (d2LitsStandaloneDelta004.q2 (-7377412590317674247539) 1 (-80)) d2Delta36Check
  simpa only [d2Delta36Fq, d2Delta36Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta36Shift
#print axioms d2Delta36Sites
#print axioms d2Delta36PData
#print axioms d2Delta36Plogs
#print axioms d2Delta36Poles
#print axioms d2Delta36Laurent
#print axioms d2Delta36Small
#print axioms d2Delta36Check
#print axioms d2Delta36Bound

def d2Delta37Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta37Ts : List LTerm := laurentClean []
def d2Delta37Lo : ℚ := (d2LitsStandaloneDelta004.q2 (20427757) 1 (-29))
def d2Delta37Hi : ℚ := (d2LitsStandaloneDelta004.q2 (41903065) 1 (-30))
def d2Delta37Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta37Qd : List (ℚ × ℚ) := []
def d2Delta37Ld : List LaurentPieceData := []
def d2Delta37Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278712285879059974209841722381144220937212525, 1, -155, -63231456716838545076474761803309816397, 1, -154, 25847145377620830817907302928901736937, 1, -158, 154879739815364415106936770617180241, 1, -157, -11839509781048064604965225479754777, 1, -159, -4335998223047519459218247543995, 1, -158, 763164063164946877959806610839, 1, -159, -780279461832487216845854423, 1, -157, -8267076236475101932327459, 1, -160, 92609303046021968090737, 1, -160, -12754447035405566169, 1, -158, -83506651934993831, 1, -157, 224214747711773, 1, -158, 95570971185, 1, -155, -10450916585, 1, -160, -1827827705, 1, -159, -3022707245, 1, -160, -2406227049, 1, -160, -1975756223, 1, -160, -1546673941, 1, -160, -1256828081, 1, -160, -967191117, 1, -160, -777522443, 1, -160, -73484281, 1, -157, -116864741, 1, -158, -347044705, 1, -160, -272945067, 1, -160, -99422715, 1, -159, -154675803, 1, -160, -1726659, 1, -154, -21254147, 1, -158, -7440875, 1, -157])
def d2Delta37S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-1038284186686177415668120127188426355, 1, -127, -943087607228547243507030675833, 1, -128, 1505880373963986009793288359, 1, -123, 288506166798364890313596505, 1, -126, -11030667319983747936035119, 1, -126, -32224310081125862254469, 1, -127, 1421565433176292592035, 1, -125, -46514490304754161017, 1, -127, -7698839539812671, 1, -123, 5520382632640491, 1, -128, -3041538654367, 1, -127, -159285792385, 1, -128, 26731157, 1, -124, 2921871, 1, -128, -709, 1, -124, -19, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta37Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta37Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta37Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta37Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta37Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta37Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta37El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta37Shift : polyRoundApx 128 d2Delta37Lo d2Delta37Hi d2Delta37Fq.poly = (d2Delta37S,d2Delta37Es) := by decide +kernel
theorem d2Delta37Sites : mergeSites d2Delta37Fq.plogs = [] := by decide +kernel
theorem d2Delta37PData : d2Delta37Pd = [] := by decide +kernel
theorem d2Delta37Plogs : plogsRoundM 16 24 20 128 d2Delta37Lo d2Delta37Hi (mergeSites d2Delta37Fq.plogs) d2Delta37Pd = some (d2Delta37Ap,d2Delta37Ep) := by
  rw [d2Delta37Sites,d2Delta37PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta37Poles : polesRoundM 16 24 12 128 d2Delta37Lo d2Delta37Hi d2Delta37Fq.poles d2Delta37Qd = some (d2Delta37Aq,d2Delta37Eq) := by decide +kernel
theorem d2Delta37Laurent : laurentRoundM 16 30 128 d2Delta37Lo d2Delta37Hi d2Delta37Ts d2Delta37Ld = some (d2Delta37Al,d2Delta37El) := by decide +kernel
theorem d2Delta37Small : chebPolyUB (vecAdd d2Delta37S (vecAdd d2Delta37Ap (vecAdd d2Delta37Aq d2Delta37Al))) d2Delta37Gam+d2Delta37Es+d2Delta37Ep+d2Delta37Eq+d2Delta37El ≤ (d2LitsStandaloneDelta004.q2 (-7377449345492865488425) 1 (-80)) := by decide +kernel
theorem d2Delta37Check : chebRoundPieceL d2Delta37Fq d2Delta37Ts 16 24 12 20 30 128 d2Delta37Lo d2Delta37Hi d2Delta37Pd d2Delta37Qd d2Delta37Ld d2Delta37Gam (d2LitsStandaloneDelta004.q2 (-7377449345492865488425) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta37Fq d2Delta37Ts 16 24 12 20 30 128 d2Delta37Lo d2Delta37Hi d2Delta37Pd d2Delta37Qd d2Delta37Ld d2Delta37Gam d2Delta37S d2Delta37Ap d2Delta37Aq d2Delta37Al d2Delta37Es d2Delta37Ep d2Delta37Eq d2Delta37El (by decide +kernel) d2Delta37Shift d2Delta37Plogs d2Delta37Poles d2Delta37Laurent]
  exact decide_eq_true d2Delta37Small
theorem d2Delta37Bound : ∀ x ∈ Icc ((d2Delta37Lo : ℚ) : ℝ) ((d2Delta37Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-7377449345492865488425) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta37Fq d2Delta37Ts 16 24 12 20 30 128 d2Delta37Lo d2Delta37Hi d2Delta37Pd d2Delta37Qd d2Delta37Ld d2Delta37Gam (d2LitsStandaloneDelta004.q2 (-7377449345492865488425) 1 (-80)) d2Delta37Check
  simpa only [d2Delta37Fq, d2Delta37Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta37Shift
#print axioms d2Delta37Sites
#print axioms d2Delta37PData
#print axioms d2Delta37Plogs
#print axioms d2Delta37Poles
#print axioms d2Delta37Laurent
#print axioms d2Delta37Small
#print axioms d2Delta37Check
#print axioms d2Delta37Bound

def d2Delta38Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta38Ts : List LTerm := laurentClean []
def d2Delta38Lo : ℚ := (d2LitsStandaloneDelta004.q2 (41903065) 1 (-30))
def d2Delta38Hi : ℚ := (d2LitsStandaloneDelta004.q2 (84853681) 1 (-31))
def d2Delta38Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta38Qd : List (ℚ × ℚ) := []
def d2Delta38Ld : List LaurentPieceData := []
def d2Delta38Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278712463048805152018014630990831192756245101, 1, -155, -26547044869608760452143115463749570925, 1, -154, 7083104743959495327114161195947002345, 1, -158, 14908235310839330414361841664360785, 1, -157, -742046016342612806676835632370713, 1, -159, 70094410616340109269140814149, 1, -158, 10885970047573486334608108951, 1, -159, -6261169728419257177108951, 1, -157, -22616030137377854231075, 1, -160, 177263376830501972593, 1, -160, -17704257628668121, 1, -158, -38679089120295, 1, -157, 60098611485, 1, -158, -156592047, 1, -155, -4503917801, 1, -160, -1818444281, 1, -159, -3022707245, 1, -160, -2404413545, 1, -160, -1975756223, 1, -160, -1546414869, 1, -160, -1256828081, 1, -160, -967167565, 1, -160, -777522443, 1, -160, -73484153, 1, -157, -116864741, 1, -158, -347044705, 1, -160, -272945067, 1, -160, -99422715, 1, -159, -154675803, 1, -160, -1726659, 1, -154, -21254147, 1, -158, -7440875, 1, -157])
def d2Delta38S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-2076569675909277972350618205238806409, 1, -128, -98916275188104597236969078361, 1, -126, 13196075120901942682426691523, 1, -128, 111073702478079115051244417, 1, -128, -1382290073463799019400103, 1, -127, 522897155501482851615, 1, -127, 162214942432265342819, 1, -128, -746413368155961767, 1, -128, -673989115769209, 1, -128, 10565923484499, 1, -128, -2110600009, 1, -126, -18443435, 1, -126, 29437, 1, -126, 163, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta38Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta38Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta38Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta38Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta38Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta38Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta38El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta38Shift : polyRoundApx 128 d2Delta38Lo d2Delta38Hi d2Delta38Fq.poly = (d2Delta38S,d2Delta38Es) := by decide +kernel
theorem d2Delta38Sites : mergeSites d2Delta38Fq.plogs = [] := by decide +kernel
theorem d2Delta38PData : d2Delta38Pd = [] := by decide +kernel
theorem d2Delta38Plogs : plogsRoundM 16 24 20 128 d2Delta38Lo d2Delta38Hi (mergeSites d2Delta38Fq.plogs) d2Delta38Pd = some (d2Delta38Ap,d2Delta38Ep) := by
  rw [d2Delta38Sites,d2Delta38PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta38Poles : polesRoundM 16 24 12 128 d2Delta38Lo d2Delta38Hi d2Delta38Fq.poles d2Delta38Qd = some (d2Delta38Aq,d2Delta38Eq) := by decide +kernel
theorem d2Delta38Laurent : laurentRoundM 16 30 128 d2Delta38Lo d2Delta38Hi d2Delta38Ts d2Delta38Ld = some (d2Delta38Al,d2Delta38El) := by decide +kernel
theorem d2Delta38Small : chebPolyUB (vecAdd d2Delta38S (vecAdd d2Delta38Ap (vecAdd d2Delta38Aq d2Delta38Al))) d2Delta38Gam+d2Delta38Es+d2Delta38Ep+d2Delta38Eq+d2Delta38El ≤ (d2LitsStandaloneDelta004.q2 (-7377456040223196059993) 1 (-80)) := by decide +kernel
theorem d2Delta38Check : chebRoundPieceL d2Delta38Fq d2Delta38Ts 16 24 12 20 30 128 d2Delta38Lo d2Delta38Hi d2Delta38Pd d2Delta38Qd d2Delta38Ld d2Delta38Gam (d2LitsStandaloneDelta004.q2 (-7377456040223196059993) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta38Fq d2Delta38Ts 16 24 12 20 30 128 d2Delta38Lo d2Delta38Hi d2Delta38Pd d2Delta38Qd d2Delta38Ld d2Delta38Gam d2Delta38S d2Delta38Ap d2Delta38Aq d2Delta38Al d2Delta38Es d2Delta38Ep d2Delta38Eq d2Delta38El (by decide +kernel) d2Delta38Shift d2Delta38Plogs d2Delta38Poles d2Delta38Laurent]
  exact decide_eq_true d2Delta38Small
theorem d2Delta38Bound : ∀ x ∈ Icc ((d2Delta38Lo : ℚ) : ℝ) ((d2Delta38Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-7377456040223196059993) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta38Fq d2Delta38Ts 16 24 12 20 30 128 d2Delta38Lo d2Delta38Hi d2Delta38Pd d2Delta38Qd d2Delta38Ld d2Delta38Gam (d2LitsStandaloneDelta004.q2 (-7377456040223196059993) 1 (-80)) d2Delta38Check
  simpa only [d2Delta38Fq, d2Delta38Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta38Shift
#print axioms d2Delta38Sites
#print axioms d2Delta38PData
#print axioms d2Delta38Plogs
#print axioms d2Delta38Poles
#print axioms d2Delta38Laurent
#print axioms d2Delta38Small
#print axioms d2Delta38Check
#print axioms d2Delta38Bound

def d2Delta39Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta39Ts : List LTerm := laurentClean []
def d2Delta39Lo : ℚ := (d2LitsStandaloneDelta004.q2 (84853681) 1 (-31))
def d2Delta39Hi : ℚ := (d2LitsStandaloneDelta004.q2 (5368827) 1 (-27))
def d2Delta39Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta39Qd : List (ℚ × ℚ) := []
def d2Delta39Ld : List LaurentPieceData := []
def d2Delta39Gam : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-278712562021143838649408257696948365646287469, 1, -155, -22922340972953579931208503121199236205, 1, -154, 7405353109539485496508720243133778409, 1, -158, 11949147843718961107376718776839505, 1, -157, -736686607288257919594969686299673, 1, -159, 196499569310332034116461867333, 1, -158, 10180130696451233429323214231, 1, -159, -6338942526633816466710999, 1, -157, -16288785742544084832803, 1, -160, 174161953214490471025, 1, -160, -21041197377650905, 1, -158, -37145243221543, 1, -157, 64406685981, 1, -158, -158046255, 1, -155, -4503917801, 1, -160, -1821168121, 1, -159, -3022707245, 1, -160, -2405273705, 1, -160, -1975756223, 1, -160, -1546500885, 1, -160, -1256828081, 1, -160, -967171661, 1, -160, -777522443, 1, -160, -73484153, 1, -157, -116864741, 1, -158, -347044705, 1, -160, -272945067, 1, -160, -99422715, 1, -159, -154675803, 1, -160, -1726659, 1, -154, -21254147, 1, -158, -7440875, 1, -157])
def d2Delta39S : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [-2076570413610778904639617640008326379, 1, -128, -341636267930020578696468895599, 1, -128, 13796289504626235553986203873, 1, -128, 89024428323282575570423007, 1, -128, -2744599015397289321897641, 1, -128, 2929394180794117033929, 1, -128, 75848369673798271383, 1, -127, -377842096118065565, 1, -127, -485418560518735, 1, -128, 2595264046525, 1, -126, -5016800777, 1, -127, -70848073, 1, -128, 125965, 1, -128, 305, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta39Ap : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta39Aq : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta39Al : List ℚ := d2LitsStandaloneDelta004.q2listC (raw_ints% [])
def d2Delta39Es : ℚ := (d2LitsStandaloneDelta004.q2 (61) 1 (-127))
def d2Delta39Ep : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta39Eq : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
def d2Delta39El : ℚ := (d2LitsStandaloneDelta004.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta39Shift : polyRoundApx 128 d2Delta39Lo d2Delta39Hi d2Delta39Fq.poly = (d2Delta39S,d2Delta39Es) := by decide +kernel
theorem d2Delta39Sites : mergeSites d2Delta39Fq.plogs = [] := by decide +kernel
theorem d2Delta39PData : d2Delta39Pd = [] := by decide +kernel
theorem d2Delta39Plogs : plogsRoundM 16 24 20 128 d2Delta39Lo d2Delta39Hi (mergeSites d2Delta39Fq.plogs) d2Delta39Pd = some (d2Delta39Ap,d2Delta39Ep) := by
  rw [d2Delta39Sites,d2Delta39PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta39Poles : polesRoundM 16 24 12 128 d2Delta39Lo d2Delta39Hi d2Delta39Fq.poles d2Delta39Qd = some (d2Delta39Aq,d2Delta39Eq) := by decide +kernel
theorem d2Delta39Laurent : laurentRoundM 16 30 128 d2Delta39Lo d2Delta39Hi d2Delta39Ts d2Delta39Ld = some (d2Delta39Al,d2Delta39El) := by decide +kernel
theorem d2Delta39Small : chebPolyUB (vecAdd d2Delta39S (vecAdd d2Delta39Ap (vecAdd d2Delta39Aq d2Delta39Al))) d2Delta39Gam+d2Delta39Es+d2Delta39Ep+d2Delta39Eq+d2Delta39El ≤ (d2LitsStandaloneDelta004.q2 (-3688729425421386968615) 1 (-79)) := by decide +kernel
theorem d2Delta39Check : chebRoundPieceL d2Delta39Fq d2Delta39Ts 16 24 12 20 30 128 d2Delta39Lo d2Delta39Hi d2Delta39Pd d2Delta39Qd d2Delta39Ld d2Delta39Gam (d2LitsStandaloneDelta004.q2 (-3688729425421386968615) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta39Fq d2Delta39Ts 16 24 12 20 30 128 d2Delta39Lo d2Delta39Hi d2Delta39Pd d2Delta39Qd d2Delta39Ld d2Delta39Gam d2Delta39S d2Delta39Ap d2Delta39Aq d2Delta39Al d2Delta39Es d2Delta39Ep d2Delta39Eq d2Delta39El (by decide +kernel) d2Delta39Shift d2Delta39Plogs d2Delta39Poles d2Delta39Laurent]
  exact decide_eq_true d2Delta39Small
theorem d2Delta39Bound : ∀ x ∈ Icc ((d2Delta39Lo : ℚ) : ℝ) ((d2Delta39Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta004.q2 (-3688729425421386968615) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta39Fq d2Delta39Ts 16 24 12 20 30 128 d2Delta39Lo d2Delta39Hi d2Delta39Pd d2Delta39Qd d2Delta39Ld d2Delta39Gam (d2LitsStandaloneDelta004.q2 (-3688729425421386968615) 1 (-79)) d2Delta39Check
  simpa only [d2Delta39Fq, d2Delta39Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta39Shift
#print axioms d2Delta39Sites
#print axioms d2Delta39PData
#print axioms d2Delta39Plogs
#print axioms d2Delta39Poles
#print axioms d2Delta39Laurent
#print axioms d2Delta39Small
#print axioms d2Delta39Check
#print axioms d2Delta39Bound

end StandaloneDelta004
end CatalanMeasure.GenD.Signed.Data.Cells
