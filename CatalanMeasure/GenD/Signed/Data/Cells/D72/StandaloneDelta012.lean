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
namespace d2LitsStandaloneDelta012
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta012
namespace StandaloneDelta012
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta012.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta012.q2listC (raw_ints% []))⟩
def d2Delta96Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta96Ts : List LTerm := laurentClean []
def d2Delta96Lo : ℚ := (d2LitsStandaloneDelta012.q2 (7365625) 1 (-25))
def d2Delta96Hi : ℚ := (d2LitsStandaloneDelta012.q2 (30510051) 1 (-27))
def d2Delta96Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta96Qd : List (ℚ × ℚ) := []
def d2Delta96Ld : List LaurentPieceData := []
def d2Delta96Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-8918660646329594106341007990014746821724694573, 1, -160, 39999577741531836821276430795864954320625, 1, -159, -2428964430814082109512945373715785712585, 1, -160, -95321369544391464185413908307932858715, 1, -157, -491599542738791213100761807121416631, 1, -159, 1105412488829933685999921071665605739, 1, -159, 18270033037836916162316898788377463, 1, -160, -3130335026922643177085683774653487, 1, -160, -16149671711658718773269451273183, 1, -159, 2641569525547099250938109654451, 1, -160, 28511078865549418627097134149, 1, -160, -184885907881838405453053303, 1, -157, -7878058659135442957382025, 1, -159, 293874201810085322202031, 1, -159, 6034119679922408418665, 1, -160, -173596994616359437545, 1, -160, -851040473527825677, 1, -159, 19710743618472587, 1, -159, 46096324145181, 1, -157, -7064107765291, 1, -160, -32246626661, 1, -159, 225822041, 1, -160, -22451749, 1, -155, -118117745, 1, -158, -108443363, 1, -158, -272659033, 1, -160, -251284605, 1, -160, -152432071, 1, -160, -17661385, 1, -157, -82483851, 1, -160, -77049551, 1, -160, -10794067, 1, -158])
def d2Delta96S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-2076536933511184700449132862398535799, 1, -128, 9580741684552393843363551599989, 1, -127, -1129166542865332209896602244745, 1, -128, -720535391254627185543187690903, 1, -128, -509185110117583129262263901, 1, -126, 2079465202262877261648245735, 1, -126, 138054992552429922180314839, 1, -128, -2937553752454980591699185, 1, -124, -60694862735638920203535, 1, -124, 158421858362137565009245, 1, -128, 3421380221866533714377, 1, -128, -177233652289843609329, 1, -127, -7553468805170971271, 1, -128, 563008360287063115, 1, -128, 11561208362572591, 1, -128, -332390278720043, 1, -127, -6518286212671, 1, -127, 301787380323, 1, -127, 11292739269, 1, -128, -432387715, 1, -128, -1937945, 1, -126, 124711, 1, -127, 4319, 1, -128, -59, 1, -127, -1, 1, -127, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta96Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta96Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta96Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta96Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta96Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta96Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta96El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta96Shift : polyRoundApx 128 d2Delta96Lo d2Delta96Hi d2Delta96Fq.poly = (d2Delta96S,d2Delta96Es) := by decide +kernel
theorem d2Delta96Sites : mergeSites d2Delta96Fq.plogs = [] := by decide +kernel
theorem d2Delta96PData : d2Delta96Pd = [] := by decide +kernel
theorem d2Delta96Plogs : plogsRoundM 16 24 20 128 d2Delta96Lo d2Delta96Hi (mergeSites d2Delta96Fq.plogs) d2Delta96Pd = some (d2Delta96Ap,d2Delta96Ep) := by
  rw [d2Delta96Sites,d2Delta96PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta96Poles : polesRoundM 16 24 12 128 d2Delta96Lo d2Delta96Hi d2Delta96Fq.poles d2Delta96Qd = some (d2Delta96Aq,d2Delta96Eq) := by decide +kernel
theorem d2Delta96Laurent : laurentRoundM 16 30 128 d2Delta96Lo d2Delta96Hi d2Delta96Ts d2Delta96Ld = some (d2Delta96Al,d2Delta96El) := by decide +kernel
theorem d2Delta96Small : chebPolyUB (vecAdd d2Delta96S (vecAdd d2Delta96Ap (vecAdd d2Delta96Aq d2Delta96Al))) d2Delta96Gam+d2Delta96Es+d2Delta96Ep+d2Delta96Eq+d2Delta96El ≤ (d2LitsStandaloneDelta012.q2 (-1844318590049274235027) 1 (-78)) := by decide +kernel
theorem d2Delta96Check : chebRoundPieceL d2Delta96Fq d2Delta96Ts 16 24 12 20 30 128 d2Delta96Lo d2Delta96Hi d2Delta96Pd d2Delta96Qd d2Delta96Ld d2Delta96Gam (d2LitsStandaloneDelta012.q2 (-1844318590049274235027) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta96Fq d2Delta96Ts 16 24 12 20 30 128 d2Delta96Lo d2Delta96Hi d2Delta96Pd d2Delta96Qd d2Delta96Ld d2Delta96Gam d2Delta96S d2Delta96Ap d2Delta96Aq d2Delta96Al d2Delta96Es d2Delta96Ep d2Delta96Eq d2Delta96El (by decide +kernel) d2Delta96Shift d2Delta96Plogs d2Delta96Poles d2Delta96Laurent]
  exact decide_eq_true d2Delta96Small
theorem d2Delta96Bound : ∀ x ∈ Icc ((d2Delta96Lo : ℚ) : ℝ) ((d2Delta96Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-1844318590049274235027) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta96Fq d2Delta96Ts 16 24 12 20 30 128 d2Delta96Lo d2Delta96Hi d2Delta96Pd d2Delta96Qd d2Delta96Ld d2Delta96Gam (d2LitsStandaloneDelta012.q2 (-1844318590049274235027) 1 (-78)) d2Delta96Check
  simpa only [d2Delta96Fq, d2Delta96Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta96Shift
#print axioms d2Delta96Sites
#print axioms d2Delta96PData
#print axioms d2Delta96Plogs
#print axioms d2Delta96Poles
#print axioms d2Delta96Laurent
#print axioms d2Delta96Small
#print axioms d2Delta96Check
#print axioms d2Delta96Bound

def d2Delta97Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta97Ts : List LTerm := laurentClean []
def d2Delta97Lo : ℚ := (d2LitsStandaloneDelta012.q2 (30510051) 1 (-27))
def d2Delta97Hi : ℚ := (d2LitsStandaloneDelta012.q2 (32605153) 1 (-27))
def d2Delta97Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta97Qd : List (ℚ × ℚ) := []
def d2Delta97Ld : List LaurentPieceData := []
def d2Delta97Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-2229643971368210382456751285820511315132660329, 1, -158, -8844105544562755478286357439334281855873, 1, -158, -44508052974798839926824940538492860490579, 1, -160, -102456652582167230690056907960366688243, 1, -158, 198254088887329513665863083631086413189, 1, -158, 8704282855058834613778623665319521709, 1, -159, -5971262180457135959386928152849137479, 1, -160, -149340378059363446394719637617638051, 1, -160, 784374529867355978261200655781879, 1, -155, 637011223176811266915192847681119, 1, -160, -67304819972260109553209373896617, 1, -160, -104329647948460753604233985613, 1, -156, 124684994681670748510456859261, 1, -160, 1489603133892423985425811747, 1, -159, -84182197304947277548986443, 1, -159, -3859439224593002814879981, 1, -160, 86110432990347406961607, 1, -159, 59268251421411029521, 1, -154, -34342125187562193743, 1, -158, -2922768220403545283, 1, -160, 87374564408781309, 1, -160, 905541428523953, 1, -159, -45110122775685, 1, -160, -460742451345, 1, -159, 4698850867, 1, -158, 31023089, 1, -160, -54996405, 1, -158, -204967163, 1, -160, -116997241, 1, -160, -28231213, 1, -158, -7770573, 1, -157, -60201731, 1, -160])
def d2Delta97S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-2076507215017239001249575198042622827, 1, -128, -1982485897872026368670788512177, 1, -126, -22227998377521028024621255145057, 1, -128, -232355392812994645270915697665, 1, -127, 772391731568757812150200092011, 1, -127, 68810868029901312719473598057, 1, -128, -46003101342444625509172184465, 1, -128, -1155938160697364538192336089, 1, -127, 768297958839673047565215683, 1, -128, 39074895055502603618805163, 1, -128, -8203275771822160610217499, 1, -128, -203651556948536550011719, 1, -127, 60586968602472077199281, 1, -128, 362104319588198240613, 1, -125, -326420866550122322529, 1, -128, -3742569991482687023, 1, -126, 1332919337423501907, 1, -128, 29365876709234543, 1, -127, -4245771763275091, 1, -128, -180725919543185, 1, -128, 2696893887673, 1, -126, 447356366213, 1, -128, -11125887671, 1, -127, -908869561, 1, -128, 37790843, 1, -128, 1540307, 1, -128, -53435, 1, -128, -2207, 1, -128, 63, 1, -128, 1, 1, -127, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta97Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta97Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta97Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta97Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta97Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta97Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta97El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta97Shift : polyRoundApx 128 d2Delta97Lo d2Delta97Hi d2Delta97Fq.poly = (d2Delta97S,d2Delta97Es) := by decide +kernel
theorem d2Delta97Sites : mergeSites d2Delta97Fq.plogs = [] := by decide +kernel
theorem d2Delta97PData : d2Delta97Pd = [] := by decide +kernel
theorem d2Delta97Plogs : plogsRoundM 16 24 20 128 d2Delta97Lo d2Delta97Hi (mergeSites d2Delta97Fq.plogs) d2Delta97Pd = some (d2Delta97Ap,d2Delta97Ep) := by
  rw [d2Delta97Sites,d2Delta97PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta97Poles : polesRoundM 16 24 12 128 d2Delta97Lo d2Delta97Hi d2Delta97Fq.poles d2Delta97Qd = some (d2Delta97Aq,d2Delta97Eq) := by decide +kernel
theorem d2Delta97Laurent : laurentRoundM 16 30 128 d2Delta97Lo d2Delta97Hi d2Delta97Ts d2Delta97Ld = some (d2Delta97Al,d2Delta97El) := by decide +kernel
theorem d2Delta97Small : chebPolyUB (vecAdd d2Delta97S (vecAdd d2Delta97Ap (vecAdd d2Delta97Aq d2Delta97Al))) d2Delta97Gam+d2Delta97Es+d2Delta97Ep+d2Delta97Eq+d2Delta97El ≤ (d2LitsStandaloneDelta012.q2 (-461075373169024764301) 1 (-76)) := by decide +kernel
theorem d2Delta97Check : chebRoundPieceL d2Delta97Fq d2Delta97Ts 16 24 12 20 30 128 d2Delta97Lo d2Delta97Hi d2Delta97Pd d2Delta97Qd d2Delta97Ld d2Delta97Gam (d2LitsStandaloneDelta012.q2 (-461075373169024764301) 1 (-76)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta97Fq d2Delta97Ts 16 24 12 20 30 128 d2Delta97Lo d2Delta97Hi d2Delta97Pd d2Delta97Qd d2Delta97Ld d2Delta97Gam d2Delta97S d2Delta97Ap d2Delta97Aq d2Delta97Al d2Delta97Es d2Delta97Ep d2Delta97Eq d2Delta97El (by decide +kernel) d2Delta97Shift d2Delta97Plogs d2Delta97Poles d2Delta97Laurent]
  exact decide_eq_true d2Delta97Small
theorem d2Delta97Bound : ∀ x ∈ Icc ((d2Delta97Lo : ℚ) : ℝ) ((d2Delta97Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-461075373169024764301) 1 (-76)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta97Fq d2Delta97Ts 16 24 12 20 30 128 d2Delta97Lo d2Delta97Hi d2Delta97Pd d2Delta97Qd d2Delta97Ld d2Delta97Gam (d2LitsStandaloneDelta012.q2 (-461075373169024764301) 1 (-76)) d2Delta97Check
  simpa only [d2Delta97Fq, d2Delta97Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta97Shift
#print axioms d2Delta97Sites
#print axioms d2Delta97PData
#print axioms d2Delta97Plogs
#print axioms d2Delta97Poles
#print axioms d2Delta97Laurent
#print axioms d2Delta97Small
#print axioms d2Delta97Check
#print axioms d2Delta97Bound

def d2Delta98Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta98Ts : List LTerm := laurentClean []
def d2Delta98Lo : ℚ := (d2LitsStandaloneDelta012.q2 (32605153) 1 (-27))
def d2Delta98Hi : ℚ := (d2LitsStandaloneDelta012.q2 (17873903) 1 (-26))
def d2Delta98Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta98Qd : List (ℚ × ℚ) := []
def d2Delta98Ld : List LaurentPieceData := []
def d2Delta98Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-8918931565259249894372255692465428953957416827, 1, -160, -14207849150865449956539066406049534320169, 1, -156, 35175998595661377122515969131269286919433, 1, -159, 4863054135433371249402362388542301858945, 1, -158, -645583938411240172624407587435158672039, 1, -158, -256517127398544221239995796035818173899, 1, -159, 5104538229856044799437937407911618133, 1, -157, 3391322559055647447032801996389141265, 1, -159, -360127754981991173800805756474723621, 1, -160, -26905239633548858649566654335494591, 1, -159, 1006716406432023124912636214935231, 1, -159, 141492019756156782428775731587029, 1, -159, -964697322098571280047571344427, 1, -157, -1053293936722550436512909532235, 1, -160, 10674562343086026287419746447, 1, -159, 181749048176792877699613009, 1, -156, -22047512396167668078213775, 1, -159, -771051306561713217393457, 1, -157, 69418890531844825278651, 1, -160, 10331168235054258836435, 1, -160, -41953331414551111121, 1, -159, -13961767546373082515, 1, -160, 38436682588162547, 1, -159, 15493752375272217, 1, -160, -6272313374231, 1, -157, -7161293014105, 1, -159, 17064850709, 1, -160, 5484221853, 1, -159, -14692107, 1, -157, -55561531, 1, -159, -67395431, 1, -160, -54806947, 1, -160])
def d2Delta98S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-1038308783992036435252785547636090551, 1, -127, -67123997316168216079831068086889, 1, -128, 37744026452877572402100463695031, 1, -128, 20595243966328724159354212016765, 1, -128, -5279961284181785493709087168103, 1, -128, -2093567088761380126897383224211, 1, -128, 326251005398676399727076472183, 1, -128, 54236921359955749387535058401, 1, -127, -11345247772238964652295136725, 1, -128, -424627760790763443474879955, 1, -125, 125628903479218093553721337, 1, -127, 35398164236473328815189455, 1, -127, -1912376951978710958072025, 1, -127, -1046805058072508292187437, 1, -128, 10520975135157467854389, 1, -126, 2874785853071732453381, 1, -126, -173030530924515705695, 1, -127, -48579115583370704045, 1, -127, 1085100810878929537, 1, -127, 648678838928031445, 1, -128, -10450507358577755, 1, -128, -1748301757606087, 1, -127, 19063181308723, 1, -127, 967739625257, 1, -124, -6179806381, 1, -124, -57134092743, 1, -128, 33346723, 1, -126, 88864431, 1, -127, 124867, 1, -127, -470549, 1, -128, -1165, 1, -127, 267, 1, -126, 1, 1, -125, -3, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta98Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta98Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta98Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta98Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta98Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta98Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta98El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta98Shift : polyRoundApx 128 d2Delta98Lo d2Delta98Hi d2Delta98Fq.poly = (d2Delta98S,d2Delta98Es) := by decide +kernel
theorem d2Delta98Sites : mergeSites d2Delta98Fq.plogs = [] := by decide +kernel
theorem d2Delta98PData : d2Delta98Pd = [] := by decide +kernel
theorem d2Delta98Plogs : plogsRoundM 16 24 20 128 d2Delta98Lo d2Delta98Hi (mergeSites d2Delta98Fq.plogs) d2Delta98Pd = some (d2Delta98Ap,d2Delta98Ep) := by
  rw [d2Delta98Sites,d2Delta98PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta98Poles : polesRoundM 16 24 12 128 d2Delta98Lo d2Delta98Hi d2Delta98Fq.poles d2Delta98Qd = some (d2Delta98Aq,d2Delta98Eq) := by decide +kernel
theorem d2Delta98Laurent : laurentRoundM 16 30 128 d2Delta98Lo d2Delta98Hi d2Delta98Ts d2Delta98Ld = some (d2Delta98Al,d2Delta98El) := by decide +kernel
theorem d2Delta98Small : chebPolyUB (vecAdd d2Delta98S (vecAdd d2Delta98Ap (vecAdd d2Delta98Aq d2Delta98Al))) d2Delta98Gam+d2Delta98Es+d2Delta98Ep+d2Delta98Eq+d2Delta98El ≤ (d2LitsStandaloneDelta012.q2 (-3688651175841747362693) 1 (-79)) := by decide +kernel
theorem d2Delta98Check : chebRoundPieceL d2Delta98Fq d2Delta98Ts 16 24 12 20 30 128 d2Delta98Lo d2Delta98Hi d2Delta98Pd d2Delta98Qd d2Delta98Ld d2Delta98Gam (d2LitsStandaloneDelta012.q2 (-3688651175841747362693) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta98Fq d2Delta98Ts 16 24 12 20 30 128 d2Delta98Lo d2Delta98Hi d2Delta98Pd d2Delta98Qd d2Delta98Ld d2Delta98Gam d2Delta98S d2Delta98Ap d2Delta98Aq d2Delta98Al d2Delta98Es d2Delta98Ep d2Delta98Eq d2Delta98El (by decide +kernel) d2Delta98Shift d2Delta98Plogs d2Delta98Poles d2Delta98Laurent]
  exact decide_eq_true d2Delta98Small
theorem d2Delta98Bound : ∀ x ∈ Icc ((d2Delta98Lo : ℚ) : ℝ) ((d2Delta98Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-3688651175841747362693) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta98Fq d2Delta98Ts 16 24 12 20 30 128 d2Delta98Lo d2Delta98Hi d2Delta98Pd d2Delta98Qd d2Delta98Ld d2Delta98Gam (d2LitsStandaloneDelta012.q2 (-3688651175841747362693) 1 (-79)) d2Delta98Check
  simpa only [d2Delta98Fq, d2Delta98Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta98Shift
#print axioms d2Delta98Sites
#print axioms d2Delta98PData
#print axioms d2Delta98Plogs
#print axioms d2Delta98Poles
#print axioms d2Delta98Laurent
#print axioms d2Delta98Small
#print axioms d2Delta98Check
#print axioms d2Delta98Bound

def d2Delta99Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta99Ts : List LTerm := laurentClean []
def d2Delta99Lo : ℚ := (d2LitsStandaloneDelta012.q2 (17873903) 1 (-26))
def d2Delta99Hi : ℚ := (d2LitsStandaloneDelta012.q2 (9460727) 1 (-25))
def d2Delta99Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta99Qd : List (ℚ × ℚ) := []
def d2Delta99Ld : List LaurentPieceData := []
def d2Delta99Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-8918861586370707909032664780674927968011595831, 1, -160, 114813915319117524579156418184755173534611, 1, -159, 11516925340476847489829471111015121249469, 1, -160, -1947824695015564419890446389447785381969, 1, -158, -35551163030626768890065174406394299435, 1, -158, 2753456048203780267870720510401331659, 1, -155, 502262053735027526338305542283860879, 1, -159, -499884105594635273329920255551366433, 1, -160, -1224209003275184254571109518907201, 1, -158, 212365350748038326388791105196293, 1, -157, 16293881577063174484431124119543, 1, -160, -1915489580058652924759787353893, 1, -159, -37529592015188845326543399159, 1, -160, 6125429044086076066871543601, 1, -160, 31043313535636854449003809, 1, -159, -7275297531364100910936729, 1, -160, -38331003201995027434749, 1, -159, 6642104993165594370357, 1, -160, 73018015096467531495, 1, -160, -4784089551807235615, 1, -160, -27552244869729693, 1, -159, 2774010184994317, 1, -160, 16833333299237, 1, -159, -1316081085417, 1, -160, -2169918639, 1, -157, 213528175, 1, -160, -115038561, 1, -159, -10650091, 1, -156, -131455561, 1, -160, -23121171, 1, -158, -35254751, 1, -159, -48570641, 1, -160])
def d2Delta99S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-259573374831529153258997201937477595, 1, -125, 59009947457210941688824331486641, 1, -128, 2816054835918235544925074211753, 1, -127, -3836537387315023081804649643979, 1, -127, -276287183416020520377141504775, 1, -128, 85361254681295918072321713023, 1, -126, 3890221204792896050744716369, 1, -127, -959902876577933161373303075, 1, -125, -37713457016342527971630343, 1, -126, 103799327407101970588869941, 1, -128, 998320843622170560872467, 1, -127, -932518829957549780843133, 1, -128, -18313797777329290094881, 1, -128, 2973247579164642917253, 1, -127, 120779267912925438365, 1, -128, -14093290605355762841, 1, -127, -148745987534143023, 1, -126, 102745494248946611, 1, -128, 565545403807419, 1, -126, -9236616643785, 1, -123, -6817560433771, 1, -128, 342335371343, 1, -127, 16638759521, 1, -128, -648695771, 1, -127, -33458711, 1, -128, 2035925, 1, -128, 28109, 1, -127, -2671, 1, -128, -5, 1, -124, 1, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta99Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta99Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta99Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta99Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta99Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta99Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta99El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta99Shift : polyRoundApx 128 d2Delta99Lo d2Delta99Hi d2Delta99Fq.poly = (d2Delta99S,d2Delta99Es) := by decide +kernel
theorem d2Delta99Sites : mergeSites d2Delta99Fq.plogs = [] := by decide +kernel
theorem d2Delta99PData : d2Delta99Pd = [] := by decide +kernel
theorem d2Delta99Plogs : plogsRoundM 16 24 20 128 d2Delta99Lo d2Delta99Hi (mergeSites d2Delta99Fq.plogs) d2Delta99Pd = some (d2Delta99Ap,d2Delta99Ep) := by
  rw [d2Delta99Sites,d2Delta99PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta99Poles : polesRoundM 16 24 12 128 d2Delta99Lo d2Delta99Hi d2Delta99Fq.poles d2Delta99Qd = some (d2Delta99Aq,d2Delta99Eq) := by decide +kernel
theorem d2Delta99Laurent : laurentRoundM 16 30 128 d2Delta99Lo d2Delta99Hi d2Delta99Ts d2Delta99Ld = some (d2Delta99Al,d2Delta99El) := by decide +kernel
theorem d2Delta99Small : chebPolyUB (vecAdd d2Delta99S (vecAdd d2Delta99Ap (vecAdd d2Delta99Aq d2Delta99Al))) d2Delta99Gam+d2Delta99Es+d2Delta99Ep+d2Delta99Eq+d2Delta99El ≤ (d2LitsStandaloneDelta012.q2 (-3688651641724666276119) 1 (-79)) := by decide +kernel
theorem d2Delta99Check : chebRoundPieceL d2Delta99Fq d2Delta99Ts 16 24 12 20 30 128 d2Delta99Lo d2Delta99Hi d2Delta99Pd d2Delta99Qd d2Delta99Ld d2Delta99Gam (d2LitsStandaloneDelta012.q2 (-3688651641724666276119) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta99Fq d2Delta99Ts 16 24 12 20 30 128 d2Delta99Lo d2Delta99Hi d2Delta99Pd d2Delta99Qd d2Delta99Ld d2Delta99Gam d2Delta99S d2Delta99Ap d2Delta99Aq d2Delta99Al d2Delta99Es d2Delta99Ep d2Delta99Eq d2Delta99El (by decide +kernel) d2Delta99Shift d2Delta99Plogs d2Delta99Poles d2Delta99Laurent]
  exact decide_eq_true d2Delta99Small
theorem d2Delta99Bound : ∀ x ∈ Icc ((d2Delta99Lo : ℚ) : ℝ) ((d2Delta99Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-3688651641724666276119) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta99Fq d2Delta99Ts 16 24 12 20 30 128 d2Delta99Lo d2Delta99Hi d2Delta99Pd d2Delta99Qd d2Delta99Ld d2Delta99Gam (d2LitsStandaloneDelta012.q2 (-3688651641724666276119) 1 (-79)) d2Delta99Check
  simpa only [d2Delta99Fq, d2Delta99Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta99Shift
#print axioms d2Delta99Sites
#print axioms d2Delta99PData
#print axioms d2Delta99Plogs
#print axioms d2Delta99Poles
#print axioms d2Delta99Laurent
#print axioms d2Delta99Small
#print axioms d2Delta99Check
#print axioms d2Delta99Bound

def d2Delta100Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta100Ts : List LTerm := laurentClean []
def d2Delta100Lo : ℚ := (d2LitsStandaloneDelta012.q2 (9460727) 1 (-25))
def d2Delta100Hi : ℚ := (d2LitsStandaloneDelta012.q2 (40985561) 1 (-27))
def d2Delta100Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta100Qd : List (ℚ × ℚ) := []
def d2Delta100Ld : List LaurentPieceData := []
def d2Delta100Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-1114824900329154851428146207982920123808016693, 1, -157, -58068923843659576686316365819119258823979, 1, -160, -78162735998760217918790532366234408167501, 1, -160, 3132939888458605993087209714579167455477, 1, -158, 3189154581310076930003526735091476632317, 1, -160, -414718156271597962438133043666534763537, 1, -160, -14247043200464774064309638465291869863, 1, -158, 5801240282832790070436450206424736257, 1, -160, 286907831282163164055793456754361309, 1, -159, -45610626780788373586638498353812213, 1, -160, -925738177404190953075686643018533, 1, -158, 230727288597994441602875485131165, 1, -160, 16564859040589438612242636179553, 1, -160, -812271283074832746379450771459, 1, -160, -54173170530126025283552786733, 1, -160, 1046818406970095821704179413, 1, -159, 134625356960008686082558117, 1, -160, -2044931381572572068717655, 1, -159, -261812450984096442453535, 1, -160, 6199679577075656351727, 1, -160, 203870368853032306783, 1, -159, -7400470355761601243, 1, -160, -517964044650803181, 1, -160, 6993579091244967, 1, -160, 544737378488775, 1, -160, -5188719893191, 1, -160, -480221217385, 1, -160, 2744520313, 1, -160, 128918041, 1, -159, -22453023, 1, -158, -53231949, 1, -160, -23297353, 1, -159])
def d2Delta100S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-2076504238223878365203315118189654049, 1, -128, -711434513597726403511086573497, 1, -123, -42580776895691675708234142857319, 1, -128, 6839609137814026978776786817319, 1, -127, 1649720048988943637242277857635, 1, -126, -425219759161981764900185322029, 1, -126, -114944153892187711425341716977, 1, -126, 92715257191946150638005545659, 1, -128, 18231605223880309179062270187, 1, -128, -718265834149840375304301269, 1, -126, -232812766966297824487779041, 1, -127, 57572617786491730250239787, 1, -128, 2066782515824417119568101, 1, -126, -201265018838358577150861, 1, -126, -107503603096332662109333, 1, -128, 1031929927049533356089, 1, -125, 1063597727493463193463, 1, -128, -64225228418750084817, 1, -128, -4121038091879107053, 1, -127, 48497826292955393, 1, -125, 12795232729075175, 1, -126, -1846376010882277, 1, -128, -259366311682077, 1, -128, 6957261317471, 1, -128, 544281943987, 1, -127, -5143892899, 1, -126, -3829317327, 1, -128, 22960265, 1, -127, 11400123, 1, -128, -66641, 1, -128, -1809, 1, -124, 7, 1, -128, 63, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta100Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta100Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta100Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta100Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta100Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta100Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta100El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta100Shift : polyRoundApx 128 d2Delta100Lo d2Delta100Hi d2Delta100Fq.poly = (d2Delta100S,d2Delta100Es) := by decide +kernel
theorem d2Delta100Sites : mergeSites d2Delta100Fq.plogs = [] := by decide +kernel
theorem d2Delta100PData : d2Delta100Pd = [] := by decide +kernel
theorem d2Delta100Plogs : plogsRoundM 16 24 20 128 d2Delta100Lo d2Delta100Hi (mergeSites d2Delta100Fq.plogs) d2Delta100Pd = some (d2Delta100Ap,d2Delta100Ep) := by
  rw [d2Delta100Sites,d2Delta100PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta100Poles : polesRoundM 16 24 12 128 d2Delta100Lo d2Delta100Hi d2Delta100Fq.poles d2Delta100Qd = some (d2Delta100Aq,d2Delta100Eq) := by decide +kernel
theorem d2Delta100Laurent : laurentRoundM 16 30 128 d2Delta100Lo d2Delta100Hi d2Delta100Ts d2Delta100Ld = some (d2Delta100Al,d2Delta100El) := by decide +kernel
theorem d2Delta100Small : chebPolyUB (vecAdd d2Delta100S (vecAdd d2Delta100Ap (vecAdd d2Delta100Aq d2Delta100Al))) d2Delta100Gam+d2Delta100Es+d2Delta100Ep+d2Delta100Eq+d2Delta100El ≤ (d2LitsStandaloneDelta012.q2 (-7377166263825235480023) 1 (-80)) := by decide +kernel
theorem d2Delta100Check : chebRoundPieceL d2Delta100Fq d2Delta100Ts 16 24 12 20 30 128 d2Delta100Lo d2Delta100Hi d2Delta100Pd d2Delta100Qd d2Delta100Ld d2Delta100Gam (d2LitsStandaloneDelta012.q2 (-7377166263825235480023) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta100Fq d2Delta100Ts 16 24 12 20 30 128 d2Delta100Lo d2Delta100Hi d2Delta100Pd d2Delta100Qd d2Delta100Ld d2Delta100Gam d2Delta100S d2Delta100Ap d2Delta100Aq d2Delta100Al d2Delta100Es d2Delta100Ep d2Delta100Eq d2Delta100El (by decide +kernel) d2Delta100Shift d2Delta100Plogs d2Delta100Poles d2Delta100Laurent]
  exact decide_eq_true d2Delta100Small
theorem d2Delta100Bound : ∀ x ∈ Icc ((d2Delta100Lo : ℚ) : ℝ) ((d2Delta100Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-7377166263825235480023) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta100Fq d2Delta100Ts 16 24 12 20 30 128 d2Delta100Lo d2Delta100Hi d2Delta100Pd d2Delta100Qd d2Delta100Ld d2Delta100Gam (d2LitsStandaloneDelta012.q2 (-7377166263825235480023) 1 (-80)) d2Delta100Check
  simpa only [d2Delta100Fq, d2Delta100Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta100Shift
#print axioms d2Delta100Sites
#print axioms d2Delta100PData
#print axioms d2Delta100Plogs
#print axioms d2Delta100Poles
#print axioms d2Delta100Laurent
#print axioms d2Delta100Small
#print axioms d2Delta100Check
#print axioms d2Delta100Bound

def d2Delta101Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta101Ts : List LTerm := laurentClean []
def d2Delta101Lo : ℚ := (d2LitsStandaloneDelta012.q2 (40985561) 1 (-27))
def d2Delta101Hi : ℚ := (d2LitsStandaloneDelta012.q2 (5254139) 1 (-24))
def d2Delta101Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta101Qd : List (ℚ × ℚ) := []
def d2Delta101Ld : List LaurentPieceData := []
def d2Delta101Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-8918775611663749949605787823864634885610391459, 1, -160, -48760063840293161294440046372963393410735, 1, -160, 3550309434479995474755360855901010905997, 1, -159, 381985126235434390342933554037844972639, 1, -160, -23467869610275018116719987695115751817, 1, -159, -1039485555797907171121365922026499237, 1, -160, 104733887879702990684381783495826015, 1, -160, 1480630187759446218456406998254729, 1, -160, -120435746541283908846156649239927, 1, -160, -1324049674629315750783125444887, 1, -160, 85157988082196284767399227499, 1, -160, 407345506096144883845286979, 1, -159, -1275196555727440663992451, 1, -155, -363862464937689486338689, 1, -160, 14093302978032170147019, 1, -160, 122387038145040681507, 1, -160, -3659861324764073071, 1, -160, -3986702736946543, 1, -157, 11511919749647, 1, -154, 1646986445657, 1, -158, -118774454699, 1, -160, -1713657587, 1, -160, -703195097, 1, -160, -358371963, 1, -160, -211089009, 1, -159, -203066045, 1, -160, -240458221, 1, -160, -111453015, 1, -160, -66310771, 1, -159, -59231967, 1, -160, -17693601, 1, -158, -7614861, 1, -158])
def d2Delta101S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-519141482615564748352150567316141045, 1, -126, -5810431556673159557661778768867, 1, -127, 1697173891574021545517357172615, 1, -127, 180305597653325615274091288959, 1, -127, -88599613914165474307307372125, 1, -128, -3911129307936562145805107787, 1, -128, 787529043525952742070572353, 1, -128, 22241212994654491835557097, 1, -128, -225919360152938619238361, 1, -124, -19863768823592749585249, 1, -126, 5105063321181822017069, 1, -127, 195367873472760141257, 1, -128, -19552219893021236689, 1, -128, -87190167960073209, 1, -126, 26992722161400621, 1, -128, 58617702609245, 1, -125, -28023857838903, 1, -128, -244285725855, 1, -127, 11278071713, 1, -127, 403570319, 1, -128, -14394805, 1, -128, -67337, 1, -126, 1851, 1, -126, 147, 1, -128, -1, 1, -126, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta101Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta101Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta101Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta101Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta101Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta101Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta101El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta101Shift : polyRoundApx 128 d2Delta101Lo d2Delta101Hi d2Delta101Fq.poly = (d2Delta101S,d2Delta101Es) := by decide +kernel
theorem d2Delta101Sites : mergeSites d2Delta101Fq.plogs = [] := by decide +kernel
theorem d2Delta101PData : d2Delta101Pd = [] := by decide +kernel
theorem d2Delta101Plogs : plogsRoundM 16 24 20 128 d2Delta101Lo d2Delta101Hi (mergeSites d2Delta101Fq.plogs) d2Delta101Pd = some (d2Delta101Ap,d2Delta101Ep) := by
  rw [d2Delta101Sites,d2Delta101PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta101Poles : polesRoundM 16 24 12 128 d2Delta101Lo d2Delta101Hi d2Delta101Fq.poles d2Delta101Qd = some (d2Delta101Aq,d2Delta101Eq) := by decide +kernel
theorem d2Delta101Laurent : laurentRoundM 16 30 128 d2Delta101Lo d2Delta101Hi d2Delta101Ts d2Delta101Ld = some (d2Delta101Al,d2Delta101El) := by decide +kernel
theorem d2Delta101Small : chebPolyUB (vecAdd d2Delta101S (vecAdd d2Delta101Ap (vecAdd d2Delta101Aq d2Delta101Al))) d2Delta101Gam+d2Delta101Es+d2Delta101Ep+d2Delta101Eq+d2Delta101El ≤ (d2LitsStandaloneDelta012.q2 (-3688695855531228894177) 1 (-79)) := by decide +kernel
theorem d2Delta101Check : chebRoundPieceL d2Delta101Fq d2Delta101Ts 16 24 12 20 30 128 d2Delta101Lo d2Delta101Hi d2Delta101Pd d2Delta101Qd d2Delta101Ld d2Delta101Gam (d2LitsStandaloneDelta012.q2 (-3688695855531228894177) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta101Fq d2Delta101Ts 16 24 12 20 30 128 d2Delta101Lo d2Delta101Hi d2Delta101Pd d2Delta101Qd d2Delta101Ld d2Delta101Gam d2Delta101S d2Delta101Ap d2Delta101Aq d2Delta101Al d2Delta101Es d2Delta101Ep d2Delta101Eq d2Delta101El (by decide +kernel) d2Delta101Shift d2Delta101Plogs d2Delta101Poles d2Delta101Laurent]
  exact decide_eq_true d2Delta101Small
theorem d2Delta101Bound : ∀ x ∈ Icc ((d2Delta101Lo : ℚ) : ℝ) ((d2Delta101Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-3688695855531228894177) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta101Fq d2Delta101Ts 16 24 12 20 30 128 d2Delta101Lo d2Delta101Hi d2Delta101Pd d2Delta101Qd d2Delta101Ld d2Delta101Gam (d2LitsStandaloneDelta012.q2 (-3688695855531228894177) 1 (-79)) d2Delta101Check
  simpa only [d2Delta101Fq, d2Delta101Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta101Shift
#print axioms d2Delta101Sites
#print axioms d2Delta101PData
#print axioms d2Delta101Plogs
#print axioms d2Delta101Poles
#print axioms d2Delta101Laurent
#print axioms d2Delta101Small
#print axioms d2Delta101Check
#print axioms d2Delta101Bound

def d2Delta102Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta102Ts : List LTerm := laurentClean []
def d2Delta102Lo : ℚ := (d2LitsStandaloneDelta012.q2 (5254139) 1 (-24))
def d2Delta102Hi : ℚ := (d2LitsStandaloneDelta012.q2 (22064107) 1 (-26))
def d2Delta102Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta102Qd : List (ℚ × ℚ) := []
def d2Delta102Ld : List LaurentPieceData := []
def d2Delta102Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-4459388717951732831085565166166055852336193973, 1, -159, 29028887714977751661922002737084470512133, 1, -159, 14028344683464919722742502605591956981727, 1, -160, -616801904731952922721652277956578426115, 1, -157, -168344488258384858774797553382186765611, 1, -159, 36346511368884051010589398773509940959, 1, -159, 2857958039642853908481832132861438085, 1, -160, -465142026899306797509885155306418437, 1, -160, -13211336616621828682843528640589637, 1, -160, 1685413635829399206848092483578233, 1, -160, 19701697582505253563944302981955, 1, -159, -3941305439446574950254885267537, 1, -160, -20627694399199348398841988261, 1, -158, 6432398636288432166742511549, 1, -160, 63778561433701258300226201, 1, -159, -7715883123645873212686075, 1, -160, -75352236359426962640547, 1, -159, 440865139992946609769, 1, -156, 69839237683021784729, 1, -159, -5044845919088574313, 1, -160, -51847220213142723, 1, -159, 2876237127024549, 1, -160, 15678902363069, 1, -158, -82788983481, 1, -156, -31700979571, 1, -160, 42933013, 1, -158, -191966389, 1, -160, -45319491, 1, -158, -7016101, 1, -156, -48937239, 1, -159, -59402001, 1, -160, -1595405, 1, -155])
def d2Delta102S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-1038284018147775729437556226740285653, 1, -127, 17049665903570206944338778104365, 1, -128, 7171665589016013453507153157491, 1, -128, -1235036905782380648549725791777, 1, -126, -164892026384082196308332807993, 1, -126, 35387849318034797520105248977, 1, -125, 2761406013944145426249072423, 1, -125, -894973378619866044432024247, 1, -125, -6337581685265650715268695, 1, -122, 103067650202011990443048751, 1, -128, 2408230282234510460136235, 1, -127, -239945899113224326626293, 1, -126, -40203250447730635629917, 1, -128, 3122796847182681904049, 1, -127, 3873924440611897703, 1, -122, -29894134531800160193, 1, -128, -292275207291240783, 1, -126, 6818999920559767, 1, -124, 2163170159846367, 1, -127, -311618183617293, 1, -128, -6413703616127, 1, -127, 354837420881, 1, -127, 1937020347, 1, -124, -1305177037, 1, -128, -61876165, 1, -128, 1951611, 1, -128, 103263, 1, -128, -2371, 1, -128, -73, 1, -127, 1, 1, -127, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta102Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta102Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta102Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta102Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta102Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta102Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta102El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta102Shift : polyRoundApx 128 d2Delta102Lo d2Delta102Hi d2Delta102Fq.poly = (d2Delta102S,d2Delta102Es) := by decide +kernel
theorem d2Delta102Sites : mergeSites d2Delta102Fq.plogs = [] := by decide +kernel
theorem d2Delta102PData : d2Delta102Pd = [] := by decide +kernel
theorem d2Delta102Plogs : plogsRoundM 16 24 20 128 d2Delta102Lo d2Delta102Hi (mergeSites d2Delta102Fq.plogs) d2Delta102Pd = some (d2Delta102Ap,d2Delta102Ep) := by
  rw [d2Delta102Sites,d2Delta102PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta102Poles : polesRoundM 16 24 12 128 d2Delta102Lo d2Delta102Hi d2Delta102Fq.poles d2Delta102Qd = some (d2Delta102Aq,d2Delta102Eq) := by decide +kernel
theorem d2Delta102Laurent : laurentRoundM 16 30 128 d2Delta102Lo d2Delta102Hi d2Delta102Ts d2Delta102Ld = some (d2Delta102Al,d2Delta102El) := by decide +kernel
theorem d2Delta102Small : chebPolyUB (vecAdd d2Delta102S (vecAdd d2Delta102Ap (vecAdd d2Delta102Aq d2Delta102Al))) d2Delta102Gam+d2Delta102Es+d2Delta102Ep+d2Delta102Eq+d2Delta102El ≤ (d2LitsStandaloneDelta012.q2 (-3688687865683562063019) 1 (-79)) := by decide +kernel
theorem d2Delta102Check : chebRoundPieceL d2Delta102Fq d2Delta102Ts 16 24 12 20 30 128 d2Delta102Lo d2Delta102Hi d2Delta102Pd d2Delta102Qd d2Delta102Ld d2Delta102Gam (d2LitsStandaloneDelta012.q2 (-3688687865683562063019) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta102Fq d2Delta102Ts 16 24 12 20 30 128 d2Delta102Lo d2Delta102Hi d2Delta102Pd d2Delta102Qd d2Delta102Ld d2Delta102Gam d2Delta102S d2Delta102Ap d2Delta102Aq d2Delta102Al d2Delta102Es d2Delta102Ep d2Delta102Eq d2Delta102El (by decide +kernel) d2Delta102Shift d2Delta102Plogs d2Delta102Poles d2Delta102Laurent]
  exact decide_eq_true d2Delta102Small
theorem d2Delta102Bound : ∀ x ∈ Icc ((d2Delta102Lo : ℚ) : ℝ) ((d2Delta102Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-3688687865683562063019) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta102Fq d2Delta102Ts 16 24 12 20 30 128 d2Delta102Lo d2Delta102Hi d2Delta102Pd d2Delta102Qd d2Delta102Ld d2Delta102Gam (d2LitsStandaloneDelta012.q2 (-3688687865683562063019) 1 (-79)) d2Delta102Check
  simpa only [d2Delta102Fq, d2Delta102Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta102Shift
#print axioms d2Delta102Sites
#print axioms d2Delta102PData
#print axioms d2Delta102Plogs
#print axioms d2Delta102Poles
#print axioms d2Delta102Laurent
#print axioms d2Delta102Small
#print axioms d2Delta102Check
#print axioms d2Delta102Bound

def d2Delta103Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta103Ts : List LTerm := laurentClean []
def d2Delta103Lo : ℚ := (d2LitsStandaloneDelta012.q2 (22064107) 1 (-26))
def d2Delta103Hi : ℚ := (d2LitsStandaloneDelta012.q2 (11555829) 1 (-25))
def d2Delta103Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta103Qd : List (ℚ × ℚ) := []
def d2Delta103Ld : List LaurentPieceData := []
def d2Delta103Gam : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-8918727102852319751793713102424221910875263687, 1, -160, -23144450560560326526126920187684677700285, 1, -159, -936785883365898120666442445399698431421, 1, -155, 502585687957986372041547522940588889871, 1, -160, 749983216224692313342958887754070460691, 1, -160, -2381341365855732803853867249339489359, 1, -159, -6876116983847715451011409205016564321, 1, -160, 30726566474490386314286254963155879, 1, -160, 32882606955502479014108846374820763, 1, -160, -94619014271402307173453148743615, 1, -160, -48406753632480801493694564558559, 1, -159, 57004093394952556905395520373, 1, -159, 193235011496460924230102272499, 1, -160, 105946782215776145213386425, 1, -160, -278271861831372388469358817, 1, -160, -311825947190008518102557, 1, -159, 301855408078801634393773, 1, -160, 1172583441704971959353, 1, -160, -254456721184928399989, 1, -160, -698447449114424921, 1, -159, 170601935571023313, 1, -160, 604452197592359, 1, -159, -46285187536225, 1, -159, -807623590859, 1, -160, 40781751763, 1, -160, 21509539, 1, -157, -29745391, 1, -157, -71367559, 1, -159, -121713677, 1, -160, -38069465, 1, -159, -64291901, 1, -160, -19680691, 1, -159])
def d2Delta103S : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [-2076545816103867073668509273173004569, 1, -128, -1391765182414159724242148127107, 1, -125, -15385213650055799303547437438739, 1, -128, 245325322439119346882230995107, 1, -127, 737516611150066327975511100327, 1, -127, -9276591557133412433320154229, 1, -127, -53216427837181269253392736695, 1, -128, 470625417731571741496874757, 1, -128, 1009143452511508240939023357, 1, -128, -5714061569023544666348381, 1, -128, -11820061316198552158429179, 1, -128, 26839787780415802875015, 1, -128, 94014334605585014167397, 1, -128, 13761762447259359717, 1, -125, -540039132778851638081, 1, -128, -2455899412485834369, 1, -128, 292267547123262489, 1, -125, 4575172382731865, 1, -126, -7870122366433365, 1, -128, -43410287777237, 1, -127, 5268825589141, 1, -126, 299704320345, 1, -128, -45684801989, 1, -128, -199705645, 1, -126, 40597611, 1, -127, 212721, 1, -125, -59681, 1, -127, -2965, 1, -128, 145, 1, -128, 1, 1, -126, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta103Ap : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta103Aq : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta103Al : List ℚ := d2LitsStandaloneDelta012.q2listC (raw_ints% [])
def d2Delta103Es : ℚ := (d2LitsStandaloneDelta012.q2 (61) 1 (-127))
def d2Delta103Ep : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta103Eq : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
def d2Delta103El : ℚ := (d2LitsStandaloneDelta012.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta103Shift : polyRoundApx 128 d2Delta103Lo d2Delta103Hi d2Delta103Fq.poly = (d2Delta103S,d2Delta103Es) := by decide +kernel
theorem d2Delta103Sites : mergeSites d2Delta103Fq.plogs = [] := by decide +kernel
theorem d2Delta103PData : d2Delta103Pd = [] := by decide +kernel
theorem d2Delta103Plogs : plogsRoundM 16 24 20 128 d2Delta103Lo d2Delta103Hi (mergeSites d2Delta103Fq.plogs) d2Delta103Pd = some (d2Delta103Ap,d2Delta103Ep) := by
  rw [d2Delta103Sites,d2Delta103PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta103Poles : polesRoundM 16 24 12 128 d2Delta103Lo d2Delta103Hi d2Delta103Fq.poles d2Delta103Qd = some (d2Delta103Aq,d2Delta103Eq) := by decide +kernel
theorem d2Delta103Laurent : laurentRoundM 16 30 128 d2Delta103Lo d2Delta103Hi d2Delta103Ts d2Delta103Ld = some (d2Delta103Al,d2Delta103El) := by decide +kernel
theorem d2Delta103Small : chebPolyUB (vecAdd d2Delta103S (vecAdd d2Delta103Ap (vecAdd d2Delta103Aq d2Delta103Al))) d2Delta103Gam+d2Delta103Es+d2Delta103Ep+d2Delta103Eq+d2Delta103El ≤ (d2LitsStandaloneDelta012.q2 (-3688667008276171737737) 1 (-79)) := by decide +kernel
theorem d2Delta103Check : chebRoundPieceL d2Delta103Fq d2Delta103Ts 16 24 12 20 30 128 d2Delta103Lo d2Delta103Hi d2Delta103Pd d2Delta103Qd d2Delta103Ld d2Delta103Gam (d2LitsStandaloneDelta012.q2 (-3688667008276171737737) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta103Fq d2Delta103Ts 16 24 12 20 30 128 d2Delta103Lo d2Delta103Hi d2Delta103Pd d2Delta103Qd d2Delta103Ld d2Delta103Gam d2Delta103S d2Delta103Ap d2Delta103Aq d2Delta103Al d2Delta103Es d2Delta103Ep d2Delta103Eq d2Delta103El (by decide +kernel) d2Delta103Shift d2Delta103Plogs d2Delta103Poles d2Delta103Laurent]
  exact decide_eq_true d2Delta103Small
theorem d2Delta103Bound : ∀ x ∈ Icc ((d2Delta103Lo : ℚ) : ℝ) ((d2Delta103Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta012.q2 (-3688667008276171737737) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta103Fq d2Delta103Ts 16 24 12 20 30 128 d2Delta103Lo d2Delta103Hi d2Delta103Pd d2Delta103Qd d2Delta103Ld d2Delta103Gam (d2LitsStandaloneDelta012.q2 (-3688667008276171737737) 1 (-79)) d2Delta103Check
  simpa only [d2Delta103Fq, d2Delta103Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta103Shift
#print axioms d2Delta103Sites
#print axioms d2Delta103PData
#print axioms d2Delta103Plogs
#print axioms d2Delta103Poles
#print axioms d2Delta103Laurent
#print axioms d2Delta103Small
#print axioms d2Delta103Check
#print axioms d2Delta103Bound

end StandaloneDelta012
end CatalanMeasure.GenD.Signed.Data.Cells
