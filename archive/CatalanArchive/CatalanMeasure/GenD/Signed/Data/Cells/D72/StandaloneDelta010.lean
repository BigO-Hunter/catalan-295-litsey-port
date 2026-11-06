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
namespace d2LitsStandaloneDelta010
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta010
namespace StandaloneDelta010
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta010.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta010.q2listC (raw_ints% []))⟩
def d2Delta80Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta80Ts : List LTerm := laurentClean []
def d2Delta80Lo : ℚ := (d2LitsStandaloneDelta010.q2 (32736225) 1 (-28))
def d2Delta80Hi : ℚ := (d2LitsStandaloneDelta010.q2 (1055743) 1 (-23))
def d2Delta80Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta80Qd : List (ℚ × ℚ) := []
def d2Delta80Ld : List LaurentPieceData := []
def d2Delta80Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-8918803534301907634948297663368119262754916183, 1, -160, -949621175960072048592002358156681047229, 1, -160, 361948233562320035885186849448149097031, 1, -159, -2187107216930366429444062805159326753, 1, -160, -319206012512391167823139109216696925, 1, -158, 5599661742964206941982580078955055, 1, -160, 430907039726860156560692822168013, 1, -159, -4242488351698201112421450979447, 1, -160, -295362323046934618848421884487, 1, -160, 776711810135066042135107199, 1, -159, 14824042785288791795872631, 1, -158, -165192579866239233034027, 1, -159, -3809507950881961086795, 1, -159, 44897313076303220759, 1, -160, 333895794544066959, 1, -159, -4153162680313729, 1, -160, -42061486003847, 1, -160, 68208931325, 1, -158, -43174191, 1, -160, -1604750013, 1, -160, -1293577297, 1, -160, -995988127, 1, -160, -799514551, 1, -160, -151504959, 1, -158, -239893783, 1, -159, -358235675, 1, -160, -279326299, 1, -160, -205632107, 1, -160, -157653393, 1, -160, -57281337, 1, -159, -86203407, 1, -160, -61916445, 1, -160])
def d2Delta80S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-1038285468178342669170700789325289127, 1, -127, -219566707100990046509224188463, 1, -128, 84868111226106209364386943779, 1, -126, -2063033140360373181380133213, 1, -128, -1193956327380944617551183271, 1, -127, 20971153413175314008473635, 1, -128, 6438635693919747102965545, 1, -128, -31713274927686978885419, 1, -127, -8820167074366476006733, 1, -128, 92808054476673349625, 1, -128, 1769889913998129659, 1, -126, -78909206082474839, 1, -128, -3637489966977731, 1, -128, 42876857029587, 1, -128, 1274995415663, 1, -128, -1982613207, 1, -125, -160576679, 1, -127, 4204827, 1, -128, 60777, 1, -128, -209, 1, -126, -9, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta80Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta80Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta80Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta80Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta80Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta80Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta80El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta80Shift : polyRoundApx 128 d2Delta80Lo d2Delta80Hi d2Delta80Fq.poly = (d2Delta80S,d2Delta80Es) := by decide +kernel
theorem d2Delta80Sites : mergeSites d2Delta80Fq.plogs = [] := by decide +kernel
theorem d2Delta80PData : d2Delta80Pd = [] := by decide +kernel
theorem d2Delta80Plogs : plogsRoundM 16 24 20 128 d2Delta80Lo d2Delta80Hi (mergeSites d2Delta80Fq.plogs) d2Delta80Pd = some (d2Delta80Ap,d2Delta80Ep) := by
  rw [d2Delta80Sites,d2Delta80PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta80Poles : polesRoundM 16 24 12 128 d2Delta80Lo d2Delta80Hi d2Delta80Fq.poles d2Delta80Qd = some (d2Delta80Aq,d2Delta80Eq) := by decide +kernel
theorem d2Delta80Laurent : laurentRoundM 16 30 128 d2Delta80Lo d2Delta80Hi d2Delta80Ts d2Delta80Ld = some (d2Delta80Al,d2Delta80El) := by decide +kernel
theorem d2Delta80Small : chebPolyUB (vecAdd d2Delta80S (vecAdd d2Delta80Ap (vecAdd d2Delta80Aq d2Delta80Al))) d2Delta80Gam+d2Delta80Es+d2Delta80Ep+d2Delta80Eq+d2Delta80El ≤ (d2LitsStandaloneDelta010.q2 (-7377459983571965656595) 1 (-80)) := by decide +kernel
theorem d2Delta80Check : chebRoundPieceL d2Delta80Fq d2Delta80Ts 16 24 12 20 30 128 d2Delta80Lo d2Delta80Hi d2Delta80Pd d2Delta80Qd d2Delta80Ld d2Delta80Gam (d2LitsStandaloneDelta010.q2 (-7377459983571965656595) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta80Fq d2Delta80Ts 16 24 12 20 30 128 d2Delta80Lo d2Delta80Hi d2Delta80Pd d2Delta80Qd d2Delta80Ld d2Delta80Gam d2Delta80S d2Delta80Ap d2Delta80Aq d2Delta80Al d2Delta80Es d2Delta80Ep d2Delta80Eq d2Delta80El (by decide +kernel) d2Delta80Shift d2Delta80Plogs d2Delta80Poles d2Delta80Laurent]
  exact decide_eq_true d2Delta80Small
theorem d2Delta80Bound : ∀ x ∈ Icc ((d2Delta80Lo : ℚ) : ℝ) ((d2Delta80Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-7377459983571965656595) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta80Fq d2Delta80Ts 16 24 12 20 30 128 d2Delta80Lo d2Delta80Hi d2Delta80Pd d2Delta80Qd d2Delta80Ld d2Delta80Gam (d2LitsStandaloneDelta010.q2 (-7377459983571965656595) 1 (-80)) d2Delta80Check
  simpa only [d2Delta80Fq, d2Delta80Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta80Shift
#print axioms d2Delta80Sites
#print axioms d2Delta80PData
#print axioms d2Delta80Plogs
#print axioms d2Delta80Poles
#print axioms d2Delta80Laurent
#print axioms d2Delta80Small
#print axioms d2Delta80Check
#print axioms d2Delta80Bound

def d2Delta81Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta81Ts : List LTerm := laurentClean []
def d2Delta81Lo : ℚ := (d2LitsStandaloneDelta010.q2 (1055743) 1 (-23))
def d2Delta81Hi : ℚ := (d2LitsStandaloneDelta010.q2 (34831327) 1 (-28))
def d2Delta81Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta81Qd : List (ℚ × ℚ) := []
def d2Delta81Ld : List LaurentPieceData := []
def d2Delta81Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-8918799960590366754983525907867971958010387249, 1, -160, 2202405132340996950232405343114353633139, 1, -159, 582257295997412582075135878756297025921, 1, -160, -10327664029455402728972183213693640249, 1, -159, -972860851525009695003721968325528969, 1, -160, 1491057194944979761535034606446275, 1, -156, 622178139394580896604450967616079, 1, -160, -6188020397072106326759886269201, 1, -159, -201159897291389481718936805197, 1, -160, 3536521555944633956453059835, 1, -160, 18848087168951059630819885, 1, -159, -626112556944026837212009, 1, -160, -2225533459509958907241, 1, -159, 73991214918858831255, 1, -160, 351242289557587865, 1, -160, -6156446070299879, 1, -160, -9698511002905, 1, -159, 374045940995, 1, -160, -958011517, 1, -160, -1732714957, 1, -160, -1091749769, 1, -160, -1080972753, 1, -160, -333716915, 1, -159, -661931551, 1, -160, -396131223, 1, -160, -196773681, 1, -159, -114068007, 1, -159, -227033653, 1, -160, -63713273, 1, -159, -127006565, 1, -160, -68995869, 1, -160, -17214007, 1, -158])
def d2Delta81S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-2076570071238359898156046442699092831, 1, -128, 130003772795271450200603035041, 1, -125, 272949385562105147801116418779, 1, -128, -19348027189455564563048812821, 1, -128, -454763856457825357068605819, 1, -126, 89197020750436305222891457, 1, -128, 4647588271183048279811087, 1, -128, -184892073998534981100515, 1, -128, -6006273611371392400389, 1, -128, 211203909229836589523, 1, -128, 2250052344406527887, 1, -127, -149506329771126815, 1, -128, -1062389928951245, 1, -127, 70651632684869, 1, -128, 670533576819, 1, -128, -23509401451, 1, -128, -148073761, 1, -128, 2876481, 1, -127, 23707, 1, -128, -1075, 1, -128, -3, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta81Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta81Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta81Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta81Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta81Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta81Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta81El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta81Shift : polyRoundApx 128 d2Delta81Lo d2Delta81Hi d2Delta81Fq.poly = (d2Delta81S,d2Delta81Es) := by decide +kernel
theorem d2Delta81Sites : mergeSites d2Delta81Fq.plogs = [] := by decide +kernel
theorem d2Delta81PData : d2Delta81Pd = [] := by decide +kernel
theorem d2Delta81Plogs : plogsRoundM 16 24 20 128 d2Delta81Lo d2Delta81Hi (mergeSites d2Delta81Fq.plogs) d2Delta81Pd = some (d2Delta81Ap,d2Delta81Ep) := by
  rw [d2Delta81Sites,d2Delta81PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta81Poles : polesRoundM 16 24 12 128 d2Delta81Lo d2Delta81Hi d2Delta81Fq.poles d2Delta81Qd = some (d2Delta81Aq,d2Delta81Eq) := by decide +kernel
theorem d2Delta81Laurent : laurentRoundM 16 30 128 d2Delta81Lo d2Delta81Hi d2Delta81Ts d2Delta81Ld = some (d2Delta81Al,d2Delta81El) := by decide +kernel
theorem d2Delta81Small : chebPolyUB (vecAdd d2Delta81S (vecAdd d2Delta81Ap (vecAdd d2Delta81Aq d2Delta81Al))) d2Delta81Gam+d2Delta81Es+d2Delta81Ep+d2Delta81Eq+d2Delta81El ≤ (d2LitsStandaloneDelta010.q2 (-3688727135761390691569) 1 (-79)) := by decide +kernel
theorem d2Delta81Check : chebRoundPieceL d2Delta81Fq d2Delta81Ts 16 24 12 20 30 128 d2Delta81Lo d2Delta81Hi d2Delta81Pd d2Delta81Qd d2Delta81Ld d2Delta81Gam (d2LitsStandaloneDelta010.q2 (-3688727135761390691569) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta81Fq d2Delta81Ts 16 24 12 20 30 128 d2Delta81Lo d2Delta81Hi d2Delta81Pd d2Delta81Qd d2Delta81Ld d2Delta81Gam d2Delta81S d2Delta81Ap d2Delta81Aq d2Delta81Al d2Delta81Es d2Delta81Ep d2Delta81Eq d2Delta81El (by decide +kernel) d2Delta81Shift d2Delta81Plogs d2Delta81Poles d2Delta81Laurent]
  exact decide_eq_true d2Delta81Small
theorem d2Delta81Bound : ∀ x ∈ Icc ((d2Delta81Lo : ℚ) : ℝ) ((d2Delta81Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-3688727135761390691569) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta81Fq d2Delta81Ts 16 24 12 20 30 128 d2Delta81Lo d2Delta81Hi d2Delta81Pd d2Delta81Qd d2Delta81Ld d2Delta81Gam (d2LitsStandaloneDelta010.q2 (-3688727135761390691569) 1 (-79)) d2Delta81Check
  simpa only [d2Delta81Fq, d2Delta81Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta81Shift
#print axioms d2Delta81Sites
#print axioms d2Delta81PData
#print axioms d2Delta81Plogs
#print axioms d2Delta81Poles
#print axioms d2Delta81Laurent
#print axioms d2Delta81Small
#print axioms d2Delta81Check
#print axioms d2Delta81Bound

def d2Delta82Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta82Ts : List LTerm := laurentClean []
def d2Delta82Lo : ℚ := (d2LitsStandaloneDelta010.q2 (34831327) 1 (-28))
def d2Delta82Hi : ℚ := (d2LitsStandaloneDelta010.q2 (17939439) 1 (-27))
def d2Delta82Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta82Qd : List (ℚ × ℚ) := []
def d2Delta82Ld : List LaurentPieceData := []
def d2Delta82Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-8918787437763650974067870153139923009660196897, 1, -160, 7847695765250573034503815781648249022149, 1, -160, 129511203226909942198061526577292347361, 1, -159, -495655997138134326487452472976751619, 1, -154, -377695317534577353315834479917022589, 1, -160, 17015047247367433305897681218872309, 1, -159, 25801962532148343613287175713219, 1, -157, -16542176226337260346954410335281, 1, -160, -6726373944755105692918901381, 1, -157, 555602754991732211939965755, 1, -157, 1719025749151167228934313, 1, -158, -370729708183566590962555, 1, -159, -278390148106999567041, 1, -160, 82857557780091122463, 1, -160, -38565242185250229, 1, -160, -1638793012161209, 1, -158, 7010984070767, 1, -160, 47663578325, 1, -157, -2428101105, 1, -160, -1599827097, 1, -160, -585486303, 1, -159, -493568089, 1, -159, -718952199, 1, -160, -597705887, 1, -160, -428359829, 1, -160, -87764611, 1, -158, -61864655, 1, -158, -99936839, 1, -159, -138498671, 1, -160, -110238551, 1, -160, -75048621, 1, -160, -14715677, 1, -158])
def d2Delta82S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-2076567080142898302278587834145115457, 1, -128, 462345312291803632360738667479, 1, -126, 3791283908160523948228370563, 1, -123, -14851040212980885504173243299, 1, -127, -352910615782985471059404167, 1, -127, 127203799022815239661542025, 1, -128, 1541125989589276243206331, 1, -128, -123547108932135362109115, 1, -127, -1605742204575883139127, 1, -128, 33177312322394418047, 1, -125, 410046619557676141, 1, -127, -11064665835397603, 1, -124, -16172969773, 1, -115, 19778235194885, 1, -126, -73771547259, 1, -128, -6257720077, 1, -126, 53590365, 1, -128, 732615, 1, -125, -17577, 1, -128, -527, 1, -127, 3, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta82Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta82Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta82Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta82Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta82Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta82Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta82El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta82Shift : polyRoundApx 128 d2Delta82Lo d2Delta82Hi d2Delta82Fq.poly = (d2Delta82S,d2Delta82Es) := by decide +kernel
theorem d2Delta82Sites : mergeSites d2Delta82Fq.plogs = [] := by decide +kernel
theorem d2Delta82PData : d2Delta82Pd = [] := by decide +kernel
theorem d2Delta82Plogs : plogsRoundM 16 24 20 128 d2Delta82Lo d2Delta82Hi (mergeSites d2Delta82Fq.plogs) d2Delta82Pd = some (d2Delta82Ap,d2Delta82Ep) := by
  rw [d2Delta82Sites,d2Delta82PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta82Poles : polesRoundM 16 24 12 128 d2Delta82Lo d2Delta82Hi d2Delta82Fq.poles d2Delta82Qd = some (d2Delta82Aq,d2Delta82Eq) := by decide +kernel
theorem d2Delta82Laurent : laurentRoundM 16 30 128 d2Delta82Lo d2Delta82Hi d2Delta82Ts d2Delta82Ld = some (d2Delta82Al,d2Delta82El) := by decide +kernel
theorem d2Delta82Small : chebPolyUB (vecAdd d2Delta82S (vecAdd d2Delta82Ap (vecAdd d2Delta82Aq d2Delta82Al))) d2Delta82Gam+d2Delta82Es+d2Delta82Ep+d2Delta82Eq+d2Delta82El ≤ (d2LitsStandaloneDelta010.q2 (-7377441323698916180097) 1 (-80)) := by decide +kernel
theorem d2Delta82Check : chebRoundPieceL d2Delta82Fq d2Delta82Ts 16 24 12 20 30 128 d2Delta82Lo d2Delta82Hi d2Delta82Pd d2Delta82Qd d2Delta82Ld d2Delta82Gam (d2LitsStandaloneDelta010.q2 (-7377441323698916180097) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta82Fq d2Delta82Ts 16 24 12 20 30 128 d2Delta82Lo d2Delta82Hi d2Delta82Pd d2Delta82Qd d2Delta82Ld d2Delta82Gam d2Delta82S d2Delta82Ap d2Delta82Aq d2Delta82Al d2Delta82Es d2Delta82Ep d2Delta82Eq d2Delta82El (by decide +kernel) d2Delta82Shift d2Delta82Plogs d2Delta82Poles d2Delta82Laurent]
  exact decide_eq_true d2Delta82Small
theorem d2Delta82Bound : ∀ x ∈ Icc ((d2Delta82Lo : ℚ) : ℝ) ((d2Delta82Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-7377441323698916180097) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta82Fq d2Delta82Ts 16 24 12 20 30 128 d2Delta82Lo d2Delta82Hi d2Delta82Pd d2Delta82Qd d2Delta82Ld d2Delta82Gam (d2LitsStandaloneDelta010.q2 (-7377441323698916180097) 1 (-80)) d2Delta82Check
  simpa only [d2Delta82Fq, d2Delta82Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta82Shift
#print axioms d2Delta82Sites
#print axioms d2Delta82PData
#print axioms d2Delta82Plogs
#print axioms d2Delta82Poles
#print axioms d2Delta82Laurent
#print axioms d2Delta82Small
#print axioms d2Delta82Check
#print axioms d2Delta82Bound

def d2Delta83Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta83Ts : List LTerm := laurentClean []
def d2Delta83Lo : ℚ := (d2LitsStandaloneDelta010.q2 (17939439) 1 (-27))
def d2Delta83Hi : ℚ := (d2LitsStandaloneDelta010.q2 (36926429) 1 (-28))
def d2Delta83Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta83Qd : List (ℚ × ℚ) := []
def d2Delta83Ld : List LaurentPieceData := []
def d2Delta83Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-4459385456713708156623404789959532902466014071, 1, -159, 2086792925184255505031191006628822092325, 1, -158, -2109421305940824936161152067095268065, 1, -154, -32210210321767389183380888495206391681, 1, -160, 314552311213506858464992953404285479, 1, -160, 33379494609488211675548632907610645, 1, -160, -256806798466793378350594601566135, 1, -160, -3928563221131980832247310425777, 1, -158, 25841720522342461394489246499, 1, -158, 2039291880550400477314251261, 1, -159, -6137855842552102105741533, 1, -158, -81821968286135449447427, 1, -157, 3788480782093097581731, 1, -160, 35082692815470868239, 1, -159, -1571626015966665, 1, -152, -2658929183175931, 1, -159, 15339587515859, 1, -159, 296017327097, 1, -160, -3453595827, 1, -160, -1475628941, 1, -160, -1074291105, 1, -160, -226299087, 1, -158, -82014441, 1, -157, -543741505, 1, -160, -389324063, 1, -160, -158419953, 1, -159, -112143327, 1, -159, -5593353, 1, -155, -125351221, 1, -160, -48985207, 1, -159, -67916477, 1, -160, -12982779, 1, -158])
def d2Delta83S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-1038281570434295981148095185884598985, 1, -127, 491503704060559177045017359355, 1, -126, -1982894693220980987939055117, 1, -123, -30153736394596038868231530253, 1, -128, 147193307322412004690973489, 1, -126, 31189624734089301373143049, 1, -126, -119970456346755125319713, 1, -124, -234708025316281032348805, 1, -128, 1543948068999425021173, 1, -127, 30441497687419773613, 1, -125, -2932180897031730721, 1, -128, -78140303497452779, 1, -127, 1809175816319409, 1, -128, 66991032568871, 1, -128, -768332291893, 1, -128, -10152679723, 1, -127, 234323201, 1, -128, 4555631, 1, -128, -53235, 1, -128, -393, 1, -127, 9, 1, -128, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta83Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta83Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta83Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta83Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta83Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta83Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta83El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta83Shift : polyRoundApx 128 d2Delta83Lo d2Delta83Hi d2Delta83Fq.poly = (d2Delta83S,d2Delta83Es) := by decide +kernel
theorem d2Delta83Sites : mergeSites d2Delta83Fq.plogs = [] := by decide +kernel
theorem d2Delta83PData : d2Delta83Pd = [] := by decide +kernel
theorem d2Delta83Plogs : plogsRoundM 16 24 20 128 d2Delta83Lo d2Delta83Hi (mergeSites d2Delta83Fq.plogs) d2Delta83Pd = some (d2Delta83Ap,d2Delta83Ep) := by
  rw [d2Delta83Sites,d2Delta83PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta83Poles : polesRoundM 16 24 12 128 d2Delta83Lo d2Delta83Hi d2Delta83Fq.poles d2Delta83Qd = some (d2Delta83Aq,d2Delta83Eq) := by decide +kernel
theorem d2Delta83Laurent : laurentRoundM 16 30 128 d2Delta83Lo d2Delta83Hi d2Delta83Ts d2Delta83Ld = some (d2Delta83Al,d2Delta83El) := by decide +kernel
theorem d2Delta83Small : chebPolyUB (vecAdd d2Delta83S (vecAdd d2Delta83Ap (vecAdd d2Delta83Aq d2Delta83Al))) d2Delta83Gam+d2Delta83Es+d2Delta83Ep+d2Delta83Eq+d2Delta83El ≤ (d2LitsStandaloneDelta010.q2 (-7377427344166892311115) 1 (-80)) := by decide +kernel
theorem d2Delta83Check : chebRoundPieceL d2Delta83Fq d2Delta83Ts 16 24 12 20 30 128 d2Delta83Lo d2Delta83Hi d2Delta83Pd d2Delta83Qd d2Delta83Ld d2Delta83Gam (d2LitsStandaloneDelta010.q2 (-7377427344166892311115) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta83Fq d2Delta83Ts 16 24 12 20 30 128 d2Delta83Lo d2Delta83Hi d2Delta83Pd d2Delta83Qd d2Delta83Ld d2Delta83Gam d2Delta83S d2Delta83Ap d2Delta83Aq d2Delta83Al d2Delta83Es d2Delta83Ep d2Delta83Eq d2Delta83El (by decide +kernel) d2Delta83Shift d2Delta83Plogs d2Delta83Poles d2Delta83Laurent]
  exact decide_eq_true d2Delta83Small
theorem d2Delta83Bound : ∀ x ∈ Icc ((d2Delta83Lo : ℚ) : ℝ) ((d2Delta83Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-7377427344166892311115) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta83Fq d2Delta83Ts 16 24 12 20 30 128 d2Delta83Lo d2Delta83Hi d2Delta83Pd d2Delta83Qd d2Delta83Ld d2Delta83Gam (d2LitsStandaloneDelta010.q2 (-7377427344166892311115) 1 (-80)) d2Delta83Check
  simpa only [d2Delta83Fq, d2Delta83Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta83Shift
#print axioms d2Delta83Sites
#print axioms d2Delta83PData
#print axioms d2Delta83Plogs
#print axioms d2Delta83Poles
#print axioms d2Delta83Laurent
#print axioms d2Delta83Small
#print axioms d2Delta83Check
#print axioms d2Delta83Bound

def d2Delta84Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta84Ts : List LTerm := laurentClean []
def d2Delta84Lo : ℚ := (d2LitsStandaloneDelta010.q2 (36926429) 1 (-28))
def d2Delta84Hi : ℚ := (d2LitsStandaloneDelta010.q2 (9493495) 1 (-26))
def d2Delta84Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta84Qd : List (ℚ × ℚ) := []
def d2Delta84Ld : List LaurentPieceData := []
def d2Delta84Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-1114844553882361491876768674869183683189705945, 1, -157, 5854467688541035212980953984284641448057, 1, -160, -470771684661824442586749963142918466585, 1, -160, -22312744993033012270712882793054907959, 1, -160, 887347102160666511657765351908170047, 1, -160, 22437482369866911675002498453521001, 1, -160, -315041948752639951700357979868909, 1, -159, -5149706675965213924566633078205, 1, -159, 56538732763111459377387538611, 1, -158, 1293035350416255931808657381, 1, -159, -24091974987039421610532111, 1, -159, -198138855026522701550009, 1, -159, 419517894476196308711, 1, -156, 39968235499799877819, 1, -160, -20344093412681711, 1, -155, -87742283931321, 1, -155, 23001028693425, 1, -159, 141638365239, 1, -160, -4389437313, 1, -160, -686147847, 1, -159, -608805013, 1, -159, -422039239, 1, -159, -372502445, 1, -159, -506634227, 1, -160, -442263035, 1, -160, -295356745, 1, -160, -127298139, 1, -159, -167134517, 1, -160, -142046765, 1, -160, -91742683, 1, -160, -299877, 1, -152, -48817251, 1, -160])
def d2Delta84S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-2076559690618708231702543167696580125, 1, -128, 1378710889967893260472080428055, 1, -128, -220875603819837976906079195163, 1, -128, -20884980144233623325460219361, 1, -128, 1659862941231991455657769803, 1, -128, 5240935859680177202016311, 1, -124, -4707983316063255503106443, 1, -128, -153820297579370009558707, 1, -128, 6754312907230559830243, 1, -128, 154401800295750424401, 1, -128, -2876791212192839521, 1, -127, -94603908032332793, 1, -128, 801253944787691, 1, -126, 38156861177741, 1, -128, -621554753401, 1, -127, -2680010865, 1, -126, 43916015, 1, -125, 2195683, 1, -128, -37521, 1, -127, -341, 1, -128, 3, 1, -126, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta84Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta84Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta84Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta84Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta84Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta84Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta84El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta84Shift : polyRoundApx 128 d2Delta84Lo d2Delta84Hi d2Delta84Fq.poly = (d2Delta84S,d2Delta84Es) := by decide +kernel
theorem d2Delta84Sites : mergeSites d2Delta84Fq.plogs = [] := by decide +kernel
theorem d2Delta84PData : d2Delta84Pd = [] := by decide +kernel
theorem d2Delta84Plogs : plogsRoundM 16 24 20 128 d2Delta84Lo d2Delta84Hi (mergeSites d2Delta84Fq.plogs) d2Delta84Pd = some (d2Delta84Ap,d2Delta84Ep) := by
  rw [d2Delta84Sites,d2Delta84PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta84Poles : polesRoundM 16 24 12 128 d2Delta84Lo d2Delta84Hi d2Delta84Fq.poles d2Delta84Qd = some (d2Delta84Aq,d2Delta84Eq) := by decide +kernel
theorem d2Delta84Laurent : laurentRoundM 16 30 128 d2Delta84Lo d2Delta84Hi d2Delta84Ts d2Delta84Ld = some (d2Delta84Al,d2Delta84El) := by decide +kernel
theorem d2Delta84Small : chebPolyUB (vecAdd d2Delta84S (vecAdd d2Delta84Ap (vecAdd d2Delta84Aq d2Delta84Al))) d2Delta84Gam+d2Delta84Es+d2Delta84Ep+d2Delta84Eq+d2Delta84El ≤ (d2LitsStandaloneDelta010.q2 (-230544286141544179915) 1 (-75)) := by decide +kernel
theorem d2Delta84Check : chebRoundPieceL d2Delta84Fq d2Delta84Ts 16 24 12 20 30 128 d2Delta84Lo d2Delta84Hi d2Delta84Pd d2Delta84Qd d2Delta84Ld d2Delta84Gam (d2LitsStandaloneDelta010.q2 (-230544286141544179915) 1 (-75)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta84Fq d2Delta84Ts 16 24 12 20 30 128 d2Delta84Lo d2Delta84Hi d2Delta84Pd d2Delta84Qd d2Delta84Ld d2Delta84Gam d2Delta84S d2Delta84Ap d2Delta84Aq d2Delta84Al d2Delta84Es d2Delta84Ep d2Delta84Eq d2Delta84El (by decide +kernel) d2Delta84Shift d2Delta84Plogs d2Delta84Poles d2Delta84Laurent]
  exact decide_eq_true d2Delta84Small
theorem d2Delta84Bound : ∀ x ∈ Icc ((d2Delta84Lo : ℚ) : ℝ) ((d2Delta84Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-230544286141544179915) 1 (-75)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta84Fq d2Delta84Ts 16 24 12 20 30 128 d2Delta84Lo d2Delta84Hi d2Delta84Pd d2Delta84Qd d2Delta84Ld d2Delta84Gam (d2LitsStandaloneDelta010.q2 (-230544286141544179915) 1 (-75)) d2Delta84Check
  simpa only [d2Delta84Fq, d2Delta84Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta84Shift
#print axioms d2Delta84Sites
#print axioms d2Delta84PData
#print axioms d2Delta84Plogs
#print axioms d2Delta84Poles
#print axioms d2Delta84Laurent
#print axioms d2Delta84Small
#print axioms d2Delta84Check
#print axioms d2Delta84Bound

def d2Delta85Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta85Ts : List LTerm := laurentClean []
def d2Delta85Lo : ℚ := (d2LitsStandaloneDelta010.q2 (9493495) 1 (-26))
def d2Delta85Hi : ℚ := (d2LitsStandaloneDelta010.q2 (76995511) 1 (-29))
def d2Delta85Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta85Qd : List (ℚ × ℚ) := []
def d2Delta85Ld : List LaurentPieceData := []
def d2Delta85Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-2229687407806387705928767854401741768547540169, 1, -158, 320865092596105111218117791774552587009, 1, -158, -9713046490062215515317896656806799397, 1, -156, -1257618562245605610838224755917891153, 1, -160, 70868340832808489149240228745475461, 1, -160, 298225662013188816887798774870831, 1, -160, -12281154905601298682027928334935, 1, -160, -16435689543072063023082595613, 1, -159, 1075788003587260348134369491, 1, -160, 1928965874742247396912497, 1, -160, -55750835344111248021061, 1, -160, -4070159599194419617, 1, -156, 942130637728488371, 1, -159, 652972285310509, 1, -159, -22165878231097, 1, -159, -4519108081, 1, -158, -152035111, 1, -156, -1135076019, 1, -159, -2092142165, 1, -160, -1451509391, 1, -160, -333111941, 1, -158, -450680307, 1, -159, -824438833, 1, -160, -543128103, 1, -160, -495234861, 1, -160, -317319489, 1, -160, -36077375, 1, -157, -89820649, 1, -159, -163091315, 1, -160, -98491391, 1, -160, -44651791, 1, -159, -52271753, 1, -160])
def d2Delta85S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-1038279090512768174481585776173252175, 1, -127, 299707687792737116725490640359, 1, -128, -72499889764904433167300555919, 1, -128, -1172637707379508129360141563, 1, -128, 66069931984683413347106067, 1, -127, 1111834547496904127765487, 1, -128, -45782935474516019615269, 1, -127, -490080455610348263257, 1, -128, 32077598980072730703, 1, -128, 57509014240574415, 1, -127, -6648713337533155, 1, -128, -15530474720429, 1, -128, 898781747657, 1, -128, 311414969, 1, -126, -84570299, 1, -128, -55791, 1, -128, 363, 1, -124, 0, 1, 0, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta85Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta85Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta85Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta85Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta85Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta85Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta85El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta85Shift : polyRoundApx 128 d2Delta85Lo d2Delta85Hi d2Delta85Fq.poly = (d2Delta85S,d2Delta85Es) := by decide +kernel
theorem d2Delta85Sites : mergeSites d2Delta85Fq.plogs = [] := by decide +kernel
theorem d2Delta85PData : d2Delta85Pd = [] := by decide +kernel
theorem d2Delta85Plogs : plogsRoundM 16 24 20 128 d2Delta85Lo d2Delta85Hi (mergeSites d2Delta85Fq.plogs) d2Delta85Pd = some (d2Delta85Ap,d2Delta85Ep) := by
  rw [d2Delta85Sites,d2Delta85PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta85Poles : polesRoundM 16 24 12 128 d2Delta85Lo d2Delta85Hi d2Delta85Fq.poles d2Delta85Qd = some (d2Delta85Aq,d2Delta85Eq) := by decide +kernel
theorem d2Delta85Laurent : laurentRoundM 16 30 128 d2Delta85Lo d2Delta85Hi d2Delta85Ts d2Delta85Ld = some (d2Delta85Al,d2Delta85El) := by decide +kernel
theorem d2Delta85Small : chebPolyUB (vecAdd d2Delta85S (vecAdd d2Delta85Ap (vecAdd d2Delta85Aq d2Delta85Al))) d2Delta85Gam+d2Delta85Es+d2Delta85Ep+d2Delta85Eq+d2Delta85El ≤ (d2LitsStandaloneDelta010.q2 (-922176948982556254943) 1 (-77)) := by decide +kernel
theorem d2Delta85Check : chebRoundPieceL d2Delta85Fq d2Delta85Ts 16 24 12 20 30 128 d2Delta85Lo d2Delta85Hi d2Delta85Pd d2Delta85Qd d2Delta85Ld d2Delta85Gam (d2LitsStandaloneDelta010.q2 (-922176948982556254943) 1 (-77)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta85Fq d2Delta85Ts 16 24 12 20 30 128 d2Delta85Lo d2Delta85Hi d2Delta85Pd d2Delta85Qd d2Delta85Ld d2Delta85Gam d2Delta85S d2Delta85Ap d2Delta85Aq d2Delta85Al d2Delta85Es d2Delta85Ep d2Delta85Eq d2Delta85El (by decide +kernel) d2Delta85Shift d2Delta85Plogs d2Delta85Poles d2Delta85Laurent]
  exact decide_eq_true d2Delta85Small
theorem d2Delta85Bound : ∀ x ∈ Icc ((d2Delta85Lo : ℚ) : ℝ) ((d2Delta85Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-922176948982556254943) 1 (-77)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta85Fq d2Delta85Ts 16 24 12 20 30 128 d2Delta85Lo d2Delta85Hi d2Delta85Pd d2Delta85Qd d2Delta85Ld d2Delta85Gam (d2LitsStandaloneDelta010.q2 (-922176948982556254943) 1 (-77)) d2Delta85Check
  simpa only [d2Delta85Fq, d2Delta85Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta85Shift
#print axioms d2Delta85Sites
#print axioms d2Delta85PData
#print axioms d2Delta85Plogs
#print axioms d2Delta85Poles
#print axioms d2Delta85Laurent
#print axioms d2Delta85Small
#print axioms d2Delta85Check
#print axioms d2Delta85Bound

def d2Delta86Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta86Ts : List LTerm := laurentClean []
def d2Delta86Lo : ℚ := (d2LitsStandaloneDelta010.q2 (76995511) 1 (-29))
def d2Delta86Hi : ℚ := (d2LitsStandaloneDelta010.q2 (20034541) 1 (-27))
def d2Delta86Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta86Qd : List (ℚ × ℚ) := []
def d2Delta86Ld : List LaurentPieceData := []
def d2Delta86Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-8918750886830857367728695530282530394295739935, 1, -160, -475466118656799024980053104074567859499, 1, -157, -87399314611120623540951761082813827977, 1, -156, 14308101270548724927275466782730675439, 1, -159, 1420568266016740454879993260155656727, 1, -158, -73371788275575749846008993583030739, 1, -160, -4407756388550487647254475722134929, 1, -159, 80420101273946584464155978766599, 1, -160, 6877143946581842310326972085799, 1, -160, -24967721040487160041535611145, 1, -159, -3149914045550063800865892725, 1, -160, 5034475920348028328771065, 1, -158, 935146779640050075706293, 1, -160, -703786482994084048901, 1, -157, -192550635126458798773, 1, -160, 566370478339864303, 1, -159, 7227127729845035, 1, -158, -168871398062185, 1, -160, -3294320563807, 1, -160, 17665168163, 1, -160, -879626353, 1, -160, -471232619, 1, -159, -723946971, 1, -160, -568531907, 1, -160, -217140545, 1, -159, -333766453, 1, -160, -253151803, 1, -160, -190232589, 1, -160, -143281047, 1, -160, -26298429, 1, -158, -19669463, 1, -158, -28196979, 1, -159])
def d2Delta86S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-259569772832058606804926533760977617, 1, -125, -113212299160933235970426215157, 1, -125, -82724586581012490431317464961, 1, -125, 3374203674386316386848624571, 1, -125, 5341417939590690422000504769, 1, -127, -68858339258537895164463093, 1, -126, -66091420355873502215161835, 1, -128, 301265743372115449328787, 1, -126, 102947557351263796902991, 1, -127, -1494804778757765851059, 1, -127, -11776203824150131295, 1, -123, 2409362733004467791, 1, -127, 447199581535127391, 1, -128, -5385687910580475, 1, -128, -368144256708049, 1, -128, 1083006525543, 1, -126, 27625873749, 1, -125, -1291150967, 1, -127, -25164421, 1, -126, 146591, 1, -125, 35927, 1, -128, -417, 1, -128, -11, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta86Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta86Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta86Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta86Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta86Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta86Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta86El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta86Shift : polyRoundApx 128 d2Delta86Lo d2Delta86Hi d2Delta86Fq.poly = (d2Delta86S,d2Delta86Es) := by decide +kernel
theorem d2Delta86Sites : mergeSites d2Delta86Fq.plogs = [] := by decide +kernel
theorem d2Delta86PData : d2Delta86Pd = [] := by decide +kernel
theorem d2Delta86Plogs : plogsRoundM 16 24 20 128 d2Delta86Lo d2Delta86Hi (mergeSites d2Delta86Fq.plogs) d2Delta86Pd = some (d2Delta86Ap,d2Delta86Ep) := by
  rw [d2Delta86Sites,d2Delta86PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta86Poles : polesRoundM 16 24 12 128 d2Delta86Lo d2Delta86Hi d2Delta86Fq.poles d2Delta86Qd = some (d2Delta86Aq,d2Delta86Eq) := by decide +kernel
theorem d2Delta86Laurent : laurentRoundM 16 30 128 d2Delta86Lo d2Delta86Hi d2Delta86Ts d2Delta86Ld = some (d2Delta86Al,d2Delta86El) := by decide +kernel
theorem d2Delta86Small : chebPolyUB (vecAdd d2Delta86S (vecAdd d2Delta86Ap (vecAdd d2Delta86Aq d2Delta86Al))) d2Delta86Gam+d2Delta86Es+d2Delta86Ep+d2Delta86Eq+d2Delta86El ≤ (d2LitsStandaloneDelta010.q2 (-7377413490246377568565) 1 (-80)) := by decide +kernel
theorem d2Delta86Check : chebRoundPieceL d2Delta86Fq d2Delta86Ts 16 24 12 20 30 128 d2Delta86Lo d2Delta86Hi d2Delta86Pd d2Delta86Qd d2Delta86Ld d2Delta86Gam (d2LitsStandaloneDelta010.q2 (-7377413490246377568565) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta86Fq d2Delta86Ts 16 24 12 20 30 128 d2Delta86Lo d2Delta86Hi d2Delta86Pd d2Delta86Qd d2Delta86Ld d2Delta86Gam d2Delta86S d2Delta86Ap d2Delta86Aq d2Delta86Al d2Delta86Es d2Delta86Ep d2Delta86Eq d2Delta86El (by decide +kernel) d2Delta86Shift d2Delta86Plogs d2Delta86Poles d2Delta86Laurent]
  exact decide_eq_true d2Delta86Small
theorem d2Delta86Bound : ∀ x ∈ Icc ((d2Delta86Lo : ℚ) : ℝ) ((d2Delta86Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-7377413490246377568565) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta86Fq d2Delta86Ts 16 24 12 20 30 128 d2Delta86Lo d2Delta86Hi d2Delta86Pd d2Delta86Qd d2Delta86Ld d2Delta86Gam (d2LitsStandaloneDelta010.q2 (-7377413490246377568565) 1 (-80)) d2Delta86Check
  simpa only [d2Delta86Fq, d2Delta86Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta86Shift
#print axioms d2Delta86Sites
#print axioms d2Delta86PData
#print axioms d2Delta86Plogs
#print axioms d2Delta86Poles
#print axioms d2Delta86Laurent
#print axioms d2Delta86Small
#print axioms d2Delta86Check
#print axioms d2Delta86Bound

def d2Delta87Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta87Ts : List LTerm := laurentClean []
def d2Delta87Lo : ℚ := (d2LitsStandaloneDelta010.q2 (20034541) 1 (-27))
def d2Delta87Hi : ℚ := (d2LitsStandaloneDelta010.q2 (41116633) 1 (-28))
def d2Delta87Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta87Qd : List (ℚ × ℚ) := []
def d2Delta87Ld : List LaurentPieceData := []
def d2Delta87Gam : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-4459381670937206591510375826667744631966772269, 1, -159, -7662783294599845375274833230987744577479, 1, -160, -349426963171494505941335760707472828035, 1, -160, 26869303538929849248172628074760653715, 1, -160, 39162565637284871004588883266436081, 1, -156, -28776404775968301159871973682884699, 1, -160, -443619837911579728170634216295143, 1, -160, 6776287585405257274100780262017, 1, -159, 77889011006006386993434244857, 1, -159, -3536052962818511369409269431, 1, -160, -31414176390214908003918757, 1, -160, 2275843162671451818943, 1, -152, 4026828542374614976923, 1, -160, -4102197828125661033, 1, -156, -352506072881489043, 1, -160, 5329292725250455, 1, -160, 11118027950437, 1, -159, -163347826865, 1, -159, -3045449849, 1, -160, -805491835, 1, -159, -1268962595, 1, -160, -126901651, 1, -157, -196822525, 1, -158, -615244273, 1, -160, -237358045, 1, -159, -361721259, 1, -160, -138982723, 1, -159, -25773793, 1, -157, -157919805, 1, -160, -113883961, 1, -160, -86976705, 1, -160, -1903415, 1, -155])
def d2Delta87S : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [-519140331995464231916839255754258263, 1, -126, -450733070153531842311599879223, 1, -126, -20485450655923678626320586061, 1, -125, 1572385395701027058007173649, 1, -124, 4578511917174905540772911, 1, -120, -26888557076889405864175845, 1, -126, -3314518645666226270504249, 1, -128, 50605927753503433642357, 1, -126, 4651915469726835656447, 1, -128, -211147427851926972133, 1, -128, -468828163795475013, 1, -125, 139109989779489937, 1, -128, 240311976717739, 1, -125, -7833855542953, 1, -125, -336515461361, 1, -127, 10175341943, 1, -127, 84907925, 1, -127, -2475393, 1, -127, -16121, 1, -127, 465, 1, -127, 1, 1, -126, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, -1, 1, -128, -1, 1, -128, -1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta87Ap : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta87Aq : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta87Al : List ℚ := d2LitsStandaloneDelta010.q2listC (raw_ints% [])
def d2Delta87Es : ℚ := (d2LitsStandaloneDelta010.q2 (61) 1 (-127))
def d2Delta87Ep : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta87Eq : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
def d2Delta87El : ℚ := (d2LitsStandaloneDelta010.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta87Shift : polyRoundApx 128 d2Delta87Lo d2Delta87Hi d2Delta87Fq.poly = (d2Delta87S,d2Delta87Es) := by decide +kernel
theorem d2Delta87Sites : mergeSites d2Delta87Fq.plogs = [] := by decide +kernel
theorem d2Delta87PData : d2Delta87Pd = [] := by decide +kernel
theorem d2Delta87Plogs : plogsRoundM 16 24 20 128 d2Delta87Lo d2Delta87Hi (mergeSites d2Delta87Fq.plogs) d2Delta87Pd = some (d2Delta87Ap,d2Delta87Ep) := by
  rw [d2Delta87Sites,d2Delta87PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta87Poles : polesRoundM 16 24 12 128 d2Delta87Lo d2Delta87Hi d2Delta87Fq.poles d2Delta87Qd = some (d2Delta87Aq,d2Delta87Eq) := by decide +kernel
theorem d2Delta87Laurent : laurentRoundM 16 30 128 d2Delta87Lo d2Delta87Hi d2Delta87Ts d2Delta87Ld = some (d2Delta87Al,d2Delta87El) := by decide +kernel
theorem d2Delta87Small : chebPolyUB (vecAdd d2Delta87S (vecAdd d2Delta87Ap (vecAdd d2Delta87Aq d2Delta87Al))) d2Delta87Gam+d2Delta87Es+d2Delta87Ep+d2Delta87Eq+d2Delta87El ≤ (d2LitsStandaloneDelta010.q2 (-1844355368508478892445) 1 (-78)) := by decide +kernel
theorem d2Delta87Check : chebRoundPieceL d2Delta87Fq d2Delta87Ts 16 24 12 20 30 128 d2Delta87Lo d2Delta87Hi d2Delta87Pd d2Delta87Qd d2Delta87Ld d2Delta87Gam (d2LitsStandaloneDelta010.q2 (-1844355368508478892445) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta87Fq d2Delta87Ts 16 24 12 20 30 128 d2Delta87Lo d2Delta87Hi d2Delta87Pd d2Delta87Qd d2Delta87Ld d2Delta87Gam d2Delta87S d2Delta87Ap d2Delta87Aq d2Delta87Al d2Delta87Es d2Delta87Ep d2Delta87Eq d2Delta87El (by decide +kernel) d2Delta87Shift d2Delta87Plogs d2Delta87Poles d2Delta87Laurent]
  exact decide_eq_true d2Delta87Small
theorem d2Delta87Bound : ∀ x ∈ Icc ((d2Delta87Lo : ℚ) : ℝ) ((d2Delta87Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta010.q2 (-1844355368508478892445) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta87Fq d2Delta87Ts 16 24 12 20 30 128 d2Delta87Lo d2Delta87Hi d2Delta87Pd d2Delta87Qd d2Delta87Ld d2Delta87Gam (d2LitsStandaloneDelta010.q2 (-1844355368508478892445) 1 (-78)) d2Delta87Check
  simpa only [d2Delta87Fq, d2Delta87Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta87Shift
#print axioms d2Delta87Sites
#print axioms d2Delta87PData
#print axioms d2Delta87Plogs
#print axioms d2Delta87Poles
#print axioms d2Delta87Laurent
#print axioms d2Delta87Small
#print axioms d2Delta87Check
#print axioms d2Delta87Bound

end StandaloneDelta010
end CatalanMeasure.GenD.Signed.Data.Cells
