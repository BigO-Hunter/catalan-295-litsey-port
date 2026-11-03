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
namespace d2LitsStandaloneDelta019
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsStandaloneDelta019
namespace StandaloneDelta019
def d2DeltaRawFq : FieldQ := ⟨d2LitsStandaloneDelta019.q2listC (raw_ints% [-6811934213464216340899824207409878583363, 60566951029857698130705, -64, -4944678539352731, 1, -62, 44841643026330681, 1, -59, -4388346628593872729, 3, -59, 66347385773745950097, 1, -61, 537575868171450589083, 5, -58, -3284512900123023485691, 1, -58, 3686863894219306563137, 7, -56, 1130040009544406732164937, 1, -59, -513945658379728065967661, 3, -54, -9622811952144916508514509, 5, -53, 19801051883602509416515721, 11, -50, 55653273355452611952578395, 3, -50, -590901024034940822964542375, 13, -48, -918213420385586944773736601, 7, -47, 12268338937454162917821834769, 15, -46, 21712666814276230498010754205, 1, -49, -189709144504088332782379804991, 17, -44, -58640380466980757107050376615, 3, -44, 2266797821537850703617304765229, 19, -42, 780836968339457801169803253641, 5, -43, -3065806255152310903171548244117, 3, -40, 1837451633181083026600962244033, 11, -40, 164145010128113135835776594736323, 23, -38, -138000998700766231147027708782299, 3, -41, -51533732279449905865455305593107, 5, -34, 357827235904534040439919520907679, 13, -35, 1794898096124467569297893057330431, 9, -34, -5009700030970561395141488399063747, 7, -35, -11836486590661727144988003200830919, 29, -31, 3387345327802829043860320127732503, 15, -29, 44203292266773431956369780515957777, 31, -29, -29846790839225387900304559855301205, 1, -32, -565223498969125047783794091864586877, 33, -29, 440690249705593905052063945190145711, 17, -28, 388991632316058211212969686728047583, 35, -25, -308427887693618529095910162048259493, 1, -28, -3704120380969933251335999568270122407, 37, -25, 7556259488410244412127444569896072027, 19, -25, 7641958869487270899683845010155007717, 39, -23, -7181800237730663078450937917788015713, 1, -26, -13654819294222330554420805153453043563, 41, -21, 1563801556403784780024758979507004593, 7, -18, 10513593460779724708325646939944036137, 43, -18, -34730472362290523382228477694511720447, 11, -19, -13773522879074524825454698898318347877, 45, -16, 28606598218315554921333923484890456351, 23, -15, 14881175295791361597770497906676086219, 47, -14, -28089437297560493812960886038120932559, 1, -17, -24310323793632294681658623828161146707, 49, -13, 111394484945057096154102426881581010777, 25, -12, 290113359596958920609038270744004939, 3, -10, -265170519642987052991100931787660128729, 13, -12, 11489100460274979870131763588668873955, 53, -9, 284955187611939195470363252310138981695, 27, -9, -34550754190584631893236111263426913951, 55, -7, -554213734603036900267361504809436653993, 7, -10, 26547419474362523256202723882523940079, 57, -4, 122162322497468933831007657374038532277, 29, -4, -15642753574346434451621955983213431787, 59, -1, -12226142440533789374472522669463876313, 15, 0, 30923208183738074208045730590138025633, 61, 0, 2224937897334281652417464377819916205, 31, 5, -3319862645323248631246339698686263511, 63, 5, -47160877907753254423758954969954836951, 1, -3, 6208394162045313981621433162667836437, 5, 2, 14220857593227791965572553770990077327, 33, 5, -27399552876781121777695736656905692051, 67, 5, -62479014129368116368381627257318711335, 17, 3, 33467485716792229978347462516388675279, 69, 6, 6248153900596759020954902491607098495, 7, 6, -18463108035201201314381768240571019907, 71, 8, -28428622818043405606226854437458820475, 9, 5, 9226419897822398465842663581900467009, 73, 10, 2939403566114361856424393913926067823, 37, 11, -41839967804505716881052334469586699, 3, 14, -137907415310575252559457127209304445, 19, 15, 53862544434105316823318200605909969, 77, 19, 187457800368429701350132357213681775, 39, 16, -161325735151614830693809895928954641, 79, 18, -2874284853797908025021620849808523, 1, 17, 109775929889592596601790679927030395, 81, 19, 15833629523961639806594494947626911, 41, 20, -16961027292763784875228764013654409, 83, 22, -7781070167390936365567261546824337, 21, 20, 9510620823223565767970498645741853, 85, 23, 1687999304027167823777230744908237, 43, 23, -2415620056436669342066641917503849, 87, 25, -635637825559230119112146794692845, 11, 22, 277351741274772508952578829808807, 89, 28, 392934213064133568583484517961, 45, 34, -57431590101145216771325355858495, 91, 30, -3103095622531914757291584489163, 23, 29, 2672367566379444654318753692059, 93, 34, 112413284832365434419749355441, 47, 33, -9374907745377423590315424245, 1, 35, 15723751947639303453784429717, 3, 30, 1057765229610100956838644788297, 97, 34, -9510145319886657546231464451, 49, 36, -69537589623508075277149655207, 99, 37, 8444547678191003875039737993, 25, 35, 16075542636103480072281293715, 101, 38, -1340459351882888291754624269, 51, 38, -1618667276082337179383425035, 103, 40, 337345324391717118098836233, 13, 37, 140344251125966795859972323, 105, 42, -8658268356352076946510773, 53, 43, -1290305572821514886164577, 107, 47, 15172656355874960065457, 9, 48, 157846311206394442846011, 109, 48, -24864309727014941799629, 55, 48, -7811739766869335369249, 111, 50, 385594398425049078729, 1, 46, 1201963048028401598069, 113, 50, -56175443213549420999, 57, 52, -16856584282681430589, 115, 53, 6748399668075941179, 29, 51, 5241625421365321, 1, 54, -130337081097451907, 59, 54, -5429611603328053, 119, 56, 2433495887286871, 15, 53]), [], mkPolesC (d2LitsStandaloneDelta019.q2listC (raw_ints% []))⟩
def d2Delta152Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta152Ts : List LTerm := laurentClean []
def d2Delta152Lo : ℚ := (d2LitsStandaloneDelta019.q2 (66061249) 1 (-26))
def d2Delta152Hi : ℚ := (d2LitsStandaloneDelta019.q2 (1058027535) 1 (-30))
def d2Delta152Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta152Qd : List (ℚ × ℚ) := []
def d2Delta152Ld : List LaurentPieceData := []
def d2Delta152Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-1088706960266573355191554213556662068226549, 1, -147, 4196534233263394960861737181620889403, 1, -146, 652602112355997687489564606895656043, 1, -148, -34107178024559918044768503603483731, 1, -147, -1484026561875853025243084261949517, 1, -147, 26171906706833857718157331333545, 1, -147, 3536628868627295506353768559405, 1, -148, 1765020669189502693824228671, 1, -145, -195002854816461475115403557, 1, -145, -3345926081302708779501417, 1, -145, 226588407525386619887029, 1, -149, 8317175456570157904277, 1, -148, 91657788423795481439, 1, -148, -202132016924788647, 1, -148, -33750877801224285, 1, -149, -106082730844079, 1, -147, -530353103607, 1, -147, 3290751713, 1, -147, 383351671, 1, -149, 2238701, 1, -148, 18491, 1, -148, 121, 1, -148, 1, 1, -149, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta152S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-2076544357401705149781389544927736053, 1, -128, 8101960001557279608856315392087, 1, -127, 633722476457611683316221952803, 1, -127, -261214739343236934338937274593, 1, -128, -11403290188123028833316623027, 1, -127, 797183973628239805917702757, 1, -128, 13538791680763426840153937, 1, -125, 54784538339717935460435, 1, -124, -95285084686621221162225, 1, -127, -3278675617757982482419, 1, -127, 54781743782435358759, 1, -128, 2031197283933953547, 1, -126, 44870085034348417, 1, -126, -388571783767459, 1, -127, -131706576092577, 1, -128, -1658414117805, 1, -127, -33254788417, 1, -128, 51085867, 1, -125, 23913265, 1, -128, 8735, 1, -122, 1155, 1, -125, 121, 1, -128, 1, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta152Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta152Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta152Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta152Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta152Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta152Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta152El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta152Shift : polyRoundApx 128 d2Delta152Lo d2Delta152Hi d2Delta152Fq.poly = (d2Delta152S,d2Delta152Es) := by decide +kernel
theorem d2Delta152Sites : mergeSites d2Delta152Fq.plogs = [] := by decide +kernel
theorem d2Delta152PData : d2Delta152Pd = [] := by decide +kernel
theorem d2Delta152Plogs : plogsRoundM 16 24 20 128 d2Delta152Lo d2Delta152Hi (mergeSites d2Delta152Fq.plogs) d2Delta152Pd = some (d2Delta152Ap,d2Delta152Ep) := by
  rw [d2Delta152Sites,d2Delta152PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta152Poles : polesRoundM 16 24 12 128 d2Delta152Lo d2Delta152Hi d2Delta152Fq.poles d2Delta152Qd = some (d2Delta152Aq,d2Delta152Eq) := by decide +kernel
theorem d2Delta152Laurent : laurentRoundM 16 30 128 d2Delta152Lo d2Delta152Hi d2Delta152Ts d2Delta152Ld = some (d2Delta152Al,d2Delta152El) := by decide +kernel
theorem d2Delta152Small : chebPolyUB (vecAdd d2Delta152S (vecAdd d2Delta152Ap (vecAdd d2Delta152Aq d2Delta152Al))) d2Delta152Gam+d2Delta152Es+d2Delta152Ep+d2Delta152Eq+d2Delta152El ≤ (d2LitsStandaloneDelta019.q2 (-1844326498974010421153) 1 (-78)) := by decide +kernel
theorem d2Delta152Check : chebRoundPieceL d2Delta152Fq d2Delta152Ts 16 24 12 20 30 128 d2Delta152Lo d2Delta152Hi d2Delta152Pd d2Delta152Qd d2Delta152Ld d2Delta152Gam (d2LitsStandaloneDelta019.q2 (-1844326498974010421153) 1 (-78)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta152Fq d2Delta152Ts 16 24 12 20 30 128 d2Delta152Lo d2Delta152Hi d2Delta152Pd d2Delta152Qd d2Delta152Ld d2Delta152Gam d2Delta152S d2Delta152Ap d2Delta152Aq d2Delta152Al d2Delta152Es d2Delta152Ep d2Delta152Eq d2Delta152El (by decide +kernel) d2Delta152Shift d2Delta152Plogs d2Delta152Poles d2Delta152Laurent]
  exact decide_eq_true d2Delta152Small
theorem d2Delta152Bound : ∀ x ∈ Icc ((d2Delta152Lo : ℚ) : ℝ) ((d2Delta152Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-1844326498974010421153) 1 (-78)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta152Fq d2Delta152Ts 16 24 12 20 30 128 d2Delta152Lo d2Delta152Hi d2Delta152Pd d2Delta152Qd d2Delta152Ld d2Delta152Gam (d2LitsStandaloneDelta019.q2 (-1844326498974010421153) 1 (-78)) d2Delta152Check
  simpa only [d2Delta152Fq, d2Delta152Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta152Shift
#print axioms d2Delta152Sites
#print axioms d2Delta152PData
#print axioms d2Delta152Plogs
#print axioms d2Delta152Poles
#print axioms d2Delta152Laurent
#print axioms d2Delta152Small
#print axioms d2Delta152Check
#print axioms d2Delta152Bound

def d2Delta153Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta153Ts : List LTerm := laurentClean []
def d2Delta153Lo : ℚ := (d2LitsStandaloneDelta019.q2 (1058027535) 1 (-30))
def d2Delta153Hi : ℚ := (d2LitsStandaloneDelta019.q2 (265292547) 1 (-28))
def d2Delta153Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta153Qd : List (ℚ × ℚ) := []
def d2Delta153Ld : List LaurentPieceData := []
def d2Delta153Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-34837790995654990394634231922783246258838683, 1, -152, 368681214327443407869895893789662775535, 1, -152, -14077203037105159661673984755173876623, 1, -148, -37831005370266696936286275557375244419, 1, -152, 11657471177677623765947196481977751665, 1, -154, 2759022371614463760157502847275296999, 1, -154, 1404126206836825254980698841281227, 1, -150, -17565191997995255850772784891225971, 1, -154, -463539902939124906561325969470063, 1, -153, 26328088417285774666590127401241, 1, -154, 260380299499372564122530565055, 1, -150, 127801533420398440154552585515, 1, -154, -2973852127755584672828040229, 1, -154, -188936935798146966797287873, 1, -153, -423530652975020464113957, 1, -149, -70476004618078017914299, 1, -153, 2349384508750465004323, 1, -152, 306975050124808177677, 1, -153, 675806908272570707, 1, -149, 280715923612241239, 1, -153, 11744699216337841, 1, -154, 206455919412013, 1, -154, 195378705273, 1, -150, 41453809903, 1, -154, 243645791, 1, -153, 5125387, 1, -154, 3037, 1, -150, 417, 1, -154, 3, 1, -154, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta153S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-2076480558627123792932093581545061961, 1, -128, 7236805653188753622137853943407, 1, -126, -14116670897249108224879973942991, 1, -127, -9856571483988318242495738122769, 1, -128, 1371374708636901473140742405263, 1, -128, 687284389627050586242655942163, 1, -128, 14318847563129221675056619931, 1, -128, -8486014672313790526225682085, 1, -127, -1848027018591255164314045405, 1, -128, 47488687672289947551157467, 1, -127, 32048981917161175638231135, 1, -128, 2024855616362113080732197, 1, -128, -331776718171986026443, 1, -120, -22930108895353609820467, 1, -128, -1672415942625978191403, 1, -128, -36939457922669603909, 1, -128, 4399544116258305165, 1, -128, 589181504894218927, 1, -128, 41780429075239627, 1, -128, 1088097262359405, 1, -127, 45609564891861, 1, -127, 1605499143095, 1, -127, 24331084435, 1, -126, 1291431573, 1, -127, 60753655, 1, -128, 319633, 1, -126, 12127, 1, -127, 417, 1, -128, 3, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta153Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta153Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta153Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta153Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta153Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta153Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta153El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta153Shift : polyRoundApx 128 d2Delta153Lo d2Delta153Hi d2Delta153Fq.poly = (d2Delta153S,d2Delta153Es) := by decide +kernel
theorem d2Delta153Sites : mergeSites d2Delta153Fq.plogs = [] := by decide +kernel
theorem d2Delta153PData : d2Delta153Pd = [] := by decide +kernel
theorem d2Delta153Plogs : plogsRoundM 16 24 20 128 d2Delta153Lo d2Delta153Hi (mergeSites d2Delta153Fq.plogs) d2Delta153Pd = some (d2Delta153Ap,d2Delta153Ep) := by
  rw [d2Delta153Sites,d2Delta153PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta153Poles : polesRoundM 16 24 12 128 d2Delta153Lo d2Delta153Hi d2Delta153Fq.poles d2Delta153Qd = some (d2Delta153Aq,d2Delta153Eq) := by decide +kernel
theorem d2Delta153Laurent : laurentRoundM 16 30 128 d2Delta153Lo d2Delta153Hi d2Delta153Ts d2Delta153Ld = some (d2Delta153Al,d2Delta153El) := by decide +kernel
theorem d2Delta153Small : chebPolyUB (vecAdd d2Delta153S (vecAdd d2Delta153Ap (vecAdd d2Delta153Aq d2Delta153Al))) d2Delta153Gam+d2Delta153Es+d2Delta153Ep+d2Delta153Eq+d2Delta153El ≤ (d2LitsStandaloneDelta019.q2 (-3688527326308498720173) 1 (-79)) := by decide +kernel
theorem d2Delta153Check : chebRoundPieceL d2Delta153Fq d2Delta153Ts 16 24 12 20 30 128 d2Delta153Lo d2Delta153Hi d2Delta153Pd d2Delta153Qd d2Delta153Ld d2Delta153Gam (d2LitsStandaloneDelta019.q2 (-3688527326308498720173) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta153Fq d2Delta153Ts 16 24 12 20 30 128 d2Delta153Lo d2Delta153Hi d2Delta153Pd d2Delta153Qd d2Delta153Ld d2Delta153Gam d2Delta153S d2Delta153Ap d2Delta153Aq d2Delta153Al d2Delta153Es d2Delta153Ep d2Delta153Eq d2Delta153El (by decide +kernel) d2Delta153Shift d2Delta153Plogs d2Delta153Poles d2Delta153Laurent]
  exact decide_eq_true d2Delta153Small
theorem d2Delta153Bound : ∀ x ∈ Icc ((d2Delta153Lo : ℚ) : ℝ) ((d2Delta153Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-3688527326308498720173) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta153Fq d2Delta153Ts 16 24 12 20 30 128 d2Delta153Lo d2Delta153Hi d2Delta153Pd d2Delta153Qd d2Delta153Ld d2Delta153Gam (d2LitsStandaloneDelta019.q2 (-3688527326308498720173) 1 (-79)) d2Delta153Check
  simpa only [d2Delta153Fq, d2Delta153Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta153Shift
#print axioms d2Delta153Sites
#print axioms d2Delta153PData
#print axioms d2Delta153Plogs
#print axioms d2Delta153Poles
#print axioms d2Delta153Laurent
#print axioms d2Delta153Small
#print axioms d2Delta153Check
#print axioms d2Delta153Bound

def d2Delta154Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta154Ts : List LTerm := laurentClean []
def d2Delta154Lo : ℚ := (d2LitsStandaloneDelta019.q2 (265292547) 1 (-28))
def d2Delta154Hi : ℚ := (d2LitsStandaloneDelta019.q2 (1062217739) 1 (-30))
def d2Delta154Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta154Qd : List (ℚ × ℚ) := []
def d2Delta154Ld : List LaurentPieceData := []
def d2Delta154Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-544344750413664230277760106620100687072815, 1, -146, -3266892340918165782806730462717248813, 1, -145, -1086524035097318487648144126088207079, 1, -147, 615711463263661738771598618308325, 1, -141, 1852289474282196674008844806310661, 1, -146, -157982841816757232546767406249, 1, -145, -4319959897544627861491424236649, 1, -147, -9258866846829025026924230623, 1, -144, 184918942634918725453811409, 1, -144, 7912395102069235247558021, 1, -144, 1059012091092551407060415, 1, -148, -5780409517229223102411, 1, -146, -359742351538683925927, 1, -147, -978282758403541849, 1, -145, 714062560176209, 1, -148, 351393899119797, 1, -146, 6672850825067, 1, -146, 79803000333, 1, -146, 2904191117, 1, -148, 2689469, 1, -145, 67229, 1, -147, 181, 1, -146, 3, 1, -148, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta154S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-519127087876507270790776871732994097, 1, -126, -25149895868701476158739465281111, 1, -128, -2100718029378944431458687505347, 1, -127, 300656543068035341072085201533, 1, -128, 56923343940237539863015816653, 1, -128, -3409572052976877091241473, 1, -128, -264390633353908030214903621, 1, -128, -9111466709869895583836299, 1, -128, 179936163875821895091295, 1, -127, 15484881659984935995107, 1, -127, 521311500547197338275, 1, -128, -11240122217428588347, 1, -127, -1405257667251268697, 1, -128, -15326772908697677, 1, -127, 2245250512637, 1, -128, 21877379096275, 1, -128, 832473459833, 1, -128, 2490651085, 1, -125, 362687823, 1, -128, 5375137, 1, -128, 16799, 1, -126, 181, 1, -126, 3, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta154Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta154Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta154Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta154Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta154Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta154Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta154El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta154Shift : polyRoundApx 128 d2Delta154Lo d2Delta154Hi d2Delta154Fq.poly = (d2Delta154S,d2Delta154Es) := by decide +kernel
theorem d2Delta154Sites : mergeSites d2Delta154Fq.plogs = [] := by decide +kernel
theorem d2Delta154PData : d2Delta154Pd = [] := by decide +kernel
theorem d2Delta154Plogs : plogsRoundM 16 24 20 128 d2Delta154Lo d2Delta154Hi (mergeSites d2Delta154Fq.plogs) d2Delta154Pd = some (d2Delta154Ap,d2Delta154Ep) := by
  rw [d2Delta154Sites,d2Delta154PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta154Poles : polesRoundM 16 24 12 128 d2Delta154Lo d2Delta154Hi d2Delta154Fq.poles d2Delta154Qd = some (d2Delta154Aq,d2Delta154Eq) := by decide +kernel
theorem d2Delta154Laurent : laurentRoundM 16 30 128 d2Delta154Lo d2Delta154Hi d2Delta154Ts d2Delta154Ld = some (d2Delta154Al,d2Delta154El) := by decide +kernel
theorem d2Delta154Small : chebPolyUB (vecAdd d2Delta154S (vecAdd d2Delta154Ap (vecAdd d2Delta154Aq d2Delta154Al))) d2Delta154Gam+d2Delta154Es+d2Delta154Ep+d2Delta154Eq+d2Delta154El ≤ (d2LitsStandaloneDelta019.q2 (-3688575404108774431699) 1 (-79)) := by decide +kernel
theorem d2Delta154Check : chebRoundPieceL d2Delta154Fq d2Delta154Ts 16 24 12 20 30 128 d2Delta154Lo d2Delta154Hi d2Delta154Pd d2Delta154Qd d2Delta154Ld d2Delta154Gam (d2LitsStandaloneDelta019.q2 (-3688575404108774431699) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta154Fq d2Delta154Ts 16 24 12 20 30 128 d2Delta154Lo d2Delta154Hi d2Delta154Pd d2Delta154Qd d2Delta154Ld d2Delta154Gam d2Delta154S d2Delta154Ap d2Delta154Aq d2Delta154Al d2Delta154Es d2Delta154Ep d2Delta154Eq d2Delta154El (by decide +kernel) d2Delta154Shift d2Delta154Plogs d2Delta154Poles d2Delta154Laurent]
  exact decide_eq_true d2Delta154Small
theorem d2Delta154Bound : ∀ x ∈ Icc ((d2Delta154Lo : ℚ) : ℝ) ((d2Delta154Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-3688575404108774431699) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta154Fq d2Delta154Ts 16 24 12 20 30 128 d2Delta154Lo d2Delta154Hi d2Delta154Pd d2Delta154Qd d2Delta154Ld d2Delta154Gam (d2LitsStandaloneDelta019.q2 (-3688575404108774431699) 1 (-79)) d2Delta154Check
  simpa only [d2Delta154Fq, d2Delta154Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta154Shift
#print axioms d2Delta154Sites
#print axioms d2Delta154PData
#print axioms d2Delta154Plogs
#print axioms d2Delta154Poles
#print axioms d2Delta154Laurent
#print axioms d2Delta154Small
#print axioms d2Delta154Check
#print axioms d2Delta154Bound

def d2Delta155Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta155Ts : List LTerm := laurentClean []
def d2Delta155Lo : ℚ := (d2LitsStandaloneDelta019.q2 (1062217739) 1 (-30))
def d2Delta155Hi : ℚ := (d2LitsStandaloneDelta019.q2 (531632645) 1 (-29))
def d2Delta155Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta155Qd : List (ℚ × ℚ) := []
def d2Delta155Ld : List LaurentPieceData := []
def d2Delta155Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-1088722144998283589526588908769018562747789, 1, -147, -2362652789621144176644037371259295243, 1, -144, -556632776404919500369731917310300045, 1, -148, 46181855411643695420008778109518639, 1, -146, 2524173631933037013236124571748883, 1, -147, -60814207542845017452561588430675, 1, -146, -10733722735368212157074679527755, 1, -148, 390250316995141086627604051, 1, -142, 991315532447933145786513123, 1, -145, 1070581230695970717082365, 1, -141, -1712255016502965867323235, 1, -149, -33385713636288359905099, 1, -147, -1069556681170631868545, 1, -148, -2121126478535110569, 1, -147, 305562994571945611, 1, -149, 498013140211133, 1, -145, 28513595948673, 1, -147, 74777122289, 1, -145, 10033760895, 1, -149, 17540379, 1, -147, 209755, 1, -148, 545, 1, -147, 9, 1, -149, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta155S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-1038286079552031448437174714501281981, 1, -127, -9145222510487314719501553668527, 1, -126, -1100393096684942130858608520871, 1, -128, 88665033029085036232782589681, 1, -125, 39008394267711769132646277497, 1, -128, -928603962875497067858465971, 1, -126, -164752148041876845463790309, 1, -127, 362240195170759817484405, 1, -126, 969119597968592695181229, 1, -128, 8408728417210126662813, 1, -126, -411758341781865231383, 1, -128, -32576132655773979957, 1, -127, -2093143933678550257, 1, -128, -2100558285840155, 1, -125, 593241169244877, 1, -127, 31046412221057, 1, -127, 889639432853, 1, -127, 9336728905, 1, -126, 313292893, 1, -127, 8764467, 1, -128, 26207, 1, -126, 545, 1, -127, 9, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta155Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta155Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta155Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta155Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta155Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta155Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta155El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta155Shift : polyRoundApx 128 d2Delta155Lo d2Delta155Hi d2Delta155Fq.poly = (d2Delta155S,d2Delta155Es) := by decide +kernel
theorem d2Delta155Sites : mergeSites d2Delta155Fq.plogs = [] := by decide +kernel
theorem d2Delta155PData : d2Delta155Pd = [] := by decide +kernel
theorem d2Delta155Plogs : plogsRoundM 16 24 20 128 d2Delta155Lo d2Delta155Hi (mergeSites d2Delta155Fq.plogs) d2Delta155Pd = some (d2Delta155Ap,d2Delta155Ep) := by
  rw [d2Delta155Sites,d2Delta155PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta155Poles : polesRoundM 16 24 12 128 d2Delta155Lo d2Delta155Hi d2Delta155Fq.poles d2Delta155Qd = some (d2Delta155Aq,d2Delta155Eq) := by decide +kernel
theorem d2Delta155Laurent : laurentRoundM 16 30 128 d2Delta155Lo d2Delta155Hi d2Delta155Ts d2Delta155Ld = some (d2Delta155Al,d2Delta155El) := by decide +kernel
theorem d2Delta155Small : chebPolyUB (vecAdd d2Delta155S (vecAdd d2Delta155Ap (vecAdd d2Delta155Aq d2Delta155Al))) d2Delta155Gam+d2Delta155Es+d2Delta155Ep+d2Delta155Eq+d2Delta155El ≤ (d2LitsStandaloneDelta019.q2 (-7377337608295806743519) 1 (-80)) := by decide +kernel
theorem d2Delta155Check : chebRoundPieceL d2Delta155Fq d2Delta155Ts 16 24 12 20 30 128 d2Delta155Lo d2Delta155Hi d2Delta155Pd d2Delta155Qd d2Delta155Ld d2Delta155Gam (d2LitsStandaloneDelta019.q2 (-7377337608295806743519) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta155Fq d2Delta155Ts 16 24 12 20 30 128 d2Delta155Lo d2Delta155Hi d2Delta155Pd d2Delta155Qd d2Delta155Ld d2Delta155Gam d2Delta155S d2Delta155Ap d2Delta155Aq d2Delta155Al d2Delta155Es d2Delta155Ep d2Delta155Eq d2Delta155El (by decide +kernel) d2Delta155Shift d2Delta155Plogs d2Delta155Poles d2Delta155Laurent]
  exact decide_eq_true d2Delta155Small
theorem d2Delta155Bound : ∀ x ∈ Icc ((d2Delta155Lo : ℚ) : ℝ) ((d2Delta155Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-7377337608295806743519) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta155Fq d2Delta155Ts 16 24 12 20 30 128 d2Delta155Lo d2Delta155Hi d2Delta155Pd d2Delta155Qd d2Delta155Ld d2Delta155Gam (d2LitsStandaloneDelta019.q2 (-7377337608295806743519) 1 (-80)) d2Delta155Check
  simpa only [d2Delta155Fq, d2Delta155Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta155Shift
#print axioms d2Delta155Sites
#print axioms d2Delta155PData
#print axioms d2Delta155Plogs
#print axioms d2Delta155Poles
#print axioms d2Delta155Laurent
#print axioms d2Delta155Small
#print axioms d2Delta155Check
#print axioms d2Delta155Bound

def d2Delta156Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta156Ts : List LTerm := laurentClean []
def d2Delta156Lo : ℚ := (d2LitsStandaloneDelta019.q2 (531632645) 1 (-29))
def d2Delta156Hi : ℚ := (d2LitsStandaloneDelta019.q2 (133170049) 1 (-27))
def d2Delta156Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta156Qd : List (ℚ × ℚ) := []
def d2Delta156Ld : List LaurentPieceData := []
def d2Delta156Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-4355069395379295298246758738516309656525043, 1, -149, -166087599513537057507743257536891399947, 1, -150, 48677659973760167533038728597891634509, 1, -150, 1356776643476246245462116942636738945, 1, -148, -27967100115249605418320837138077991, 1, -146, -7748935349307149924098812038883491, 1, -147, 542655695095350147783206927504039, 1, -152, 1070358401952158106591039606746823, 1, -152, 10878793014529693708173005257353, 1, -150, -837395399364959799281419396685, 1, -152, -127131126108698279589860486597, 1, -152, -68065792982455384111988693, 1, -146, -619291604677028232437039, 1, -147, 547232498527481284104439, 1, -149, 114901793053372426896191, 1, -151, 3552021619260431640719, 1, -151, 20332177928397153211, 1, -149, 1490348718553591351, 1, -151, 22736849578566647, 1, -151, 73979972335295, 1, -149, 208862738813, 1, -147, 2072666591, 1, -147, 584152957, 1, -152, 4603221, 1, -152, 8167, 1, -150, 209, 1, -152, 1, 1, -152, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta156S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-2076670626644353760157647361401594159, 1, -128, -21777242618629167355981090682959, 1, -127, 12032652020781875762381288633723, 1, -127, 5474869215729096526747880008567, 1, -128, -427311345022889543413245458855, 1, -127, -30455674343700602496141696729, 1, -125, 90640552621230224394892971, 1, -126, 4111109190066233012882203005, 1, -128, 42710652381737410835827651, 1, -125, -3010537990694515122046701, 1, -126, -1935969245197864252926679, 1, -127, -269316704301629159491381, 1, -128, -2809776610908461237445, 1, -128, 521442095856756144881, 1, -127, 110941016082321469651, 1, -128, 6888145779898711063, 1, -128, 158046906641033455, 1, -127, 5799736349153177, 1, -127, 11069372324857, 1, -123, 9225750079817, 1, -128, 208461390853, 1, -128, 1034679911, 1, -126, 72921153, 1, -128, 1149499, 1, -128, 16321, 1, -128, 209, 1, -128, 1, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta156Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta156Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta156Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta156Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta156Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta156Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta156El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta156Shift : polyRoundApx 128 d2Delta156Lo d2Delta156Hi d2Delta156Fq.poly = (d2Delta156S,d2Delta156Es) := by decide +kernel
theorem d2Delta156Sites : mergeSites d2Delta156Fq.plogs = [] := by decide +kernel
theorem d2Delta156PData : d2Delta156Pd = [] := by decide +kernel
theorem d2Delta156Plogs : plogsRoundM 16 24 20 128 d2Delta156Lo d2Delta156Hi (mergeSites d2Delta156Fq.plogs) d2Delta156Pd = some (d2Delta156Ap,d2Delta156Ep) := by
  rw [d2Delta156Sites,d2Delta156PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta156Poles : polesRoundM 16 24 12 128 d2Delta156Lo d2Delta156Hi d2Delta156Fq.poles d2Delta156Qd = some (d2Delta156Aq,d2Delta156Eq) := by decide +kernel
theorem d2Delta156Laurent : laurentRoundM 16 30 128 d2Delta156Lo d2Delta156Hi d2Delta156Ts d2Delta156Ld = some (d2Delta156Al,d2Delta156El) := by decide +kernel
theorem d2Delta156Small : chebPolyUB (vecAdd d2Delta156S (vecAdd d2Delta156Ap (vecAdd d2Delta156Aq d2Delta156Al))) d2Delta156Gam+d2Delta156Es+d2Delta156Ep+d2Delta156Eq+d2Delta156El ≤ (d2LitsStandaloneDelta019.q2 (-3688793794428383916327) 1 (-79)) := by decide +kernel
theorem d2Delta156Check : chebRoundPieceL d2Delta156Fq d2Delta156Ts 16 24 12 20 30 128 d2Delta156Lo d2Delta156Hi d2Delta156Pd d2Delta156Qd d2Delta156Ld d2Delta156Gam (d2LitsStandaloneDelta019.q2 (-3688793794428383916327) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta156Fq d2Delta156Ts 16 24 12 20 30 128 d2Delta156Lo d2Delta156Hi d2Delta156Pd d2Delta156Qd d2Delta156Ld d2Delta156Gam d2Delta156S d2Delta156Ap d2Delta156Aq d2Delta156Al d2Delta156Es d2Delta156Ep d2Delta156Eq d2Delta156El (by decide +kernel) d2Delta156Shift d2Delta156Plogs d2Delta156Poles d2Delta156Laurent]
  exact decide_eq_true d2Delta156Small
theorem d2Delta156Bound : ∀ x ∈ Icc ((d2Delta156Lo : ℚ) : ℝ) ((d2Delta156Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-3688793794428383916327) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta156Fq d2Delta156Ts 16 24 12 20 30 128 d2Delta156Lo d2Delta156Hi d2Delta156Pd d2Delta156Qd d2Delta156Ld d2Delta156Gam (d2LitsStandaloneDelta019.q2 (-3688793794428383916327) 1 (-79)) d2Delta156Check
  simpa only [d2Delta156Fq, d2Delta156Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta156Shift
#print axioms d2Delta156Sites
#print axioms d2Delta156PData
#print axioms d2Delta156Plogs
#print axioms d2Delta156Poles
#print axioms d2Delta156Laurent
#print axioms d2Delta156Small
#print axioms d2Delta156Check
#print axioms d2Delta156Bound

def d2Delta157Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta157Ts : List LTerm := laurentClean []
def d2Delta157Lo : ℚ := (d2LitsStandaloneDelta019.q2 (133170049) 1 (-27))
def d2Delta157Hi : ℚ := (d2LitsStandaloneDelta019.q2 (2133863437) 1 (-31))
def d2Delta157Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta157Qd : List (ℚ × ℚ) := []
def d2Delta157Ld : List LaurentPieceData := []
def d2Delta157Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-2177523851047621724494703225278829640401951, 1, -148, 93683821666307669015496149568085773883, 1, -149, 3631716322352091841471552452106974221, 1, -147, -1383645064047648819790628294030963259, 1, -149, -20451789162124058356366300139452565, 1, -146, 3031551381057728445117051477095519, 1, -149, 187514202943461145093993993779299, 1, -147, 18084596607449232800297687306785, 1, -149, -996735614392992609427625070583, 1, -149, -142992227330515018720033101791, 1, -150, -741686809204563372180694293, 1, -148, 46035579575422978892462431, 1, -150, 618982593403004439699327, 1, -147, 177321999048676729706165, 1, -150, 1059095329296570769253, 1, -148, 77261954469247534155, 1, -150, 284853760903300631, 1, -148, 14039541919955983, 1, -150, 36923713770193, 1, -148, 1347450756337, 1, -150, 1348732075, 1, -147, 76569267, 1, -150, 121343, 1, -148, 2765, 1, -150, 7, 1, -149, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta157S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-2076655575430821521706602859005653225, 1, -128, 23329207272401472404272577329975, 1, -127, 14484490360735666202167354164883, 1, -128, -666879410962632904414815848575, 1, -126, -641382272536028894374869597617, 1, -128, 22148338725956059450410063689, 1, -128, 11565834074867365566701935173, 1, -128, 571565570051493809672800477, 1, -128, -59922401270317944712300249, 1, -128, -8757758423450968953586543, 1, -128, -369365694007272197477673, 1, -128, 5339030878972679259791, 1, -127, 597249734781630308927, 1, -126, 172035878458297677603, 1, -128, 2059653616535076927, 1, -126, 150436498039535697, 1, -127, 8880924765256755, 1, -128, 109484022059001, 1, -127, 288045233145, 1, -124, 84115214855, 1, -128, 1347397743, 1, -128, 9563209, 1, -127, 121259, 1, -127, 2765, 1, -128, 7, 1, -126, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta157Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta157Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta157Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta157Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta157Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta157Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta157El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta157Shift : polyRoundApx 128 d2Delta157Lo d2Delta157Hi d2Delta157Fq.poly = (d2Delta157S,d2Delta157Es) := by decide +kernel
theorem d2Delta157Sites : mergeSites d2Delta157Fq.plogs = [] := by decide +kernel
theorem d2Delta157PData : d2Delta157Pd = [] := by decide +kernel
theorem d2Delta157Plogs : plogsRoundM 16 24 20 128 d2Delta157Lo d2Delta157Hi (mergeSites d2Delta157Fq.plogs) d2Delta157Pd = some (d2Delta157Ap,d2Delta157Ep) := by
  rw [d2Delta157Sites,d2Delta157PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta157Poles : polesRoundM 16 24 12 128 d2Delta157Lo d2Delta157Hi d2Delta157Fq.poles d2Delta157Qd = some (d2Delta157Aq,d2Delta157Eq) := by decide +kernel
theorem d2Delta157Laurent : laurentRoundM 16 30 128 d2Delta157Lo d2Delta157Hi d2Delta157Ts d2Delta157Ld = some (d2Delta157Al,d2Delta157El) := by decide +kernel
theorem d2Delta157Small : chebPolyUB (vecAdd d2Delta157S (vecAdd d2Delta157Ap (vecAdd d2Delta157Aq d2Delta157Al))) d2Delta157Gam+d2Delta157Es+d2Delta157Ep+d2Delta157Eq+d2Delta157El ≤ (d2LitsStandaloneDelta019.q2 (-3688775918722664081163) 1 (-79)) := by decide +kernel
theorem d2Delta157Check : chebRoundPieceL d2Delta157Fq d2Delta157Ts 16 24 12 20 30 128 d2Delta157Lo d2Delta157Hi d2Delta157Pd d2Delta157Qd d2Delta157Ld d2Delta157Gam (d2LitsStandaloneDelta019.q2 (-3688775918722664081163) 1 (-79)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta157Fq d2Delta157Ts 16 24 12 20 30 128 d2Delta157Lo d2Delta157Hi d2Delta157Pd d2Delta157Qd d2Delta157Ld d2Delta157Gam d2Delta157S d2Delta157Ap d2Delta157Aq d2Delta157Al d2Delta157Es d2Delta157Ep d2Delta157Eq d2Delta157El (by decide +kernel) d2Delta157Shift d2Delta157Plogs d2Delta157Poles d2Delta157Laurent]
  exact decide_eq_true d2Delta157Small
theorem d2Delta157Bound : ∀ x ∈ Icc ((d2Delta157Lo : ℚ) : ℝ) ((d2Delta157Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-3688775918722664081163) 1 (-79)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta157Fq d2Delta157Ts 16 24 12 20 30 128 d2Delta157Lo d2Delta157Hi d2Delta157Pd d2Delta157Qd d2Delta157Ld d2Delta157Gam (d2LitsStandaloneDelta019.q2 (-3688775918722664081163) 1 (-79)) d2Delta157Check
  simpa only [d2Delta157Fq, d2Delta157Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta157Shift
#print axioms d2Delta157Sites
#print axioms d2Delta157PData
#print axioms d2Delta157Plogs
#print axioms d2Delta157Poles
#print axioms d2Delta157Laurent
#print axioms d2Delta157Small
#print axioms d2Delta157Check
#print axioms d2Delta157Bound

def d2Delta158Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta158Ts : List LTerm := laurentClean []
def d2Delta158Lo : ℚ := (d2LitsStandaloneDelta019.q2 (2133863437) 1 (-31))
def d2Delta158Hi : ℚ := (d2LitsStandaloneDelta019.q2 (533727747) 1 (-29))
def d2Delta158Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta158Qd : List (ℚ × ℚ) := []
def d2Delta158Ld : List LaurentPieceData := []
def d2Delta158Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-34022619698425086896658584496029575175253, 1, -142, 1424578351585519947280948481577892053, 1, -144, -3517585399816701497368871143423919, 1, -143, -3085217905333368321768812061497147, 1, -144, -974686028593443425269898087511, 1, -140, 1045787211120317901723619288525, 1, -143, 8374022372061038233428585297, 1, -142, -167364244001049627892854471, 1, -143, -904756236254992923850639, 1, -140, -70885573124989197580063, 1, -143, 117516432446085783473, 1, -142, 14719858208895355117, 1, -143, 26689783421504919, 1, -140, 7944841618621783, 1, -145, 27697317818043, 1, -144, 308585377487, 1, -145, 177911185, 1, -142, 5563679, 1, -145, 9371, 1, -144, 55, 1, -145, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta158S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-2076575802217987594250245681830766059, 1, -128, 10939365123866687067706876368553, 1, -127, -106391741903208857201834046239, 1, -127, -23618167567357256467758118811, 1, -125, -1928252263168776172016662701, 1, -128, 511209397355851197977985587, 1, -128, 8206033860098970977018145, 1, -127, -325635989216753208107165, 1, -128, -14141384163301583110995, 1, -127, -555057519397067875875, 1, -128, 3632370498518744459, 1, -128, 229594444002985391, 1, -127, 6666388223446289, 1, -127, 124065835937511, 1, -127, 3460741595911, 1, -128, 38561350413, 1, -128, 355738031, 1, -128, 2781317, 1, -128, 9371, 1, -127, 55, 1, -127, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta158Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta158Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta158Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta158Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta158Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta158Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta158El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta158Shift : polyRoundApx 128 d2Delta158Lo d2Delta158Hi d2Delta158Fq.poly = (d2Delta158S,d2Delta158Es) := by decide +kernel
theorem d2Delta158Sites : mergeSites d2Delta158Fq.plogs = [] := by decide +kernel
theorem d2Delta158PData : d2Delta158Pd = [] := by decide +kernel
theorem d2Delta158Plogs : plogsRoundM 16 24 20 128 d2Delta158Lo d2Delta158Hi (mergeSites d2Delta158Fq.plogs) d2Delta158Pd = some (d2Delta158Ap,d2Delta158Ep) := by
  rw [d2Delta158Sites,d2Delta158PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta158Poles : polesRoundM 16 24 12 128 d2Delta158Lo d2Delta158Hi d2Delta158Fq.poles d2Delta158Qd = some (d2Delta158Aq,d2Delta158Eq) := by decide +kernel
theorem d2Delta158Laurent : laurentRoundM 16 30 128 d2Delta158Lo d2Delta158Hi d2Delta158Ts d2Delta158Ld = some (d2Delta158Al,d2Delta158El) := by decide +kernel
theorem d2Delta158Small : chebPolyUB (vecAdd d2Delta158S (vecAdd d2Delta158Ap (vecAdd d2Delta158Aq d2Delta158Al))) d2Delta158Gam+d2Delta158Es+d2Delta158Ep+d2Delta158Eq+d2Delta158El ≤ (d2LitsStandaloneDelta019.q2 (-7377401862000940515285) 1 (-80)) := by decide +kernel
theorem d2Delta158Check : chebRoundPieceL d2Delta158Fq d2Delta158Ts 16 24 12 20 30 128 d2Delta158Lo d2Delta158Hi d2Delta158Pd d2Delta158Qd d2Delta158Ld d2Delta158Gam (d2LitsStandaloneDelta019.q2 (-7377401862000940515285) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta158Fq d2Delta158Ts 16 24 12 20 30 128 d2Delta158Lo d2Delta158Hi d2Delta158Pd d2Delta158Qd d2Delta158Ld d2Delta158Gam d2Delta158S d2Delta158Ap d2Delta158Aq d2Delta158Al d2Delta158Es d2Delta158Ep d2Delta158Eq d2Delta158El (by decide +kernel) d2Delta158Shift d2Delta158Plogs d2Delta158Poles d2Delta158Laurent]
  exact decide_eq_true d2Delta158Small
theorem d2Delta158Bound : ∀ x ∈ Icc ((d2Delta158Lo : ℚ) : ℝ) ((d2Delta158Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-7377401862000940515285) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta158Fq d2Delta158Ts 16 24 12 20 30 128 d2Delta158Lo d2Delta158Hi d2Delta158Pd d2Delta158Qd d2Delta158Ld d2Delta158Gam (d2LitsStandaloneDelta019.q2 (-7377401862000940515285) 1 (-80)) d2Delta158Check
  simpa only [d2Delta158Fq, d2Delta158Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta158Shift
#print axioms d2Delta158Sites
#print axioms d2Delta158PData
#print axioms d2Delta158Plogs
#print axioms d2Delta158Poles
#print axioms d2Delta158Laurent
#print axioms d2Delta158Small
#print axioms d2Delta158Check
#print axioms d2Delta158Bound

def d2Delta159Fq : FieldQ := fieldClean d2DeltaRawFq
def d2Delta159Ts : List LTerm := laurentClean []
def d2Delta159Lo : ℚ := (d2LitsStandaloneDelta019.q2 (533727747) 1 (-29))
def d2Delta159Hi : ℚ := (d2LitsStandaloneDelta019.q2 (4270869527) 1 (-32))
def d2Delta159Pd : List (ℚ × (List ℚ × List ℚ)) := []
def d2Delta159Qd : List (ℚ × ℚ) := []
def d2Delta159Ld : List LaurentPieceData := []
def d2Delta159Gam : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-34022100828936524687801033348960923364735, 1, -142, 326326759115947854523718936353193025, 1, -143, -136963490783860479570365494184409, 1, -138, -96141213731279026171102189387741, 1, -142, 38637773188158551330920768301, 1, -139, 20401027126679430787045851921, 1, -142, 5520890602833893758781415, 1, -138, -353954361131662900731255, 1, -140, -4388523558434172358187, 1, -140, -27023804361742749869, 1, -141, 26291156869126097, 1, -138, 5840037646220675, 1, -142, 4625594853371, 1, -139, 161459707241, 1, -142, 33809953, 1, -138, 5860285, 1, -144, 3307, 1, -142, 25, 1, -144, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta159S : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [-2076544106275125629414810303345225119, 1, -128, 9976312574109718832793972453051, 1, -128, -133828824828775995838461074013, 1, -127, -11748442222501818511850266201, 1, -127, 150669838332266915044474379, 1, -128, 19932555067437527637218523, 1, -128, 86401071404409830486089, 1, -127, -2764317888889982138227, 1, -127, -68587104768329578951, 1, -127, -422748739399342541, 1, -127, 13131702951649749, 1, -128, 45608896889689, 1, -125, 2312324108839, 1, -127, 40359432979, 1, -128, 16903323, 1, -124, 1464965, 1, -128, 3307, 1, -127, 25, 1, -128, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0])
def d2Delta159Ap : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta159Aq : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta159Al : List ℚ := d2LitsStandaloneDelta019.q2listC (raw_ints% [])
def d2Delta159Es : ℚ := (d2LitsStandaloneDelta019.q2 (61) 1 (-127))
def d2Delta159Ep : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta159Eq : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
def d2Delta159El : ℚ := (d2LitsStandaloneDelta019.q2 (0) 1 (0))
/-- kcost: one root shift, followed by normalization and dyadic rounding. -/
theorem d2Delta159Shift : polyRoundApx 128 d2Delta159Lo d2Delta159Hi d2Delta159Fq.poly = (d2Delta159S,d2Delta159Es) := by decide +kernel
theorem d2Delta159Sites : mergeSites d2Delta159Fq.plogs = [] := by decide +kernel
theorem d2Delta159PData : d2Delta159Pd = [] := by decide +kernel
theorem d2Delta159Plogs : plogsRoundM 16 24 20 128 d2Delta159Lo d2Delta159Hi (mergeSites d2Delta159Fq.plogs) d2Delta159Pd = some (d2Delta159Ap,d2Delta159Ep) := by
  rw [d2Delta159Sites,d2Delta159PData]
  simp only [plogsRoundM]
  decide +kernel
theorem d2Delta159Poles : polesRoundM 16 24 12 128 d2Delta159Lo d2Delta159Hi d2Delta159Fq.poles d2Delta159Qd = some (d2Delta159Aq,d2Delta159Eq) := by decide +kernel
theorem d2Delta159Laurent : laurentRoundM 16 30 128 d2Delta159Lo d2Delta159Hi d2Delta159Ts d2Delta159Ld = some (d2Delta159Al,d2Delta159El) := by decide +kernel
theorem d2Delta159Small : chebPolyUB (vecAdd d2Delta159S (vecAdd d2Delta159Ap (vecAdd d2Delta159Aq d2Delta159Al))) d2Delta159Gam+d2Delta159Es+d2Delta159Ep+d2Delta159Eq+d2Delta159El ≤ (d2LitsStandaloneDelta019.q2 (-7377331249726317625595) 1 (-80)) := by decide +kernel
theorem d2Delta159Check : chebRoundPieceL d2Delta159Fq d2Delta159Ts 16 24 12 20 30 128 d2Delta159Lo d2Delta159Hi d2Delta159Pd d2Delta159Qd d2Delta159Ld d2Delta159Gam (d2LitsStandaloneDelta019.q2 (-7377331249726317625595) 1 (-80)) = true := by
  unfold chebRoundPieceL
  rw [roundMergeUBL_of_parts d2Delta159Fq d2Delta159Ts 16 24 12 20 30 128 d2Delta159Lo d2Delta159Hi d2Delta159Pd d2Delta159Qd d2Delta159Ld d2Delta159Gam d2Delta159S d2Delta159Ap d2Delta159Aq d2Delta159Al d2Delta159Es d2Delta159Ep d2Delta159Eq d2Delta159El (by decide +kernel) d2Delta159Shift d2Delta159Plogs d2Delta159Poles d2Delta159Laurent]
  exact decide_eq_true d2Delta159Small
theorem d2Delta159Bound : ∀ x ∈ Icc ((d2Delta159Lo : ℚ) : ℝ) ((d2Delta159Hi : ℚ) : ℝ), fieldTower d2DeltaRawFq (poleF d2DeltaRawFq.poles) 0 x+lfieldTower [] 0 x ≤ ((d2LitsStandaloneDelta019.q2 (-7377331249726317625595) 1 (-80)) : ℝ) := by
  have h := chebRoundPieceL_sound d2Delta159Fq d2Delta159Ts 16 24 12 20 30 128 d2Delta159Lo d2Delta159Hi d2Delta159Pd d2Delta159Qd d2Delta159Ld d2Delta159Gam (d2LitsStandaloneDelta019.q2 (-7377331249726317625595) 1 (-80)) d2Delta159Check
  simpa only [d2Delta159Fq, d2Delta159Ts, fieldClean_sound, laurentClean_sound, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] using h
#print axioms d2Delta159Shift
#print axioms d2Delta159Sites
#print axioms d2Delta159PData
#print axioms d2Delta159Plogs
#print axioms d2Delta159Poles
#print axioms d2Delta159Laurent
#print axioms d2Delta159Small
#print axioms d2Delta159Check
#print axioms d2Delta159Bound

end StandaloneDelta019
end CatalanMeasure.GenD.Signed.Data.Cells
