module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearLogCache011
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearLogCache011
open D72.LogTransfer
def d2Log176Q : ℚ := (d2LitsNearLogCache011.q2 (2047) 1 (-10))
def d2Log176V : ℚ := (d2LitsNearLogCache011.q2 (22804303202042520325688915844346460579992912637198636025896618576995081373445849148802854803671456953422804153262002463581843737504868917728059581559987165731431) 1548025109046995746135074291673120223985398108996635409357288885854289350473439289655423409303061008372884335494132437806525 (-124))
def d2Log176E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log176Lo : ℚ := (d2LitsNearLogCache011.q2 (117849784574005720502559470782022550697) 1 (-127))
def d2Log176Hi : ℚ := (d2LitsNearLogCache011.q2 (235699569148011441005118941564045101399) 1 (-128))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log176Eval : logQ 16 d2Log176Q = some (d2Log176V,d2Log176E) := by decide +kernel
theorem d2Log176Bounds : ((d2Log176Lo : ℚ):ℝ) ≤ Real.log ((d2Log176Q:ℚ):ℝ) ∧ Real.log ((d2Log176Q:ℚ):ℝ) ≤ ((d2Log176Hi:ℚ):ℝ) := log_interval d2Log176Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log176Eval
#print axioms d2Log176Bounds
def d2Log177Q : ℚ := (d2LitsNearLogCache011.q2 (4095) 1 (-11))
def d2Log177V : ℚ := (d2LitsNearLogCache011.q2 (1202185863347262099734733034954986106607849412780485406331874643980042606542916021953762763081037255139635215876864957894515727728946607010398857) 81579249640871598507455108313433485570773333951440667092935660803549442828761516154738598997585587750403475 (-124))
def d2Log177E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log177Lo : ℚ := (d2LitsNearLogCache011.q2 (235782676332921046060508772343518835487) 1 (-128))
def d2Log177Hi : ℚ := (d2LitsNearLogCache011.q2 (58945669083230261515127193085879708873) 1 (-126))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log177Eval : logQ 16 d2Log177Q = some (d2Log177V,d2Log177E) := by decide +kernel
theorem d2Log177Bounds : ((d2Log177Lo : ℚ):ℝ) ≤ Real.log ((d2Log177Q:ℚ):ℝ) ∧ Real.log ((d2Log177Q:ℚ):ℝ) ≤ ((d2Log177Hi:ℚ):ℝ) := log_interval d2Log177Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log177Eval
#print axioms d2Log177Bounds
def d2Log178Q : ℚ := (d2LitsNearLogCache011.q2 (8191) 1 (-12))
def d2Log178V : ℚ := (d2LitsNearLogCache011.q2 (325604769887175935390044843612870631727632411703878904732735521280414539263032349591170117076883642917141452419687635373073818726284922512708814581332699896139762950525867783863) 22091353750900963743259904126380601984290579679584509339455906747333761263671399084320614618842694943750556200591786474416450650890773410861 (-124))
def d2Log178E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log178Lo : ℚ := (d2LitsNearLogCache011.q2 (29478027789392184103658175691507326025) 1 (-125))
def d2Log178Hi : ℚ := (d2LitsNearLogCache011.q2 (235824222315137472829265405532058608205) 1 (-128))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log178Eval : logQ 16 d2Log178Q = some (d2Log178V,d2Log178E) := by decide +kernel
theorem d2Log178Bounds : ((d2Log178Lo : ℚ):ℝ) ≤ Real.log ((d2Log178Q:ℚ):ℝ) ∧ Real.log ((d2Log178Q:ℚ):ℝ) ≤ ((d2Log178Hi:ℚ):ℝ) := log_interval d2Log178Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log178Eval
#print axioms d2Log178Bounds
def d2Log179Q : ℚ := (d2LitsNearLogCache011.q2 (16383) 1 (-13))
def d2Log179V : ℚ := (d2LitsNearLogCache011.q2 (7925297606000858919903661654807276938036127084937940418463774637171505350653206309891976913882648130265784087830744279453032630622370647045653515890392910201700806341079895612417084491399) 537661452404359057990896084776827019070725502706510489947063033676627050673055784721901403896250782903714498298518752377195994933135807514190673828125 (-124))
def d2Log179E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log179Lo : ℚ := (d2LitsNearLogCache011.q2 (117922496702114031557590469108299774923) 1 (-127))
def d2Log179Hi : ℚ := (d2LitsNearLogCache011.q2 (235844993404228063115180938216599549851) 1 (-128))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log179Eval : logQ 16 d2Log179Q = some (d2Log179V,d2Log179E) := by decide +kernel
theorem d2Log179Bounds : ((d2Log179Lo : ℚ):ℝ) ≤ Real.log ((d2Log179Q:ℚ):ℝ) ∧ Real.log ((d2Log179Q:ℚ):ℝ) ≤ ((d2Log179Hi:ℚ):ℝ) := log_interval d2Log179Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log179Eval
#print axioms d2Log179Bounds
def d2Log180Q : ℚ := (d2LitsNearLogCache011.q2 (32767) 1 (-14))
def d2Log180V : ℚ := (d2LitsNearLogCache011.q2 (442558679579240378708402198593188344944889222996655651823057801680783378283865431903148792498042727947268649642602334545871964880948220901341090114754761978995773966646211) 30022376081062499122518733450461191857939124999348565690982937630010421528330819024908039089922916517383807768999576050496097564311025 (-124))
def d2Log180E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log180Lo : ℚ := (d2LitsNearLogCache011.q2 (58963844618334168894545997448193064043) 1 (-126))
def d2Log180Hi : ℚ := (d2LitsNearLogCache011.q2 (235855378473336675578183989792772256177) 1 (-128))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log180Eval : logQ 16 d2Log180Q = some (d2Log180V,d2Log180E) := by decide +kernel
theorem d2Log180Bounds : ((d2Log180Lo : ℚ):ℝ) ≤ Real.log ((d2Log180Q:ℚ):ℝ) ∧ Real.log ((d2Log180Q:ℚ):ℝ) ≤ ((d2Log180Hi:ℚ):ℝ) := log_interval d2Log180Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log180Eval
#print axioms d2Log180Bounds
def d2Log181Q : ℚ := (d2LitsNearLogCache011.q2 (65535) 1 (-15))
def d2Log181V : ℚ := (d2LitsNearLogCache011.q2 (28347459988160300810520272976125827827037997875836002971225853512191660501101160276082568426439636879595319697915932700377614798563355344494558077891531720791318679759306135031889662346246189522970669251132497) 1922997803748809377328876973838541128143202774675647478941176141378016289978277126090252240961803408159731513768054568160328665981344790789618423589807092457558029727010475 (-124))
def d2Log181E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log181Lo : ℚ := (d2LitsNearLogCache011.q2 (235860570889040275073298496280523153127) 1 (-128))
def d2Log181Hi : ℚ := (d2LitsNearLogCache011.q2 (58965142722260068768324624070130788283) 1 (-126))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log181Eval : logQ 16 d2Log181Q = some (d2Log181V,d2Log181E) := by decide +kernel
theorem d2Log181Bounds : ((d2Log181Lo : ℚ):ℝ) ≤ Real.log ((d2Log181Q:ℚ):ℝ) ∧ Real.log ((d2Log181Q:ℚ):ℝ) ≤ ((d2Log181Hi:ℚ):ℝ) := log_interval d2Log181Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log181Eval
#print axioms d2Log181Bounds
def d2Log182Q : ℚ := (d2LitsNearLogCache011.q2 (131071) 1 (-16))
def d2Log182V : ℚ := (d2LitsNearLogCache011.q2 (5305758896716440713751348105448762680728899254004687553787074672632871468084060572935037670649998829940559171884913723091205656229950328347423045916240044856143337376580163348060238058319758931298054717790473549387) 359921150059362106426046429028006303105978045741396139390184672752272728566073365898872305648900092751162201690956600068742617288174290826126648535831846605551590542646738762569 (-124))
def d2Log182E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log182Lo : ℚ := (d2LitsNearLogCache011.q2 (235863167067180456037649452571866433397) 1 (-128))
def d2Log182Hi : ℚ := (d2LitsNearLogCache011.q2 (117931583533590228018824726285933216701) 1 (-127))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log182Eval : logQ 16 d2Log182Q = some (d2Log182V,d2Log182E) := by decide +kernel
theorem d2Log182Bounds : ((d2Log182Lo : ℚ):ℝ) ≤ Real.log ((d2Log182Q:ℚ):ℝ) ∧ Real.log ((d2Log182Q:ℚ):ℝ) ≤ ((d2Log182Hi:ℚ):ℝ) := log_interval d2Log182Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log182Eval
#print axioms d2Log182Bounds
def d2Log183Q : ℚ := (d2LitsNearLogCache011.q2 (262143) 1 (-17))
def d2Log183V : ℚ := (d2LitsNearLogCache011.q2 (817282523302027667292451825135876023788308362408074976694932080333144915754314135431322454606935000759388634956231449598961605394613127043457) 55440824308068557114796372908358884434714205961402685248258568988244388009434260311536490917205810546875 (-124))
def d2Log183E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log183Lo : ℚ := (d2LitsNearLogCache011.q2 (235864465148822774055959591310595074527) 1 (-128))
def d2Log183Hi : ℚ := (d2LitsNearLogCache011.q2 (58966116287205693513989897827648768633) 1 (-126))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log183Eval : logQ 16 d2Log183Q = some (d2Log183V,d2Log183E) := by decide +kernel
theorem d2Log183Bounds : ((d2Log183Lo : ℚ):ℝ) ≤ Real.log ((d2Log183Q:ℚ):ℝ) ∧ Real.log ((d2Log183Q:ℚ):ℝ) ≤ ((d2Log183Hi:ℚ):ℝ) := log_interval d2Log183Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log183Eval
#print axioms d2Log183Bounds
def d2Log184Q : ℚ := (d2LitsNearLogCache011.q2 (524287) 1 (-18))
def d2Log184V : ℚ := (d2LitsNearLogCache011.q2 (30498883039523813049225643621793769050281201746982771643305142524314400971365557790281355512187182725801378285355740075092055891740563127898004062994565423920492472019291860797854475576127998173602253799421987413589537778110374309751) 2068903365861336488365527876507426233200731549957860944779323054053083571499388452742154765917415729284935199369372940697183014085360866017527456031938836997354266961554104032417567799647734204525 (-124))
def d2Log184E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log184Lo : ℚ := (d2LitsNearLogCache011.q2 (235865114187787006477785679934764735217) 1 (-128))
def d2Log184Hi : ℚ := (d2LitsNearLogCache011.q2 (117932557093893503238892839967382367611) 1 (-127))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log184Eval : logQ 16 d2Log184Q = some (d2Log184V,d2Log184E) := by decide +kernel
theorem d2Log184Bounds : ((d2Log184Lo : ℚ):ℝ) ≤ Real.log ((d2Log184Q:ℚ):ℝ) ∧ Real.log ((d2Log184Q:ℚ):ℝ) ≤ ((d2Log184Hi:ℚ):ℝ) := log_interval d2Log184Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log184Eval
#print axioms d2Log184Bounds
def d2Log185Q : ℚ := (d2LitsNearLogCache011.q2 (1048575) 1 (-19))
def d2Log185V : ℚ := (d2LitsNearLogCache011.q2 (26218698576873008600587039925968467851584277416972236993757445970810736788871327575344795445039207806398196941061623342803241876252975830069735189224815105194783194243688093801647062979223848929289449335518246447856212589652014862485353867199319) 1778552972957734459048725581221698900675471223635326512264956973288452432311241284800390408602583231991863301146453045480760976700810882663529438624952502702030210372746782331225408711054658870939577832365325 (-124))
def d2Log185E : ℚ := (d2LitsNearLogCache011.q2 (748285983818036882200524517778798007073564696510465) 262143 (-278))
def d2Log185Lo : ℚ := (d2LitsNearLogCache011.q2 (235865438706804893107923981645189377529) 1 (-128))
def d2Log185Hi : ℚ := (d2LitsNearLogCache011.q2 (117932719353402446553961990822594688767) 1 (-127))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log185Eval : logQ 16 d2Log185Q = some (d2Log185V,d2Log185E) := by decide +kernel
theorem d2Log185Bounds : ((d2Log185Lo : ℚ):ℝ) ≤ Real.log ((d2Log185Q:ℚ):ℝ) ∧ Real.log ((d2Log185Q:ℚ):ℝ) ≤ ((d2Log185Hi:ℚ):ℝ) := log_interval d2Log185Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log185Eval
#print axioms d2Log185Bounds
def d2Log186Q : ℚ := (d2LitsNearLogCache011.q2 (1) 1 (1))
def d2Log186V : ℚ := (d2LitsNearLogCache011.q2 (235865763225513294137944142764154484399) 1 (-128))
def d2Log186E : ℚ := (d2LitsNearLogCache011.q2 (1496571967636073764401049035557596014147129393020929) 262143 (-278))
def d2Log186Lo : ℚ := (d2LitsNearLogCache011.q2 (117932881612756647068972071382077242197) 1 (-127))
def d2Log186Hi : ℚ := (d2LitsNearLogCache011.q2 (58966440806378323534486035691038621101) 1 (-126))
-- kcost: one shared-node rational log at n16; per-log declaration, outward dyadic endpoints.
theorem d2Log186Eval : logQ 16 d2Log186Q = some (d2Log186V,d2Log186E) := by decide +kernel
theorem d2Log186Bounds : ((d2Log186Lo : ℚ):ℝ) ≤ Real.log ((d2Log186Q:ℚ):ℝ) ∧ Real.log ((d2Log186Q:ℚ):ℝ) ≤ ((d2Log186Hi:ℚ):ℝ) := log_interval d2Log186Eval (by decide +kernel) (by decide +kernel)
#print axioms d2Log186Eval
#print axioms d2Log186Bounds
end CatalanMeasure.GenD.Signed.Data.Cells
