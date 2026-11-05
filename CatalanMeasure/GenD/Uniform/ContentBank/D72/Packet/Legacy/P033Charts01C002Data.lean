module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C002
#time def pivTape : List (Fin 87) :=
  []

#time def freeTape : List (Fin 87) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 87) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩, .inr ⟨30, by decide⟩, .inr ⟨31, by decide⟩, .inr ⟨32, by decide⟩, .inr ⟨33, by decide⟩, .inr ⟨34, by decide⟩, .inr ⟨35, by decide⟩, .inr ⟨36, by decide⟩, .inr ⟨37, by decide⟩, .inr ⟨38, by decide⟩, .inr ⟨39, by decide⟩, .inr ⟨40, by decide⟩, .inr ⟨41, by decide⟩, .inr ⟨42, by decide⟩, .inr ⟨43, by decide⟩, .inr ⟨44, by decide⟩, .inr ⟨45, by decide⟩, .inr ⟨46, by decide⟩, .inr ⟨47, by decide⟩, .inr ⟨48, by decide⟩, .inr ⟨49, by decide⟩, .inr ⟨50, by decide⟩, .inr ⟨51, by decide⟩, .inr ⟨52, by decide⟩, .inr ⟨53, by decide⟩, .inr ⟨54, by decide⟩, .inr ⟨55, by decide⟩, .inr ⟨56, by decide⟩, .inr ⟨57, by decide⟩, .inr ⟨58, by decide⟩, .inr ⟨59, by decide⟩, .inr ⟨60, by decide⟩, .inr ⟨61, by decide⟩, .inr ⟨62, by decide⟩, .inr ⟨63, by decide⟩, .inr ⟨64, by decide⟩, .inr ⟨65, by decide⟩, .inr ⟨66, by decide⟩, .inr ⟨67, by decide⟩, .inr ⟨68, by decide⟩, .inr ⟨69, by decide⟩, .inr ⟨70, by decide⟩, .inr ⟨71, by decide⟩, .inr ⟨72, by decide⟩, .inr ⟨73, by decide⟩, .inr ⟨74, by decide⟩, .inr ⟨75, by decide⟩, .inr ⟨76, by decide⟩, .inr ⟨77, by decide⟩, .inr ⟨78, by decide⟩, .inr ⟨79, by decide⟩, .inr ⟨80, by decide⟩, .inr ⟨81, by decide⟩, .inr ⟨82, by decide⟩, .inr ⟨83, by decide⟩, .inr ⟨84, by decide⟩, .inr ⟨85, by decide⟩, .inr ⟨86, by decide⟩]

#time def roles : GraphRoles 87 0 87 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [4179948839976999111891518679841385, 50249653545189029186547486317161079, 101519035291729949961517456245681239, 2340075830687481850128978976592151, 47089432906563921663078451248678775, 94999010621065468999496958589247703, 756541962156357987200831033319319, 45569501883814065486289528363976777, 91902392828221629162167148579336233, 756192677943565482485562188898199, 45576348982251205688676789182040137, 91902043544008836657451879734915113, 2341179730692789836334530448740631, 47081887239701196451260652741773175, 94999415952645191976271972372553943, 4177909672598566792708458657774185, 50258708443636785361345850079521399, 101518505355936548605314961479068759, 6469528823354712347544409665618409, 55437706584898330036677570057321545, 112165943851889827745567829802461353, 9532158277118086462646639952186135, 63197766090346210056434669410758217, 128167630952362626555758879420265897, 13801311335895551838791115172198039, 74502023139134502961970849961693815, 151501100565376264857196634544650071, 20041275226952598622720601843719145, 90800388762137313734016899755154295, 185343687128224415318708351560567255, 29378442171712435352143377121102185, 114584573593039700207412053649132105]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [234763404526889449293572330525388585, 43970644764475338139083399461433495, 149557273105562184438303653997358665, 308112491463077222784799107107924265, 67099013350430728301348627394078231, 202525863121990376485578852571999095, 419182149577983289225231133963435991, 105626633810325647497835241007891305, 283755299806423641041000908785515127, 591907796738739665024415002365405527, 170245837305206718710922893777315561, 413779130742641671481249334587781705, 867780267854272031233173137150612393, 285628293030206244191328856346918935, 624246974416837078462846696340146249, 1323654398189684994135424887274846889, 491135132515953924917982230752579479, 985035716803054159863907047281619575, 2100417823735845163244735974374345303, 888443533741562907426313360721862889, 1606517239448744928298811157845305207, 3479996489993361995589031565848787671, 1643781263089755393201290581452737129, 2761922784286179974716533768725345353, 6012221286824680296216635508023387689, 3247065849422004731527436046074325399, 4894079765628255714701392320750779465, 10903068399336440420945362135550450217, 6519724624740182798963642992455164695, 9256054483130189437771405860873996151, 20669858873498627951436441174079940311, 14293544818345707772080000297072075881]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p02 : List Int :=
  decoded (raw_ints% [17933529015108621312628678305661108855, 41483128316584518522480084463607180887, 31441518585442467335267294912166487017, 37843144119821604981931406455018147913, 87218191720372693629827379672845743785, 78301396760953121943125056806490627351, 80816566185993555983163268129994082889, 196961107066768282908219731391502858153, 190814860300957318261185922922838839447, 194445937641727848868181520067999402615, 466077364128678723112530711120832324951, 560143930544650206382543799640722390505, 462446286787908192505535113975671761783, 1217036154974286247756260433684393554903, 1533402111977975398550918700490387252073, 1314733798731028261633269119349444183625, 3310582197496911852689722933815503197481, 5673860341805754465383534803623239994007, 3529250510743858989607372514956446265929, 10517844651280641716624176437929130443561, 17765519141627033031204145719517191424023, 12662454482342537192400338726595924171639, 33957224134713429213211856961069561861591, 1651546627057921079272015233211291, 20363658289350325129805625, 20363658289350325129805625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 30, 30] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01 ++ chartRows000_p02

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01 ++ chartRows001_p02

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01 ++ chartRows002_p02

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002]

#time def graph : KernelGraph 87 0 87 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 818.0838 s provisional ×3 model; 1363473 exact original rank units.
end C002

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033
