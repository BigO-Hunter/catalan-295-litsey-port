module
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.Bases002
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart132
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis018 (basis)

#time def pivTape : List (Fin 48) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩]

#time def freeTape : List (Fin 48) :=
  [⟨46, by decide⟩, ⟨47, by decide⟩]

#time def roleTape : List (Fin 46 ⊕ Fin 2) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩, .inl ⟨27, by decide⟩, .inl ⟨28, by decide⟩, .inl ⟨29, by decide⟩, .inl ⟨30, by decide⟩, .inl ⟨31, by decide⟩, .inl ⟨32, by decide⟩, .inl ⟨33, by decide⟩, .inl ⟨34, by decide⟩, .inl ⟨35, by decide⟩, .inl ⟨36, by decide⟩, .inl ⟨37, by decide⟩, .inl ⟨38, by decide⟩, .inl ⟨39, by decide⟩, .inl ⟨40, by decide⟩, .inl ⟨41, by decide⟩, .inl ⟨42, by decide⟩, .inl ⟨43, by decide⟩, .inl ⟨44, by decide⟩, .inl ⟨45, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 48 46 2 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291]) [5] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [183030453198107526408214433103546724749782954169452036606431967866200793688244136804573579573356027189751181922436138601558612099162780242593165227988264155321, 13226978481896553660719329000904027933746866693654399323980851107638329977107654791078265387134514728877868139436071395094820943363234345500646693223468675]) [5, 1] [true, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [199650547576601646512742539504713955603350461998232007950415362253704595427843150929841526775304534874167435347877028553614912415600414688790902899026956254665, 28908892252929351801688102202410281361284499929779203349649912274960855092610376482923838165512383887804334080618525544253495989318867856285849641735928225]) [5, 0] [false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [197590552415321662027705365505284617105602279329546749922846334016852341293182747984620111496679182001683501521158172322217182210388489924770672766986025753345, 28967576388376644472007798487521047671718290056063016490682090499751257196313653405480216099198872687899526937194556905099391018608004165996129023085643625]) [5, 0] [false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [185179739511925739701761591601127010498434408730858999541231401168193954203346961049262417958597993033653133615361950195642108859557683938392642092400261578289, 13181028632220289148971825995945066131455516778637280576838020479730038795282225422296648174213649645841121616151373440836256715756066499928855554340802875]) [5, 1] [true, true]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [634951541203099359607764774257394182213064448288121869056275134360562105745521386771362092006071375282673015736106348769855922190740857377627181012815563105, 4978951318719081682912613491154712689615452907870048427043206278676724698499745322459171612409488972963558947536888774849127615315722766334389420933775]) [5, 3] [true, false]

#time def tailRows014 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows015 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows016 : List Int :=
  decoded (raw_ints% [347432361794930659066968966837169472760743942633084727298968713555919830139084353785700349034110538985928613337928918269332886253477286154786147077543694175, 11748109592052769394229142729804814994464928364963265721444632650439872081180630394183233199657296948339059616039184646078426678712153078126399321362075]) [5, 0] [true, false]

#time def tailRows017 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows018 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows019 : List Int :=
  decoded (raw_ints% [122553417085775151339787773107613184278085832399298179193290661944877756009756097440386579779689453171006337655067908008626854203606510409255658919673708175, 5292396120419029740437680309663760672117251690826139885621654696633765840253197054527845198867229257754073675384530867485142886737936369217939875891175]) [5, 0] [true, false]

#time def tailRows020 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows021 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows022 : List Int :=
  decoded (raw_ints% [72577358826995775939955058861968258684916260171865427141860051283610320089275667172568200534601138130133593848863013854768910562851709028005511734907722385, 453999251234334451820131477198933489852454693440569465991209232289968919893008874291868979235192610815332096844665580392487879104156106697169287222775]) [5, 2] [true, false]

#time def tailRows023 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows024 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows025 : List Int :=
  decoded (raw_ints% [23190365518093936282149828483810011976286938044443741201462429400376191777007350973173750610920892878903993169913992193998165512204509815031447873364208531, 380326308437522305045991283701877203988513236739535220796086852737200936962129018469366277198326189125497499474557098819430180802122074812087141427225]) [5, 1] [true, false]

#time def tailRows026 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows027 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows028 : List Int :=
  decoded (raw_ints% [13166740313481216965519603249852076214216339711466740919239756168710048062221341560719437119549975923036152694077284610292699630831512529743563886159800925, 228493463519966696804843696307237155631524225464695068729931140366321041338476973091556881532284040142691252622148743103205488495224400596296184166375]) [5, 0] [true, false]

#time def tailRows029 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows030 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows031 : List Int :=
  decoded (raw_ints% [3399980739070110248042688416657375323257762407029355720554847141614719901513510374040667563391597183958386793856166928683659909521853615761398317333161573, 85512055066612405388848628055812785891326825849604059730998505273686531130447689662865140476146793893623608302471227241957344804347984823415109137975]) [5, 0] [true, false]

#time def tailRows032 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows033 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows034 : List Int :=
  decoded (raw_ints% [1813292130038475693744078339874024365603590660400104827668444046109679008300922282424687758440219732880124459725350321364721574363185246427497768794148875, 9751255732295269717072365439596364615625511468684078169057312703028134567431479235652506990609367412565929576265470781309364052388202233718351711325]) [5, 1] [true, false]

#time def tailRows035 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows036 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows037 : List Int :=
  decoded (raw_ints% [330662713962075226281480645419705081999949398140514132735181232173868183597609749739098072120222768877200835204003242279101932788192351102325588290579795, 1579912374331234636808966409484910246671005589399829612331864208356755931390423056541629411073423914539507259615088090210160483693133890163005769775]) [5, 2] [true, false]

#time def tailRows038 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows039 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows040 : List Int :=
  decoded (raw_ints% [164280596199886301889832168333886449452673122602573147687433526291533160491310093979320548771497201655374114076630943976524160633261110798056075698437389, 827001962125719308891781827841319153482675320415431741710541204197297660190166924355438392780964007463009976383048659630514567986684311459710851325]) [5, 0] [true, false]

#time def tailRows041 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows042 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows043 : List Int :=
  decoded (raw_ints% [15761713343021894571964626967463593056411404457098462977187010070289909916499785639463296816178369319577920665525668121403074818021572082431756867155725, 223877830132325495533853878210819299822373062304287062796758914632637758840269742523490232630505149934150936902750751568959896165420208321413041625]) [5, 0] [true, false]

#time def tailRows044 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows045 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026, tailRows027, tailRows028, tailRows029, tailRows030, tailRows031, tailRows032, tailRows033, tailRows034, tailRows035, tailRows036, tailRows037, tailRows038, tailRows039, tailRows040, tailRows041, tailRows042, tailRows043, tailRows044, tailRows045]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 243713808082670679, 607961471833528647, 903606052351478391, 408653258148199, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 148605599185470525, 21287570016248979, 2657579116665153, 33492646265533, 34493884425]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 7, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 151387994194904603, 316775219116482765, 479454851877279743, 29647858210765, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 574818220719425045, 82182751500561625, 30784799536760355, 17884419880187, 34493884425]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 5, 0, 9] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 42752080057047641, 82153752508489405, 121632278287850089, 1287776777631, 2653375725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 11503129264860577, 9858052665717051, 13149481030992733, 382384666239, 2653375725]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 2, 0, 1, 0, 7] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 14506004138969, 3286080299633617, 1178500505039373, 16702287793, 241215975]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 7, 0, 2, 1, 7] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 7999856339602525, 1428740422078035, 2284494004056855, 40302108395, 241215975]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 1, 8] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01

#time def chartRows041_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows041_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 3185008400933739, 5143448511010413, 7104202620437757, 19654382787, 241215975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows041 : List Int := chartRows041_p00 ++ chartRows041_p01

#time def chartRows042_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows042_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 10779199526665917, 1347097410982869, 3390769184895, 137214899495, 2653375725]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows042 : List Int := chartRows042_p00 ++ chartRows042_p01

#time def chartRows043_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows043_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 921127886614713, 5388403269205461, 3543418908064545, 270237044875, 2653375725]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows043 : List Int := chartRows043_p00 ++ chartRows043_p01

#time def chartRows044_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows044_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 68764961739507579, 22120174836938097, 19738301156030679, 5078031246511, 34493884425]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 1, 7] [true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows044 : List Int := chartRows044_p00 ++ chartRows044_p01

#time def chartRows045_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows045_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 18846794612867301, 24577310582145795, 30432132043502931, 2517392931665, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows045 : List Int := chartRows045_p00 ++ chartRows045_p01

#time def chartRows046_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows046_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 3704376525300633, 180768027125319, 2069991948020901, 6075502698933, 34493884425]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 1, 6] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows046 : List Int := chartRows046_p00 ++ chartRows046_p01

#time def chartRows047_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows047_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 2642697641777463, 1578738665705661, 3450924256520043, 38689526940519, 34493884425]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows047 : List Int := chartRows047_p00 ++ chartRows047_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040, chartRows041, chartRows042, chartRows043, chartRows044, chartRows045, chartRows046, chartRows047]

#time def graph : KernelGraph 48 46 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 1.6214s provisional (8107 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 605) (2 ^ 1) (2 ^ 531) (2 ^ 60) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 50 48 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 605) (2 ^ 1) (2 ^ 531) (2 ^ 60) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 48 := by decide +kernel

#time def refs000 : List (Fin 48) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 50 48 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart132

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart134
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis019 (basis)

#time def pivTape : List (Fin 32) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩]

#time def freeTape : List (Fin 32) :=
  [⟨4, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩]

#time def roleTape : List (Fin 16 ⊕ Fin 16) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨12, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨13, by decide⟩, .inr ⟨9, by decide⟩, .inl ⟨14, by decide⟩, .inr ⟨10, by decide⟩, .inl ⟨15, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩]

#time def roles : GraphRoles 32 16 16 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925]) [3] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 148302629674147425808232585891605685811743297441062345989144524032701652046712771595408560786807111740205834057611566911411682318350338721792557308505317, 148302599078582649050663130814077834975954682169561475741824186275553084669737013367722815665489610725314381524098528728769469081193432012019732627396625, 148302614376365037429447858352841760393848989805311910865484355154127368358224892481565688226148361232760107790855047820090575699771885366906144967950971, 148302614376365037429447858352841760393848989805311910865484355154127368358224892481565688226148361232760107790855047820090575699771885366906144967950971]) [3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 1, 0] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [152718032073121333088227223204620288104408552584782535240856634929154102356127480399611758643716488271944109745293518952347312485936255654845886433631056960055699939441510838000971933004312937727932454689249724898561916050279198612708581964922589645652285556890068681617559592795584076299602033817394148875, 152718032073121333088227223204620288104408552584782535240856634929154102356127480399611758643716488271944109745293518952347312485936255654845886433631056960055699939441510838000971933004312937727932454689249724898561916050279198612708581964922589645652285556890068681617559592795584076299602033817394148875, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 2224539445112211387123488788374085287176149461615935189837167860490524780700691573931128411802106676103087510864173503671175234775255080826888359627579755, 2224538986178739735759946962211167524639320232543422136127362794133296270046055200515842234982344160879715722861477930931542036217901480180295989410949375, 2224539215645475561441717875292626405907734847079678662982265327311910525373373387223485323392225418491401616862825717301358635496578280503592174519264565, 2224539215645475561441717875292626405907734847079678662982265327311910525373373387223485323392225418491401616862825717301358635496578280503592174519264565]) [4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 2, 1] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [152718032073121333088227223204620288104408552584782535240856634929154102356127480399611758643716488271944109745293518952347312485936255654845886433631056960055699939441510838000971933004312937727932454689249724898561916050279198612708581964922589645652285556890068681617559592795584076299602033817394148875, 152718032073121333088227223204620288104408552584782535240856634929154102356127480399611758643716488271944109745293518952347312485936255654845886433631056960055699939441510838000971933004312937727932454689249724898561916050279198612708581964922589645652285556890068681617559592795584076299602033817394148875, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 114733367912840885456540729440634207307268128263427451266589307127663659093353821544204940628805842947000673893184908299639338400161648092554157595, 6267372836175025213464059845799307881033552499659328877267376893151559239136474933495887342304775061743273202441917040658856917463409552616079928439936675, 783421590180207162577896798657322305049918149048900076729990703320281513934101980017758224762479304117178781930155393434243577228008894056803979485722385, 12534745557616682514087234235057886321432897692050529491107302519713811350609290773637953140404609494680703457883160188132805535287480705070511764325715755, 12534745557616682514087234235057886321432897692050529491107302519713811350609290773637953140404609494680703457883160188132805535287480705070511764325715755]) [3, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 6, 3, 2] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 7648891194189392363769381962708947153817875217561830084439287141844243939556921436280329375253722863133378259545660553309289226677443206170277173, 758058117151879778513349560017036973602358810656436444670047532479291327513735258542987876098863008935440171342481750290010313952880702309790613295916605, 758058132449662166892134287555800899020253118292186879793707701357865611202223137656830748659521759442885897609238269381331420571459155664677025636470951, 379029062400385486351370961893209468155652982237155831115938808459289234678989599049954656189596192094581517237930004917835433631084964493616909733096889, 379029062400385486351370961893209468155652982237155831115938808459289234678989599049954656189596192094581517237930004917835433631084964493616909733096889]) [0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 4, 3] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 13551882795482518361477749448953898154196382644524383752575122705163307785639649412016692619220601315599280875837369025028233147165406494478890887311833447983822727064490556054866265741568878415843515122731417441649208286976017568317917570539041047047873450687412708717520974763529866348117172026805241453176265696374627486424356670283300270561772132979536756943029946045005762626883145551593166289193006734611577316362624932893123648674578885938142379601834583125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 3874919971778404231172268880084334358888965597243042672545409718478254259632277147413132926928328662627484192685417001889704764684207244239794318611207852704593763002550279642461514289650136707326102590336241384433152221974462268102975062792109388893131645394119701871394815289068502193914156661296486656428125, 3874879246969851398816778686158146460145471088295686730536012156708939818538315513418359697126023671563945007589484923617984138734210994571619693041492217756071081482566428572904714030468002223876041808348324251173179272130182193650011673836918742869226138117971197853079717273177090038160476767420802017988425, 3874899609374127814994523783121240409517218342769364701540710937593597039085296330415746312027176167095714600137450962753844451709209119405707005826350035230332422242558354107683114160059069465601072199342282817803165747052322230876493368314514065881178891756045449862237266281122796116037316714358644337208275, 3874899609374127814994523783121240409517218342769364701540710937593597039085296330415746312027176167095714600137450962753844451709209119405707005826350035230332422242558354107683114160059069465601072199342282817803165747052322230876493368314514065881178891756045449862237266281122796116037316714358644337208275]) [0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 2, 1] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 1227777550355234030920908488457590770636540566060550757869533096614985857686303133852591630411147042199223034336908679802852649901606227095037459352920121009997982112184374686473032424208090815849649057169481925620617877602902892025110798740564826936596475500049652657021172389167264164532078361823148193972525, 1227736825546681198565418294531402871893046057113194815860135534845671416592341499857818400608842051135683849240976601531132023951609977426862833783204486061475300592200523616916232165025956332399588275181564792360644927758622817572147409785374180912690968223901148638706074373275852008778398467947463555532825, 1227757187950957614743163391494496821264793311586872786864834315730328637139322316855205015509994546667453441788942640666992336926608102260950146568062303535736641352192449151694632294617023574124618666175523358990631402680762854798629104262969503924643721861975400647863623381221558086655238414885305874752675, 1227757187950957614743163391494496821264793311586872786864834315730328637139322316855205015509994546667453441788942640666992336926608102260950146568062303535736641352192449151694632294617023574124618666175523358990631402680762854798629104262969503924643721861975400647863623381221558086655238414885305874752675]) [0, 0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 2, 1] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 133036613796264719086800098017036183503845097097748283556980755216082726053073102722208746921416690330468552358901663666891788932986157408225633766145200689906792972060940999758182788741296945640224981300686754525588712747035630713051664112393917430623492244581786705064937750274485725622543533005146533400525, 16628304074265813874740943691936151102246433732613662256828920596719264472447836777939429933855055320572969510614830512370204055685886873897747171714536494097015324008122279046122840493220415597213723225463433901324434410745701512476352109199531990580889428193082587560770405787704085835515444942028171723825, 266063046390391230084727647552525392321816566958657581611612119989836841832655796945724186392257132895052308443820307765853421378473252399407611139861492642682915564125919232127165512687060270417934767104394225736184188033001242812862480985990173355270607670126447405551100996576118412306667092541371907191125, 266063046390391230084727647552525392321816566958657581611612119989836841832655796945724186392257132895052308443820307765853421378473252399407611139861492642682915564125919232127165512687060270417934767104394225736184188033001242812862480985990173355270607670126447405551100996576118412306667092541371907191125]) [0, 0, 0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 4, 6, 3, 2] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 95382529716525192931697675380854722023814195615301733590236167565513161074306601016068108010726696678058535164604953163271596583056229496657801023272152935657397569616045567929016401456982827374806487905784040979423629614707590219329921449302874696711972459482441479194089964208251846505536712931846695234875, 95362167312248776753952578417760772652066941141623762585537386680855940527325784018681493109574201146288942616638914027411283608058104662570488238414335461396056809624120033150616271865915585649776096911825474349437154692567552992848226971707551684759218821408189470036540956262545768628696765994004376015025, 47686174257193492421412563449653873668970284189231374043943388561592275400408096258687400280075224456086869445310966797670720047778583539807072315421622099263363594810041400269908168330724603256145646204402378832215196076818785803044537105252606595367797820222657737307657730117699403783558369731462767812475, 47686174257193492421412563449653873668970284189231374043943388561592275400408096258687400280075224456086869445310966797670720047778583539807072315421622099263363594810041400269908168330724603256145646204402378832215196076818785803044537105252606595367797820222657737307657730117699403783558369731462767812475]) [0, 0, 0, 0, 0, 2, 3, 3, 3, 3, 3, 3, 3, 2, 4, 3] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 75815064635380346261815507237492869817129330173342465671037462965177480239039646260110605852717149130114959782083894865638787919961104824199011492861507583408591474535555149802864823199700634858251669438185070544555561383615428383030048702274841940519172127922175435297882663669938701417349872206127892322125, 75774339826827513906325313311304971073634821225986523661639901195863039145078012265337376050412158066575774686151816593918161969964855156024385923145872634885909954551704080246064564017566151408190887450267937284582611539335353930066659747084195916613664851773671416982784647778526545663669978330443253882425, 75794702231103930084070410274398920445382075699664494666338682080520259692058829262723990951564653598345367234117855729778474944962979990111698708003690109147250714543629615024464693608633393133221278444226503914569086461475391156548354224679518928566418489847923426140333655724232623540509925268285573102275, 75794702231103930084070410274398920445382075699664494666338682080520259692058829262723990951564653598345367234117855729778474944962979990111698708003690109147250714543629615024464693608633393133221278444226503914569086461475391156548354224679518928566418489847923426140333655724232623540509925268285573102275]) [0, 0, 0, 0, 0, 0, 2, 3, 3, 3, 3, 3, 2, 1, 2, 1] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 24446926721585964572515676690802364101353456653076605643355417832208504107495886511819871062672615838217046470993391885341409846733778407673382514219154664009694398839927311684562381599665728357665188381699793868617513384151468611716361277169632071163708818523050168352839921091526617599219787695759448048925, 24406201913033132217025482764614465357858947705720663633957856062894063013534252517046641260367624774677861375061313613620783896737528739498756944503519715487012878856076242127762122417531244907604406393782660608644563539871394158752972321978986047258201542374546150037741905200114461845539893820074809609225, 24426564317309548394770579727708414729606202179398634638656636947551283560515069514433256161520120306447453923027352749481096871735653573586069729361337189748353638848001776906162252008598486632634797387741227238631038462011431385234666799574309059210955180448798159195290913145820539722379840757917128829075, 24426564317309548394770579727708414729606202179398634638656636947551283560515069514433256161520120306447453923027352749481096871735653573586069729361337189748353638848001776906162252008598486632634797387741227238631038462011431385234666799574309059210955180448798159195290913145820539722379840757917128829075]) [0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 3, 3, 2, 1, 2, 1] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 4225039492365722741229533268452472672216103823971406240339664929857364947529662454293647600190394585493793220711554433121708730306025176050780540557314977764150365458525080371424844713285349589255080804807522849035983640271562313338459617650396963656521356243685334169261111589995393262251602881937429998225, 4204677088089306563484436305358523300468849350293435235640884045200144400548845456907032699037899053724200672745515297261395755307900341963467755699497503502809605466599545593024715122218107864224689810848956219049508718131525086856765140055073951703767718169433325011712103644289315385411655944095110778375, 1053714572556878663089246196726374496585619146783105184497568621882188668509813488900085037403536704902249236682133716297888060701740689751781037032101560158369996365640578245556194979437932181684971326957059883510686544800385925024403094713183864420036134301639832397621651904285588580957907353254067597075, 1053714572556878663089246196726374496585619146783105184497568621882188668509813488900085037403536704902249236682133716297888060701740689751781037032101560158369996365640578245556194979437932181684971326957059883510686544800385925024403094713183864420036134301639832397621651904285588580957907353254067597075]) [0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 3, 3, 2, 5, 4] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 279183977003611293714449679861074312770103321548568236126893532042815229190596629947897313557572680513458199252789502690325385986026179817788068732990080145200718986898914031680568836600668686521797617714628814899449564922106048820827562668987495580215951625853139465924357817366041936127029277926247328975, 548186751869014498556350878175173939666579406258150969904396621757020184890784761202487176538897595142120124522559437450494284472989942591919745037071423159731057977835060674161072877667716510528399738449974314805661668774193484400807886540313485184055084214580274353074211661879044933834085086931335048025, 1106554705876237085985250237897322565206786049355287442158183685842650643271978021098281803654042956169036523028138442831145056445042302227495882503051583450132495951632888737522210550869053883571994973879231944604560798618405582042463011878288476344486987466286553284922927296611128806088143642783829705975, 1106554705876237085985250237897322565206786049355287442158183685842650643271978021098281803654042956169036523028138442831145056445042302227495882503051583450132495951632888737522210550869053883571994973879231944604560798618405582042463011878288476344486987466286553284922927296611128806088143642783829705975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 5, 3, 3, 2] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows014 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 624054953631643298863021416323646498732982476154023428677112624543247095638570149624691414633632651770048084856994668011587043644629616197424820067861643370252014272289044101810961808791957390976520666554259314727705944100976006989644460115643319550556760829596689900821992672458313854285961410913831951925, 583330145078810943372827490135747755238473528798081419279550855228806001676936154851461612328641588230862988924916396290961093648379948022799250352226694847570494288437974545010702626657473940915738678637126054754756099820901554026255504924997295645049484681092671585723976781046158100606067535229193512225, 603692549355227121117924453229697126985728002476052423978331739886026548657753152238076513481137120000455536890955532151274068646504782110112035210044169108911254280363509323410832217724715665946129672595692684741231021960938780507949982520320307597803122755344680743272984726752235977446014473071512732075, 603692549355227121117924453229697126985728002476052423978331739886026548657753152238076513481137120000455536890955532151274068646504782110112035210044169108911254280363509323410832217724715665946129672595692684741231021960938780507949982520320307597803122755344680743272984726752235977446014473071512732075]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 2, 1, 2, 1] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows015 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10181202138208088872548481546974685873627236838985502349390442328610273490408498693307450576247765884796273983019567930156487499062417043656392428908737130670379995962767389200064795533620862515195496979283314993237461070018613240847238797661505976376819037126004578774503972853038938419973468921159609925, 117594981962401027885368250034809453984077071112185632656192563664954659912826463170228821840716088659917699083959334376538927353676627242721729978963513212188181123263776263764890290037032939470604374951068994683817076333068403186869957294536275311832122353187162137459249403314185776835347104348107151125, 76870173409568672395174323846910710489568123756243623258630794350513565951192468396999019535725025120732603151881062655912977357426959068096160263328564689506661139412706706964631107902549489409822387033935734710867232052993950223481002103890251406324846204683143822361233511902030023155453228663468711425, 97232577685984850140271286940860082236822597434214627957411679007734112932009465783613920688220556890325151117920198516225952355551793155408945121146038950847421131338241485364760698969791214440213380992502364697342154193031176705175479699213263359078484278935152979910241457608107899995400166505787931275, 97232577685984850140271286940860082236822597434214627957411679007734112932009465783613920688220556890325151117920198516225952355551793155408945121146038950847421131338241485364760698969791214440213380992502364697342154193031176705175479699213263359078484278935152979910241457608107899995400166505787931275]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 2, 1] [false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016]

#time def graph : KernelGraph 32 16 16 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 1.0554s provisional (5277 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 2094) (2 ^ 538) (2 ^ 1543) (2 ^ 2) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 50 32 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 2094) (2 ^ 538) (2 ^ 1543) (2 ^ 2) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 17 := by decide +kernel

#time def refs000 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 50 32 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart134

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart135
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis019 (basis)

#time def pivTape : List (Fin 32) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩]

#time def freeTape : List (Fin 32) :=
  [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩]

#time def roleTape : List (Fin 2 ⊕ Fin 30) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩]

#time def roles : GraphRoles 32 2 30 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [1] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [1, 15, 15, 15, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [3248718156302293, 153249755291656299, 3682730505183007, 177148238062579, 75947560727451563, 111764286200552667, 104604938443789, 141912268055651243, 110603593406652027, 6933564475920757, 82642276787854059, 1862669326526147, 7270333812219957, 169646525959334271, 66707367592907061, 11986389195451971, 111723612036733887, 164657847388938021, 9572986821392259, 265537639522950039, 207776599422626481, 70997165225106687, 188307506607871959, 148959869145258843, 54426275378899263, 549526300423376787, 105835794723630909, 61136765541401487, 406012608123469011, 722316516439028847, 47461791511219407, 1527714549085800579]) [1, 0, 6, 5, 0, 1, 5, 0, 1, 1, 0, 7, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [1156710744649512423, 1097731418322283401, 1165401272302979523, 611072332254168363, 882816588647142729, 5918640222374934183, 2212418667993049791, 3572336729189479929, 4696667626891550439, 12452327383012202169, 3019242967425896889, 34497334055890773615, 25635486776242955805, 80937110673169489683, 28850611366298725551, 56305541692132119633, 121096094322158517, 11141524669275]) [1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1061007268018421, 7420789397812997, 18911860164832341, 221203545725877, 10430063499000923, 17629649351088043, 338286064751349, 6978382306361243, 17746731870113515, 689763462706613, 11106635628503621, 18774781397571477, 2142881998729547, 8357909231774469, 21607426859007637, 2149146707426955, 15392399625962715, 25899455565164139, 6398194611633717, 12656202646628379, 34446796884224811, 5957479290401013, 28188788849230149, 46802470786259541, 20716194389582475, 24571161227430405, 73476144466243029, 19279497125298123, 69621177628395099, 113471835981123627, 85702075454476917, 63130155478026651]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [218453408560898667, 81224331739641141, 241025328537348933, 385379815755016725, 511485857973973707, 225578818957308933, 978090005468631573, 495475823117271051, 1263997044485296347, 1985051686559876331, 5324095953483368373, 1216530465191851035, 7804623463160515755, 5254890819747838581, 11912188951452033093, 18383610236391722709, 9986433716425381, 655383804075]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [24683953105505, 597672374989909, 253759526760211, 1034941262791, 367997825839925, 474555570312589, 630516192313, 564554254580597, 471320169748765, 34932819872369, 388174343993941, 255648559579819, 36744022265537, 704285534070073, 72871745162193, 59751618804823, 535150433056089, 739221221172727, 53820585841191, 1182298484508657, 966365630464755, 385466235889683, 965715119785617, 364868259509205, 343825352222979, 2724163428067389, 1094382313074741, 386924074629957, 2341016528677533, 4080286276892289, 353074422643989, 8914948622146701]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [7040280265988073, 8906222464118421, 7990207290981357, 8679400210341225, 8386599787943973, 44539838478620385, 8662905668186211, 44555244067340445, 41536606442757249, 132148710595369707, 43251131577299469, 400981791017343945, 307761461884649535, 2808873686097914295, 387545659061153001, 200196088196072673, 532203006625927, 655383804075]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 5, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [66397265376073, 513781370409975, 1226872982503717, 24460605484953, 646694346717669, 1136015111642691, 30296680432953, 464860159440069, 1141851186590691, 47924841595273, 707287707583575, 1220072708618917, 166618376110495, 560709842630615, 1434615926324685, 166706929031567, 1040524459804565, 1767941231466747, 535409248753217, 894123700693749, 2470057409251531, 512580271512273, 2111342957310999, 3518046929517021, 2013966381245223, 1919284243718295, 6044593582274517, 1940265711268695, 6139275719801445, 9998825674788435, 10706838179340201, 5799815666255685]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [22645929565397331, 10478639871641721, 27552952078481847, 43831407616379253, 99015654809511759, 26757095409539127, 153325702297532733, 98201627213487039, 225584261697505365, 350542984320531531, 2903339719256864625, 223160349836513205, 3352084330790883195, 2899784207184828545, 6032263700211234615, 9155208257232576365, 646635123939895, 655383804075]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [19115549486591, 316372623397271, 142984668715281, 1754121775825, 217334952490671, 263345544392321, 1086994896175, 302339649190671, 262011290633021, 23335905028091, 226030911660071, 143760592726731, 24290988280755, 395683269303035, 83787019690577, 20775772908051, 323194864783091, 442542158675267, 19642320055855, 728095635831851, 604214530530891, 305939922998365, 637471985676771, 247180933438169, 289771613090181, 1951855327825311, 792217634920611, 775868757070989, 1796558438037495, 3425944397073381, 749835826358781, 8158805384393223]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [6477353563932921, 13573698625039455, 7795245048907743, 10775361920844969, 13376920008409335, 62453599884551043, 6062667809392341, 46825532816897961, 61302925082545083, 436482525018731751, 46704061344133331, 1560870650025285795, 1184719278306982087, 10926423759811084415, 1555832888094811675, 292752249710969865, 305084886917153, 655383804075]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 6, 0, 9] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [2803924157645, 22307708309281, 50709935037133, 1435635963237, 25598302570207, 46470374916251, 1625297879037, 19436436382807, 46660036832051, 2204357922965, 28848898328281, 50489692634053, 8522294210915, 23845152228737, 61216344767933, 8525562826795, 45893486750111, 78264201805643, 30762643302733, 40896277882327, 117552407935171, 30012863980357, 107418773355577, 178327915218261, 145118150297491, 100922005843041, 353458929496109, 142708346503611, 397655073950559, 641285426297211, 1170443423253021, 386338698850263]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [1954437196053843, 1163027446271349, 2738541920456601, 4287908065578213, 29887286688443331, 2712393591392961, 35338222200292893, 29860964681403211, 62513115297343263, 95086473570139435, 811531292509567379, 62434322954199383, 686583854258024733, 811646325548695259, 1560549469721791495, 2309761472316287371, 26756929597389, 50414138775]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [273008499481, 6521135778363, 6218535542179, 59178619823, 4823901308071, 2806669961697, 37097434193, 6284421299071, 1397814684441, 153946233233, 4972291044843, 6244141104889, 634014522135, 8747561030799, 1873485139989, 1194118036659, 7508349133383, 10516191155409, 579296501153, 18300505324071, 15221613233339, 10808914541099, 16777093151831, 14173856889525, 2638068908677, 61536163488467, 49708903954857, 81669285040207, 58986195690663, 35482616157443, 80848512839595, 388213303649295]) [2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 3, 0, 1, 1, 0, 3, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [152224131254787, 969532818404691, 382380247049043, 2324362412158551, 1935997872731125, 8144475850886823, 3099712960849529, 12215676145846097, 8126371737973543, 40727280788954205, 24438838718545589, 187306342482650729, 138467662809429771, 437048562553038341, 187384338010391169, 15606451394157337, 6764552541141, 50414138775]) [2, 2, 0, 1, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 0, 7] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [37937841349, 584634191745, 637214235585, 48606509539, 613918596727, 1149946278933, 52369897279, 487421172667, 1153709666673, 7998788851, 718658391285, 158758734345, 139504431575, 615401794283, 806534524359, 279130960417, 1276676117585, 2171208872285, 1214523295587, 1173663715117, 3664863128289, 149953681435, 3705722708759, 1519753968839, 4223174730103, 3572922618077, 7862497393521, 8398586961373, 20598421629171, 32569931208621, 183825998828159, 20370096540823]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [224794516998153, 5739992863915, 388250419285489, 74037535933949, 2132650123006053, 387729639831383, 1744660093447617, 4265816652183983, 8142350072738723, 12020437085091323, 35292224240939923, 8143903664536583, 19005970503664617, 2205623230251203, 62442098409141123, 22397041607155947, 337576038467, 4583103525]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 2, 1, 7] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [303623644451, 647654577345, 2613662086689, 19291815211, 253682321887, 2290746627027, 12199019221, 314181381067, 2283653831037, 326014521101, 519563662995, 2621867371359, 332472391305, 954377283235, 3280354283765, 1474020152545, 213009013575, 5086846827615, 1452152216745, 607099358945, 8013019196905, 9607451647745, 2304188271045, 19072623061395, 9527583679605, 12035849083525, 38207658388745, 192111384417325, 5915885975325, 239846626485675, 191857275200445, 102073616750425]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [623815286103445, 4082068427597515, 203689047151095, 3266395866293625, 4083010083520095, 3877921194096665, 11431474377411235, 31024028221963705, 484915129546125, 15509543761032375, 31019473611359505, 848315844620845, 77553045594355585, 152017735764931927, 27140152574990505, 43445216559216837, 729321432785, 4583103525]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 6, 0, 0, 1, 0, 1, 8] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [2182372646083, 15344676293589, 32136500442581, 1644975140845, 14609451502909, 28309152655653, 1718822702875, 12054726011899, 28383000217683, 1949335151173, 18047096908659, 32051158071731, 10006679504253, 15953396314245, 44007172727157, 10010555406195, 38060455917165, 64024407637605, 61214176853115, 35974507126635, 135249139896915, 60922758510405, 160488809623395, 257386075260435, 1110159925690365, 157820024147445, 1428468759461205, 1109226362550675, 2380808661004125, 3647855047702245, 21392552903428965, 2376272749248795]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [16635471493176045, 21395398641622395, 40404297145853805, 59423423038227405, 148189510898827965, 40414524533995995, 67370689218978165, 148179507132757875, 255974724651802125, 363739707250564005, 665418577281567621, 255944489731519755, 153499362898245741, 665462102670311931, 1074862429911333117, 1484380042850125293, 4289859136083, 50414138775]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [1398063092633, 250300983503, 8696431857387, 48286727841, 1646776514353, 7250082036913, 30746542431, 1954121140183, 7232541851503, 1453394727431, 104845191049, 8716683121365, 1470582636521, 1703757933807, 11640660485317, 8857892030481, 3148105693305, 21969135152319, 8805687125685, 12265407898095, 39632714308485, 146299339445325, 5976896409495, 194737740879495, 146106773452275, 39641186835855, 487143853777095, 2535667997755125, 158060566271265, 1902417370525755, 2536278184356525, 2377103250411705]) [0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [6974363552637405, 15848258085977115, 594554404521315, 6337616348983185, 15846012471226245, 6735577417782705, 38031886906186545, 64660269444218547, 13467794853140985, 10782370066805757, 64671052697451207, 51189114608653137, 140113692208475511, 204757891332210033, 25601628922155111, 26853573716685, 2523623737505, 50414138775]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [2647888961899, 63308693191807, 63455796629927, 9003441757033, 53011344220451, 107316595655225, 9220783503655, 45301809677741, 107533937401847, 2476539061177, 71452911227761, 63330438575105, 16829052031057, 65114122167157, 101941620759573, 67332333624619, 206085327476217, 338531783267993, 1009253729959419, 199778789416395, 1415117846852031, 252100018557015, 2224592787395055, 1716385825519755, 3882238469712345, 2216578937872515, 5543891076790905, 15531687664424025, 28833314970303705, 42148423696855215, 86537915367113655, 28846796390975535]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [28857804005834415, 21632403206506575, 144242515763923605, 100962666099487185, 79313515186645257, 144212429261077065, 14399557860790179, 317283127713949173, 490265605729238451, 663336304182110559, 910763281335028059, 490353826166821281, 69856150561031673, 227659287017161281, 1331260956940817667, 875772139421320755, 68751574553725, 655383804075]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [74953130382917, 61450765283247, 303537439179119, 1155558865461, 26420694557427, 227428749930741, 740063118795, 30147603208893, 227013254184075, 76263032262203, 53581452233649, 304016349565073, 76694636359127, 136558238679989, 456974018186403, 1075573432053127, 16284511074097, 1609242086598657, 1074373489314559, 303032917683279, 3759189007966343, 14522428441193841, 1204649577907335, 9688865943912939, 14526894904786845, 13310296770460725, 38738189289893625, 71000740833421875, 6661122663439755, 17735656638741405, 70986634116213795, 28845222031480575]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [159723031588377075, 230746491022017453, 57664388789334285, 36825317426583, 230798110611615393, 173056046959056303, 461581426951059429, 593361329326351311, 43283430455570277, 99018208236323511, 593114933523255351, 13134540073977969, 1087458054613283151, 1307579465795360121, 419981211700974243, 372993522341178381, 94622642390509, 655383804075]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 1, 7] [true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [40227901099279, 184653226877585, 349359642675081, 37307399545309, 124478514698217, 271824342030493, 37705544642659, 110038427786967, 272222487127843, 38973045146929, 199889603983535, 348901076917431, 576425828767185, 187984518080825, 964299950831545, 576464135131995, 1352741261517905, 2117189914730725, 6722159180601445, 1340912788344815, 4028505130738725, 6723714301585855, 12091577099684985, 17474378612926025, 28242523023065505, 12106515814826895, 4044430108553625, 28237542216899715, 44393468946446025, 60524495348518845, 79862336785268541, 44368568618972535]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [8899700780150019, 79877415647987391, 115331204624091057, 150840051653105913, 181349041827613281, 115386262677002247, 49368425473480023, 181296443300442651, 247366879031135505, 313277059654575909, 356885920525159845, 247206623923883055, 137687582429858715, 357113584416077007, 466404962019184185, 576311922511378137, 48698442971795, 655383804075]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [19101322891097, 1257345155657, 38209088403379, 67054152165, 4524502133513, 19040711360117, 43156428315, 4962326470463, 19016813636267, 19176623266247, 1141914640457, 38236593330829, 307242718318037, 12069474868355, 1225854183871253, 3073738618693835, 380325255307285, 1540641716504545, 3074814136947785, 2687515422906475, 7689194472146165, 10757794665466135, 673622220410125, 6213943627815, 5376878778694955, 2017569810639915, 10752669139614115, 12908549977044309, 4029634337874705, 3220997941264761, 12914908190129379, 8873410355764479]) [4, 7, 4, 4, 5, 4, 4, 5, 4, 4, 7, 4, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [22602460225908927, 25358400041970525, 4442636926127337, 10158968374067781, 50670492567996675, 8242494843103023, 81069355903802163, 87897844203107037, 32899944863487327, 43842004268691801, 88117771535327703, 54927864830694945, 132173611469742939, 139851764309797449, 6902228333980047, 80439618695273193, 14327602823619, 655383804075]) [1, 1, 3, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 5, 7] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [22868441164630805, 482321797561491, 1916678694106069, 162182726727317, 172420779642407, 492559850476581, 162573657417467, 157956344106857, 492950781166731, 5242535622147349, 497568094477341, 26219317656841685, 47022287091090411, 7769837127857061, 15560433812101377, 11755202986962789, 39061197579452955, 856277600398773, 32666750628549115, 39250974819994095, 3244667785587205, 130618430332024765, 91605804934743505, 235328090561523585, 255907185098037571, 45683727756015335, 110039335795510779, 16003926353323951, 82150690081647033, 50241333869463751, 26475690717398049, 82347683070576273]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 7, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [29297805141315555, 423141173182946829, 129654835657537359, 612369783530791173, 630829069762431219, 258445807041794283, 404681886951306783, 158115696776486829, 371519398447356501, 107326246239633969, 222477768273518451, 374016980064153033, 37572605245559079, 882856735146171909, 518391674646717303, 1171606124311300449, 12392559929368437, 11141524669275]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017]

#time def graph : KernelGraph 32 2 30 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.9710s provisional (4855 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 619) (2 ^ 538) (2 ^ 5) (2 ^ 68) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 50 32 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 619) (2 ^ 538) (2 ^ 5) (2 ^ 68) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 18 := by decide +kernel

#time def refs000 : List (Fin 18) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 50 32 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart135

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart136
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis019 (basis)

#time def pivTape : List (Fin 32) :=
  [⟨0, by decide⟩]

#time def freeTape : List (Fin 32) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 31) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩, .inr ⟨30, by decide⟩]

#time def roles : GraphRoles 32 1 31 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [9946536609346648155246269623755207625559739055591365556399116419864600741726608064496864050482047704026566849227364709189307689617465677603475428973515933731599]) [1] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [962444315494271371887568286855108658761466575886270260194486008599598090254319546207307882001832226202821519345336141364810385298252963700684689564127969637043, 962444315494271371887568286855108658761466575886270260194486008599598090254319546207307882001832226202821519345336141364810385298252963700684689564127969637043, 105546781249965916471261924798857831425816250050761065666939204612087170088791737480380081789737819440312015472212972254587938546172889966478687318721840422713561, 47800122320309634158007827587551311900128255497584850055270044096111284673532564707941608869627885868142724311492803772699315428277712144437605944874162244490981, 105546781249965916471261924798857831425816250050761065666939204612087170088791737480380081789737819440312015472212972254587938546172889966478687318721840422713561, 0, 105546781249965916471261924798857831425816250050761065666939204612087170088791737480380081789737819440312015472212972254587938546172889966478687318721840422713561, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [4, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1061007268018421, 7420789397812997, 18911860164832341, 221203545725877, 10430063499000923, 17629649351088043, 338286064751349, 6978382306361243, 17746731870113515, 689763462706613, 11106635628503621, 18774781397571477, 2142881998729547, 8357909231774469, 21607426859007637, 2149146707426955, 15392399625962715, 25899455565164139, 6398194611633717, 12656202646628379, 34446796884224811, 5957479290401013, 28188788849230149, 46802470786259541, 20716194389582475, 24571161227430405, 73476144466243029, 19279497125298123, 69621177628395099, 113471835981123627, 85702075454476917, 63130155478026651]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [218453408560898667, 81224331739641141, 241025328537348933, 385379815755016725, 511485857973973707, 225578818957308933, 978090005468631573, 495475823117271051, 1263997044485296347, 1985051686559876331, 5324095953483368373, 1216530465191851035, 7804623463160515755, 5254890819747838581, 11912188951452033093, 18383610236391722709, 9986433716425381, 655383804075]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [24683953105505, 597672374989909, 253759526760211, 1034941262791, 367997825839925, 474555570312589, 630516192313, 564554254580597, 471320169748765, 34932819872369, 388174343993941, 255648559579819, 36744022265537, 704285534070073, 72871745162193, 59751618804823, 535150433056089, 739221221172727, 53820585841191, 1182298484508657, 966365630464755, 385466235889683, 965715119785617, 364868259509205, 343825352222979, 2724163428067389, 1094382313074741, 386924074629957, 2341016528677533, 4080286276892289, 353074422643989, 8914948622146701]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [7040280265988073, 8906222464118421, 7990207290981357, 8679400210341225, 8386599787943973, 44539838478620385, 8662905668186211, 44555244067340445, 41536606442757249, 132148710595369707, 43251131577299469, 400981791017343945, 307761461884649535, 2808873686097914295, 387545659061153001, 200196088196072673, 532203006625927, 655383804075]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 5, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [66397265376073, 513781370409975, 1226872982503717, 24460605484953, 646694346717669, 1136015111642691, 30296680432953, 464860159440069, 1141851186590691, 47924841595273, 707287707583575, 1220072708618917, 166618376110495, 560709842630615, 1434615926324685, 166706929031567, 1040524459804565, 1767941231466747, 535409248753217, 894123700693749, 2470057409251531, 512580271512273, 2111342957310999, 3518046929517021, 2013966381245223, 1919284243718295, 6044593582274517, 1940265711268695, 6139275719801445, 9998825674788435, 10706838179340201, 5799815666255685]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [22645929565397331, 10478639871641721, 27552952078481847, 43831407616379253, 99015654809511759, 26757095409539127, 153325702297532733, 98201627213487039, 225584261697505365, 350542984320531531, 2903339719256864625, 223160349836513205, 3352084330790883195, 2899784207184828545, 6032263700211234615, 9155208257232576365, 646635123939895, 655383804075]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [19115549486591, 316372623397271, 142984668715281, 1754121775825, 217334952490671, 263345544392321, 1086994896175, 302339649190671, 262011290633021, 23335905028091, 226030911660071, 143760592726731, 24290988280755, 395683269303035, 83787019690577, 20775772908051, 323194864783091, 442542158675267, 19642320055855, 728095635831851, 604214530530891, 305939922998365, 637471985676771, 247180933438169, 289771613090181, 1951855327825311, 792217634920611, 775868757070989, 1796558438037495, 3425944397073381, 749835826358781, 8158805384393223]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [6477353563932921, 13573698625039455, 7795245048907743, 10775361920844969, 13376920008409335, 62453599884551043, 6062667809392341, 46825532816897961, 61302925082545083, 436482525018731751, 46704061344133331, 1560870650025285795, 1184719278306982087, 10926423759811084415, 1555832888094811675, 292752249710969865, 305084886917153, 655383804075]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 6, 0, 9] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [2803924157645, 22307708309281, 50709935037133, 1435635963237, 25598302570207, 46470374916251, 1625297879037, 19436436382807, 46660036832051, 2204357922965, 28848898328281, 50489692634053, 8522294210915, 23845152228737, 61216344767933, 8525562826795, 45893486750111, 78264201805643, 30762643302733, 40896277882327, 117552407935171, 30012863980357, 107418773355577, 178327915218261, 145118150297491, 100922005843041, 353458929496109, 142708346503611, 397655073950559, 641285426297211, 1170443423253021, 386338698850263]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [1954437196053843, 1163027446271349, 2738541920456601, 4287908065578213, 29887286688443331, 2712393591392961, 35338222200292893, 29860964681403211, 62513115297343263, 95086473570139435, 811531292509567379, 62434322954199383, 686583854258024733, 811646325548695259, 1560549469721791495, 2309761472316287371, 26756929597389, 50414138775]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [273008499481, 6521135778363, 6218535542179, 59178619823, 4823901308071, 2806669961697, 37097434193, 6284421299071, 1397814684441, 153946233233, 4972291044843, 6244141104889, 634014522135, 8747561030799, 1873485139989, 1194118036659, 7508349133383, 10516191155409, 579296501153, 18300505324071, 15221613233339, 10808914541099, 16777093151831, 14173856889525, 2638068908677, 61536163488467, 49708903954857, 81669285040207, 58986195690663, 35482616157443, 80848512839595, 388213303649295]) [2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 3, 0, 1, 1, 0, 3, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [152224131254787, 969532818404691, 382380247049043, 2324362412158551, 1935997872731125, 8144475850886823, 3099712960849529, 12215676145846097, 8126371737973543, 40727280788954205, 24438838718545589, 187306342482650729, 138467662809429771, 437048562553038341, 187384338010391169, 15606451394157337, 6764552541141, 50414138775]) [2, 2, 0, 1, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 0, 7] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [37937841349, 584634191745, 637214235585, 48606509539, 613918596727, 1149946278933, 52369897279, 487421172667, 1153709666673, 7998788851, 718658391285, 158758734345, 139504431575, 615401794283, 806534524359, 279130960417, 1276676117585, 2171208872285, 1214523295587, 1173663715117, 3664863128289, 149953681435, 3705722708759, 1519753968839, 4223174730103, 3572922618077, 7862497393521, 8398586961373, 20598421629171, 32569931208621, 183825998828159, 20370096540823]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [224794516998153, 5739992863915, 388250419285489, 74037535933949, 2132650123006053, 387729639831383, 1744660093447617, 4265816652183983, 8142350072738723, 12020437085091323, 35292224240939923, 8143903664536583, 19005970503664617, 2205623230251203, 62442098409141123, 22397041607155947, 337576038467, 4583103525]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 2, 1, 7] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [303623644451, 647654577345, 2613662086689, 19291815211, 253682321887, 2290746627027, 12199019221, 314181381067, 2283653831037, 326014521101, 519563662995, 2621867371359, 332472391305, 954377283235, 3280354283765, 1474020152545, 213009013575, 5086846827615, 1452152216745, 607099358945, 8013019196905, 9607451647745, 2304188271045, 19072623061395, 9527583679605, 12035849083525, 38207658388745, 192111384417325, 5915885975325, 239846626485675, 191857275200445, 102073616750425]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [623815286103445, 4082068427597515, 203689047151095, 3266395866293625, 4083010083520095, 3877921194096665, 11431474377411235, 31024028221963705, 484915129546125, 15509543761032375, 31019473611359505, 848315844620845, 77553045594355585, 152017735764931927, 27140152574990505, 43445216559216837, 729321432785, 4583103525]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 6, 0, 0, 1, 0, 1, 8] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [2182372646083, 15344676293589, 32136500442581, 1644975140845, 14609451502909, 28309152655653, 1718822702875, 12054726011899, 28383000217683, 1949335151173, 18047096908659, 32051158071731, 10006679504253, 15953396314245, 44007172727157, 10010555406195, 38060455917165, 64024407637605, 61214176853115, 35974507126635, 135249139896915, 60922758510405, 160488809623395, 257386075260435, 1110159925690365, 157820024147445, 1428468759461205, 1109226362550675, 2380808661004125, 3647855047702245, 21392552903428965, 2376272749248795]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [16635471493176045, 21395398641622395, 40404297145853805, 59423423038227405, 148189510898827965, 40414524533995995, 67370689218978165, 148179507132757875, 255974724651802125, 363739707250564005, 665418577281567621, 255944489731519755, 153499362898245741, 665462102670311931, 1074862429911333117, 1484380042850125293, 4289859136083, 50414138775]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [1398063092633, 250300983503, 8696431857387, 48286727841, 1646776514353, 7250082036913, 30746542431, 1954121140183, 7232541851503, 1453394727431, 104845191049, 8716683121365, 1470582636521, 1703757933807, 11640660485317, 8857892030481, 3148105693305, 21969135152319, 8805687125685, 12265407898095, 39632714308485, 146299339445325, 5976896409495, 194737740879495, 146106773452275, 39641186835855, 487143853777095, 2535667997755125, 158060566271265, 1902417370525755, 2536278184356525, 2377103250411705]) [0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [6974363552637405, 15848258085977115, 594554404521315, 6337616348983185, 15846012471226245, 6735577417782705, 38031886906186545, 64660269444218547, 13467794853140985, 10782370066805757, 64671052697451207, 51189114608653137, 140113692208475511, 204757891332210033, 25601628922155111, 26853573716685, 2523623737505, 50414138775]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [2647888961899, 63308693191807, 63455796629927, 9003441757033, 53011344220451, 107316595655225, 9220783503655, 45301809677741, 107533937401847, 2476539061177, 71452911227761, 63330438575105, 16829052031057, 65114122167157, 101941620759573, 67332333624619, 206085327476217, 338531783267993, 1009253729959419, 199778789416395, 1415117846852031, 252100018557015, 2224592787395055, 1716385825519755, 3882238469712345, 2216578937872515, 5543891076790905, 15531687664424025, 28833314970303705, 42148423696855215, 86537915367113655, 28846796390975535]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [28857804005834415, 21632403206506575, 144242515763923605, 100962666099487185, 79313515186645257, 144212429261077065, 14399557860790179, 317283127713949173, 490265605729238451, 663336304182110559, 910763281335028059, 490353826166821281, 69856150561031673, 227659287017161281, 1331260956940817667, 875772139421320755, 68751574553725, 655383804075]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [74953130382917, 61450765283247, 303537439179119, 1155558865461, 26420694557427, 227428749930741, 740063118795, 30147603208893, 227013254184075, 76263032262203, 53581452233649, 304016349565073, 76694636359127, 136558238679989, 456974018186403, 1075573432053127, 16284511074097, 1609242086598657, 1074373489314559, 303032917683279, 3759189007966343, 14522428441193841, 1204649577907335, 9688865943912939, 14526894904786845, 13310296770460725, 38738189289893625, 71000740833421875, 6661122663439755, 17735656638741405, 70986634116213795, 28845222031480575]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [159723031588377075, 230746491022017453, 57664388789334285, 36825317426583, 230798110611615393, 173056046959056303, 461581426951059429, 593361329326351311, 43283430455570277, 99018208236323511, 593114933523255351, 13134540073977969, 1087458054613283151, 1307579465795360121, 419981211700974243, 372993522341178381, 94622642390509, 655383804075]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 1, 7] [true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [40227901099279, 184653226877585, 349359642675081, 37307399545309, 124478514698217, 271824342030493, 37705544642659, 110038427786967, 272222487127843, 38973045146929, 199889603983535, 348901076917431, 576425828767185, 187984518080825, 964299950831545, 576464135131995, 1352741261517905, 2117189914730725, 6722159180601445, 1340912788344815, 4028505130738725, 6723714301585855, 12091577099684985, 17474378612926025, 28242523023065505, 12106515814826895, 4044430108553625, 28237542216899715, 44393468946446025, 60524495348518845, 79862336785268541, 44368568618972535]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [8899700780150019, 79877415647987391, 115331204624091057, 150840051653105913, 181349041827613281, 115386262677002247, 49368425473480023, 181296443300442651, 247366879031135505, 313277059654575909, 356885920525159845, 247206623923883055, 137687582429858715, 357113584416077007, 466404962019184185, 576311922511378137, 48698442971795, 655383804075]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [19101322891097, 1257345155657, 38209088403379, 67054152165, 4524502133513, 19040711360117, 43156428315, 4962326470463, 19016813636267, 19176623266247, 1141914640457, 38236593330829, 307242718318037, 12069474868355, 1225854183871253, 3073738618693835, 380325255307285, 1540641716504545, 3074814136947785, 2687515422906475, 7689194472146165, 10757794665466135, 673622220410125, 6213943627815, 5376878778694955, 2017569810639915, 10752669139614115, 12908549977044309, 4029634337874705, 3220997941264761, 12914908190129379, 8873410355764479]) [4, 7, 4, 4, 5, 4, 4, 5, 4, 4, 7, 4, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [22602460225908927, 25358400041970525, 4442636926127337, 10158968374067781, 50670492567996675, 8242494843103023, 81069355903802163, 87897844203107037, 32899944863487327, 43842004268691801, 88117771535327703, 54927864830694945, 132173611469742939, 139851764309797449, 6902228333980047, 80439618695273193, 14327602823619, 655383804075]) [1, 1, 3, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 5, 7] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [22868441164630805, 482321797561491, 1916678694106069, 162182726727317, 172420779642407, 492559850476581, 162573657417467, 157956344106857, 492950781166731, 5242535622147349, 497568094477341, 26219317656841685, 47022287091090411, 7769837127857061, 15560433812101377, 11755202986962789, 39061197579452955, 856277600398773, 32666750628549115, 39250974819994095, 3244667785587205, 130618430332024765, 91605804934743505, 235328090561523585, 255907185098037571, 45683727756015335, 110039335795510779, 16003926353323951, 82150690081647033, 50241333869463751, 26475690717398049, 82347683070576273]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 7, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [29297805141315555, 423141173182946829, 129654835657537359, 612369783530791173, 630829069762431219, 258445807041794283, 404681886951306783, 158115696776486829, 371519398447356501, 107326246239633969, 222477768273518451, 374016980064153033, 37572605245559079, 882856735146171909, 518391674646717303, 1171606124311300449, 12392559929368437, 11141524669275]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016]

#time def graph : KernelGraph 32 1 31 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.9234s provisional (4617 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 1146) (2 ^ 538) (2 ^ 536) (2 ^ 65) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 50 32 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 1146) (2 ^ 538) (2 ^ 536) (2 ^ 65) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 17 := by decide +kernel

#time def refs000 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 50 32 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart136
