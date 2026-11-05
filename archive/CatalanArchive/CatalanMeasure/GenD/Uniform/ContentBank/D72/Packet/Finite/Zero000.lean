module
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.Bases000
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.Bases001
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart010
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis001 (basis)

#time def pivTape : List (Fin 4) :=
  []

#time def freeTape : List (Fin 4) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 4) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩]

#time def roles : GraphRoles 4 0 4 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [841087744955, 31842687635191, 12293268698209, 77900090449, 15648211667735, 23122248927871, 44558906287, 29349884740823, 22855519454575, 1693379234411, 17074096668919, 12452684969641, 1710541809323, 36123401678467, 3538661372877, 3044608322437, 23916263906211, 36109049437213, 2418453862149, 60480268257963, 47035173806385, 19858464154737, 43263894803403, 17932636421355, 15375662270001, 139914124876911, 53482336055079, 20049132980343, 104766543883407, 202536866301531, 15926581802871, 460700252562399]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [346439725434387, 463655348161239, 359591852729343, 436900700403555, 386705025067287, 2315321645207355, 431040443508909, 2329822683055575, 1906411952998491, 6770512165214073, 2071421791171671, 20953903109651955, 15573001113668565, 25427625141373, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [4174038243619, 26434282918605, 67219209864151, 990388481379, 36610888701927, 62054783139153, 1446091167939, 24453505955847, 62510485825713, 2719958953219, 39503071037805, 66676535946871, 9064345948885, 29893423862285, 78460840848975, 9001263296021, 57631762935575, 96526450093881, 29321928956891, 47895950454327, 134849642346793, 27420725669019, 116275620849357, 191592296972703, 109813041813549, 102737401792365, 328826064455271, 103405267500525, 335901704476455, 542044373769345, 578623522428051, 309547936793415]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [1224073163697921, 556911170823891, 1493148749332557, 2359607856949863, 5290106698096869, 1423370278441197, 8206625725870623, 5203179932337189, 12073362145526295, 18699912356304681, 153404597385682155, 11829730143115575, 177307689674324025, 35696624053885, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [871213311893, 16978502562413, 7296850115523, 123080568475, 10466471275893, 13476325782203, 72856342885, 15993858014613, 13375877331023, 1191377284553, 11049322018973, 7356483650673, 1224824643105, 20759367152825, 4282292307251, 1084548570693, 15948620591393, 22692188154881, 980019272785, 38112144283913, 30950459528793, 16040342157295, 31628928955953, 12727719694307, 14523615570423, 102273512913093, 40737418252473, 40746977950815, 89723391237645, 177492407976999, 38009935925391, 428249336519613]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [335006235729411, 713622561588405, 393802878640773, 562324334584299, 688735265928045, 3282739582873233, 315875812085631, 2463816517131081, 3148743942352953, 22926273899661741, 2443471013688923, 82124868131067825, 62184574146221773, 15464913542939, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [164772273455, 1149235894459, 2720974401967, 67479401703, 1406966234053, 2488722726809, 81383841903, 1014277091053, 2502627167009, 120493930535, 1569733917859, 2704504939447, 454930506785, 1255264952123, 3279929376767, 452388143305, 2479594931429, 4187248026857, 1645446991327, 2160041238733, 6285083161489, 1585087643383, 5770488914083, 9515617796199, 7727823983089, 5330216525499, 18828529422671, 7526190063609, 21226136880261, 34082543469369, 61965231553359, 20382596652717]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [103573965086337, 61285006410951, 145156599986979, 226824203050647, 1574938191829569, 142952609474619, 1863047401291167, 1572199444070569, 3295032983646117, 5010185037191305, 42697375594780481, 3287351497615757, 36114991113518607, 1442873337711, 2653375725, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, false, false, false, false, true, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [6725669747, 349165897257, 322247010091, 3995978927, 241522764949, 18209272011, 2409771857, 333181981549, 144881072553, 15975032659, 251161852377, 324121982281, 4090499955, 460982242821, 388796047239, 125375002857, 382057850937, 68361881217, 119231063213, 962482254249, 395750557903, 284251069303, 858982103789, 1479234317625, 136499503993, 3236490808673, 2593734472203, 4297346552713, 3042974167677, 929634880111, 4217114100945, 20425877019525]) [3, 0, 1, 1, 0, 5, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [7975769847273, 51025227391119, 19911430571457, 122219108577729, 12711475279055, 428627696148477, 325961365592407, 2571771643753967, 426678639501217, 67003702372785, 2574077521085347, 9858458878867391, 3644983820384217, 349149689079, 2653375725, 0]) [2, 2, 0, 1, 4, 0, 1, 1, 0, 6, 1, 0, 2, 0, 7, 0] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [4284468487, 30258561535, 67812065415, 2416102941, 33269035393, 61111493987, 2682107001, 25426355653, 61377498047, 3438589327, 38633249395, 67498194375, 14782455025, 32303534307, 85719238727, 14733357523, 68198159445, 115235051275, 64343819113, 61770249353, 194312227911, 63175728855, 196885797671, 321831775879, 446005492569, 188121707063, 831012997303, 442122309587, 1088896782809, 1719140799459, 9681008279081, 1072366326237]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [11842271388127, 9667980837455, 20450913340971, 31191260504663, 224457618334159, 20408328001147, 183598376992041, 224509978690077, 428464323327347, 632565974016277, 1857732831104697, 428611629379007, 1000656878398343, 36048266951, 241215975, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [15464160001, 34569272315, 136344482059, 1270780201, 12935444357, 119609541857, 776040151, 16649246057, 119114801807, 17036494351, 26646928865, 136927336309, 17331638675, 50334986465, 171295469335, 77517567563, 10994641885, 266144675573, 75696948163, 31963138507, 419359191299, 505623685147, 119675515703, 1000679824609, 498900718247, 633476239175, 2005204228003, 10111067566655, 309288116975, 12615172512905, 10087307052847, 5372271902915]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [32813547132407, 214846430740313, 10705883286797, 171945576555059, 214951354922437, 204101886934483, 601743362217809, 1632833583842483, 25530683954455, 816138866702237, 1632167192159515, 44647865528375, 4081139642704235, 37952160515, 241215975, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 6, 0, 1, 8, 0] [true, true, true, true, false, true, false, false, false, false, true, false, true, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [10905429563, 72511237989, 154789445101, 7638798845, 71372777549, 136245216693, 8101920395, 57233640299, 136708338243, 9434344013, 87576618339, 154244602651, 48023971557, 76102328325, 211702918221, 47944254819, 183624561453, 307671144597, 293536971435, 171990837963, 649152370851, 291499390125, 770698504323, 1234188732411, 5314032132741, 754989618213, 6839720255277, 5307278289987, 11398762769805, 17461030678005, 102347418391989, 11369546198187]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [79579109423997, 102369961103475, 193296074014173, 284296488919461, 709090782835365, 193370376008763, 322424332812429, 709000477665699, 1224885491656557, 1740515593313493, 3183430169934741, 1224630579322635, 733914098955549, 20711859333, 241215975, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 0] [false, true, false, true, true, true, true, false, true, false, false, false, false, false, true, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [6584150737, 1210991197, 41389491723, 284122389, 7714740917, 34521218597, 175153899, 9403807187, 34412250107, 6930122959, 246559213, 41517526965, 7004263219, 8166965073, 55451913143, 42373376559, 14894158035, 104829552921, 41988027975, 58707306705, 189190957455, 700001012715, 28441093005, 931179998145, 698567745975, 189677079855, 2329748756835, 12132362523405, 755449931985, 9104046020595, 12137394570525, 11373654203985]) [0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [33373803114525, 75828956418375, 2845486159635, 30317758733325, 75806943156315, 32227651107195, 181953658308015, 309380749173033, 64424998517775, 51620147708703, 309519262196193, 244925446958643, 670520159077929, 11993410615, 241215975, 0]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 1, 6, 0] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [43939445653, 254086884541, 515921714107, 35912645179, 217895383913, 436069623275, 37045895605, 182261594183, 437202873701, 40342929499, 291987175123, 514591698805, 272849863699, 262947453181, 827784492003, 272675014717, 837686902521, 1373309370419, 4087483417437, 808297482615, 5733467802573, 4082508009795, 9012653737395, 13903459229805, 62865193668405, 8973313502205, 44879226428805, 62881655125035, 116717733599415, 170626075222245, 350376858610725, 116789996747865]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [116869128263445, 350322158592315, 584035983622035, 817568145466485, 1284316146010989, 583854320436765, 116425841952189, 1284534496863219, 1984596308399943, 2685276484826397, 3688188360758157, 1985214673289673, 281622620931459, 34991322485, 2653375725, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [301502022491, 250892647161, 1225177616417, 5677752003, 105472574901, 917997841923, 3526648125, 122607447579, 915846738045, 308326177829, 214471797927, 1227699563999, 309936814241, 553541072987, 1845962556069, 4354434690361, 65551076521, 6510334060671, 4347071851057, 1226993940837, 15211840602089, 58795037548263, 4871480463225, 39236125095117, 58822603955955, 53887061784915, 156853766599335, 287453195524005, 26975561746365, 71776824968715, 287356917788565, 116783066869545]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [646586938281285, 934195296579459, 233405794295835, 251440509609, 934613314193559, 700629162840369, 1869060051282627, 2402252908677633, 175301879974431, 401420456798553, 2399642066821353, 106351484114829, 4400474518700433, 381669909727, 2653375725, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 1, 7, 0] [true, true, true, true, false, true, false, false, false, true, true, false, true, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [2140794695929, 9666712564955, 18430403460471, 1951429509919, 6622896199587, 14338179254623, 1978058402209, 5763853545117, 14364808146913, 2056347483079, 10579013004005, 18399214032201, 30344919202935, 9876548511275, 50800480718215, 30341339413737, 71268851409875, 111486739334887, 353766584494903, 70559227338749, 211938505746279, 353883031114297, 636264317579931, 919588121355479, 1486559508930903, 637206834889845, 213088356461127, 1486174672931745, 2336854700281875, 3185822538323775, 4202820628715871, 2335142510973645]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [469176582539649, 4204094466482121, 6068786557149867, 7937738512658343, 9547186189709991, 6073046421990597, 2594646789430473, 9542118564915081, 13025585822270115, 16494657965194599, 18763817170057815, 13011190707839565, 7272959360051865, 1285699884775, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 7, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [8031689089981, 1064979568097, 16068696177647, 33910341465, 1888544407639, 8003096746201, 21194948775, 2096048794729, 7990381353511, 8071999590211, 954869678207, 16083575892497, 8082255428629, 2542012096235, 32237830911337, 80888279900167, 9991994785043, 40568193560201, 80930613748675, 70720231515227, 202387087209043, 283101693309785, 4433663685227, 216007647933, 282942222341807, 106190730897279, 565827908003659, 679391038133997, 212003603378175, 169379092211469, 679945640026149, 467009576339439]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [1189957585948677, 1334665053393015, 233971018323987, 535238172581811, 1332272015896305, 108456934631697, 2131698896707509, 2313179593188651, 864329979248331, 1150791319415163, 2328035344587615, 1445524116135075, 3490423618361103, 6025096316907, 34493884425, 0]) [0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 1, 6, 0] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [4422438325285, 11922576602271, 732993118261, 4011569220437, 4301190462347, 12212197844181, 4023743532587, 3899438161397, 12224372156331, 1014971753093, 12348677527521, 10154001350645, 9098029569777, 12019212186141, 6012114282723, 36393506487993, 60435559030695, 84809853332547, 101148884806775, 60767800789845, 20054475013765, 25273976560625, 141862210582855, 91095158017755, 49505674210097, 141424011695155, 42631762718811, 198197667866933, 254183183097921, 310956839269699, 328071653158827, 254971324038711]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [181082853977805, 81873608916723, 401960123219733, 237241617423957, 121793048775003, 400017547295073, 157402737707397, 489461272784073, 572384266980291, 661827992469291, 697340376482247, 578904998273073, 453948888771117, 9577869768831, 34493884425, 0]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [216983723467207, 53980996468967, 262221526336149, 86901403458663, 245016367457, 41663600589721, 158029356135, 257190679607, 128723033404519, 129534712663609, 31520124390631, 653649902955, 129454641971509, 96614305673913, 259643004538073, 258797021070443, 48967258790439, 130300625439139, 258493263253283, 81091357698265, 386989658884587, 388171012728957, 160558745672405, 257311909408913, 389321863285617, 225988297332427, 520180966605661, 517915517959471, 57190779403303, 391587311931807, 513927229729951, 72981805156761]) [0, 1, 0, 0, 8, 0, 0, 8, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3] [false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [640255435757615, 646386525753345, 285164112116739, 507796139734221, 663505409452269, 354459305126301, 802095795471393, 777519788817075, 189170648667765, 688081416106587, 671788222444251, 211530241845387, 761226595154739, 119801312450839, 34493884425, 34493884425]) [0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1, 9, 9] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016]

#time def graph : KernelGraph 4 0 4 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.6162s provisional (3081 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 982) (2 ^ 917) (2 ^ 0) (2 ^ 58) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 48 4 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 982) (2 ^ 917) (2 ^ 0) (2 ^ 58) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 17 := by decide +kernel

#time def refs000 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 48 4 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 17) := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 48 4 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 17) := [⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 48 4 basis.matrix :=
  verified.pickRows _

#time def refs003 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart003 : Chart :=
  (graph.chart chartRows).pickRows (refs003.map (Fin.cast unionLength.symm))

#time theorem chartSound003 : chart003.Sound 48 4 basis.matrix :=
  verified.pickRows _

#time def refs004 : List (Fin 17) := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart004 : Chart :=
  (graph.chart chartRows).pickRows (refs004.map (Fin.cast unionLength.symm))

#time theorem chartSound004 : chart004.Sound 48 4 basis.matrix :=
  verified.pickRows _

#time def refs005 : List (Fin 17) := [⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart005 : Chart :=
  (graph.chart chartRows).pickRows (refs005.map (Fin.cast unionLength.symm))

#time theorem chartSound005 : chart005.Sound 48 4 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart010

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart018
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis002 (basis)

#time def pivTape : List (Fin 6) :=
  []

#time def freeTape : List (Fin 6) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 6) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩]

#time def roles : GraphRoles 6 0 6 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows : List (List Int) :=
  [chartRows000]

#time def graph : KernelGraph 6 0 6 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.1922s provisional (961 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 1378) (2 ^ 1370) (2 ^ 0) (2 ^ 1) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 47 6 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 1378) (2 ^ 1370) (2 ^ 0) (2 ^ 1) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 1 := by decide +kernel

#time def refs000 : List (Fin 1) := [⟨0, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 47 6 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 1) := [⟨0, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 47 6 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart018

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart028
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis003 (basis)

#time def pivTape : List (Fin 7) :=
  []

#time def freeTape : List (Fin 7) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 7) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩]

#time def roles : GraphRoles 7 0 7 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows : List (List Int) :=
  [chartRows000]

#time def graph : KernelGraph 7 0 7 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.1786s provisional (893 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 597) (2 ^ 589) (2 ^ 0) (2 ^ 1) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 40 7 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 597) (2 ^ 589) (2 ^ 0) (2 ^ 1) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 1 := by decide +kernel

#time def refs000 : List (Fin 1) := [⟨0, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 40 7 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart028

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart038
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis004 (basis)

#time def pivTape : List (Fin 3) :=
  []

#time def freeTape : List (Fin 3) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 3) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩]

#time def roles : GraphRoles 3 0 3 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [5077443, 143531603, 224945857, 8662731, 76336811, 228531145, 13018589, 160857065, 250212465, 62018615, 102373989, 325249669, 51172061, 284894295, 438440345, 279828683, 204718111, 769441089, 226509237, 844551661, 1275779009, 1980283599, 657736585, 3482571845, 1704022285, 4805118859, 7166877729, 43600754971, 4065781155, 52471654985, 57505825, 1091475]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [7526083, 60820927, 309947471, 4499773, 90389767, 306921161, 40422673, 16330175, 351843607, 42822125, 16351555, 435088405, 187211249, 108142825, 665121779, 179320249, 318023689, 1031653277, 1189234141, 143731537, 2400207667, 1154919281, 753628915, 4744361089, 23100948005, 1442382355, 29000228375, 22961271733, 24608205835, 75062448113, 158736777, 1091475]) [0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [4469275, 52711639, 92081823, 5350465, 34900909, 92963013, 6616483, 63412569, 104929961, 35257287, 48133875, 146803731, 32951829, 133927143, 215012847, 219287665, 114037533, 467252341, 207578755, 572502473, 894118761, 4000950311, 529195043, 5102647827, 3941757989, 8574403095, 13045356127, 77219767167, 8412711021, 60232653051, 48275549, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [491571, 5926963, 28290283, 294861, 7972393, 28093573, 5330069, 1519, 33718503, 5482379, 6651231, 44530951, 32632499, 11704203, 82645829, 32090303, 45934961, 147368631, 530488647, 21897253, 709947581, 528149769, 72052951, 1768585997, 9136830671, 571944275, 6840094905, 9146522231, 8560407063, 25123447807, 14390927, 363825]) [0, 1, 0, 0, 1, 0, 0, 13, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [316975, 2108601, 3990967, 342457, 1565391, 4016449, 191205, 2793515, 1185329, 1323881, 2330211, 242859, 2586813, 8089039, 13006063, 39981989, 7503837, 55574865, 19832449, 88053017, 16902719, 307933803, 86833633, 110245239, 617445823, 1143682195, 1674294385, 3430827049, 1148058013, 1139086841, 2153971, 51975]) [0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 5, 0, 0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [823067, 7306631, 66406203, 495845, 9089153, 66078981, 21294533, 15109107, 87869359, 21550761, 39472839, 130714653, 299571657, 9164967, 451837071, 298653377, 21190281, 1050062105, 4026972319, 335313245, 2678256837, 4030919795, 3687927823, 10736148951, 19726889581, 1847803275, 4959820835, 19710473565, 8019480879, 44397183981, 33614635, 363825]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [4949919, 17332727, 36250543, 5101329, 13967897, 36401953, 5352839, 27535385, 46856121, 79881335, 24673575, 132090295, 79542047, 187298055, 291513677, 933115153, 183757669, 562059429, 934915917, 1678932251, 2430090499, 3919052643, 1686074165, 554046227, 3910187545, 6159173035, 8383286415, 11086496759, 6134300925, 1206977201, 20600231, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [33495, 15026437, 4089433, 20265, 17421067, 4076203, 15987187, 15350677, 32373059, 128236229, 81369815, 515118197, 1278493427, 158937583, 635139001, 1279687505, 1115753797, 3193319933, 4483837735, 560374961, 10830297, 2239355951, 1684041969, 4486689967, 5362648557, 839490495, 1363397361, 5373304443, 919651647, 9372555639, 257683, 1091475]) [5, 2, 5, 5, 2, 5, 3, 2, 3, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 2, 1, 1, 3, 1, 1, 4, 1, 8, 5] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [31488119, 33869519, 94662807, 31686569, 29305169, 94861257, 128122409, 97242657, 634313713, 1152204951, 186732747, 389768829, 72118401, 957719637, 673967049, 199954523, 967161669, 162622561, 3190147697, 2241552731, 5738929821, 6269907407, 555746507, 2659170111, 1578615323, 1007088669, 2481299647, 2590342437, 63929301, 1469572533, 63075463, 1091475]) [2, 2, 2, 2, 2, 2, 0, 2, 0, 0, 1, 0, 4, 1, 2, 4, 1, 2, 0, 1, 0, 0, 3, 0, 2, 3, 2, 2, 7, 2, 2, 6] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [7541879007, 341905759, 3783304481, 25456863, 365918209, 11350640351, 11264799425, 2760702935, 111297789, 11251311677, 8337453753, 22404813313, 22566604387, 4245304371, 11089520603, 22520224891, 7114575317, 33997308675, 33599451429, 14029616149, 22918082137, 33798488985, 19370300795, 44479858277, 45937371911, 4942218209, 32340975351, 45111030839, 6641767779, 58707427399, 1879287263, 12006225]) [0, 4, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 7] [false, true, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [12006225]) [7] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009]

#time def graph : KernelGraph 3 0 3 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.2662s provisional (1331 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 485) (2 ^ 441) (2 ^ 0) (2 ^ 37) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 33 3 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 485) (2 ^ 441) (2 ^ 0) (2 ^ 37) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 10 := by decide +kernel

#time def refs000 : List (Fin 10) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 33 3 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 10) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 33 3 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart038

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart043
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis005 (basis)

#time def pivTape : List (Fin 1) :=
  []

#time def freeTape : List (Fin 1) :=
  [⟨0, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 1) :=
  [.inr ⟨0, by decide⟩]

#time def roles : GraphRoles 1 0 1 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0]) [1, 0, 0, 0, 0] [true, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [1756568163, 74895984593, 116555197429, 3381025683, 39902644673, 118179654949, 5767454275, 81658035959, 127328134907, 24085436125, 51437553223, 157181025307, 20008191245, 129828908209, 201274652677, 90346693187, 91453935713, 311629537109, 71297838803, 310522294583, 473274069099, 435469204205, 234049613319, 980041112107, 355649265405, 1181460702993, 1771159581717, 3569603772915, 945348144129, 5696412620037, 3116206618467, 8320668248823]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [12382223011419, 14788970699, 156080925, 0, 0]) [0, 2, 9, 0, 0] [true, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [225220265, 15669960809, 19984113219, 139061591, 23397384569, 19811795871, 2003648263, 16782453537, 5523391829, 2177389845, 31411977621, 1642162839, 4002014241, 25492012917, 36456023751, 3807112439, 63428091549, 52074277111, 35530711987, 55948912429, 11902401747, 33879751613, 205550939497, 20578709697, 130527755935, 191467918881, 459564941059, 127466593131, 1249772986977, 975553639191, 6049229393703, 1211200663929]) [2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 5, 2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [1819929054789, 20434553749, 156080925, 0, 0]) [3, 0, 7, 0, 0] [true, false, true, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [109976559, 1850627039, 3174704341, 137458503, 1214100743, 3202186285, 184092857, 2125544045, 3523737645, 832550795, 1582286457, 4540381297, 773962193, 3790645635, 6146894285, 3697576679, 3130210843, 10618433157, 3408468081, 11185798993, 17724477917, 25981171587, 9947147005, 47114117585, 24791387425, 63148142167, 97886676597, 568488328663, 59529921855, 691166392685, 561923003353, 1200124799493]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [1821577724701, 821170225, 14189175, 0, 0]) [0, 1, 7, 0, 0] [true, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [64674619, 805361131, 3872289623, 40051909, 1098446371, 3847666913, 516313129, 52838315, 4404031951, 540817925, 403689875, 5461163005, 2358011417, 1386230965, 8359992347, 2299316737, 3972770917, 13017320501, 15130343413, 1842773851, 30446980651, 14884897673, 9551557165, 60462221737, 298406217485, 18570445375, 373753336895, 297496343773, 317509331815, 969655898153, 6313325117087, 79016697287]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [5046172875161, 1968482121, 14189175, 0, 0]) [0, 0, 7, 0, 0] [false, false, true, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [66977695, 674232187, 1233465939, 74441485, 492256057, 1240929729, 88114839, 823115157, 1403486053, 461890091, 668485735, 1953490983, 447536977, 1746895339, 2862918051, 2856919805, 1563559689, 6167374833, 2783210935, 7460734949, 11807505573, 52038046283, 7129981559, 66628762791, 51738132641, 111536827515, 170404941715, 1003636246707, 110606246841, 781493172351, 1005260594505, 1895735665899]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [2790390013563, 650221817, 4729725, 0, 0]) [0, 0, 7, 0, 0] [false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [4536073, 78435319, 361004129, 2820343, 99798709, 359288399, 68905047, 40627831, 431013789, 70634477, 42175939, 570553313, 420383837, 151890139, 1061571627, 416230489, 589087593, 1898185953, 6879190361, 142030157, 9193606803, 6861892347, 3734138977, 22934689511, 118880044853, 7430012975, 89083462995, 118943929853, 111411766899, 326907437701, 743780028451, 55756958439]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [297928660897, 182770101, 4729725, 0, 0]) [0, 0, 5, 0, 0] [true, false, true, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [15218675, 94602033, 184228511, 16014281, 74407803, 185024117, 4387095, 126630595, 109293389, 15089137, 109504563, 178424127, 119295729, 368056787, 596857079, 1819474237, 348096021, 2535627045, 226494173, 4007005261, 3083527333, 7005163887, 3972002789, 10020823749, 28051016339, 52034305835, 76113319385, 156117205577, 52130029889, 51952869853, 19494369433, 260200105319]) [0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [182012515447, 99723593, 4729725, 0, 0]) [1, 0, 4, 0, 0] [true, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [11862669, 144392667, 1282132221, 7404915, 173174721, 1277674467, 414530531, 296190249, 1699609913, 419114327, 760879973, 2533254771, 5833471399, 5588317, 8785840497, 5822650339, 1648587843, 20441962235, 78563131533, 6537954915, 52298518959, 78608165265, 71968780161, 209469815757, 384452353887, 36035105175, 96374372865, 384286699095, 156241786863, 865113425847, 1248057026169, 312216488745]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 8, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [1343098773, 646997445, 14189175, 0, 0]) [0, 0, 5, 0, 0] [true, false, true, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [196773361, 668730933, 1424378977, 200959711, 558874683, 1428565327, 209346061, 1070650355, 1838871099, 3116277165, 977566805, 5164494325, 3109263873, 7303204685, 11390035363, 36390842767, 7196094551, 21891543531, 36429128623, 65478480849, 94711514921, 152846489937, 65662162695, 21705846393, 152692833495, 240214499025, 327245169825, 432319729689, 239723504295, 47618273631, 433132531959, 624424960353]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [817833988017, 810576169, 14189175, 0, 0]) [0, 0, 5, 0, 0] [false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [58171575, 2167608671, 9307191959, 36446025, 2456901521, 9285466409, 9141969209, 275506837, 18463881643, 18329592637, 5799435365, 73541294341, 182893926211, 22737702029, 91023039233, 182999129125, 159696184751, 456916094569, 640869771035, 20032678387, 954547341, 160107897299, 120293396571, 320563976893, 383909621109, 120042540525, 96762253083, 192155550759, 131808112269, 83932308693, 378449129085, 264268560993]) [1, 2, 1, 1, 2, 1, 1, 5, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 2, 3, 2, 2, 3, 2, 3, 4, 5, 3, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [74717828223, 4682681767, 156080925, 0, 0]) [4, 1, 5, 0, 0] [false, false, true, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [2259800771, 2403875471, 6789693363, 2270091821, 2126017121, 6799984413, 18330736087, 6944059113, 90891345959, 164751590793, 26834804571, 55529508747, 41220635397, 136975354341, 48145455141, 114374736331, 138047737017, 5784202337, 456765655471, 320523590983, 821717363403, 896567602801, 159358959227, 381915416073, 112437178697, 288022005909, 88384351019, 185308624983, 290389755561, 12987156969, 1467096594303, 453212494023]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 6, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [2118387548151, 4524747067, 156080925, 0, 0]) [0, 3, 6, 0, 0] [true, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [1276180345683, 29000487323, 635504841389, 3444945747, 30739674773, 1915130132819, 1903959164525, 467452742915, 14615914041, 1901774999513, 1412124368157, 3791118249997, 3810827731303, 717161128299, 1882065518207, 3805926068479, 1199351681573, 5734688281575, 5691889236801, 2371603811881, 3848725113253, 5712339717765, 3293185873655, 7555503841313, 7681148866619, 835183976471, 5586694692459, 7606442302571, 1096990748241, 9700896476731, 9148242486357, 4265706396687]) [0, 5, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1] [false, true, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [8159096292945, 320337752147, 2029052025, 2029052025, 0]) [0, 0, 7, 7, 0] [false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [1427254563, 106426930193, 170725621429, 3710339283, 62871436673, 173008706149, 9211387075, 113847608759, 185930432507, 30882380125, 81294210823, 226024199707, 30232436045, 175612369009, 287139015877, 113237869187, 141759082913, 430609321109, 103304459603, 402088107383, 647151649899, 521815895405, 348368002119, 1272272004907, 484510675005, 1445719898193, 2278598575317, 4024910095155, 1317389352129, 6788019345477, 3891868545507, 9495540088503]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [14704797986139, 21519109499, 156080925, 0, 156080925]) [0, 2, 9, 0, 9] [true, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0]) [0, 0, 0, 0, 0] [false, false, false, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035]

#time def graph : KernelGraph 1 0 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.8442s provisional (4221 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 359) (2 ^ 308) (2 ^ 0) (2 ^ 44) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 37 1 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 359) (2 ^ 308) (2 ^ 0) (2 ^ 44) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 36 := by decide +kernel

#time def refs000 : List (Fin 36) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 36) := [⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 36) := [⟨24, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs003 : List (Fin 36) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩]
#time def chart003 : Chart :=
  (graph.chart chartRows).pickRows (refs003.map (Fin.cast unionLength.symm))

#time theorem chartSound003 : chart003.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs004 : List (Fin 36) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩]
#time def chart004 : Chart :=
  (graph.chart chartRows).pickRows (refs004.map (Fin.cast unionLength.symm))

#time theorem chartSound004 : chart004.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs005 : List (Fin 36) := [⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩]
#time def chart005 : Chart :=
  (graph.chart chartRows).pickRows (refs005.map (Fin.cast unionLength.symm))

#time theorem chartSound005 : chart005.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs006 : List (Fin 36) := [⟨24, by decide⟩]
#time def chart006 : Chart :=
  (graph.chart chartRows).pickRows (refs006.map (Fin.cast unionLength.symm))

#time theorem chartSound006 : chart006.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs007 : List (Fin 36) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩]
#time def chart007 : Chart :=
  (graph.chart chartRows).pickRows (refs007.map (Fin.cast unionLength.symm))

#time theorem chartSound007 : chart007.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs008 : List (Fin 36) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩]
#time def chart008 : Chart :=
  (graph.chart chartRows).pickRows (refs008.map (Fin.cast unionLength.symm))

#time theorem chartSound008 : chart008.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs009 : List (Fin 36) := [⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩]
#time def chart009 : Chart :=
  (graph.chart chartRows).pickRows (refs009.map (Fin.cast unionLength.symm))

#time theorem chartSound009 : chart009.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs010 : List (Fin 36) := [⟨24, by decide⟩]
#time def chart010 : Chart :=
  (graph.chart chartRows).pickRows (refs010.map (Fin.cast unionLength.symm))

#time theorem chartSound010 : chart010.Sound 37 1 basis.matrix :=
  verified.pickRows _

#time def refs011 : List (Fin 36) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩]
#time def chart011 : Chart :=
  (graph.chart chartRows).pickRows (refs011.map (Fin.cast unionLength.symm))

#time theorem chartSound011 : chart011.Sound 37 1 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart043

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart053
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis007 (basis)

#time def pivTape : List (Fin 1) :=
  []

#time def freeTape : List (Fin 1) :=
  [⟨0, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 1) :=
  [.inr ⟨0, by decide⟩]

#time def roles : GraphRoles 1 0 1 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0]) [1, 0, 0, 0, 0, 0, 0] [true, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 1, 0, 0, 0]) [0, 0, 0, 1, 0, 0, 0] [false, false, false, true, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [1756568163, 74895984593, 116555197429, 3381025683, 39902644673, 118179654949, 5767454275, 81658035959, 127328134907, 24085436125, 51437553223, 157181025307, 20008191245, 129828908209, 201274652677, 90346693187, 91453935713, 311629537109, 71297838803, 310522294583, 473274069099, 435469204205, 234049613319, 980041112107, 355649265405, 1181460702993, 1771159581717, 3569603772915, 945348144129, 5696412620037, 3116206618467, 8320668248823]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [12382223011419, 92183850623613, 7177761381063, 107682280253499, 14788970699, 156080925, 0]) [0, 0, 0, 0, 2, 9, 0] [true, false, true, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [225220265, 15669960809, 19984113219, 139061591, 23397384569, 19811795871, 2003648263, 16782453537, 5523391829, 2177389845, 31411977621, 1642162839, 4002014241, 25492012917, 36456023751, 3807112439, 63428091549, 52074277111, 35530711987, 55948912429, 11902401747, 33879751613, 205550939497, 20578709697, 130527755935, 191467918881, 459564941059, 127466593131, 1249772986977, 975553639191, 6049229393703, 1211200663929]) [2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 5, 2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [1819929054789, 6023177591501, 25446690561789, 2419015400545, 20434553749, 156080925, 0]) [3, 1, 0, 4, 0, 7, 0] [true, false, true, false, false, true, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [109976559, 1850627039, 3174704341, 137458503, 1214100743, 3202186285, 184092857, 2125544045, 3523737645, 832550795, 1582286457, 4540381297, 773962193, 3790645635, 6146894285, 3697576679, 3130210843, 10618433157, 3408468081, 11185798993, 17724477917, 25981171587, 9947147005, 47114117585, 24791387425, 63148142167, 97886676597, 568488328663, 59529921855, 691166392685, 561923003353, 1200124799493]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [1821577724701, 13209241506965, 1183375928561, 10825740778911, 821170225, 14189175, 0]) [0, 0, 0, 0, 1, 7, 0] [true, true, true, true, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [64674619, 805361131, 3872289623, 40051909, 1098446371, 3847666913, 516313129, 52838315, 4404031951, 540817925, 403689875, 5461163005, 2358011417, 1386230965, 8359992347, 2299316737, 3972770917, 13017320501, 15130343413, 1842773851, 30446980651, 14884897673, 9551557165, 60462221737, 298406217485, 18570445375, 373753336895, 297496343773, 317509331815, 969655898153, 6313325117087, 79016697287]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [5046172875161, 6317307457363, 749476973159, 17676805449611, 1968482121, 14189175, 0]) [0, 0, 4, 0, 0, 7, 0] [false, true, false, true, false, true, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [66977695, 674232187, 1233465939, 74441485, 492256057, 1240929729, 88114839, 823115157, 1403486053, 461890091, 668485735, 1953490983, 447536977, 1746895339, 2862918051, 2856919805, 1563559689, 6167374833, 2783210935, 7460734949, 11807505573, 52038046283, 7129981559, 66628762791, 51738132641, 111536827515, 170404941715, 1003636246707, 110606246841, 781493172351, 1005260594505, 1895735665899]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [2790390013563, 6950518630475, 1899914942169, 3154868022407, 650221817, 4729725, 0]) [0, 0, 0, 0, 0, 7, 0] [false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [4536073, 78435319, 361004129, 2820343, 99798709, 359288399, 68905047, 40627831, 431013789, 70634477, 42175939, 570553313, 420383837, 151890139, 1061571627, 416230489, 589087593, 1898185953, 6879190361, 142030157, 9193606803, 6861892347, 3734138977, 22934689511, 118880044853, 7430012975, 89083462995, 118943929853, 111411766899, 326907437701, 743780028451, 55756958439]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [297928660897, 743498280049, 39523016347, 1785206969397, 182770101, 4729725, 0]) [0, 0, 5, 0, 0, 5, 0] [true, false, true, false, false, true, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [15218675, 94602033, 184228511, 16014281, 74407803, 185024117, 4387095, 126630595, 109293389, 15089137, 109504563, 178424127, 119295729, 368056787, 596857079, 1819474237, 348096021, 2535627045, 226494173, 4007005261, 3083527333, 7005163887, 3972002789, 10020823749, 28051016339, 52034305835, 76113319385, 156117205577, 52130029889, 51952869853, 19494369433, 260200105319]) [0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [182012515447, 143115667835, 259779881039, 26241342491, 99723593, 4729725, 0]) [1, 2, 0, 1, 0, 4, 0] [true, true, true, true, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [11862669, 144392667, 1282132221, 7404915, 173174721, 1277674467, 414530531, 296190249, 1699609913, 419114327, 760879973, 2533254771, 5833471399, 5588317, 8785840497, 5822650339, 1648587843, 20441962235, 78563131533, 6537954915, 52298518959, 78608165265, 71968780161, 209469815757, 384452353887, 36035105175, 96374372865, 384286699095, 156241786863, 865113425847, 1248057026169, 312216488745]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 8, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [1343098773, 1248788894997, 935573452443, 2495502822393, 646997445, 14189175, 0]) [0, 0, 1, 0, 0, 5, 0] [true, true, false, true, false, true, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [196773361, 668730933, 1424378977, 200959711, 558874683, 1428565327, 209346061, 1070650355, 1838871099, 3116277165, 977566805, 5164494325, 3109263873, 7303204685, 11390035363, 36390842767, 7196094551, 21891543531, 36429128623, 65478480849, 94711514921, 152846489937, 65662162695, 21705846393, 152692833495, 240214499025, 327245169825, 432319729689, 239723504295, 47618273631, 433132531959, 624424960353]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [817833988017, 981188582889, 626541559623, 269777937087, 810576169, 14189175, 0]) [0, 0, 0, 0, 0, 5, 0] [false, false, false, true, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [58171575, 2167608671, 9307191959, 36446025, 2456901521, 9285466409, 9141969209, 275506837, 18463881643, 18329592637, 5799435365, 73541294341, 182893926211, 22737702029, 91023039233, 182999129125, 159696184751, 456916094569, 640869771035, 20032678387, 954547341, 160107897299, 120293396571, 320563976893, 383909621109, 120042540525, 96762253083, 192155550759, 131808112269, 83932308693, 378449129085, 264268560993]) [1, 2, 1, 1, 2, 1, 1, 5, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 2, 3, 2, 2, 3, 2, 3, 4, 5, 3, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [74717828223, 3020500623855, 15415063551, 4852608404967, 4682681767, 156080925, 0]) [4, 0, 8, 0, 1, 5, 0] [false, false, true, false, false, true, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [2259800771, 2403875471, 6789693363, 2270091821, 2126017121, 6799984413, 18330736087, 6944059113, 90891345959, 164751590793, 26834804571, 55529508747, 41220635397, 136975354341, 48145455141, 114374736331, 138047737017, 5784202337, 456765655471, 320523590983, 821717363403, 896567602801, 159358959227, 381915416073, 112437178697, 288022005909, 88384351019, 185308624983, 290389755561, 12987156969, 1467096594303, 453212494023]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 6, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [2118387548151, 2216013111393, 886317083181, 1369471031061, 4524747067, 156080925, 0]) [0, 0, 1, 0, 3, 6, 0] [true, true, true, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [1276180345683, 29000487323, 635504841389, 3444945747, 30739674773, 1915130132819, 1903959164525, 467452742915, 14615914041, 1901774999513, 1412124368157, 3791118249997, 3810827731303, 717161128299, 1882065518207, 3805926068479, 1199351681573, 5734688281575, 5691889236801, 2371603811881, 3848725113253, 5712339717765, 3293185873655, 7555503841313, 7681148866619, 835183976471, 5586694692459, 7606442302571, 1096990748241, 9700896476731, 9148242486357, 4265706396687]) [0, 5, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1] [false, true, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [8159096292945, 9477772876401, 4760279493393, 10466919069813, 320337752147, 2029052025, 2029052025]) [0, 0, 1, 0, 0, 7, 7] [false, false, true, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037]

#time def graph : KernelGraph 1 0 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.9366s provisional (4683 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 362) (2 ^ 308) (2 ^ 0) (2 ^ 47) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 39 1 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 362) (2 ^ 308) (2 ^ 0) (2 ^ 47) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 38 := by decide +kernel

#time def refs000 : List (Fin 38) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 39 1 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 38) := [⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 39 1 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 38) := [⟨25, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 39 1 basis.matrix :=
  verified.pickRows _

#time def refs003 : List (Fin 38) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩]
#time def chart003 : Chart :=
  (graph.chart chartRows).pickRows (refs003.map (Fin.cast unionLength.symm))

#time theorem chartSound003 : chart003.Sound 39 1 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart053

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart057
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis008 (basis)

#time def pivTape : List (Fin 8) :=
  []

#time def freeTape : List (Fin 8) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 8) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩]

#time def roles : GraphRoles 8 0 8 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001]

#time def graph : KernelGraph 8 0 8 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.2624s provisional (1312 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 1723) (2 ^ 1715) (2 ^ 0) (2 ^ 1) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 47 8 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 1723) (2 ^ 1715) (2 ^ 0) (2 ^ 1) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 2 := by decide +kernel

#time def refs000 : List (Fin 2) := [⟨0, by decide⟩, ⟨1, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 47 8 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 2) := [⟨0, by decide⟩, ⟨1, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 47 8 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart057

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart065
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis009 (basis)

#time def pivTape : List (Fin 2) :=
  []

#time def freeTape : List (Fin 2) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 2) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 2 0 2 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [232076440787, 1019434538685, 3051292519943, 28506852627, 1799781540471, 2790709226529, 62951677107, 962420833431, 2825154051009, 121589003507, 1925684894685, 3009694731623, 457799757605, 1205598840445, 3589083492735, 385144090213, 2841284409895, 4432027340553, 1526334164683, 1975887020871, 6343505595449, 1188974705547, 5893952739261, 9058814465679, 5885588004477, 4353836431965, 16133377175703, 4651881734205, 17665128748215, 26670846914385, 31991287063683, 13657599900375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [63314015712273, 26494785428163, 81647702875581, 121800088204119, 301370630251317, 66647170756701, 449665503883599, 266444035730037, 684388963378215, 1017480169864953, 1641684480365, 2029052025, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0] [true, false, true, false, true, false, true, false, true, false, false, true, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [53770695739, 1199556674869, 128465493921, 5014608595, 748349836389, 953894821249, 3179357485, 1119322937349, 946553816809, 77282625859, 799219556149, 32392308519, 86185457715, 1428453440785, 600010978091, 141126010683, 1143961387009, 1568459435263, 133904371195, 2557461526249, 2118520199019, 1023051255665, 2215196356569, 1704690098537, 961955832129, 6649666548909, 1348596821217, 632754195075, 6063019685085, 11418376677597, 606908491107, 26897800791309]) [1, 0, 4, 3, 0, 1, 3, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 4, 0, 1, 4, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [21335678167053, 43152428092095, 25484091400509, 17335843547001, 42353611052655, 199507513159689, 77424706666377, 583436412072717, 194898535611129, 1364075848530843, 1081494647107, 2029052025, 0, 0]) [1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 0, 9, 0, 0] [true, false, true, false, true, false, true, false, true, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [9381981583, 55243881899, 139223964335, 3282808263, 74598100853, 126559174489, 4276996143, 48678265373, 127553362369, 6201526375, 83152093139, 138031884887, 25020685825, 61081318123, 169254097087, 23280098345, 133193464789, 217554881257, 92210572127, 107641514813, 333045551729, 83455622903, 317614609043, 508711746759, 441331665425, 274552760619, 1033499035087, 409699038105, 1200277939893, 1884529738617, 3597812296335, 1093950836829]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [5892041073057, 3460430487687, 8395902532563, 12950283857079, 92416989586593, 8014811812203, 108827703931359, 91567888576649, 193229881705749, 292812582094601, 74302972959, 156080925, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0] [true, false, true, false, true, false, true, false, true, false, false, true, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [1614854809, 23113801581, 10562923729, 76643779, 15908183717, 19204417533, 48726589, 21887501117, 19092748773, 1971743929, 16687809141, 10629699529, 2106184095, 29774476833, 12668663541, 241311753, 25112545521, 35165487273, 1872679951, 60662381217, 50378183173, 34460555053, 55075424737, 46164729015, 33497344511, 198504601429, 80143678797, 64056117221, 189064802781, 450009170989, 63245584995, 1223402476965]) [1, 0, 2, 3, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 6, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [959215979853, 6018027291849, 1200994162701, 3615112805841, 6005457538535, 25295511644361, 9626855221033, 9449089476781, 25222824316841, 125926263647895, 22740702267, 156080925, 0, 0]) [1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 0, 7, 0, 0] [true, false, true, false, true, false, true, true, true, true, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [246986891, 1579294775, 3650741235, 130978113, 1824459569, 3272776231, 149487093, 1317338549, 3291285211, 187881131, 2123433755, 3628653435, 841310525, 1693100811, 4657845091, 812593919, 3806054805, 6311749535, 3710572949, 3318288649, 10834916403, 3557374755, 11227200703, 18102864107, 26020581237, 10433038159, 47680820099, 25471187791, 63268363177, 99172589127, 568704819973, 61375413741]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [693348596891, 566357841355, 1200678003123, 1828411258219, 13207065181667, 1194091096451, 10812296082093, 13221314004561, 25213452360211, 37240675268321, 1948864063, 14189175, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0] [true, false, true, false, false, false, false, true, false, true, false, true, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [459238819, 276128705, 4306060141, 47128279, 818895841, 3799693043, 30073129, 1057386541, 3782637893, 513663589, 424484485, 4326374611, 534469025, 785525065, 5374507225, 2327243357, 1383437995, 8236219607, 2291443717, 3898293487, 12854906681, 15010273873, 229680107, 30156624271, 14861707013, 295446365, 60028605157, 297853346225, 18536588725, 372743658395, 297355974913, 316761913585]) [0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 7, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [967952979533, 6316959119267, 157946281819, 5051650164821, 6318882289783, 3000098602841, 17687491573871, 48037506257957, 6002989726145, 24031132394303, 297831185, 14189175, 0, 0]) [0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 3, 7, 0, 0] [true, true, true, true, false, true, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [211218273, 1317763479, 2859722231, 144001175, 1330740479, 2504502783, 154565825, 1029761129, 2515067433, 177526263, 1639872129, 2847159521, 927000607, 1384813655, 3951686391, 912044969, 3493873343, 5790731967, 5717071105, 3208903593, 12419848041, 5633310455, 14928015553, 23770229601, 104085208351, 14475524503, 133488748407, 103786350697, 223098432255, 341360307455, 2007209442879, 222048225897]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [1562062784727, 2008471057545, 3791320453503, 5577743285151, 13901834834335, 3794893889193, 6315620491639, 13894272914089, 24012349215167, 34111728240063, 383867563, 4729725, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 0, 0] [false, true, false, true, true, true, true, false, true, false, false, true, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [194533609, 604986817, 1276523655, 10307019, 477003229, 1071683027, 6601269, 584372779, 1067977277, 206345191, 490205767, 1280923737, 210950731, 997063161, 1698219659, 1255738761, 912107229, 3164909151, 1247954577, 3508540683, 5668602489, 20616062883, 3408016383, 27532619949, 20583741471, 44740666449, 68732424303, 356740390659, 44575499325, 267424224885, 356848098579, 668740114869]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [981012714123, 2230674133983, 669120697833, 892813321281, 2230259252067, 3792608153097, 5353746707331, 9096835981983, 3791397806301, 1512830022585, 91941079, 14189175, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 5, 0, 0] [false, false, false, false, true, false, true, true, true, true, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [233366449, 1294919563, 2651329351, 188499907, 1123043339, 2229462995, 195470605, 917919749, 2236433693, 211159327, 1513984549, 2643063625, 1450102927, 1340238403, 4304325879, 1440949741, 4414190403, 7195378547, 21834540861, 4222137885, 30470869149, 21781052175, 48083272125, 74086462185, 336245926785, 47784242235, 240378412425, 336436083075, 624408581445, 913060422285, 1873429232205, 625087923915]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [623932726845, 1872633781935, 3122449882965, 4369995740985, 6869170375137, 3120179639955, 626540852217, 6873891736467, 10615890867309, 14369602963821, 360586975, 14189175, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 0, 0] [true, false, true, false, false, false, false, true, false, true, false, true, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [2220969671, 7701024399, 9279926567, 12671967, 6416889393, 1752067257, 8143905, 7498272927, 1747539195, 2278645289, 6547191873, 9301377689, 2301602531, 16612854083, 13881625509, 16030637063, 15753601997, 24122251083, 2001462787, 144857950587, 28082295221, 432189045963, 143847220365, 287836460487, 432346669965, 1583898233265, 1152372176415, 1057028179935, 1585539459495, 264668756745, 1056766556865, 6872327206215]) [1, 0, 1, 3, 0, 3, 3, 0, 3, 1, 0, 1, 1, 0, 1, 2, 0, 2, 5, 0, 3, 1, 0, 1, 1, 0, 1, 2, 0, 2, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [2378463493545, 6867200642649, 6868592995425, 3259458171, 6869208369639, 20596475364381, 13733149554117, 4418882747697, 20608240483131, 365853366621, 5750448119, 156080925, 0, 0]) [2, 1, 0, 1, 1, 0, 1, 3, 0, 4, 1, 5, 0, 0] [true, true, true, false, false, true, false, false, false, true, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [9656997569, 42552489535, 81392283711, 8763981599, 29182796607, 62971304543, 8901424289, 25024526337, 63108747233, 9219513599, 46985645185, 81229685121, 137140025535, 43463553535, 227589224255, 136970843097, 321265696255, 501700092887, 1601194201703, 317405239729, 962523265719, 1602221532497, 2881122707151, 4165938999919, 6725239940463, 2887037825265, 957079408047, 6721597465665, 10569357173775, 14403916814175, 19021826501631, 10556157106065]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [2103687778209, 19036952835441, 27474295829487, 35955091558863, 43178165061711, 27517748564817, 11813879332593, 43089080959641, 58882034293935, 74453366688759, 355661255, 156080925, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 0, 0] [true, true, false, true, true, true, false, false, true, false, false, true, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [236316251629, 128877807287, 478654103843, 1196590395, 113460044927, 241141261819, 771455685, 126484626497, 240716127109, 237668952979, 115002956297, 479156535773, 119109143003, 601822532455, 477521887379, 297262560011, 591439528309, 296209604831, 1189491513605, 4154378427721, 2970960963311, 2082339934625, 4166526526111, 2113696167, 8325673836893, 12504341049279, 16663488360061, 19972508233713, 12484821147675, 5016653963241, 19984704364341, 27440675418147]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 2, 1, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [34940558634813, 39296805595545, 27484587581007, 15628457403609, 4906272149295, 51152935772943, 7864815673287, 33884672721867, 51015766807713, 17199678568461, 44685647217, 2029052025, 0, 0]) [0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 3, 5, 0, 0] [false, false, false, true, true, false, true, true, true, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [520370956927, 694633994427, 12189902201, 235602768859, 248588701819, 707619927387, 236414389669, 223428456709, 708431548197, 119168387903, 721417481157, 147897839209, 1070827651617, 700102008321, 180033953439, 2142598774119, 3561893125311, 5004389891109, 5947453335577, 3585095539917, 1199535329651, 2970758949899, 8333013545843, 2672358976431, 5827784482709, 8297940259679, 621923105013, 11676571108363, 14978124384993, 18356755233677, 19272765154677, 15055201957047]) [1, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 3, 0, 0, 0, 0, 0] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [10760561187363, 9593034939267, 23567405924361, 3462284230731, 14389919702877, 23316937800021, 4526126079657, 29287156726215, 33992272887147, 39962491813341, 569130565731, 2029052025, 0, 0]) [0, 1, 0, 3, 1, 0, 2, 0, 0, 0, 0, 6, 0, 0] [true, true, false, true, true, true, false, false, true, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [3190621753079, 787562519929, 3835040042133, 1277264519631, 232676687701, 632846230577, 2842223055, 244850999851, 1912952973263, 1904022043913, 468195598457, 11773152405, 1901977616213, 1414320044211, 3794226507721, 3809221560451, 358445504439, 1886982563483, 3806023514971, 149681344765, 5728262511939, 5698459531389, 2372241497215, 3835826495521, 5711868330849, 3303558015149, 7574501366717, 7649938606967, 1669813416817, 5636431090599, 7605692223527, 2173190295909]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [9619199739895, 9358855408305, 4266065389893, 7866036555117, 9527461006893, 5012474816487, 11020279860081, 12362834198955, 657674452125, 8184906668019, 1756415448803, 2029052025, 2029052025, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 1, 7, 7, 0] [false, false, false, true, true, false, true, true, true, false, false, true, true, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [347876685347, 1570317591405, 4476633797303, 22013886147, 2558439520551, 4106743225809, 69444643587, 1526289819111, 4154173983249, 194721182627, 2697328807725, 4418339809463, 594862683605, 1915732184365, 5207923675695, 590555776693, 3887054174935, 6393342135993, 1952597522203, 3096843737751, 8936495434889, 1768340612667, 7792249219341, 12657433569759, 7276680667437, 6633524963085, 21702454849863, 6616426796685, 22345610554215, 35595562313985, 37762894265043, 19866378556455]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [79974883375713, 35387915994483, 97871399084301, 153125693635239, 335788180698597, 90642210545421, 524301790328319, 327362069947077, 769447760481495, 1187452040973993, 2412255241325, 2029052025, 0, 2029052025]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 10] [true, false, true, false, true, false, true, false, true, false, false, true, false, true]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016]

#time def graph : KernelGraph 2 0 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.5406s provisional (2703 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 461) (2 ^ 402) (2 ^ 0) (2 ^ 52) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 46 2 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 461) (2 ^ 402) (2 ^ 0) (2 ^ 52) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 17 := by decide +kernel

#time def refs000 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 46 2 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 17) := [⟨14, by decide⟩, ⟨15, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 46 2 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 17) := [⟨15, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 46 2 basis.matrix :=
  verified.pickRows _

#time def refs003 : List (Fin 17) := [⟨16, by decide⟩]
#time def chart003 : Chart :=
  (graph.chart chartRows).pickRows (refs003.map (Fin.cast unionLength.symm))

#time theorem chartSound003 : chart003.Sound 46 2 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart065

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart071
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis010 (basis)

#time def pivTape : List (Fin 6) :=
  []

#time def freeTape : List (Fin 6) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 6) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩]

#time def roles : GraphRoles 6 0 6 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001]

#time def graph : KernelGraph 6 0 6 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.2208s provisional (1104 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 1720) (2 ^ 1712) (2 ^ 0) (2 ^ 1) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 47 6 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 1720) (2 ^ 1712) (2 ^ 0) (2 ^ 1) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 2 := by decide +kernel

#time def refs000 : List (Fin 2) := [⟨0, by decide⟩, ⟨1, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 47 6 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart071
