module
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.Bases001
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.Bases002
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart081
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis011 (basis)

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
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 408653258148199, 34493884425, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 33492646265533, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 29647858210765, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 17884419880187, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 1287776777631, 2653375725, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, false, false, false, false, true, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 382384666239, 2653375725, 0]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 0, 7, 0] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 16702287793, 241215975, 0]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 7, 0] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 40302108395, 241215975, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 1, 8, 0] [true, true, true, true, false, true, false, false, false, false, true, false, true, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 19654382787, 241215975, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 0] [false, true, false, true, true, true, true, false, true, false, false, false, false, false, true, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 137214899495, 2653375725, 0]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 1, 6, 0] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 270237044875, 2653375725, 0]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 5078031246511, 34493884425, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 1, 7, 0] [true, true, true, false, false, true, false, false, false, true, true, false, true, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 2517392931665, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 6075502698933, 34493884425, 0]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 1, 6, 0] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 38689526940519, 34493884425, 0]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 8, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016]

#time def graph : KernelGraph 2 0 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.5638s provisional (2819 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 1068) (2 ^ 1002) (2 ^ 0) (2 ^ 59) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 48 2 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 1068) (2 ^ 1002) (2 ^ 0) (2 ^ 59) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 17 := by decide +kernel

#time def refs000 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 48 2 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 17) := [⟨1, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 48 2 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 17) := [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 48 2 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart081

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart087
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis012 (basis)

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
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0]) [1, 0, 0, 0] [true, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [1756568163, 74895984593, 116555197429, 3381025683, 39902644673, 118179654949, 5767454275, 81658035959, 127328134907, 24085436125, 51437553223, 157181025307, 20008191245, 129828908209, 201274652677, 90346693187, 91453935713, 311629537109, 71297838803, 310522294583, 473274069099, 435469204205, 234049613319, 980041112107, 355649265405, 1181460702993, 1771159581717, 3569603772915, 945348144129, 5696412620037, 3116206618467, 8320668248823]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [12382223011419, 14788970699, 156080925, 0]) [0, 2, 9, 0] [true, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [225220265, 15669960809, 19984113219, 139061591, 23397384569, 19811795871, 2003648263, 16782453537, 5523391829, 2177389845, 31411977621, 1642162839, 4002014241, 25492012917, 36456023751, 3807112439, 63428091549, 52074277111, 35530711987, 55948912429, 11902401747, 33879751613, 205550939497, 20578709697, 130527755935, 191467918881, 459564941059, 127466593131, 1249772986977, 975553639191, 6049229393703, 1211200663929]) [2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 5, 2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [1819929054789, 20434553749, 156080925, 0]) [3, 0, 7, 0] [true, false, true, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [109976559, 1850627039, 3174704341, 137458503, 1214100743, 3202186285, 184092857, 2125544045, 3523737645, 832550795, 1582286457, 4540381297, 773962193, 3790645635, 6146894285, 3697576679, 3130210843, 10618433157, 3408468081, 11185798993, 17724477917, 25981171587, 9947147005, 47114117585, 24791387425, 63148142167, 97886676597, 568488328663, 59529921855, 691166392685, 561923003353, 1200124799493]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [1821577724701, 821170225, 14189175, 0]) [0, 1, 7, 0] [true, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [64674619, 805361131, 3872289623, 40051909, 1098446371, 3847666913, 516313129, 52838315, 4404031951, 540817925, 403689875, 5461163005, 2358011417, 1386230965, 8359992347, 2299316737, 3972770917, 13017320501, 15130343413, 1842773851, 30446980651, 14884897673, 9551557165, 60462221737, 298406217485, 18570445375, 373753336895, 297496343773, 317509331815, 969655898153, 6313325117087, 79016697287]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [5046172875161, 1968482121, 14189175, 0]) [0, 0, 7, 0] [false, false, true, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [66977695, 674232187, 1233465939, 74441485, 492256057, 1240929729, 88114839, 823115157, 1403486053, 461890091, 668485735, 1953490983, 447536977, 1746895339, 2862918051, 2856919805, 1563559689, 6167374833, 2783210935, 7460734949, 11807505573, 52038046283, 7129981559, 66628762791, 51738132641, 111536827515, 170404941715, 1003636246707, 110606246841, 781493172351, 1005260594505, 1895735665899]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [2790390013563, 650221817, 4729725, 0]) [0, 0, 7, 0] [false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [4536073, 78435319, 361004129, 2820343, 99798709, 359288399, 68905047, 40627831, 431013789, 70634477, 42175939, 570553313, 420383837, 151890139, 1061571627, 416230489, 589087593, 1898185953, 6879190361, 142030157, 9193606803, 6861892347, 3734138977, 22934689511, 118880044853, 7430012975, 89083462995, 118943929853, 111411766899, 326907437701, 743780028451, 55756958439]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [297928660897, 182770101, 4729725, 0]) [0, 0, 5, 0] [true, false, true, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [15218675, 94602033, 184228511, 16014281, 74407803, 185024117, 4387095, 126630595, 109293389, 15089137, 109504563, 178424127, 119295729, 368056787, 596857079, 1819474237, 348096021, 2535627045, 226494173, 4007005261, 3083527333, 7005163887, 3972002789, 10020823749, 28051016339, 52034305835, 76113319385, 156117205577, 52130029889, 51952869853, 19494369433, 260200105319]) [0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [182012515447, 99723593, 4729725, 0]) [1, 0, 4, 0] [true, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [11862669, 144392667, 1282132221, 7404915, 173174721, 1277674467, 414530531, 296190249, 1699609913, 419114327, 760879973, 2533254771, 5833471399, 5588317, 8785840497, 5822650339, 1648587843, 20441962235, 78563131533, 6537954915, 52298518959, 78608165265, 71968780161, 209469815757, 384452353887, 36035105175, 96374372865, 384286699095, 156241786863, 865113425847, 1248057026169, 312216488745]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 8, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [1343098773, 646997445, 14189175, 0]) [0, 0, 5, 0] [true, false, true, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [196773361, 668730933, 1424378977, 200959711, 558874683, 1428565327, 209346061, 1070650355, 1838871099, 3116277165, 977566805, 5164494325, 3109263873, 7303204685, 11390035363, 36390842767, 7196094551, 21891543531, 36429128623, 65478480849, 94711514921, 152846489937, 65662162695, 21705846393, 152692833495, 240214499025, 327245169825, 432319729689, 239723504295, 47618273631, 433132531959, 624424960353]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [817833988017, 810576169, 14189175, 0]) [0, 0, 5, 0] [false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [58171575, 2167608671, 9307191959, 36446025, 2456901521, 9285466409, 9141969209, 275506837, 18463881643, 18329592637, 5799435365, 73541294341, 182893926211, 22737702029, 91023039233, 182999129125, 159696184751, 456916094569, 640869771035, 20032678387, 954547341, 160107897299, 120293396571, 320563976893, 383909621109, 120042540525, 96762253083, 192155550759, 131808112269, 83932308693, 378449129085, 264268560993]) [1, 2, 1, 1, 2, 1, 1, 5, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 2, 3, 2, 2, 3, 2, 3, 4, 5, 3, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [74717828223, 4682681767, 156080925, 0]) [4, 1, 5, 0] [false, false, true, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [2259800771, 2403875471, 6789693363, 2270091821, 2126017121, 6799984413, 18330736087, 6944059113, 90891345959, 164751590793, 26834804571, 55529508747, 41220635397, 136975354341, 48145455141, 114374736331, 138047737017, 5784202337, 456765655471, 320523590983, 821717363403, 896567602801, 159358959227, 381915416073, 112437178697, 288022005909, 88384351019, 185308624983, 290389755561, 12987156969, 1467096594303, 453212494023]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 6, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [2118387548151, 4524747067, 156080925, 0]) [0, 3, 6, 0] [true, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [1276180345683, 29000487323, 635504841389, 3444945747, 30739674773, 1915130132819, 1903959164525, 467452742915, 14615914041, 1901774999513, 1412124368157, 3791118249997, 3810827731303, 717161128299, 1882065518207, 3805926068479, 1199351681573, 5734688281575, 5691889236801, 2371603811881, 3848725113253, 5712339717765, 3293185873655, 7555503841313, 7681148866619, 835183976471, 5586694692459, 7606442302571, 1096990748241, 9700896476731, 9148242486357, 4265706396687]) [0, 5, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1] [false, true, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [8159096292945, 320337752147, 2029052025, 2029052025]) [0, 0, 7, 7] [false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034]

#time def graph : KernelGraph 1 0 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.7998s provisional (3999 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 359) (2 ^ 308) (2 ^ 0) (2 ^ 44) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 36 1 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 359) (2 ^ 308) (2 ^ 0) (2 ^ 44) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 35 := by decide +kernel

#time def refs000 : List (Fin 35) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 36 1 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 35) := [⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 36 1 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 35) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 36 1 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart087

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart089
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis013 (basis)

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
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0]) [1, 0, 0, 0] [true, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [1756568163, 74895984593, 116555197429, 3381025683, 39902644673, 118179654949, 5767454275, 81658035959, 127328134907, 24085436125, 51437553223, 157181025307, 20008191245, 129828908209, 201274652677, 90346693187, 91453935713, 311629537109, 71297838803, 310522294583, 473274069099, 435469204205, 234049613319, 980041112107, 355649265405, 1181460702993, 1771159581717, 3569603772915, 945348144129, 5696412620037, 3116206618467, 8320668248823]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [12382223011419, 14788970699, 156080925, 0]) [0, 2, 9, 0] [true, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [225220265, 15669960809, 19984113219, 139061591, 23397384569, 19811795871, 2003648263, 16782453537, 5523391829, 2177389845, 31411977621, 1642162839, 4002014241, 25492012917, 36456023751, 3807112439, 63428091549, 52074277111, 35530711987, 55948912429, 11902401747, 33879751613, 205550939497, 20578709697, 130527755935, 191467918881, 459564941059, 127466593131, 1249772986977, 975553639191, 6049229393703, 1211200663929]) [2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 5, 2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [1819929054789, 20434553749, 156080925, 0]) [3, 0, 7, 0] [true, false, true, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [109976559, 1850627039, 3174704341, 137458503, 1214100743, 3202186285, 184092857, 2125544045, 3523737645, 832550795, 1582286457, 4540381297, 773962193, 3790645635, 6146894285, 3697576679, 3130210843, 10618433157, 3408468081, 11185798993, 17724477917, 25981171587, 9947147005, 47114117585, 24791387425, 63148142167, 97886676597, 568488328663, 59529921855, 691166392685, 561923003353, 1200124799493]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [1821577724701, 821170225, 14189175, 0]) [0, 1, 7, 0] [true, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [64674619, 805361131, 3872289623, 40051909, 1098446371, 3847666913, 516313129, 52838315, 4404031951, 540817925, 403689875, 5461163005, 2358011417, 1386230965, 8359992347, 2299316737, 3972770917, 13017320501, 15130343413, 1842773851, 30446980651, 14884897673, 9551557165, 60462221737, 298406217485, 18570445375, 373753336895, 297496343773, 317509331815, 969655898153, 6313325117087, 79016697287]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [5046172875161, 1968482121, 14189175, 0]) [0, 0, 7, 0] [false, false, true, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [66977695, 674232187, 1233465939, 74441485, 492256057, 1240929729, 88114839, 823115157, 1403486053, 461890091, 668485735, 1953490983, 447536977, 1746895339, 2862918051, 2856919805, 1563559689, 6167374833, 2783210935, 7460734949, 11807505573, 52038046283, 7129981559, 66628762791, 51738132641, 111536827515, 170404941715, 1003636246707, 110606246841, 781493172351, 1005260594505, 1895735665899]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [2790390013563, 650221817, 4729725, 0]) [0, 0, 7, 0] [false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [4536073, 78435319, 361004129, 2820343, 99798709, 359288399, 68905047, 40627831, 431013789, 70634477, 42175939, 570553313, 420383837, 151890139, 1061571627, 416230489, 589087593, 1898185953, 6879190361, 142030157, 9193606803, 6861892347, 3734138977, 22934689511, 118880044853, 7430012975, 89083462995, 118943929853, 111411766899, 326907437701, 743780028451, 55756958439]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [297928660897, 182770101, 4729725, 0]) [0, 0, 5, 0] [true, false, true, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [15218675, 94602033, 184228511, 16014281, 74407803, 185024117, 4387095, 126630595, 109293389, 15089137, 109504563, 178424127, 119295729, 368056787, 596857079, 1819474237, 348096021, 2535627045, 226494173, 4007005261, 3083527333, 7005163887, 3972002789, 10020823749, 28051016339, 52034305835, 76113319385, 156117205577, 52130029889, 51952869853, 19494369433, 260200105319]) [0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [182012515447, 99723593, 4729725, 0]) [1, 0, 4, 0] [true, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [11862669, 144392667, 1282132221, 7404915, 173174721, 1277674467, 414530531, 296190249, 1699609913, 419114327, 760879973, 2533254771, 5833471399, 5588317, 8785840497, 5822650339, 1648587843, 20441962235, 78563131533, 6537954915, 52298518959, 78608165265, 71968780161, 209469815757, 384452353887, 36035105175, 96374372865, 384286699095, 156241786863, 865113425847, 1248057026169, 312216488745]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 8, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [1343098773, 646997445, 14189175, 0]) [0, 0, 5, 0] [true, false, true, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [196773361, 668730933, 1424378977, 200959711, 558874683, 1428565327, 209346061, 1070650355, 1838871099, 3116277165, 977566805, 5164494325, 3109263873, 7303204685, 11390035363, 36390842767, 7196094551, 21891543531, 36429128623, 65478480849, 94711514921, 152846489937, 65662162695, 21705846393, 152692833495, 240214499025, 327245169825, 432319729689, 239723504295, 47618273631, 433132531959, 624424960353]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [817833988017, 810576169, 14189175, 0]) [0, 0, 5, 0] [false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [58171575, 2167608671, 9307191959, 36446025, 2456901521, 9285466409, 9141969209, 275506837, 18463881643, 18329592637, 5799435365, 73541294341, 182893926211, 22737702029, 91023039233, 182999129125, 159696184751, 456916094569, 640869771035, 20032678387, 954547341, 160107897299, 120293396571, 320563976893, 383909621109, 120042540525, 96762253083, 192155550759, 131808112269, 83932308693, 378449129085, 264268560993]) [1, 2, 1, 1, 2, 1, 1, 5, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 2, 3, 2, 2, 3, 2, 3, 4, 5, 3, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [74717828223, 4682681767, 156080925, 0]) [4, 1, 5, 0] [false, false, true, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [2259800771, 2403875471, 6789693363, 2270091821, 2126017121, 6799984413, 18330736087, 6944059113, 90891345959, 164751590793, 26834804571, 55529508747, 41220635397, 136975354341, 48145455141, 114374736331, 138047737017, 5784202337, 456765655471, 320523590983, 821717363403, 896567602801, 159358959227, 381915416073, 112437178697, 288022005909, 88384351019, 185308624983, 290389755561, 12987156969, 1467096594303, 453212494023]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 6, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [2118387548151, 4524747067, 156080925, 0]) [0, 3, 6, 0] [true, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [1427254563, 106426930193, 170725621429, 3710339283, 62871436673, 173008706149, 9211387075, 113847608759, 185930432507, 30882380125, 81294210823, 226024199707, 30232436045, 175612369009, 287139015877, 113237869187, 141759082913, 430609321109, 103304459603, 402088107383, 647151649899, 521815895405, 348368002119, 1272272004907, 484510675005, 1445719898193, 2278598575317, 4024910095155, 1317389352129, 6788019345477, 3891868545507, 9495540088503]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [14704797986139, 21519109499, 156080925, 156080925]) [0, 2, 9, 9] [true, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034]

#time def graph : KernelGraph 1 0 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.7998s provisional (3999 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 342) (2 ^ 291) (2 ^ 0) (2 ^ 44) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 36 1 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 342) (2 ^ 291) (2 ^ 0) (2 ^ 44) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 35 := by decide +kernel

#time def refs000 : List (Fin 35) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 36 1 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 35) := [⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 36 1 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 35) := [⟨23, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 36 1 basis.matrix :=
  verified.pickRows _

#time def refs003 : List (Fin 35) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩]
#time def chart003 : Chart :=
  (graph.chart chartRows).pickRows (refs003.map (Fin.cast unionLength.symm))

#time theorem chartSound003 : chart003.Sound 36 1 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart089

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart093
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis014 (basis)

#time def pivTape : List (Fin 32) :=
  []

#time def freeTape : List (Fin 32) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 32) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩, .inr ⟨30, by decide⟩, .inr ⟨31, by decide⟩]

#time def roles : GraphRoles 32 0 32 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 243713808082670679, 607961471833528647, 903606052351478391, 408653258148199, 34493884425, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, true]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 148605599185470525, 21287570016248979, 2657579116665153, 33492646265533, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 7, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 151387994194904603, 316775219116482765, 479454851877279743, 29647858210765, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 574818220719425045, 82182751500561625, 30784799536760355, 17884419880187, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 5, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 42752080057047641, 82153752508489405, 121632278287850089, 1287776777631, 2653375725, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 11503129264860577, 9858052665717051, 13149481030992733, 382384666239, 2653375725, 0]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 2, 0, 1, 0, 7, 0] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 14506004138969, 3286080299633617, 1178500505039373, 16702287793, 241215975, 0]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 7, 0, 2, 1, 7, 0] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 7999856339602525, 1428740422078035, 2284494004056855, 40302108395, 241215975, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 1, 8, 0] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 3185008400933739, 5143448511010413, 7104202620437757, 19654382787, 241215975, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 0] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 10779199526665917, 1347097410982869, 3390769184895, 137214899495, 2653375725, 0]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6, 0] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 921127886614713, 5388403269205461, 3543418908064545, 270237044875, 2653375725, 0]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6, 0] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 68764961739507579, 22120174836938097, 19738301156030679, 5078031246511, 34493884425, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 1, 7, 0] [true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 18846794612867301, 24577310582145795, 30432132043502931, 2517392931665, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 3704376525300633, 180768027125319, 2069991948020901, 6075502698933, 34493884425, 0]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 1, 6, 0] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 2642697641777463, 1578738665705661, 3450924256520043, 38689526940519, 34493884425, 0]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017]

#time def graph : KernelGraph 32 0 32 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.9656s provisional (4828 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 605) (2 ^ 538) (2 ^ 0) (2 ^ 60) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 51 32 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 605) (2 ^ 538) (2 ^ 0) (2 ^ 60) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 18 := by decide +kernel

#time def refs000 : List (Fin 18) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 51 32 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 18) := [⟨1, by decide⟩, ⟨2, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 51 32 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 18) := [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 51 32 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart093

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart099
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis015 (basis)

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
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 408653258148199, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 33492646265533, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 29647858210765, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 17884419880187, 34493884425, 0]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 1287776777631, 2653375725, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0] [true, false, true, false, true, false, true, false, true, false, false, false, false, false, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 382384666239, 2653375725, 0]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 0, 7, 0] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 16702287793, 241215975, 0]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 7, 0] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 40302108395, 241215975, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 1, 8, 0] [true, true, true, true, false, true, false, false, false, false, true, false, true, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 19654382787, 241215975, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8, 0] [false, true, false, true, true, true, true, false, true, false, false, false, false, false, true, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 137214899495, 2653375725, 0]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 1, 6, 0] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 270237044875, 2653375725, 0]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 5078031246511, 34493884425, 0]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 1, 7, 0] [true, true, true, false, false, true, false, false, false, true, true, false, true, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 2517392931665, 34493884425, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, false, true, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 6075502698933, 34493884425, 0]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 1, 6, 0] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 38689526940519, 34493884425, 0]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 8, 0] [true, true, false, true, true, true, false, false, true, false, false, false, true, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [3687119410095959, 913209274530199, 4435174773188613, 1477410431683671, 8424712390373, 729355068591017, 2773071940695, 8815643080523, 2209538572215383, 2201048950196393, 541954664924567, 11262693959685, 2198856648721253, 1636847793042921, 4388642904957961, 4402353443321371, 828450991898343, 2185146110357843, 4399874651798611, 1382752825139225, 6617081984762139, 6591588557044269, 2742972668001925, 4425368079516481, 6602336385324129, 3826082906765819, 8768556862851917, 8826519283175327, 964840929330551, 6544373965000719, 8793597448934927, 1250109094102377]) [0, 1, 0, 0, 7, 0, 0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3] [false, false, true, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [11075742767109535, 10906211488634865, 4934233731612723, 8963128727409597, 11016927048578973, 5905775112225357, 12960009809804241, 13635894912191715, 3041346658483125, 10341041946191499, 13178628844222347, 3865059899983179, 16473481810222563, 2030573545821143, 586396035225, 586396035225]) [0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1, 9, 9] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016]

#time def graph : KernelGraph 2 0 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.5638s provisional (2819 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 1087) (2 ^ 1021) (2 ^ 0) (2 ^ 59) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 48 2 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 1087) (2 ^ 1021) (2 ^ 0) (2 ^ 59) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 17 := by decide +kernel

#time def refs000 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 48 2 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 17) := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 48 2 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 17) := [⟨16, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 48 2 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart099

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart106
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis016 (basis)

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

-- kcost: 0.4254s provisional (2127 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 272) (2 ^ 129) (2 ^ 0) (2 ^ 135) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 90 87 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 272) (2 ^ 129) (2 ^ 0) (2 ^ 135) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 3 := by decide +kernel

#time def refs000 : List (Fin 3) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 90 87 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 3) := [⟨1, by decide⟩, ⟨2, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 90 87 basis.matrix :=
  verified.pickRows _

#time def refs002 : List (Fin 3) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
#time def chart002 : Chart :=
  (graph.chart chartRows).pickRows (refs002.map (Fin.cast unionLength.symm))

#time theorem chartSound002 : chart002.Sound 90 87 basis.matrix :=
  verified.pickRows _

#time def refs003 : List (Fin 3) := [⟨1, by decide⟩, ⟨2, by decide⟩]
#time def chart003 : Chart :=
  (graph.chart chartRows).pickRows (refs003.map (Fin.cast unionLength.symm))

#time theorem chartSound003 : chart003.Sound 90 87 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart106

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart116
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis017 (basis)

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
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 1950) (2 ^ 1942) (2 ^ 0) (2 ^ 1) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 47 6 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 1950) (2 ^ 1942) (2 ^ 0) (2 ^ 1) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 1 := by decide +kernel

#time def refs000 : List (Fin 1) := [⟨0, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 47 6 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart116

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart126
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
  []

#time def freeTape : List (Fin 48) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 48) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩, .inr ⟨30, by decide⟩, .inr ⟨31, by decide⟩, .inr ⟨32, by decide⟩, .inr ⟨33, by decide⟩, .inr ⟨34, by decide⟩, .inr ⟨35, by decide⟩, .inr ⟨36, by decide⟩, .inr ⟨37, by decide⟩, .inr ⟨38, by decide⟩, .inr ⟨39, by decide⟩, .inr ⟨40, by decide⟩, .inr ⟨41, by decide⟩, .inr ⟨42, by decide⟩, .inr ⟨43, by decide⟩, .inr ⟨44, by decide⟩, .inr ⟨45, by decide⟩, .inr ⟨46, by decide⟩, .inr ⟨47, by decide⟩]

#time def roles : GraphRoles 48 0 48 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001]

#time def graph : KernelGraph 48 0 48 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.1770s provisional (885 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 9) (2 ^ 1) (2 ^ 0) (2 ^ 1) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 50 48 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 9) (2 ^ 1) (2 ^ 0) (2 ^ 1) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 2 := by decide +kernel

#time def refs000 : List (Fin 2) := [⟨0, by decide⟩, ⟨1, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 50 48 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart126

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart137
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
  []

#time def freeTape : List (Fin 32) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 32) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩, .inr ⟨30, by decide⟩, .inr ⟨31, by decide⟩]

#time def roles : GraphRoles 32 0 32 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 243713808082670679, 607961471833528647, 903606052351478391, 408653258148199, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 148605599185470525, 21287570016248979, 2657579116665153, 33492646265533, 34493884425]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 7, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 151387994194904603, 316775219116482765, 479454851877279743, 29647858210765, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 574818220719425045, 82182751500561625, 30784799536760355, 17884419880187, 34493884425]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 5, 0, 9] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 42752080057047641, 82153752508489405, 121632278287850089, 1287776777631, 2653375725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 11503129264860577, 9858052665717051, 13149481030992733, 382384666239, 2653375725]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 2, 0, 1, 0, 7] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 14506004138969, 3286080299633617, 1178500505039373, 16702287793, 241215975]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 7, 0, 2, 1, 7] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 7999856339602525, 1428740422078035, 2284494004056855, 40302108395, 241215975]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 1, 8] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 3185008400933739, 5143448511010413, 7104202620437757, 19654382787, 241215975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 10779199526665917, 1347097410982869, 3390769184895, 137214899495, 2653375725]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 921127886614713, 5388403269205461, 3543418908064545, 270237044875, 2653375725]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 68764961739507579, 22120174836938097, 19738301156030679, 5078031246511, 34493884425]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 1, 7] [true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 18846794612867301, 24577310582145795, 30432132043502931, 2517392931665, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 3704376525300633, 180768027125319, 2069991948020901, 6075502698933, 34493884425]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 1, 6] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 2642697641777463, 1578738665705661, 3450924256520043, 38689526940519, 34493884425]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016]

#time def graph : KernelGraph 32 0 32 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.9050s provisional (4525 native units *0.0002s/unit; not a measured rate).
#time theorem check : graph.chartCheck basis roles chartRows (2 ^ 605) (2 ^ 538) (2 ^ 0) (2 ^ 60) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 50 32 basis.matrix :=
  graph.chartCheck_sound basis roles chartRows (2 ^ 605) (2 ^ 538) (2 ^ 0) (2 ^ 60) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 17 := by decide +kernel

#time def refs000 : List (Fin 17) := [⟨0, by decide⟩, ⟨1, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 50 32 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 17) := [⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 50 32 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart137
