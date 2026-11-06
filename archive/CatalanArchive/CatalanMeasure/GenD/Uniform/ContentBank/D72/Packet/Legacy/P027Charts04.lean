module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C008
#time def pivTape : List (Fin 87) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]

#time def freeTape : List (Fin 87) :=
  []

#time def roleTape : List (Fin 87 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩, .inl ⟨27, by decide⟩, .inl ⟨28, by decide⟩, .inl ⟨29, by decide⟩, .inl ⟨30, by decide⟩, .inl ⟨31, by decide⟩, .inl ⟨32, by decide⟩, .inl ⟨33, by decide⟩, .inl ⟨34, by decide⟩, .inl ⟨35, by decide⟩, .inl ⟨36, by decide⟩, .inl ⟨37, by decide⟩, .inl ⟨38, by decide⟩, .inl ⟨39, by decide⟩, .inl ⟨40, by decide⟩, .inl ⟨41, by decide⟩, .inl ⟨42, by decide⟩, .inl ⟨43, by decide⟩, .inl ⟨44, by decide⟩, .inl ⟨45, by decide⟩, .inl ⟨46, by decide⟩, .inl ⟨47, by decide⟩, .inl ⟨48, by decide⟩, .inl ⟨49, by decide⟩, .inl ⟨50, by decide⟩, .inl ⟨51, by decide⟩, .inl ⟨52, by decide⟩, .inl ⟨53, by decide⟩, .inl ⟨54, by decide⟩, .inl ⟨55, by decide⟩, .inl ⟨56, by decide⟩, .inl ⟨57, by decide⟩, .inl ⟨58, by decide⟩, .inl ⟨59, by decide⟩, .inl ⟨60, by decide⟩, .inl ⟨61, by decide⟩, .inl ⟨62, by decide⟩, .inl ⟨63, by decide⟩, .inl ⟨64, by decide⟩, .inl ⟨65, by decide⟩, .inl ⟨66, by decide⟩, .inl ⟨67, by decide⟩, .inl ⟨68, by decide⟩, .inl ⟨69, by decide⟩, .inl ⟨70, by decide⟩, .inl ⟨71, by decide⟩, .inl ⟨72, by decide⟩, .inl ⟨73, by decide⟩, .inl ⟨74, by decide⟩, .inl ⟨75, by decide⟩, .inl ⟨76, by decide⟩, .inl ⟨77, by decide⟩, .inl ⟨78, by decide⟩, .inl ⟨79, by decide⟩, .inl ⟨80, by decide⟩, .inl ⟨81, by decide⟩, .inl ⟨82, by decide⟩, .inl ⟨83, by decide⟩, .inl ⟨84, by decide⟩, .inl ⟨85, by decide⟩, .inl ⟨86, by decide⟩]

#time def roles : GraphRoles 87 87 0 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows001 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows002 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows003 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows004 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows005 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows006 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows007 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows008 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows009 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows010 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows011 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows012 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows013 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows014 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows015 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows016 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows017 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows018 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows019 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows020 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows021 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows022 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows023 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows024 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows025 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows026 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows027 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows028 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows029 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows030 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows031 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows032 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows033 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows034 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows035 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows036 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows037 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows038 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows039 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows040 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows041 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows042 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows043 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows044 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows045 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows046 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows047 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows048 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows049 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows050 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows051 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows052 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows053 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows054 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows055 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows056 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows057 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows058 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows059 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows060 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows061 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows062 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows063 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows064 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows065 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows066 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows067 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows068 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows069 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows070 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows071 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows072 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows073 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows074 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows075 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows076 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows077 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows078 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows079 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows080 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows081 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows082 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows083 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows084 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows085 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows086 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026, tailRows027, tailRows028, tailRows029, tailRows030, tailRows031, tailRows032, tailRows033, tailRows034, tailRows035, tailRows036, tailRows037, tailRows038, tailRows039, tailRows040, tailRows041, tailRows042, tailRows043, tailRows044, tailRows045, tailRows046, tailRows047, tailRows048, tailRows049, tailRows050, tailRows051, tailRows052, tailRows053, tailRows054, tailRows055, tailRows056, tailRows057, tailRows058, tailRows059, tailRows060, tailRows061, tailRows062, tailRows063, tailRows064, tailRows065, tailRows066, tailRows067, tailRows068, tailRows069, tailRows070, tailRows071, tailRows072, tailRows073, tailRows074, tailRows075, tailRows076, tailRows077, tailRows078, tailRows079, tailRows080, tailRows081, tailRows082, tailRows083, tailRows084, tailRows085, tailRows086]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01 ++ chartRows000_p02

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1076774668307122009342793450035, 66366597411325419241048957881, 705298494161537822269391603873, 5254522520610992319684870999, 7460718103841667143478247825, 376730696666195179393086717161, 1492191102869811117774943385, 4476319995746025722545864305, 10444846996717881748249168745, 1492190411463027674932226135, 4476335898102044907928361055, 10444846305311098305406451495, 200550348518706993519883649367, 7460700818672081072410316575, 582535523455479024890721333527, 47750787792716494722060000205, 272171722888339712046737426247, 735335084181469523688544982689, 432139274796144494568300136673, 71620425306036802436505064995, 65060800174739059331669722763, 561064854007164807674747732075, 1456385376296238266226463120445, 156680916187783192446215844975, 4631764687823040696205499598235, 2172638990722622428262485863305, 2626284046214680692772398369265, 10495484664423413214761541761519, 1587689655763401214989518238895, 12500965306031773218194642990489, 960972638231941107909178119595, 4161422836850395393249527949107]) [0, 1, 0, 0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 4, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2] [false, true, true, true, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [956791804037478598105172487203, 3699445183490221581947397308133, 2256200897164363216647194239485, 1373417106823602746823115226661, 8451772650374001126442443576255, 10636357897110490934540061283425, 43118462526725415478306578515385, 65656471860451645517368206252235, 3939370856045274693148055097285, 30989781984100231165504071313105, 814144609928472805061842694503, 44383756066230663648288083685385, 182401709775074190356689271069, 31503182569631147616119476444805, 682792416331383472900684319273, 2242477082087531013881273110619, 12787536986167613942099866340093, 81628974212293926816189822093835, 174679900578092700628678141889217, 219220952227434174087788126153095, 3026186142459057617299795505205, 31753514663173859517010117923785, 2862018749670439031074482680675, 34397994503785061817899576014815, 2318490366291680141421796616935, 22191310076702905815287800349559, 8421888856222698506998135217495, 195342099174756413209736183351, 103092971817418177164180191131865, 54367245803026561443251625383421, 470655827391849080654208112459273, 544532555612875870810413470439779]) [4, 3, 2, 4, 0, 2, 0, 0, 1, 0, 2, 1, 9, 2, 1, 4, 0, 1, 0, 0, 3, 0, 4, 3, 7, 4, 3, 6, 0, 3, 0, 0] [false, false, true, false, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true]

#time def chartRows001_p02 : List Int :=
  decoded (raw_ints% [69405416392527383136187650261885, 29216243596391387007974833151359, 48310918545692974980180713536515, 327063572400769625037406968906095, 44284999137453523982697593214655, 199966618260572886987500828306735, 123838257790244516784535203884175, 1592768552183386495216891130525, 326033909244509490214378982323093, 472802900641521922912596344320845, 1023963194947064302470501263196433, 1134480305966743849695795441355295, 101097825727132486714921889219459, 215516798224829942989084804164231, 64052359635447429997750899186991, 330838702662610963391599548517225, 89461399051593334168044864417937, 195399254949284440848947382035455, 155111612814657233276081707528505, 23787951394674828742446622993705, 764880228255997292068967177372785, 450758317134526800004189979624595, 1947467045535475558981400265757145, 445518290617164957903046263477, 20363658289350325129805625]) [1, 0, 2, 1, 4, 2, 1, 6, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 4, 0, 2, 0, 1, 10] [true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01 ++ chartRows001_p02

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01 ++ chartRows002_p02

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01 ++ chartRows003_p02

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01 ++ chartRows004_p02

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01 ++ chartRows005_p02

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01 ++ chartRows006_p02

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01 ++ chartRows007_p02

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01 ++ chartRows008_p02

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01 ++ chartRows009_p02

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01 ++ chartRows010_p02

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01 ++ chartRows011_p02

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01 ++ chartRows012_p02

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01 ++ chartRows013_p02

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01 ++ chartRows014_p02

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01 ++ chartRows015_p02

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01 ++ chartRows016_p02

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01 ++ chartRows017_p02

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01 ++ chartRows018_p02

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01 ++ chartRows019_p02

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01 ++ chartRows020_p02

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01 ++ chartRows021_p02

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01 ++ chartRows022_p02

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01 ++ chartRows023_p02

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p02 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01 ++ chartRows024_p02

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01 ++ chartRows025_p02

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01 ++ chartRows026_p02

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01 ++ chartRows027_p02

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01 ++ chartRows028_p02

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01 ++ chartRows029_p02

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01 ++ chartRows030_p02

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01 ++ chartRows031_p02

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01 ++ chartRows032_p02

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01 ++ chartRows033_p02

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01 ++ chartRows034_p02

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01 ++ chartRows035_p02

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01 ++ chartRows036_p02

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01 ++ chartRows037_p02

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01 ++ chartRows038_p02

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01 ++ chartRows039_p02

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01 ++ chartRows040_p02

#time def chartRows041_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041 : List Int := chartRows041_p00 ++ chartRows041_p01 ++ chartRows041_p02

#time def chartRows042_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042 : List Int := chartRows042_p00 ++ chartRows042_p01 ++ chartRows042_p02

#time def chartRows043_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043 : List Int := chartRows043_p00 ++ chartRows043_p01 ++ chartRows043_p02

#time def chartRows044_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044 : List Int := chartRows044_p00 ++ chartRows044_p01 ++ chartRows044_p02

#time def chartRows045_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045 : List Int := chartRows045_p00 ++ chartRows045_p01 ++ chartRows045_p02

#time def chartRows046_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046 : List Int := chartRows046_p00 ++ chartRows046_p01 ++ chartRows046_p02

#time def chartRows047_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047 : List Int := chartRows047_p00 ++ chartRows047_p01 ++ chartRows047_p02

#time def chartRows048_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048 : List Int := chartRows048_p00 ++ chartRows048_p01 ++ chartRows048_p02

#time def chartRows049_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049 : List Int := chartRows049_p00 ++ chartRows049_p01 ++ chartRows049_p02

#time def chartRows050_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050 : List Int := chartRows050_p00 ++ chartRows050_p01 ++ chartRows050_p02

#time def chartRows051_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051 : List Int := chartRows051_p00 ++ chartRows051_p01 ++ chartRows051_p02

#time def chartRows052_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052 : List Int := chartRows052_p00 ++ chartRows052_p01 ++ chartRows052_p02

#time def chartRows053_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053_p02 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053 : List Int := chartRows053_p00 ++ chartRows053_p01 ++ chartRows053_p02

#time def chartRows054_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054 : List Int := chartRows054_p00 ++ chartRows054_p01 ++ chartRows054_p02

#time def chartRows055_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055 : List Int := chartRows055_p00 ++ chartRows055_p01 ++ chartRows055_p02

#time def chartRows056_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056 : List Int := chartRows056_p00 ++ chartRows056_p01 ++ chartRows056_p02

#time def chartRows057_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057 : List Int := chartRows057_p00 ++ chartRows057_p01 ++ chartRows057_p02

#time def chartRows058_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058 : List Int := chartRows058_p00 ++ chartRows058_p01 ++ chartRows058_p02

#time def chartRows059_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows059_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows059_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows059 : List Int := chartRows059_p00 ++ chartRows059_p01 ++ chartRows059_p02

#time def chartRows060_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows060_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows060_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows060 : List Int := chartRows060_p00 ++ chartRows060_p01 ++ chartRows060_p02

#time def chartRows061_p00 : List Int :=
  decoded (raw_ints% [4179948839976999111891518679841385, 50249653545189029186547486317161079, 101519035291729949961517456245681239, 2340075830687481850128978976592151, 47089432906563921663078451248678775, 94999010621065468999496958589247703, 756541962156357987200831033319319, 45569501883814065486289528363976777, 91902392828221629162167148579336233, 756192677943565482485562188898199, 45576348982251205688676789182040137, 91902043544008836657451879734915113, 2341179730692789836334530448740631, 47081887239701196451260652741773175, 94999415952645191976271972372553943, 4177909672598566792708458657774185, 50258708443636785361345850079521399, 101518505355936548605314961479068759, 6469528823354712347544409665618409, 55437706584898330036677570057321545, 112165943851889827745567829802461353, 9532158277118086462646639952186135, 63197766090346210056434669410758217, 128167630952362626555758879420265897, 13801311335895551838791115172198039, 74502023139134502961970849961693815, 151501100565376264857196634544650071, 20041275226952598622720601843719145, 90800388762137313734016899755154295, 185343687128224415318708351560567255, 29378442171712435352143377121102185, 114584573593039700207412053649132105]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows061_p01 : List Int :=
  decoded (raw_ints% [234763404526889449293572330525388585, 43970644764475338139083399461433495, 149557273105562184438303653997358665, 308112491463077222784799107107924265, 67099013350430728301348627394078231, 202525863121990376485578852571999095, 419182149577983289225231133963435991, 105626633810325647497835241007891305, 283755299806423641041000908785515127, 591907796738739665024415002365405527, 170245837305206718710922893777315561, 413779130742641671481249334587781705, 867780267854272031233173137150612393, 285628293030206244191328856346918935, 624246974416837078462846696340146249, 1323654398189684994135424887274846889, 491135132515953924917982230752579479, 985035716803054159863907047281619575, 2100417823735845163244735974374345303, 888443533741562907426313360721862889, 1606517239448744928298811157845305207, 3479996489993361995589031565848787671, 1643781263089755393201290581452737129, 2761922784286179974716533768725345353, 6012221286824680296216635508023387689, 3247065849422004731527436046074325399, 4894079765628255714701392320750779465, 10903068399336440420945362135550450217, 6519724624740182798963642992455164695, 9256054483130189437771405860873996151, 20669858873498627951436441174079940311, 14293544818345707772080000297072075881]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows061_p02 : List Int :=
  decoded (raw_ints% [17933529015108621312628678305661108855, 41483128316584518522480084463607180887, 31441518585442467335267294912166487017, 37843144119821604981931406455018147913, 87218191720372693629827379672845743785, 78301396760953121943125056806490627351, 80816566185993555983163268129994082889, 196961107066768282908219731391502858153, 190814860300957318261185922922838839447, 194445937641727848868181520067999402615, 466077364128678723112530711120832324951, 560143930544650206382543799640722390505, 462446286787908192505535113975671761783, 1217036154974286247756260433684393554903, 1533402111977975398550918700490387252073, 1314733798731028261633269119349444183625, 3310582197496911852689722933815503197481, 5673860341805754465383534803623239994007, 3529250510743858989607372514956446265929, 10517844651280641716624176437929130443561, 17765519141627033031204145719517191424023, 12662454482342537192400338726595924171639, 33957224134713429213211856961069561861591, 1651546627057921079272015233211291, 20363658289350325129805625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 30] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false]

#time def chartRows061 : List Int := chartRows061_p00 ++ chartRows061_p01 ++ chartRows061_p02

#time def chartRows062_p00 : List Int :=
  decoded (raw_ints% [34780605565279667155044429179155, 1622985015865069380197817776110095, 1639519449299543884097663514073747, 9746628794815198450981058713677, 1516931460472899719377331535320779, 1530971722989723755983650420860729, 12515790709811032599058133002339, 1467038955148026204982120836691263, 739734708550325964790334026501841, 12520091162059478001261783132259, 1466868297633655588981099003311423, 739736858776450187491435851566801, 9743232587279959350733530634317, 1517119319796264116987167969220299, 1530966739064079690387067608803129, 34793141047922884617555522529555, 1622760019030134938592835493460495, 1639525951509045297025112776399507, 108262645678227883449003486322315, 1795464448179647193927612149456739, 454343719820779737427306826945233, 160026582489575822038438117555441, 2055810601743046472388849438749755, 32588501678920666487447951744667, 116702559859716941938952762099495, 2435570778137950482081364619678503, 2479095809659932361113012553413119, 665343799432664815168661064559, 2989431080620782007900471535545715, 3053156954688890630357272542666317, 504830988618616399795713855162265, 3798194879376048023546782479895335]) [2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 7, 2, 0, 1, 10, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows062_p01 : List Int :=
  decoded (raw_ints% [1949321984308515707759670431441395, 760489935610602225959612334831327, 5008755035095247607083326956194775, 2581982446423125020637333526438191, 147338904189606149344477735907565, 6840154621818456927385231819220643, 7103166061973701461990101274968229, 934502948204200844382537798320717, 9723599969162644386106614505236855, 10150883191898952345510998758870183, 3079509533664969635985765403159175, 14316178207452063682445534205786379, 1887424827746540458782729969833849, 5202315192560907425089075141174765, 22041638103822522930049676117873555, 5845305837049550182834170075751183, 4615129892041635784036039804602209, 35125438977695693382801834770485439, 37813798324842379724497835053383915, 4193273015862427860745143428553229, 58962677240155609202337994554691227, 63817150172375362735550488376801249, 32473396838900379235031053874681621, 102217807231494539154724129627337103, 56531819537362726706781057982847893, 64060995895581490053607226554524123, 188856264595757126142462210053417711, 104799015904603661351100198197450765, 34392904131751627278054814410944935, 358461790813820499369153035845433595, 411230644231795321868026880593205393, 148776577564327654811658001988238727]) [2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows062_p02 : List Int :=
  decoded (raw_ints% [739142730703783162591339240628536671, 846355415887457140603562142213462587, 725416776013994670225305905308493059, 1548674411328441737862417051751343411, 467331336757526780113046012874608275, 1740332772625310370077211965693598313, 3640809834759761843492562861862508907, 541884361958676520094337740312565559, 2498420388946556501735124391509610651, 8510005501829683218171264914525736663, 11072248446187835534302162671213344087, 1686174635726725908683220324494626285, 23628172946332213857373557993939394115, 29558486309894755807238174050189575669, 48751541166261171250323231980564677649, 62467593845084912296034315298353777783, 45899712280984867163513584313355631799, 150883580710661094396493805335240533847, 218634337611376898858666485916198104711, 145717273219445999986922102971258237547, 49777563471467074598512884413952451853, 666001916687729289882009536639315913171, 1238759142693026287946544161900996238589, 1709080660430103218407752372432057, 20363658289350325129805625]) [0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 0, 25] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true]

#time def chartRows062 : List Int := chartRows062_p00 ++ chartRows062_p01 ++ chartRows062_p02

#time def chartRows063_p00 : List Int :=
  decoded (raw_ints% [4716167559297041234218016148577, 52941442385759450166278957073929, 107041472221886918693393375250915, 2628282050721903934061642453079, 49383862276830427292896402028409, 99697022611867973525113716649259, 847225494610218206682939025679, 47684878284315642298155672167771, 96221515066535851384369135170501, 846999500098965860958914111759, 47689411287609990879530523977051, 96221289072024599038645110256581, 2628995647236140279376965210199, 49378877284513574020073500391289, 99697284219359705178980989578539, 4714851691326900745290299575393, 52947402582082271438284454397449, 107041131557922746203648254364131, 7353744948789335668200121446921, 58808580667167375510654099542075, 119109728198038982617138675386445, 10945013457738714472172556571655, 67654892479660942774684697291291, 137408486604567032757511353405021, 16042173041036335877183449776879, 80698607582644804454999212685385, 164395673103342083106867359753555, 23661339852778719499279024034105, 99739238561733614529051596845049, 204099185997157138483329833564539, 35302502716981704335670814053185, 128021287288202243453557260753595]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows063_p01 : List Int :=
  decoded (raw_ints% [263063028566917562318279671651829, 53996301435528440381076911066335, 170344243995697023200393224951419, 352361832719427707035027396771349, 84362423399174481375109978960231, 236013890159259124215711082886265, 490720557554130628791214286797915, 136682271261107790209097085981745, 339069090794045985950613182871881, 711765252214412900375421351739891, 227055038919594569010771180824729, 509378432681474704633905254849755, 1075502562395115259595289618546365, 395463693852105020557706804279703, 793179168633235123972155544521339, 1698021295166814849163767603650797, 706219421280120190626244442876351, 1300305820385684745749318863409161, 2799704410299040060347718850806851, 1340944788631725721981494864970569, 2205618011193475505224644430274041, 4846868620210885972955458158653771, 2599959990248241197783713067005969, 3982195397649136189712308593350299, 8787773399090852892720666090630309, 5472253604111738429297536177629231, 7405537991689957900792070564285979, 16859986993450832519801915335265509, 11640290784879931087376041481970167, 14926702605872613048307380948608761, 33972531382442502036475492994864907, 27793130517492970971734138823500929]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows063_p02 : List Int :=
  decoded (raw_ints% [30686119561449820075544153528226313, 73405952684815404095585673300336003, 65645223709772046668898764151250857, 70512963640858554991775658595610619, 166844306912080421736218576275087789, 184406703924408448224975441496395431, 161976566980993913413341681830728027, 416896234546260916630092781922734077, 490867476617018218744429555351615503, 439326371489675451441726541588401481, 1092170415087687583599497778770745011, 1732945408802919518814941995804956121, 1143711520215030350902200792533959033, 3315983300507625321158869329927316635, 5300124500875981401567785928998770017, 3905217189095514489071610533198313723, 10349053210186526241541597254731042773, 27259171948384428080163050841877023487, 11743960521966993154037772650531499067, 42908349659446935723272434025606836277, 98356857879640930173654529731062247943, 58423561085864370649397712216952360697, 168524379487472293977090014598546107707, 27939409945295989981902847849873, 656892202882268552574375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 25] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false]

#time def chartRows063 : List Int := chartRows063_p00 ++ chartRows063_p01 ++ chartRows063_p02

#time def chartRows064_p00 : List Int :=
  decoded (raw_ints% [313517825912104134897397746195, 27229883895186420951172470170093, 27532659715594589459380442085039, 349527363050629153422951055191, 25327292928705924888409232030425, 25579533685844914612944948989877, 223884716111846400642828997865, 24433664990781387723788861728565, 12328297121815904952728108940815, 223931884821632576309432620265, 24431754064258539285837916038965, 12328320706170798040561410752015, 349452921823748412615435452247, 25329392530067918029026592209625, 25579479140810725482663125028789, 313586410152329083666126178835, 27227377438848526586761399656941, 27532730625067538642558500648623, 1967443453147025605162768698381, 30346775092505183367684611070985, 3844314964852985072798221757793, 2938838629017089701375928802975, 35097151251436629007412474450465, 8915200450246998972231117890925, 543276117901462271135664041365, 42102129608573542173188326282885, 42945849373216783759385712697595, 3223360499700452047162170625379, 52481987024283421683753723774145, 53738779315829386022795366279273, 9748142923298639603513271509955, 67889013606177158550485691285917]) [3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 3, 4, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows064_p01 : List Int :=
  decoded (raw_ints% [34966821619264464860316489519993, 15016524298596643835247709001877, 91474558717477980097806809813965, 47349155230212106579696979775909, 11960537930569789589596394725905, 127955110800563733891476527293425, 133635910620160436173834458005505, 610228507372294390332137247405, 187158862162036296814577967621205, 196611610953126856334284031291235, 66715513073396828006255188695481, 284173608687871097816503662629105, 75595437124587631330449000955159, 116964114833429983463310021993035, 454020914455623608839598722403129, 15189418012661791774730037953411, 54387672128517230299092095197671, 752030068021591031669743750601245, 820576179752676241451039617292871, 207042568589676276558919096393245, 1324223668511899293625072245565865, 1452212005446097715765246190870045, 853073155512302319506407278660975, 2408370616739001244141096521747205, 1359685149068876294194745831158755, 1782481860833217082251985588855617, 4736516290561108571650701360209765, 2677462657241635995073942264917051, 2081400429050774990694316213548235, 9538298060071869573149038877169673, 11300208033418039053788502545786189, 2417291299478114848049565790086157]) [2, 1, 0, 2, 2, 0, 1, 7, 0, 1, 1, 0, 3, 1, 0, 6, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows064_p02 : List Int :=
  decoded (raw_ints% [21387719722967308497205231068595645, 25132174089432048427375398133227287, 26542422809780211066713695207212645, 48214958851721707141942091518548185, 3833985131070294930392959781299035, 69598259308492608451190128659266295, 127557410962088152764060011897446225, 39371111053849384601047795091815875, 14984166486772806518633046389860809, 326607996085692140946702606155613365, 466829367312255051153510051264302739, 362018876429795679406197778942151895, 1086544066115547769956574980848538001, 1430613783960211314264034351386379473, 3624432723696721745541754371639092251, 3222759007524057576196284837692828525, 2889542130258262209309092140454887757, 12958079811535281856226225787178692845, 15584274960902434752123592467404907005, 11180798397874264010193082219863780305, 81457289771103043665092567346468376965, 55055078253665185001101187986407599905, 198234256149489897206797524919843007385, 28786731019243005998970033069819, 656892202882268552574375]) [0, 1, 1, 0, 5, 1, 0, 3, 5, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 24] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true]

#time def chartRows064 : List Int := chartRows064_p00 ++ chartRows064_p01 ++ chartRows064_p02

#time def chartRows065_p00 : List Int :=
  decoded (raw_ints% [91610339208456281933607562935, 955018532506383198831375089765, 1932801211402751651765833114401, 50769256156177985393968666105, 886172339687912171000850461701, 1790421616038117384438256885361, 16317869768356029094859747273, 853480020194027228043437757555, 1723334490113583369949428471983, 16315101637599085747796422601, 853536600151200112811130967155, 1723331721982826426602365147311, 50777990432217820714442020345, 886110223469225399539030602757, 1790424814052643333064603590257, 91594255730516690024902651575, 955092581015635754240015007845, 1932797060215377843803948262177, 144058291545762921389444973735, 1069298734930258779588835905907, 2168449607491657455218295887487, 216942479858943231239045883769, 1243209164107161597018904955315, 2529450378896363607846786744991, 322544941548673100552292428777, 1503183694648145242066927673445, 3068937800303979939638125057537, 484476074266329321859545742375, 1888299047204507798123489812869, 3875958816118982362049963228689, 737916011533848684703392864215, 2472135843180803885786019158195]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows065_p01 : List Int :=
  decoded (raw_ints% [5098350901919160368612901835279, 1157874519474575786761505786985, 3364131070272205167530275541299, 6994141432927584840077800486479, 1859895705352378001427761984793, 4787884882129955459309030732165, 10011911657754538628267068258257, 3118563666142136893129229345879, 7083922480976961170385799510885, 14990371029249053522824059588929, 5369375132827119719369484362695, 11025012214414229245567489423923, 23478309828218310135322773297503, 9785932996048554803456127045785, 17822672746631200609124768236275, 38633617957093984658148384705983, 18285243192585370620401454111625, 30596878206511338852479743515493, 66704794145727910082005965863393, 36874469907666811694991079993671, 54393159131801941849927676459525, 121864507245980092397398499968689, 75667340966444277816003894475383, 104345818021844962242461903502835, 234406318120091181908393474437743, 172829727690934609408264864247305, 205727841064690497481935465410291, 482903386777470069132662233160431, 394636144552098199166347954082105, 450005273403714181058991631997445, 1050369259020502877707275051489841, 1058346170903457390864468100850935]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows065_p02 : List Int :=
  decoded (raw_ints% [995000130168886895814631373574501, 2503351574476058467738091106422881, 2732423798827778311305538540365287, 2566697615210628962787927833699315, 6294121544207294169908097747639103, 9180549328108400323525841742931641, 6459847727824443518425708454305075, 18207094671143472804739478030936031, 27362593922407934818077870892109865, 20927796271427429609839611319562597, 54750237921659807946343190665977537, 133238781256491379926175430314654055, 61185035572640313154581450238524805, 215351613100559122690596491872741457, 471774733037845259754691641258862615, 287405358784410189462190471948870707, 820365127394895762371463563446258127, 5742673226810482494065187329370834089, 1004734501648330832663964732756250035, 7034813087243223516191342534075954831, 25200405328114375230044934250623277657, 11772751812405375177592565130690538885, 37977891642168081240301464114070066577, 253051443826400991712430084667, 22651455271802363881875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 24] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false]

#time def chartRows065 : List Int := chartRows065_p00 ++ chartRows065_p01 ++ chartRows065_p02

#time def chartRows066_p00 : List Int :=
  decoded (raw_ints% [6105207267355467771872940245, 245410484160765528416225101999, 248404666476229528598623898447, 845623439196476078102714941, 226978019722271657693530933915, 229429264427946784430056298429, 2159952305677736009904857699, 218350534106478293916938223887, 110252162304348619897664860601, 2160251265785420382782325347, 218338210499560713653911503119, 110252311784402462084103594425, 845505562583504545747969597, 226991539169619975448067525275, 229428919335258380916973270973, 6106074985276619603973128405, 245394388502232859117846530223, 248405113806479656490903284559, 19336972921924973753984815459, 275840139051832932279852552515, 69988559174739467363208589207, 29239669242365596434516347657, 322742280189932754133785792059, 41066359857906054955166939993, 21974082098322480869992694557, 392798816021295318017917943143, 401718712302258997815837256715, 16608103868454736893475045903, 498534936976512601093727348515, 512099291972722907129722829441, 102866501638171866092862814345, 658528477916571108313518677591]) [2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows066_p01 : List Int :=
  decoded (raw_ints% [340699104542356860398242913699, 162676534787028895354308878543, 910000943529200065465178605895, 473470622754957241121828760143, 66935013301299517325964628931, 1309234617064686689730754191763, 1377357833502141446901824914553, 226256511307616954265776581319, 1980961156349992342680612668791, 2097610909322573424737236592915, 807589180880953929598142565199, 3119286707525622323856966842315, 209857069551172578929183270047, 1480048627069513956243945327605, 5211317879873808061073182929587, 1411337730192307287177255053389, 1459477589754565183403209781263, 9039481215803678148832748152735, 10044354727347873471759385103687, 183637371183884275803651000299, 16887138597910329528298861179691, 18839705784741300664282636675781, 13114147211932194262766292521461, 32545064727340865451700076191007, 18915124437278895876382880603405, 29407112364139072494346503095483, 69343727445639106579364031265535, 40175754225314529254939278411877, 4810832333784091315424448938195, 150173514183897155429086088572939, 186731938155313592051016242930357, 97743355492140962871268440381881]) [2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 1, 0, 3, 2, 0, 1, 6, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows066_p02 : List Int :=
  decoded (raw_ints% [377236996807820950766528763310015, 459191966480140978840344306705239, 640024535379273854789145310577851, 932120358121024858399233611627987, 323675803210924189843006624511713, 1881121904415168298112645940908897, 2937335138324916369923110005621419, 119245301644941841008556804672925, 4450812336662284266491660321924353, 8456607975781698050849817375263575, 14598596230377875743369784334291203, 7799240329483987744493312967662305, 38543833831623190501856392581016243, 54697182221638395254326356848789129, 367246742939694007407744875061570529, 133244453247525501962742824857860455, 226570443239634176820022241890504439, 1604516387230285562501567847597191207, 1507530805590399220132835892827298359, 1212452008324623961774678603219885307, 3637118960730880862314610803490753899, 6551310002168667751969014215246625283, 10519055439043989963207518159926053775, 260615081010940464142369778937, 22651455271802363881875]) [0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 0, 22] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, false, true]

#time def chartRows066 : List Int := chartRows066_p00 ++ chartRows066_p01 ++ chartRows066_p02

#time def chartRows067_p00 : List Int :=
  decoded (raw_ints% [8682323710983520233441788185, 83536485053896002422659220645, 169262575272678244893215685811, 4779499851481717628799784623, 77043766507798722237114676981, 155800751710213007030974113003, 1531329728995523775336050647, 73977485350932567165059651399, 149489922129735765626838277733, 1531155366896977351479275479, 73981107049807674686442575687, 149489747767637219202981502565, 4780049685661540868321007279, 77039796084726521868018202357, 155800952820195737422781785323, 8681312406175549710408925465, 83541206421130756423084590245, 169262314912032828001511718067, 13788131099563638664160729489, 94402420897077621288836053287, 191731758417772016376081373021, 21053063611300881190813108191, 111117468620258033751406049223, 226572953128636536231055210701, 31830965143313705909356376343, 136508548119679383670462269669, 279456981883251123331224695235, 48854436905214577522538572353, 174779398906885445570118801909, 360142383931779406763119643931, 76249873980022755446589454425, 234217421930108538715539414375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows067_p01 : List Int :=
  decoded (raw_ints% [485246694817016739732247670709, 123364626018410733178300727943, 327279146866930956463297710759, 684861194815450228357137853077, 204810822198488707883397157407, 480946673966930005072140870261, 1013036643032349669418835738427, 358070207903799896068210821321, 736900791263908372230092025573, 1575917673134638273370443717155, 643610049564835876921892216961, 1197087089774529797208562512903, 2577597930603274046360546755437, 1241289645246325081221256766415, 2024120890393580126073876459495, 4462497625414435004503695738813, 2450686351212344221509275954631, 3679666380267179959651076045733, 8154473621873104307234228459859, 5341989626752896441010693148849, 6925493592818268569092428368757, 15947149599838344969754197563339, 11757004943815277713092919940617, 14363645633772972841672462343431, 33046144170406519123857810652805, 30021985113063975457940636508087, 30439503480448823995278268249991, 74825134227285772294891367101509, 74951067594591020668796985272335, 74407615859900923757553735359605, 179798186934940768421628988881931, 238974485409190875306379087332857]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows067_p02 : List Int :=
  decoded (raw_ints% [180341638669630865332872238794661, 493723739938722664396805061487123, 692151835422889788027014970371313, 552356586678282674370311910025319, 1424850060770803327730199119191293, 3180449756141194368788661641632319, 1564645309515410441386902179537287, 5297451652334887484545875731194925, 11025800552536207006792698042504439, 6913256098960671411947635193289957, 19503701961012288860127235415331683, 125382310086383092776935070310841505, 23616246414587824454972298264546165, 155911812599931588643855003768677627, 545236559702766367368964468111640889, 257677876271726856965817775814972967, 826530682389081048789754542191160021, 4727079166702151998010949207766603929, 1114089365820120559192901234487827943, 3355311924610304581852230197463803019, 27885885028697235233674872178106189697, 9196480457132577139056080639718234891, 35968276120009691813538051583336596645, 44486224745915441281664368499, 7550485090600787960625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 22] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows067 : List Int := chartRows067_p00 ++ chartRows067_p01 ++ chartRows067_p02

#time def chartRows068_p00 : List Int :=
  decoded (raw_ints% [290595397391340085646481089, 42972683113558554778756709383, 43552379481668134860184342409, 639459842982840204272621327, 39482549491516273571268278011, 39948696616571733766467251043, 406789384239746487167233243, 37857004369695833144575738767, 19131493773183153435377387573, 406827917798486046459305179, 37855391954557287622599345039, 19131513039962523215023423541, 639399103155714781151538959, 39484316040889777330412959483, 39948652204034962038809230179, 290623312651663924888966337, 42970584779803005871811656711, 43552436911559703000224038793, 3722868246228159393901394207, 48784262045743022926859882267, 3100018228687573362077322731, 5711133300128230010684838229, 57862057764715643447417233539, 14758573301339390799455849033, 2187720316249500902159382417, 71628795246255942969599235183, 73496307770483796817145764029, 6763780053513150198122742423, 92865582824707657881967352211, 95774749142508100822028778543, 21552336221062856656246627737, 125739035674361144554581174567]) [4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 5, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows068_p01 : List Int :=
  decoded (raw_ints% [65427322735298628937260445563, 35168189577045720128874656079, 179074927708959084506953863159, 93787585634352917329821087471, 30115964995374160169423311029, 266411793982544025070079798883, 282975290836499875127363453079, 26532572561610009780327942549, 420002647671952365862340351391, 449337511073688234587521845333, 200040224768087860634087742867, 690932954968304181555326879667, 188877006522054033585730339599, 386972843475696752077562120649, 1220163546744303808398691322859, 167815136791500093381821402739, 51450903389389656499350951913, 2238824328871091189865575362263, 2552708392037932003121748573169, 888228397299734541278631432253, 4513021363665241824357152245291, 5152379640867635589668626668283, 4421364440433882333256733935117, 9344651507268967520094626820287, 5675100437950493502741311733953, 10840002762667851807162319124419, 22198479125400771157384087985759, 13305784039501360572950838263721, 16813689843913425958550969824859, 52704662557940374748743903317963, 71078950529497424870165935301579, 2996657165633055871461069339733]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 4, 5, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 6] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows068_p02 : List Int :=
  decoded (raw_ints% [156707997876708178825791846584631, 200599359517582064674022093822753, 427438662772324604107306334909447, 436276779758971526295760778803787, 90491381448770557083510330950457, 1464764877681016216116803086993469, 1866462648966006595255017186222419, 654033648010876319223048017376643, 4017598077800107901354349326362807, 6295336290483036390762973126777663, 20151291780924953098426392461951269, 34766447424076872621051593189248483, 66148031893767733016924606408027331, 105754578940279129945946976145899463, 575211852254754279031151232797739903, 284426915683098017359175718640765527, 199962189233160701921550535136671737, 3417580475282459542164478096777209801, 2234699377125249383107680324782932281, 2196358353001767612519365199924146589, 2984060409975371922993942686399372289, 13385894985446740151298736668468073677, 1842176361335250921215323123826758401, 45877142660798855545356191121, 7550485090600787960625]) [0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 21] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows068 : List Int := chartRows068_p00 ++ chartRows068_p01 ++ chartRows068_p02

#time def chartRows069_p00 : List Int :=
  decoded (raw_ints% [999071269505249270463780825, 8807861046173361927118345167, 17872291436413273945027306807, 545561495269438081177719751, 8065359120734662747445180815, 16327658671638586593385806231, 174165751777032919262607015, 7716738055634485764762905665, 15607931424592115592945479465, 174152005787642060928767655, 7717027617180596908919966785, 15607917678602724734611640105, 545604819757713320645358535, 8065042067209769886620440975, 16327674504148080116185766295, 998991661779862297915766745, 8808237256696023550210683855, 17872270985685655734746891575, 1605169077668934102152081785, 10063025390769494482451974465, 20476431725134452134814740105, 2491789626323565482694024775, 12018575412033891754514847425, 24573390429126951719660846665, 3843526967438005036335164135, 15046604643416625447840024015, 30908707022888522238690035575, 6054735577744428360845298681, 19705629346909901827185175695, 40806969568070955635870498391, 9730704185684969612560678425, 27156075798905482169530621377]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows069_p01 : List Int :=
  decoded (raw_ints% [56592409331500353609276475497, 16344803146914553573206661479, 39167037718279841052306532545, 82667916664099876795043815401, 28241901095306631588087763335, 59845682092734589315943944335, 127254620906321061956338240215, 52028138827574340002982055065, 95650839908893104228482059215, 207524660829202033547408058615, 98579929071579831372022555449, 163901959747883269321908054465, 358132728728356204922412669129, 204588051886924730232115145735, 292810698052052766972527170113, 661300709686860766526550370313, 432582850767843937671062338471, 573078063521732729786138345935, 1298471612341629434429727854519, 1048748110934940913663058382265, 1157976399587740642314651847055, 2779802574044414285763848575255, 2522998262914248583951116551385, 2670574285391614557112255110465, 6351548947893603783378023508905, 7609243267220217323804445772327, 6203972925416237810216884949825, 16483790478028069691133585832617, 21345651655723744822254639418695, 17889060819832049204721146655119, 45438685400972031837192671023639, 92211459856528766441879963571033]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows069_p02 : List Int :=
  decoded (raw_ints% [48895276236863727454726163787215, 158995796913224543101327274013367, 312127982677368925891490270967545, 202311980532889582088481073797185, 563335239447122235434697508551945, 3299559144916169079307779849172935, 673151241591601579237706705722305, 4175022367040660240633967628692425, 14199515925482833742898729003088487, 6801430270365227740704040772143055, 21674097437439663062840476480953847, 111828325772669235881961196227735175, 29072183092557269065035164711899279, 75954712409746739076221990743692841, 669609602334380703241524393717482087, 216855221274973244023218351683327295, 857392640516796678199707580688910103, 1078581596100418229472535626871179495, 1310147021576204137418013622723064895, 448420646750759151968696347535212695, 10903022865007357350306941143664707335, 1940307970925863214921852902059031695, 11533183814357016427810780423000674135, 1179460169119907700968192977, 1510097018120157592125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 21] [true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows069 : List Int := chartRows069_p00 ++ chartRows069_p01 ++ chartRows069_p02

#time def chartRows070_p00 : List Int :=
  decoded (raw_ints% [33639544641842341008458645, 1135041740613794115939054125, 1152137054428725697048165441, 9175945711865892374515485, 1034674189676287914123442177, 1048154182297577445533186211, 11620078788613587408917993, 988226609223939837946806365, 499915160330750144313103139, 11620850800826327941339625, 988193874521833564487770205, 499915546336856514579313955, 9175337546326210416895005, 1034710012427245149712164865, 1048153293659844198767547555, 33641778631078566695275925, 1134999275263052931158090285, 1152138201107306173825679425, 109196998249627163490871985, 1303844241475873683274372265, 332154689154772617676775815, 170430337619681157960606435, 1571787268261561585121578225, 100515380780524924509911355, 133652270081229396083451049, 1985565591954598315116798005, 2045980970270538742286090213, 53063902402608117660630185, 2641005428911396753789186617, 2737796729653862475738033791, 700438036098955747535374635, 3683610468838058080256963925]) [2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 5, 2, 0, 1, 4, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows070_p01 : List Int :=
  decoded (raw_ints% [1931372992486841582279224953, 1187289455858541921045906045, 5442757573307219743930685157, 2875236738465590416569865293, 133600483329829380071628147, 8432768292272225764440588105, 9075370666066992835331686983, 1982295349684196417455424211, 13993188506416300068514886565, 15177569098712655751388585757, 8021436192302070598476370885, 24291131089745797104083981793, 3395449498797889898096975633, 16602205651021621855415623415, 46078933275624582462420370105, 12946809458426702909666949841, 19586138531069933612359479015, 90699953693832284525746475453, 107561720546868300718802380809, 23092723004184416402667175937, 202768041524184051361296202225, 239104889625745833554190042587, 270577961739092387456188068031, 460183521760782946968421290445, 301026871690787943310523407183, 745922393444862089993963210385, 1285079888480553601186048474349, 809277049282765182035599046391, 779862030076539602408632682555, 3443873095540231306944274131985, 5483924612316550863699692033387, 5210572374905506678911238099985]) [2, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows070_p02 : List Int :=
  decoded (raw_ints% [13762872369705187239724171395229, 19024517482433722631156698963577, 105993024187658550978385147194969, 45128452094784284738234178931865, 33859671604975821741841080589629, 453489249802062520681685113683851, 437734969120339391153264760175105, 86865120051203044828429322904667, 1695761549459959921950068499932635, 1859085451303034367464974633667269, 2243112888708232964591017302944083, 320024427975361571549149449180345, 13128357426559339984447283239285975, 26116199378051293387636719050351433, 30211044318144988756333098009629395, 80067168110389527949117284356501051, 8193359225164722605224592894132059, 319794175035608003287873444924905509, 107715819846020615040885108799231605, 166809250451711773416878678573135393, 7687206690684789464730431562062475, 1199109532032042485202376495343120985, 591915022413553234403787349574676495, 1219416143712410379065082731, 1510097018120157592125]) [0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 7, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 0, 18] [true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, false, true]

#time def chartRows070 : List Int := chartRows070_p00 ++ chartRows070_p01 ++ chartRows070_p02

#time def chartRows071_p00 : List Int :=
  decoded (raw_ints% [6338341151454375010992163, 50761281970479399113778291, 103186535957325478531126169, 3427374628528334822001765, 46086912835391704406355715, 93420820177342768698132241, 1089542441737868455568813, 43906532713422729469774761, 88903903107076565420561663, 1089481718444020618923437, 43907827951915967495218089, 88903842383782717583916287, 3427565930508473415021669, 46085496150310770707621635, 93420890032735211617861393, 6337989940194335189116963, 50762959812932914325261427, 103186445903438020222000025, 10327090624119719394927995, 58761476030699441085855561, 119851526467752074806044983, 16357680680344832689599221, 71417141061172353115117417, 146536297772216626890572199, 25850020396201472145568013, 91476837391389106465054003, 188743998848762931725739433, 42051912336496076882176651, 123117181853575297406253443, 256645931581460480753484097, 70044192467836742957859971, 175580662064381260229407305]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows071_p01 : List Int :=
  decoded (raw_ints% [368742036385793300593520719, 123344644867034705676970077, 263205566789248783321973385, 562130873720664749228350767, 223922946717296305102050261, 422269951798450671583347459, 909398465304995760007371105, 441591413654223616352880851, 711051460223841393526073907, 1574912825676515681462302217, 894044229598628635827617131, 1305452779106897904289109161, 2910548468929367933642800199, 2051646697129271627404725221, 2499139919421098665181308169, 5856239395657268196875142551, 4737544619401503187864928957, 5408746173365441159098559603, 12645430712188043012144796729, 13466724766521752719287650555, 11974229158224105040911166083, 30849700098111298919297376241, 36446348612923653125075177011, 32342195706408946597673860713, 80762773477556704763660203807, 147390397275378890605970768781, 84866926384071411291061520105, 264599519365859248494706149599, 485520803793982789496717028293, 327122990257166727809615398275, 897510720435220928597393946673, 4744013475420353879628488485123]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows071_p02 : List Int :=
  decoded (raw_ints% [1055908533972036990284495576691, 6127044999649557597722599460089, 20170002625439993289351300345051, 9815149941097874487066592368521, 31041061100509904766702388290263, 142849162146253276125095761117867, 41395913784852023568987096266793, 91638098420303378069042072482553, 870785896876659773080320386431763, 275883174351408677763124929867213, 1105273157443216427274458220032183, 1166066003571443970367089118846699, 1700175879968467522591653676596733, 809993050748432229987689487617247, 13013591462455939971764056171906915, 2056248832791479262971053307826185, 13369664415278951712143455803136367, 1360288153953665113526706597155011, 24327007044943412420936458667217097, 25022967723781226570380805377888271, 121065614445467057868278639899423691, 664327475115850964082359886483837, 97402934875639496411424541118690431, 27381219277194963385529583, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18] [true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows071 : List Int := chartRows071_p00 ++ chartRows071_p01 ++ chartRows071_p02

#time def chartRows072_p00 : List Int :=
  decoded (raw_ints% [430109274257525019349135, 26245399222929609517865875, 26692165524871263883699209, 464573472749125257175389, 23698057632752718094739463, 24042581482342913291951891, 292459699639158663360983, 22528811440936607460462763, 11410487418602752057120065, 292473510970444451676119, 22528218834196083441295531, 11410494324268394951277633, 464551721619394527068253, 23698705484818385267167239, 24042565602746023408367891, 430129232914072625399695, 26244632607151239657841555, 26692185977641102964103177, 2838773601602169377332323, 30580773211443547273562359, 3906434563862445355379285, 4524753251655751696066001, 37599727013559917167170847, 9653750841039370979108151, 456557419467115264936011, 48679786218066554057826363, 50444675327287079851474781, 5995997099963008960190809, 66819401859455294123075551, 69741588238686942010832575, 20682028533911636434161245, 96647763017770625739352835]) [3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 3, 5, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows072_p01 : List Int :=
  decoded (raw_ints% [51207805486262298182687719, 36756534466132110880828171, 149547515995101839859720531, 79927086986284171840182427, 35316361446372013449058067, 243673900882299069262665519, 267243431331444481459309159, 17471139623266045701438949, 432078407566077947452185067, 477645271210316873968936885, 311690706086185400665405847, 802750368826812531708711887, 232276273570657660061463581, 704004142189256739850435845, 1678841231910819550113808455, 121549996409879548797606001, 484971866374513328434794599, 3618766937583839491110455267, 4588691550245382834351310257, 2574067365198735037874678799, 9438391093903032805070522039, 11676713746140906223839846251, 20107399591583355057091160977, 24211305859173719794107885659, 18466124034060865678340182413, 65246340535891503958258995519, 89867989460236453033435165947, 61142994097798295186015260661, 305713163641282142586490411465, 285196668002739735627143867735, 798958656014052379503270339771, 645485493241372890743875236997]) [2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 3, 1, 0, 5, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows072_p02 : List Int :=
  decoded (raw_ints% [2535573298590493593725358457667, 3992326956262108227651752110689, 17263140405637707918331515364917, 10612964559864705987529147659687, 167013616818907939495379098535, 106326980555287053444403534441159, 66516988323960338079600703002001, 33569748109333717372609828028079, 15987764915745961434603908574993, 414694957661283507790084990104949, 112703853666654231458011577953531, 758925362766893193910892032063685, 445091488979910427827724371397775, 1533048991193099847840603754773783, 24277692628093263129894959836731, 5656707944473862043497051266404531, 1513311012049396486266246429532211, 13506502698507902244472981551899021, 347980718467537375308144532050851, 5252079183518601267535191826335665, 3827786515131018737366555149342081, 48369302849557746934394874941191553, 31666234095807142254276475503254513, 28412602621901363961095749, 65656392092180764875]) [0, 1, 1, 0, 7, 1, 0, 3, 4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 17] [true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, true, true, false, true, false, false, true]

#time def chartRows072 : List Int := chartRows072_p00 ++ chartRows072_p01 ++ chartRows072_p02

#time def chartRows073_p00 : List Int :=
  decoded (raw_ints% [3765932040461730242021661, 27110015153718886064951423, 55235607853957384253033403, 2011729450170635068350483, 24359660659776767946060319, 49457946363325018942661259, 636279753565536554481379, 23086556253377615928250457, 46809937159588847319829397, 636254493821773628873443, 23087101152645694837097561, 46809911899845084394221461, 2011808996904979815395859, 24359065241021163185997343, 49457975390571837838490763, 3765786111321370666136349, 27110719146455654467889279, 55235570498798188320022971, 6242067640897736210912781, 31890637463663904518270041, 65243424251017295197072101, 10139078711695538168948499, 39594854428251126889714841, 81624570603610569576933381, 16510183479166362776734339, 52168794887054980856167039, 108273832794472470522616219, 27977739730230349439396621, 72615221386583852443183519, 152761756003869182738747179, 48735365930522325364266429, 108124274347515679734960281]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows073_p01 : List Int :=
  decoded (raw_ints% [229474861664621857542410229, 91295971306672463555796099, 170085953247628503171716377, 369506198901816646462472757, 176497918080048588296366643, 290716216960860606846552479, 637300088288537698314635499, 382282452602509872277692861, 523081789407725679764449663, 1196080458971096158888695003, 843709831696123055116585517, 1055281122165880351401938201, 2422072743269729086282973381, 2251480166764991193424229683, 2210501452799971789997620697, 5517262741730843334823788581, 5851978226924946926653973283, 5558241455695862738250397567, 13620721135420781454901991547, 22047025745863480953244731693, 13914457906649865643305567263, 41519725108209209334800696523, 70394017613914077607948602717, 49652292947422824644739860953, 133960768467986767895994030933, 631532938959391995587951448867, 154702493134478020859202772697, 835887725041292841091894082517, 2647186825509151851239042150227, 1312718170866206815820642758687, 4114607489509836687918887681611, 16651716803610281079840002970787]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true]

#time def chartRows073_p02 : List Int :=
  decoded (raw_ints% [5449076144152781723337287073151, 9889922488591292540682073138949, 103745044190938751344401963577011, 31990715436354355343859363182887, 130286683483140324964924039686747, 110638967933067479388851045023827, 202041012237724720965466640080871, 123392759741011596920474958239931, 1411523720011760179030470943420611, 189287220429780603433842726864767, 1398769928203816061498847030204507, 103624374045445552488729677687373, 2621006427785795637095475246760351, 2913918022261021793018047651312491, 11988652107391205938589533767098371, 396535968520671708411302082239513, 8971109711084738593082756438098507, 7679851030599226313024195989180733, 21356297786996616240083592287436391, 28639612849075170844696486194377611, 75576530266372977122728874515640691, 14963166092677780917637089896121953, 39257066386698579965008192332082347, 7375192486802389311881883, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 17] [true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows073 : List Int := chartRows073_p00 ++ chartRows073_p01 ++ chartRows073_p02

#time def chartRows074_p00 : List Int :=
  decoded (raw_ints% [258041433789429411119825, 7037824102413853921371855, 7175330039746688328956695, 134408174947860310625, 6280670241921805092062235, 6383979229874611590557045, 86010927100944896433235, 5936752333240982256731855, 3011350180240224388981905, 86013827684032621796275, 5936626533518025506329295, 3011351630531768251663425, 8601837799009631263271, 6280807643977112743916955, 6383975898315877325547797, 258049807904645307229505, 7037661771791258308027983, 7175334323693476140431479, 869409889484590800720803, 8345206107214275201752995, 2140210957246839388902823, 1422528317379614569767945, 10515301329729621510911195, 1356597754481445365762505, 1191515241444373256633745, 14035319376732733480824775, 14658340836119924009135475, 1019717473836250508695937, 20047423261284607563981155, 21120241214353672557186713, 7456069465977070638526585, 30350798958112741619959767]) [2, 0, 1, 12, 0, 1, 1, 0, 2, 1, 0, 2, 6, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows074_p01 : List Int :=
  decoded (raw_ints% [16327590287837872615248523, 14079166930658815412287487, 49871701125192890118087495, 27095208486155815640655559, 7400433245031304225064185, 86667466680748003269109715, 97871316883095663593855345, 31883768645862005816978595, 168278633045693757719114455, 191240587154944892128069275, 164617211208164599978077039, 341737615847644049804938475, 26226583478427093983756469, 418491393088177709525143765, 826747477878352157631422611, 250683484987793953310831077, 759337234528627526191506163, 2015703188200354887905513535, 2939899802096608575151480399, 595675471829026093309716065, 6901445354107372367163471915, 9223978045786072374012221245, 40848798644342344664498066885, 21077318286729189873816427615, 27419090232380312892494008325, 169848890241275581068728092619, 170296639931476751025155739455, 132767934675189275759107088077, 125157665776026304086070294275, 700472879251831514148728798091, 565876566616556300101620085427, 3159307891266611792679037492987]) [2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 1, 0, 3, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true]

#time def chartRows074_p02 : List Int :=
  decoded (raw_ints% [3834748664901364979729093677345, 7885753675357990318148257425601, 5874203818770762612421404582075, 24573990250881062827283571145805, 2082541409780112822771231957375, 81736168459608284138118056597025, 19662066610181685469956524650955, 2477506457476831108107954167175, 6695730823869596432113819043925, 302370683587552073725188655242295, 174407836746606072461800228034475, 165267629590236371219271283534525, 73227913201138456926867077002355, 473271219966600219551057268015775, 473514151099379066206984835654255, 2341911389856229865783151881310105, 803927944713462385317563618904065, 3974242419126260207359952211301655, 1820828691196377807901072265614665, 946436189299978185258920068919635, 1092497235941151287776858331743675, 13555058286648810963656656963896515, 10237103741490821728985225676115625, 7691412907325547151196345, 65656392092180764875]) [0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 0, 15] [false, true, true, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows074 : List Int := chartRows074_p00 ++ chartRows074_p01 ++ chartRows074_p02

#time def chartRows075_p00 : List Int :=
  decoded (raw_ints% [1144283840079327772016195, 7307086463131001717385055, 14933201685638241271637105, 601861690697621234100725, 6481831382427911782235855, 13187056154861292265520185, 189175838862301298582605, 6103363081735759249183605, 12396018625301369732836855, 189170487774690029695117, 6103479704703309185070645, 12396013274213758463949367, 601878536156833910595125, 6481704057285139308573839, 13187062298145282404239609, 1144252957885261667687555, 7307236777016977006260895, 14933193792187377982522289, 1937991170369686450018955, 8770209973055662643948949, 18015437920442326100228799, 3251523048122248628548293, 11183219117756349906298805, 23204952138934261178796047, 5500093095402255010690573, 15273256069300159901045535, 31956568282458764818034913, 9837269214858364157950875, 22183405308560859927679951, 47293930592719383986676361, 18155419673908979336801795, 34947794499016888216947285]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows075_p01 : List Int :=
  decoded (raw_ints% [75286619481486727481429031, 37054068387158259513050205, 58494244656378818601283541, 130496107542553966331281031, 77841189984633094890320197, 109055931273333407243047695, 245391365914345320734651433, 194210796838592361441385299, 214176624625645008381923935, 517443352737570777066356929, 482246319068235582493941275, 497477524950518130125818293, 1193900468644398721001683503, 1683272193927089735908855125, 1178669262762116173369806485, 3359418981639724039404479903, 5183863226477693378668615645, 3864021912804697601943528543, 10226554402044507153981950673, 42367421156783169704027800491, 11546395715717502930707037775, 57777838785305370236678366809, 174614203020698746081369379539, 88598864226371037009999129525, 274759462962787286022075546839, 960412684225281491052322171475, 360774801757114995093445796853, 511039018241795458948877245097, 6148767188150052456532741074475, 1832226504224191945094645213425, 7620218890617129406533940491047, 4872941950698957599690912832675]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false]

#time def chartRows075_p02 : List Int :=
  decoded (raw_ints% [11936759574542989917972036352097, 8896044128068224263375768732847, 75417551561911408846671597851691, 7913657397173723254287180451925, 71394449384542142182986741951519, 19265663281908054062800761505125, 138898343549279827775371159351285, 166077664228361605092459101308335, 579334354865484167299171322763475, 46444983960989831379888703462175, 393991027355214508143911459950015, 460122699920543860355500036493765, 1019770366181688506822971486175665, 1433448082141242535798582819207255, 3313171874039109676951268050864675, 873800415880097889331111369525355, 1419601091977323280797185195163655, 3896474731483300648903486591657085, 5606573381896530847079564615553685, 8629247697499733606651939837685415, 15334634595911216166021070915108891, 6919149047086503408475861813788815, 2808912166928181910465644485766391, 4019371381429392260913325, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 15] [false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows075 : List Int := chartRows075_p00 ++ chartRows075_p01 ++ chartRows075_p02

#time def chartRows076_p00 : List Int :=
  decoded (raw_ints% [39696263813383230213409, 3815644892530454235746441, 3902926537845526999435175, 83367341631847346426793, 3355067962146468079709365, 3418621744074766464874317, 51604012408415299601453, 3148706159475675464332097, 1600141524201328236209639, 51605250967668063218237, 3148651912512806881303553, 1600142143480954618018031, 83365392429102030223185, 3355127163346347717205045, 3418620322787781359700669, 39697156884816680638099, 3815575051945623123089033, 3902928362724518865251831, 549615272385263002226281, 4625436183660481497624213, 596265111273539414072863, 929966931177987636812691, 6014036141486675131994157, 1562425773437891487905469, 409098171067526989232787, 8345303908372432044874977, 8816062709199661545365715, 1478675505657790608525633, 12559606878567106959718749, 13409806404785350719348129, 5862006059473416533685759, 20174707953634756913080041]) [4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows076_p01 : List Int :=
  decoded (raw_ints% [11114581737787174235042577, 12000416370580165584180201, 36007631116460773094461785, 20045792952813965293975557, 14454674428356258677193723, 68176373435955419249800845, 81001351132920613526518761, 17503192946322628036586523, 151645026543310842512011569, 179923471774923643027252299, 234688211390835143368440981, 348227460577117467835185213, 121156113737762324635509843, 708268077619365351347072319, 1090397872106651415985775493, 44611898248789056039298521, 172073245488074636637259053, 3181299771054578873223474489, 7642192677199003516996914687, 11237384985567875842698368555, 23115773294580204905554934277, 35623306503953143574785941493, 114755637409640255328423597013, 93080379655597585614810422929, 28328780467275680034120459205, 746769087892351198125063437931, 435906776343980816408139453775, 459091143118271406760863976677, 244533112438641507667293761701, 2893995971913807206885443328795, 1175885149251610996312203867883, 135290596384991848894949862673]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 6, 6, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 7] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false]

#time def chartRows076_p02 : List Int :=
  decoded (raw_ints% [1520358123165151244930210639833, 7971779244265150348299174866591, 3017325904987698091681345638081, 31740396702644106110221721515493, 613990728684135211539290991117, 62989599921411166988446602351893, 13589661743115943611655593192157, 10081142674632785531876986249517, 13776782115724102077635363549635, 220218002983000561843564687892079, 158421299082838717426496001548501, 170864846126103292892189614885653, 206838852108469689630510223602003, 128201264706471460047341774024265, 429544009958740733813108100312663, 1146700766025825781293952231193145, 449737483458709389822414552054117, 1502682826468080088034408930606271, 1511337187726493245621922177648649, 86831924795960287288235863092687, 1193591571289682021647757136523953, 4864030539846494570843683491231939, 4063529818639364705906394929839551, 4220496648352592841142447, 65656392092180764875]) [0, 1, 1, 0, 6, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 14] [true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows076 : List Int := chartRows076_p00 ++ chartRows076_p01 ++ chartRows076_p02

#time def chartRows077_p00 : List Int :=
  decoded (raw_ints% [716190059151948200304235, 3987867309624416205324485, 8184011183223915973607189, 369079623437021129732917, 3479953814447551567978469, 7098741500634946643570037, 115097562884795288495893, 3249708062750373945858651, 6614564314313130225341227, 115095261753486070595701, 3249758688677960990986683, 6614562013181821007441035, 369086865202059425732821, 3479898586257346087050053, 7098744140137366503769557, 716176791196643291193355, 3987932419082079842452325, 8184007796536069220695733, 1247284932822982025847083, 4912252168650632669436763, 10147469520555694537736171, 2185634474638856280085429, 6482502284728043894146491, 13580388928017532843668683, 3886786573298035919220501, 9283521117928345229607621, 19652809975954425042974613, 7497653373469061485980747, 14256075431324115732587493, 31037249922721522448175861, 14956701827114276999193195, 24278827864866468201569115]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows077_p01 : List Int :=
  decoded (raw_ints% [53491605123304860933349803, 34769834620758722477596149, 44169479085552669730973883, 103218141571177860410139147, 82010943073358286781328469, 93818497106383913156761413, 219998919265294869669063765, 263594243112313696723499403, 208191365232269243293630821, 565604105450966853173891637, 778275714799191792751174827, 621006983331011306603760219, 1607474063362472342648565867, 5741024133285760621205178165, 1764742794830652828795980475, 8126773911447424756604918859, 23183025044106306283829147797, 12103055249902532549014116549, 37050823088839491661639244821, 109249314707787127746978713653, 48130792883043265396454276069, 49015466574841329801510321035, 724294354969264842817014394901, 206395574165671722944943310757, 882559136251893300365503429589, 374310523684067303058944644981, 1400457917055486420237574513733, 1232542967537090840123573179509, 7911828960290613175595488713685, 542225473202462883172945979205, 7053596516437589638530860179157, 3506391909249089027998861907723]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false]

#time def chartRows077_p02 : List Int :=
  decoded (raw_ints% [14423200003525739930953402913637, 18471817385977291842125210800565, 54331002206802603996648653099989, 7555009291700640939170669794651, 32352792911576223126524580391701, 52089803447353770080212623034699, 94238804410079468062343903286341, 138773598565732597203385856526389, 278740090309678439553563756150293, 96624597603006899221254576274747, 87876688296592072269965276589205, 374436877233504845075949918836555, 463241376209277411044783609014245, 741053655839775356899478951576053, 1160953145097256985073609304399509, 652249156864002790930645261398363, 45462612023976783098180433986901, 1957639157530407236995454946169611, 1858664913985236559102434999784773, 3164054914651641005167244684556021, 4119914200997292676757911338805077, 3263029158196811683060264630940859, 1001779871184755565404788291920555, 69532822206061438858683, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 14] [true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows077 : List Int := chartRows077_p00 ++ chartRows077_p01 ++ chartRows077_p02

#time def chartRows078_p00 : List Int :=
  decoded (raw_ints% [6315057964017873016203, 262391996278160983119909, 269606461994062434341003, 6495776869299274579771, 226300463997820901432473, 231354676399392393116649, 3969411032306125672299, 210425781323766786481741, 26799213953560964785601, 3969478038943124026407, 210422819868596398743277, 53598444658781179159729, 6495671448390812948497, 226303693479539282587369, 231354599570849466562317, 3157577254831663955427, 262388191455722902331253, 269606560506284404102727, 45348166183041585803231, 327346165634152529161033, 170107672363989650774687, 80230477567700981501681, 443780856187889245544177, 232896994239360934427143, 9457279271404275046129, 648268075904956455167757, 697340934388891251094031, 147225340774165271445507, 1049046729557762848496433, 1143108084279690194723109, 660459771352464516534249, 1826070802098278626731813]) [3, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows078_p01 : List Int :=
  decoded (raw_ints% [524504634295121313537093, 1515162641780884133231931, 3690885814967620914633429, 534205118789229237989319, 2331001247666224737355119, 7886721369221815159659537, 10450806087427167511856721, 3360518316513753606123621, 22338895796297418813474381, 28554881848814631411061443, 93822308000693322318267507, 61655014433441872857637473, 67909631557781484076911717, 374395549747769512405532101, 397628127799070708086544409, 302018560432012901438811521, 404329167694083388964920333, 1559237213424519922479765877, 638884000164538240576526189, 5477431964560680884975915903, 6071638555306263515352180919, 13211064600062233566388039327, 4141582442755781045424118077, 42260218503060927157327561347, 625760815200869196591117283, 112305230020179461362936936271, 10494691215716860666344291389, 24105616594126857029361325323, 30317989468320311614176600333, 406960701577656918294420183737, 269363675333327512708735438229, 45331223481828307657248169671]) [3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 6, 1, 0, 3, 2, 0, 1, 5] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, true, false, true, true]

#time def chartRows078_p02 : List Int :=
  decoded (raw_ints% [253038606962279353579757094053, 395299921439284786578882075841, 759115792384280092080645643769, 2494237601259354771769462675207, 939857644766408900587749217173, 3506392026875760494819767646361, 2783424562574841014742825481023, 433780472479331300781811784123, 629584135665838318501507045313, 11531330506243687207509607910237, 9410626057161129644395447577111, 6892289429983362494451822787777, 17363267778731985177305399968993, 662720282521111203503858364061, 24737535320508887293526936405359, 43606984933623212748104974391979, 9464848474488625269731680904213, 46233767206102373805097013987427, 81586873503303563996802345652443, 511348812886281705229895188587, 49932950498936240866641067004907, 141328083890786282472283081557729, 129736506191613840971022501962457, 294866693850133926405815, 65656392092180764875]) [0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 0, 10] [true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows078 : List Int := chartRows078_p00 ++ chartRows078_p01 ++ chartRows078_p02

#time def chartRows079_p00 : List Int :=
  decoded (raw_ints% [1341623336388758567111135, 6364088249587132168281191, 13140465122564777192443301, 672169031373159057777873, 5434753536588886457050975, 11126672754802859567554293, 207469715090037382384345, 5019750186840814052725445, 10247034008339663127392075, 207466834893029886120625, 5019814106408811692282285, 10247031128142655631128355, 672178092868412126406249, 5434683856626873824966695, 11126676055904097643655229, 1341606743666428232681015, 6364170292145635945094783, 13140460892438938002742493, 2425985862462948732253231, 8117897343959730290328725, 16908053498568314967676739, 4522840962135206493829785, 11216142017071533409601245, 23856880323166470193759755, 8617032639605873264014225, 17163579268230143277988295, 36996753924907549951603765, 18669964150724154648549599, 28450207296283279937629695, 64283750715237577864167589, 41619835035980411082486615, 54503507569678452575087493]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows079_p01 : List Int :=
  decoded (raw_ints% [124573549901942143595203803, 122414818144891008183849441, 111689877368244102102602925, 288608203082813562861539859, 344013747088591563990596505, 299333143859460468942786375, 755036768316296135035985805, 2265135183463143135102925095, 799717371545427230083795935, 3364185698868030834129507405, 8920259202800080850864070815, 4829603510785746739148636565, 14549580085131254820096503315, 35040379810214311779729029495, 18640235777145588931811937565, 11570540522282976108768455365, 243350788242503134753747159935, 65251156109642876820309422425, 289961708575000422642244644795, 58058087515239196998056162575, 468061340707860680575682382305, 475254409302264360397935642155, 2331058375889277351779322085895, 50865018920835517175802902725, 1913862054102252188379442606315, 1489883835620714764439400779409, 4194055411070694022982961789485, 5734804265612244304598165471619, 14098870094575211939853925782455, 3030632690162265046054604461543, 6874181993342252870816359531427, 16065035972530579014248095300969]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true]

#time def chartRows079_p02 : List Int :=
  decoded (raw_ints% [24003684778079729856724889775425, 37038088060448043824918380614851, 63965125835088241089859165726095, 29099439254898892982441586140395, 10862001802109618250692689810275, 98383816676406134788217741760505, 103926566892096752322993441676765, 173210944313603994128769597296875, 236398299572652215414482959226639, 167668194097913376593993897380615, 35196461417357913502504379830741, 453119836494936128110419017850945, 368870032253207678505972476776513, 654321674650230430022397597246843, 746331318977650994403403628310839, 738571478891958879626844138321275, 361110192167515563729412986786949, 1727952380857461394968118167509185, 1123792605702094310300834779845165, 2113173507667596825642108809033075, 2074374311089228341976568326199175, 2717333282822963910309392196697095, 1766751577435829878633658650343085, 3620522114738383939888609, 1510097018120157592125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10] [false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows079 : List Int := chartRows079_p00 ++ chartRows079_p01 ++ chartRows079_p02

#time def chartRows080_p00 : List Int :=
  decoded (raw_ints% [387312893425857282822695, 3389468601703922895252615, 876408624521193167784583, 193662471135990903102195, 2847174607613907881378659, 1462329566761462242606721, 7262061106518714537497, 2614818717159959282843835, 2672900173534783865811271, 29048581714158554933879, 2614788652205309016178755, 2672900848110951259379053, 193660349113252365558465, 2847207370873227722314867, 731164590163130183701319, 387316778101098482346305, 3389430048658318478412615, 1752817743933435791355023, 183281713208984419114525, 4396474483277621651700087, 4626079118803907741514451, 690239718373746741046091, 6321937460002069184245015, 6739685408387338900064733, 2899245935371823679613993, 9918392230267595580068815, 2754852695126664015442727, 6279812271632709021142805, 17918921201489363902700987, 10099234493755594381263853, 1102243071849215843940295, 35037641316798431664640035]) [1, 0, 3, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 5, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows080_p01 : List Int :=
  decoded (raw_ints% [44114170408731351286715231, 24102306735676187502093855, 88462477799839177914879867, 109954673029671179793947661, 298444364090753749811018097, 227856095202207931681390875, 114150912647944326152288367, 1158035025765249588887899945, 1282239934162854177158952255, 956541520223890321654035755, 1024226043587553624683670205, 4859996198263206287232990655, 1025786108137184266538709365, 14651906980292686176315176125, 15105376763238003817779771025, 34426504243072771117903742435, 2877217019086769842540994425, 112355259644078283123288418345, 15213275296142843406998275065, 260963454240079465625721547165, 3596508686890924447615793325, 101493785037297430920134720665, 24186593815290031500201640981, 931498557316239579379597770315, 657443774836994579467604116343, 735488223697460204750160094905, 770374493402390083558836718067, 620039922035605578031102945619, 1821893984176404996503677697375, 4952407232263442058621682988925, 978227588401732746008775208201, 6233282027888786634106885413905]) [1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false]

#time def chartRows080_p02 : List Int :=
  decoded (raw_ints% [6517201443303229902455874071433, 249238845052725326784053441863, 2572461928033380721084519163913, 19980720879291704477805858666695, 17021607430127760172013068953283, 10777073236993931617369698005509, 34642189405230861634896432551175, 5757308668273419821611749597917, 44342001924667075153689921273655, 66235865016659748461151725377377, 15034709932595379641704391921689, 63741628591108299052768095000485, 142725818293437438979863252543445, 20369606531970147333869696979963, 4979814719396686076305779423655, 188730649347773447749920654624563, 182356486547861958826813642597519, 83002683601339062883648156625041, 494690465789338378787276513684395, 175705190365877787501302270904397, 500510343145044829549517386835119, 475290819462939055319264598375765, 122702629995461291953877857295201, 3892947391510629953961027, 1510097018120157592125]) [0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 6, 0, 1, 2, 0, 1, 1, 0, 3, 0, 9] [false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows080 : List Int := chartRows080_p00 ++ chartRows080_p01 ++ chartRows080_p02

#time def chartRows081_p00 : List Int :=
  decoded (raw_ints% [4633546666406968547364341, 18103113212338650472531069, 37741789182773486364952335, 2226809186139534028992963, 15005129304027867345056925, 30881433330226983788595031, 677746367050740123618241, 13649494840059582414545143, 27976877777036709635983827, 677740032210126791134261, 13649636569926387097820443, 27976871442196096303499847, 2226829111148533034554323, 15004974904479835996813665, 30881440585554756129188431, 4633510199846909159955221, 18103294792223453166929089, 37741779896550198323697975, 8838328889824213134265335, 24271995304173654316724107, 51213618986221320617918531, 18160924400341012040819965, 35779952571871879435459759, 78212872276386545793003831, 38300121816268499977462491, 60593844104855678398364037, 134673918492996057811286287, 102673800352699689917255725, 112380196204408879390384741, 275647840661964247706004503, 272419448178678285155900047, 265941444810255058232875487]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows081_p01 : List Int :=
  decoded (raw_ints% [650741089193342222779160275, 1580397441708521937865832741, 657219092561765449702184835, 2503557979080542445800893063, 6031192548397314585978862499, 3426736328227298933964540969, 10115147969186378969645588303, 18992307395965626685304125691, 12719604189356394621659909833, 2845966878381933129679674889, 140728907590842484371673218041, 34557878463703954436643710413, 162567181865190044186657018621, 6098455734590309625084743763, 268738210992328574121686526249, 309394545190622838183414980425, 1158298168682650801815155028907, 46754789932884573686813197939, 842805167757437654006655304719, 981849784492094375043543542301, 2047858126372973029508623531565, 2982953120932182830865353875927, 6050065058973203982134758506145, 1916944779051304176400273886663, 2085262153548926776225861087917, 8142006328725980731393171352427, 10052271991573434934760893480725, 16277333541248111489753790946489, 23811527599445913203586662236531, 14367067878400657286386068818191, 607812270528179017560300062385, 42339768084798735927894674918645]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false]

#time def chartRows081_p02 : List Int :=
  decoded (raw_ints% [37570783207318391472412430992337, 65543483413716470113921037092791, 76604323372666904399007764789097, 70312468291196814569403281019099, 31278928125848301642807947222339, 170260773300177990060474142314275, 115637863538015417325603098585857, 215586168546996592816673959881033, 210937405501229778183559303160955, 270209078309159165551545003609451, 174909536345944804693588799034353, 575060334757686640992267396858893, 306236947464444139041515507736053, 611088203912971614482237900985495, 511318720431329457550708531465041, 879911591206214116432989790108335, 674829818239328797923796766379347, 1705781423285429568188675547061627, 716400493398214776059901555194029, 1542270325477430227815587312147321, 1109935687965843136253846514699587, 2531651255364645019944361304014919, 2138116060797016659750416344509361, 10593833962295113728079169, 7550485090600787960625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 9] [true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows081 : List Int := chartRows081_p00 ++ chartRows081_p01 ++ chartRows081_p02

#time def chartRows082_p00 : List Int :=
  decoded (raw_ints% [5532937747349079086649675, 9822055874443323375097945, 41058512593018077449784471, 2655865955421624458525499, 7940731548391175806469453, 32869708890247373904609297, 774608581414822550517607, 3583094959510849458286223, 29439234353410926895566191, 774614543521560875614057, 3583061483488176627975923, 29439240315517665220662641, 2655847205104097907713349, 7940804462543259792186503, 32869702064143324003990047, 5532972055777795592219925, 9821970172080451163665195, 41058521325025217503923321, 11397819316480496004627993, 3368444129580263846101607, 57989312697283509100771239, 23570092621382782469285913, 5304947372140236792073297, 92957224635146787574685145, 60418596277104208707080101, 37043869139703837853692341, 176945913533633778751051159, 155361515833254958101485429, 81638385765665155875373289, 392726025643992945559616689, 841538095371762015403008105, 96202692486479397977588885]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows082_p01 : List Int :=
  decoded (raw_ints% [1389625636849009919064110223, 3151809528589397123602287129, 461588240568713585639190697, 5382973260810169058069405457, 8705949763787910619736153451, 3344214913562355919557464899, 171166974388344438064460865, 67348849818451825255291043547, 7782773282650483448457772057, 76225966556628080313091657863, 12545369642131626106307397943, 8000579363111183666966697331, 156120186017211531674690099353, 508784648968925469193232885545, 1270508932798881847172823125, 340119093309582311412235388249, 487875694577047107678737964501, 444780014064035999857499306897, 1336779436855554888284206238295, 2445883396023792835534669059483, 467547551652264998123972794501, 621228264591190839571724856687, 3580078186087097704856261326983, 1000551690979878417838584876293, 6647189846702081379962655243153, 8880731418349176465079350485001, 1556265317217416353366144266241, 1346536614440002619739566085135, 17098881157750301831585672291365, 6879628036389419629402180732415, 24633075961659475676925456691231, 26396397374314938510377640624523]) [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0] [true, false, true, false, false, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true]

#time def chartRows082_p02 : List Int :=
  decoded (raw_ints% [13986350523315469124853383758883, 15335559745094838998133488358073, 63960501553377453470124922802247, 4879192334481379720243864973027, 75021339182597552982369075068697, 67166543129675494166474156162169, 12493537757515496086317884760841, 71815297606299512286019841708775, 202399785422021157071974342767429, 47649773791749975285498696270061, 197751030945397138952428657220823, 150190647567405757731382886868075, 152425634391959172726702803724065, 249960168800012538293020113120177, 565360518996043472233834130285623, 51270436887827891222942095299007, 465590997763436691672196904033521, 299308541610649324874658210698041, 206467442302042149753565663280779, 731642975148830839031372823621103, 1431985881295484083791265751628789, 196767667834993542428774020100027, 999651447757302569634551138705727, 23295725170183578268217073, 7550485090600787960625]) [1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 9] [true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows082 : List Int := chartRows082_p00 ++ chartRows082_p01 ++ chartRows082_p02

#time def chartRows083_p00 : List Int :=
  decoded (raw_ints% [21079504996450081821460763, 64228103147805928604947343, 136258014773030979608639279, 9460709941221491002878123, 50950406628774969182231173, 105717799835359406784300393, 2821671549933098342177563, 45306683265362946599191097, 93435418344204817439244707, 2821654681443178535388013, 45307063528908772497876047, 93435401475714897632455157, 9460762984850201556838173, 50949992628249303669967123, 105717819142008277724681343, 21079407962122939457928413, 64228589498609175611552393, 136257990088981418739447929, 43652924748000490969368757, 93108808552495182585823949, 200990322799104849166745099, 107722214311664762863612141, 151534438994610157550289907, 352365461858770102999725997, 268393985180334783833817413, 308553237175824708313048231, 728481661350769649697155551, 1352930229596128320790676309, 688322409355279725217924733, 2349805876127232754321649273, 4960749693464113673912703637, 3014413696368081349894400849]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows083_p01 : List Int :=
  decoded (raw_ints% [8663485799187474749025029219, 11796627309017002595485567619, 10609821796283507073043332007, 1827608183634585827452165237, 96295574916295424847485893027, 20578840921665923841076734389, 106264594041677841615519295409, 31877000505464748526721255491, 181981328036307342621928454047, 234437169463438014989726443927, 662153665605859515771115438597, 84332841932595420894519245371, 395839495636956752254667739179, 712995436227314026604501460637, 1142326003175411688920302423147, 1770988597470130294630284638413, 2905648204466454035538566942107, 1341658030522032632314483675903, 421664170769009714303780843057, 4638303873713641880836098041323, 4668970405757496382156831461067, 7965616248949105630678445826487, 9652271794516282462876598310277, 7934949716905251129357712406743, 2951648328146465048637945557533, 20278204046070301039112453613773, 14635573183275068543596365159487, 26978827512440118453351106366517, 26273499710931765938322214398883, 32621458375235350948867194820803, 20983531847578653554141345581407, 70292432016483941589289183132323]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, true, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true]

#time def chartRows083_p02 : List Int :=
  decoded (raw_ints% [37911426238588463333048063638279, 75582399879837053973470051949799, 61155215704395906828131409707669, 107963405657732532229711171443843, 84719616191925088734627825374453, 207658920065759840752223055013773, 84399005170203350323214755777059, 184094519578230658845726639346989, 124536169693447705364245639100859, 307354434473787149274734938583703, 267217269950542794233704055259903, 544441127854489255943322257066091, 164673334216692060405276522424659, 401760027597394167073863840907047, 223676770876454263591663139034549, 781527821235191362611909575548479, 722524384575429159425522958938589, 1299937882773070679772010712345949, 282680207536216466778049755644439, 801090269074095783938150892441909, 351149665953104999973485088635619, 1818347944310949996932111849143419, 1749878485894061463736676516152239, 78668759884740530715050021, 22651455271802363881875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows083 : List Int := chartRows083_p00 ++ chartRows083_p01 ++ chartRows083_p02

#time def chartRows084_p00 : List Int :=
  decoded (raw_ints% [26557766042749367254950415, 4502745780146426069068421, 153382398858180998391124371, 11951154285692782859486763, 13695175083272203507769805, 114873478529738848276687193, 3319718514383510620778255, 24070811955478625693060605, 99602605729662554796422175, 3319734453399947929135505, 24070631652160896394761355, 99602621668678992104779425, 11951104170589118345505813, 13695273204439286811098055, 114873460292668058379420743, 26557857699518301144359665, 1125679244460937960633349, 153382422162775477869286221, 64402363956938486132025277, 53948404108396874766555775, 244342643819232265145671163, 156025691965829053448118085, 100424099779688500872292445, 464770699741999804725814525, 730329404633973952633602425, 52493524018556482053668465, 1351125796341802810807535035, 2614576303779597314578112525, 415376752206831226752947435, 4696031504755374078019249985, 5221842157481277292178987255, 2824550399853823242792786385]) [0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows084_p01 : List Int :=
  decoded (raw_ints% [2088765651053694100418375255, 45667403505479503018442591495, 4391088653067614838673092385, 48800480011907086210203203495, 21836800460132077386147278755, 21421426552812839887824902555, 116304683977518666614793073745, 282929065213039957225352420585, 6556972278299923056205092785, 144787580775389213224412068085, 340559248615071949879273332373, 240086212107414277449702615475, 768275894603501120329037821043, 1121747221910599435254877390355, 314331359501872257654452961233, 12912078692026365046566236939, 1962654140850736154376986514943, 27551906556349536181411711715, 3097313441453361954678430142237, 3373311921727154056948127753285, 824161390674431948361266776855, 1686655660576944052107288903895, 7819950308080708776189999912225, 2491650911923968899142952978405, 9506606569230918781030838761615, 8310613576170701240382692556703, 6171627526731844879467466358515, 9015943301140926316838146117137, 25007113263722491895454641226075, 2909481332123366170619869789149, 24301783538752266818999187665641, 17440859318129340709850597351393]) [0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0] [true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false]

#time def chartRows084_p02 : List Int :=
  decoded (raw_ints% [2354435717123830876998396858445, 31868037484345418004603231540323, 68683246744093952904907916425325, 11621896653882608368610857773095, 54256068577877875610155282236395, 31690471667120592806831116543595, 49847761007103305888920741557765, 91248843654851235708232082118125, 168391091788716134008444382487159, 5017143753309496109555064692625, 108832719800985491107043416912629, 49570326121140792085631856056445, 59271665390806414059761820464697, 227653485468560833029855943343343, 377748442634243864243076228156729, 29501751107902807647411597285945, 199665283286823823298852140869831, 63736298339098719024212592250935, 259205111852631036123552587227335, 513677427581968968517715776775625, 788683472938668495658415801060115, 17117273615597955688400497482495, 338742343695798246164912616535425, 89970082450465182823037393, 22651455271802363881875]) [4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 9] [false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows084 : List Int := chartRows084_p00 ++ chartRows084_p01 ++ chartRows084_p02

#time def chartRows085_p00 : List Int :=
  decoded (raw_ints% [1107100429612165832687165155, 2358436961757127572556983815, 5207868666656526234783510187, 433208243740894524201040515, 1742331275287232829539361217, 3667559993303465877895304517, 125150433686898538040196841, 1492020474275338524154902785, 3109201315875672815654067161, 125149996144563611319809191, 1492030407913435753458967535, 3109200878333337888933679511, 433209619299551009146794765, 1742320466564465746794521167, 3667560493777452509400283467, 1107097914355640483130283405, 2358449646512537771752557065, 5207868027432644001677361637, 2647419544006331497367042375, 3956516295275746713055087977, 8962385485794615982174687417, 11523550245523372128845426679, 7653288734525200766486641815, 23133355275324319608387156471, 40173643005946592244605972445, 27003616786322490970745941335, 74830548526794283981838555595, 65127055456634971737439084035, 88000574746418385255698586705, 49877136076105904489005444005, 624266166744835948525583321865, 103250494126947452504132226735]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true]

#time def chartRows085_p01 : List Int :=
  decoded (raw_ints% [639516086125365015774016961895, 392350563815669762181018943545, 1160531758743253511795468057025, 1656132816685870726480619227305, 3440293731687689035276376936205, 887951621758286976866170113825, 1391810351186148546614738765355, 4621474961803664533534811286861, 5720055704632124558757285815385, 9453579044677502115425926988421, 12162864102476589824118459266265, 8354998301849042090203452459897, 1912189904004576824842279009017, 23520377220448972230195746905065, 18605672500321055089479632717145, 33771051418920985229471927162313, 32647686044244492150604212326685, 38685756139048902370188041350233, 24643742595125465309063461740693, 84930791003874127247752668392189, 46689699588167929211728791936225, 92934734452993154089293418978181, 71590879980795672480200387051561, 131175825868699352125317295434145, 106274645476071608856845700318809, 249213873171805948657520417216025, 96492060373423415748671982166897, 214530107676530012280875103948777, 132388543778323406057174084126605, 367251920474912545189723538997905, 331355437070012554881221437038197, 633303899787659887483530498570125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false]

#time def chartRows085_p02 : List Int :=
  decoded (raw_ints% [168285027183223396365676186086313, 434337006495970738659483145658533, 206619452485685245139124001371129, 899355879100407229777337458142345, 861021453797945381003889642857529, 1445763896986964900454380708027593, 244953877788147093912571816655945, 791361895674704764589615066541193, 259257562730781402690769822383325, 1992171914873522571131423957912841, 1977868229930888262353225952185461, 3035680897959939238160237897789565, 273561247673415711468967828110705, 1317070230759832378497781767987429, 205408356884125053485184688773705, 4079189881046355905189051837666289, 4147342771835646563172834977003289, 5958561967793276683023280135938297, 137255466094834395501401549436705, 2016627552841755173335629847708713, 123965466715837176302246501335923, 7837934054540197460857508434210305, 8099154987350869032661156484982933, 3157484548134346033735337671, 656892202882268552574375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false]

#time def chartRows085 : List Int := chartRows085_p00 ++ chartRows085_p01 ++ chartRows085_p02

#time def chartRows086_p00 : List Int :=
  decoded (raw_ints% [770168873050577917775753555, 712446257624691591995469233, 3157843417102032768950189671, 308069847582281121680452259, 481391014401035833591748825, 2079604696469173729493983857, 77016967043711593496926151, 202188205021205235157508487, 1694517881843181014316605447, 77017174476024711431395001, 202187023678662120047411337, 1694518089275494132251074297, 308069195520007371408002909, 481393584518435181746411975, 2079604459271526215090472207, 770170065123441858132287405, 712443242877331611502825583, 3157843719914975444630762521, 3157681605502315553631740521, 312890912410469259969674845, 7085695390540732856394790447, 10705293823709164777679468705, 483765606047455895641820763, 20948670819752213187705999673, 13400836201008924525987041019, 11956857473351041817558168085, 18253128442452453439398427359, 146023074682559438190363202155, 9530711352629277360852474915, 141170782441115909276951815815, 114369324401988769430491931055, 67033108604604198186402517035]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows086_p01 : List Int :=
  decoded (raw_ints% [401563181525664116897806949025, 704007005970508794048832843905, 61950017877309023395672202985, 188074500042855907720533963825, 1057281268930569549842895359109, 569940788761300397676027809835, 1949362774943934251612262166839, 2180642342357175508989946220235, 933381233175951503051550953139, 826001701517328292465211305713, 4724725177159070807576405209071, 50334423549871097228559950325, 6079365817998918024101140123593, 5121206084190168171944927618745, 947835985995779826131213563983, 5682884910967820659732617713919, 15352604427300878690898258741821, 3510504530594293060631009208345, 14790925600523226203110568646647, 9735796887689573057082231609299, 11561260483317759386373404485889, 20407733140134531836926595779169, 41070767746012977469588978418359, 3112646178547639998225611200477, 30398831493568018689744614248489, 15199420763048643660728879412521, 14754753631347609041607786966235, 56270178476532352498604713254327, 96022515744666022289887436856845, 8974128405953363664277657011567, 54951758031182313452011603015039, 18557710527234854432167883128931]) [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0] [false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true]

#time def chartRows086_p02 : List Int :=
  decoded (raw_ints% [66513008481970804206671862924375, 132416563248613481309731156742953, 203114965034680611367356198258407, 2395895530320372691972556529341, 89256112313301984489792924644385, 13159594686580900799359031980849, 8537622284544362947542770958377, 279211482661401695057790090921943, 397479402774415611623990051031893, 3576012565299410031468805863485, 131427514799594817365558992090799, 13462623135096750747627420131365, 260877446221705804463305715697861, 542369540709107179737176463254057, 730719446253924641873737353025503, 8519317850198080389548112997425, 174887282409720711388933469640081, 82341575989734777946458177402447, 234921000016109418705215818663821, 987948304653380131209129000068031, 1276030923992584989359782790582517, 65302940289338617167361951407597, 205741043349470080204195613112039, 1964006145076305343362971613, 656892202882268552574375]) [1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 8] [true, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true]

#time def chartRows086 : List Int := chartRows086_p00 ++ chartRows086_p01 ++ chartRows086_p02

#time def chartRows087_p00 : List Int :=
  decoded (raw_ints% [53718802044552238191975789435, 53716354736241305400284204235, 142051797054449008376724812087, 13131173700493551583766794403, 34616640273655464784464818417, 75201821309403218600982228249, 3581246683952737265838456219, 27454007335254202232750615429, 58489400924956929751376977627, 3581240577269598341634069669, 27454146905749990252787905979, 58489394818273790827172591077, 13131192894837997742168164253, 34616488489793398916018754767, 75201828290381386910974824999, 53718766961233839624505007685, 53716532695425985737124234485, 142051788146453224277647996937, 177869122876461093236585642705, 142054022412261078165028770137, 373639677984148157138738647327, 158769713630759520494907392719, 409454778448348172210295519895, 392739087229849729880416897313, 2097426766263479523805277694755, 175485404849257962824786015301, 1863457392664389314419768190161, 1980439120659188381841976987947, 3785398754078610875400259869615, 5941323279587057220067022872863, 8648748602896680008381724747765, 4136363646167634726508739991195]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, true, true]

#time def chartRows087_p01 : List Int :=
  decoded (raw_ints% [726986202650434406472724886955, 14615131812883931947919354365557, 13512098451714749141363189625915, 23990866618431046362773804000277, 22887852627566888934716228258235, 25093899979600229169329968739919, 15718145803748089375976930107599, 56845387837403210453266059180531, 32263606803419028728069266890555, 64015094661222010012005357331167, 45578726760845958894726179507985, 88596875695206191737202149621143, 75281755737779261570545237003713, 164732111013500437072107538502065, 58893846718272889061383092125415, 135029082036567134396288481006337, 71526185916133883878390034584747, 240867346331794682407012927382987, 228235007133933687590005984923655, 398631577737035969803893705072019, 84158525113994878695396977044079, 241922756519236166092277754733111, 84686088984936235753787236109541, 556395809142277257200774482761051, 555868245271335900142384223695589, 851751954382787596986547906627493, 85213652855877592812177495175003, 380569798096387932597950919041445, 52053754975259856875467136635635, 1147108099623297936772321330493935, 1180267997503915672709031689033303, 1659933446833788685512034091008011]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true]

#time def chartRows087_p02 : List Int :=
  decoded (raw_ints% [18893857094642120938756778096267, 531719204305132869678469538610343, 83671789219359895693871461868111, 2172758794044279434251746851522087, 2275324440358281450884375091486465, 3012646838331993523045844992882833, 186237435533361912326499701832489, 653650608754352176467598439528257, 412639952832014810250043153588717, 3852534882619707611839943134243579, 4078937399918360509763486585999807, 5165230002461937208811786146040795, 639042470130667708173586605344945, 673652649711561888798256406452271, 1067647584174771282500549726540491, 6477925122304166805783629157838011, 6906530236348270380110592279033557, 8452273387551817780522115298509877, 1496252698218874856827512847736037, 478095567028776117910973292935829, 2235038274983995574109886845192693, 10426621652799468755260601439181743, 11165407229564589472542975436638399, 97885299549500623284350300761, 20363658289350325129805625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] [false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, false]

#time def chartRows087 : List Int := chartRows087_p00 ++ chartRows087_p01 ++ chartRows087_p02

#time def chartRows088_p00 : List Int :=
  decoded (raw_ints% [14803857849709820671489174583, 88340245338074107726552404527, 243056111942980213315575930385, 7162554564727481894951720013, 40589739558270909266980147957, 6267485414839693088357854527, 2387515975740786947887211471, 31039808820254252566938644423, 33427258213521793969072184719, 2387518879649277407826623921, 31039675655307761475431302073, 33427261117430284429011597169, 7162550001442711172189786163, 40589884338851362198245140107, 6267484999995623022652224177, 191001010373696901691774460983, 88340075666849450852949591377, 448860930385098527794163923951, 105049882793692600335721303159, 115795447356274131945009800545, 534812057965102829150217081775, 1919556110761255152899816611425, 8354903563421574741385855891, 1489793935589844924085320832809, 2139206653756259866258109706391, 1687965216048706889009797010335, 5548556700107359943243247150625, 3275662447672279109959991889755, 2155916460883103015740881418173, 568219229259530794790686538753, 6317348532424748352499208719455, 4863359679295851330910186769175]) [0, 1, 0, 3, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 5, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 1, 1] [false, true, false, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, true, true, false, false, true]

#time def chartRows088_p01 : List Int :=
  decoded (raw_ints% [9024791750837496667668514070457, 7119548892982851198973909159035, 10478780603966393689257536020737, 8222591390279393821193813630877, 21115123405784431577864942165187, 9375738106669851067037631548895, 20012080908487888955645037693345, 22690887745519271757003682198725, 31751466207602469466472348309637, 59563520883025369310016277518339, 107886744246532402958359039638259, 6657574819424710344983025324915, 71014111109026305405346444318645, 25947426598354952884824121472587, 38067639019464966745943345664311, 152953428757203755478881362484317, 233899413357485954934107748949029, 12632276959505532194858070822757, 106893411198637152340050507937299, 3289997468918606125499714483861, 157764135318556021442221057620407, 81908208670112170693039849737721, 56640066084577396820347979453903, 527712916168892307140787112687, 17330960483980614536577911826973, 2039537234550234351154170182241, 295356393358063153120562778010817, 39025050518829240029617115822679, 202045249536012651857232837174217, 33160308668972641925607510028543, 37786898522494754334147693154537, 135724638872314962298210556096621]) [1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 2, 1, 2, 3, 1, 3, 4, 1, 4, 2, 1, 2, 0] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, true, false, true, true, true, true, false]

#time def chartRows088_p02 : List Int :=
  decoded (raw_ints% [512824604785987454308368570686051, 1095053231106344587063732677411637, 1352715254665499114506312656386397, 51282165101671160186301523034039, 121937384686839565144369422878139, 328971813551215503803633676294731, 419945324939755830098972042850173, 1803624452903554183454315755559267, 2152574870247464706900478301625587, 226407483347873183431030630226653, 19978603792695019642528869771589, 327495070174927698680844256657287, 1312684220367953046702534215925241, 1413771807195007561952347842355875, 1643544019039829530466420503270841, 428582657001982213930657883087921, 97722858330105730166771595742321, 583746455464691150971783231473451, 1974403817711706014230306790616441, 2129567616174414951271432139001971, 2425045013875606738699752162529761, 738910253927400088012908579858981, 288269057763499363543463207945661, 114126127046635196322043377901, 20363658289350325129805625]) [1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 9] [true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false]

#time def chartRows088 : List Int := chartRows088_p00 ++ chartRows088_p01 ++ chartRows088_p02

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040, chartRows041, chartRows042, chartRows043, chartRows044, chartRows045, chartRows046, chartRows047, chartRows048, chartRows049, chartRows050, chartRows051, chartRows052, chartRows053, chartRows054, chartRows055, chartRows056, chartRows057, chartRows058, chartRows059, chartRows060, chartRows061, chartRows062, chartRows063, chartRows064, chartRows065, chartRows066, chartRows067, chartRows068, chartRows069, chartRows070, chartRows071, chartRows072, chartRows073, chartRows074, chartRows075, chartRows076, chartRows077, chartRows078, chartRows079, chartRows080, chartRows081, chartRows082, chartRows083, chartRows084, chartRows085, chartRows086, chartRows087, chartRows088]

#time def graph : KernelGraph 87 87 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 4.7526 s provisional ×3 model; 7921 exact original rank units.
#time theorem checked : chart.check 89 87 basis.matrix = true := by decide +kernel
end C008

namespace C009
#time def pivTape : List (Fin 87) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]

#time def freeTape : List (Fin 87) :=
  [⟨85, by decide⟩, ⟨86, by decide⟩]

#time def roleTape : List (Fin 85 ⊕ Fin 2) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩, .inl ⟨27, by decide⟩, .inl ⟨28, by decide⟩, .inl ⟨29, by decide⟩, .inl ⟨30, by decide⟩, .inl ⟨31, by decide⟩, .inl ⟨32, by decide⟩, .inl ⟨33, by decide⟩, .inl ⟨34, by decide⟩, .inl ⟨35, by decide⟩, .inl ⟨36, by decide⟩, .inl ⟨37, by decide⟩, .inl ⟨38, by decide⟩, .inl ⟨39, by decide⟩, .inl ⟨40, by decide⟩, .inl ⟨41, by decide⟩, .inl ⟨42, by decide⟩, .inl ⟨43, by decide⟩, .inl ⟨44, by decide⟩, .inl ⟨45, by decide⟩, .inl ⟨46, by decide⟩, .inl ⟨47, by decide⟩, .inl ⟨48, by decide⟩, .inl ⟨49, by decide⟩, .inl ⟨50, by decide⟩, .inl ⟨51, by decide⟩, .inl ⟨52, by decide⟩, .inl ⟨53, by decide⟩, .inl ⟨54, by decide⟩, .inl ⟨55, by decide⟩, .inl ⟨56, by decide⟩, .inl ⟨57, by decide⟩, .inl ⟨58, by decide⟩, .inl ⟨59, by decide⟩, .inl ⟨60, by decide⟩, .inl ⟨61, by decide⟩, .inl ⟨62, by decide⟩, .inl ⟨63, by decide⟩, .inl ⟨64, by decide⟩, .inl ⟨65, by decide⟩, .inl ⟨66, by decide⟩, .inl ⟨67, by decide⟩, .inl ⟨68, by decide⟩, .inl ⟨69, by decide⟩, .inl ⟨70, by decide⟩, .inl ⟨71, by decide⟩, .inl ⟨72, by decide⟩, .inl ⟨73, by decide⟩, .inl ⟨74, by decide⟩, .inl ⟨75, by decide⟩, .inl ⟨76, by decide⟩, .inl ⟨77, by decide⟩, .inl ⟨78, by decide⟩, .inl ⟨79, by decide⟩, .inl ⟨80, by decide⟩, .inl ⟨81, by decide⟩, .inl ⟨82, by decide⟩, .inl ⟨83, by decide⟩, .inl ⟨84, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

#time def roles : GraphRoles 87 85 2 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [461317271737533839309493527188181152199811908835670810870131270855364143350295737571048844245041067061181402116030581122061004110781768219031211086408464864280873563633134265190343348943122676234663951426494295165374384311395703008135018134155632468017291234499794803722539917086262962036281719491983766043539151644234537902664061377022885750943919127199492563782206230511923409064180123676338161573779476899182219126914353634579399429666339604357287182995522579181532857616903898241011076928467160585278477383592120336084209080895588715973745989150421929545702477119080351698761685846404923884788516874847902429223873587860651973]) [5] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [404158503766705314364775413423833199673809122662732098570926091178534221881708638322411277591434230038476121928658499942841184580924158395244435417523344852500062126997854178709313319517968677202777767231250066945884150770271199648645912424294271657028637410970362370617499002329045484471701479873799905966144381231576466628296644401936516904654315279919708014507096109086505485210479828816939201692475870617282135335667453794728359803744695518975037741620030343709404312918160267017189956380294670195155291378769499470582070483149872396420680331165134514938372789747273236146941824513213773672178033262942510246642080873463386010108377297357193, 483488034314003238318940421739911701346119239725944239161440114959420492556934469128640840810967798314629743476416657172738015475276897136965536869767294352648695428650732949513163901722882592565073836450876065587782989553826894293946681955942182262055874678777789039081590300412709360244823221196515483893925624689156876762764866094001512459427470058226729558006112658844988919474667172743343074293875378015749561522851772896910613908348626097146001451380282736263020086505814004026177540736912150873926470130173381683027728085042607668263274572983195657857526558160443976531987540993030327498839153825309588223496955981256237827043712575]) [11, 0] [true, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [85016609950384041528056715734262359529062565721954955289781503287765796183010699394707991108468626719425349319341088261560294233448157886467598355562060045660421412120973499952896630898095286486025024906516719587134326859872142739689430318120229394627989239974361661743018568695247542526665030934035332925618752840873020335838200610194880013142008470126158080745724735759872339859721931958410759335101563118265882140819021852109675827470570273631787782021252228134435504872348005145384743482110674267137715187447205838731248709641753715012643730246102580289551768948451287192345924771388766024887590538016681473744385209593384204901394565542751877, 1598160196350723261005919549341946536289771151678475856961932769680554346202770389519917488639459548291205002233905132130966744340317052901851418768496279697979454087680589363580504440900569661488323575309507909653757618272398687412001697316486618337700508167591750116074320501479900314864346739720935800629803825055520196465545242751471266742613731114130993814844617587131515031324358864622144084947978992517952938161740092983208485832568883217364274247793822916422836777933720816786077838606965141024031664314731553194829060952436200011729155753793901449014569857967783501473776462582281068045132902580746651570135032965018659132458245875]) [5, 0] [false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [59483894543860421080099334167449506448375524839766356346627953297180897478447253058004667243828197632673018355090308137366270864598483417330903533495131620556249603847002472201239352804163003639979145648539091737984382257903054869027413315606835688005868614513774375332533202442947507106952630494007660415254147521039871590626173171127733181940165814526800953673959179449058335055279920839375220539309466893042729679121928585542062327663616206274497188387413511010332386664632093927599769785984987722375780435471378681064088395266987549586354648847533015814650306234770183344448625163415148612135657032848283949322871252578934712593684319234377015, 560936478943300336568097322458091312865794566231246784731634498432504877402675262672273932613447729122125424290576276223856726291026355624720717039335708673452406969162879995469552313460018189079476132435799270586707173535084746634684920763871716437410187791667906609299094776905337473777453544504329039204895103112751891312059167478208850457904398829179786942203231993025672831154659244517544083940574657368590193845257161877421617539862673996227860349086377736698408527040909629790456271314551187587448830225811087128221843602884515446630678228035509112079065075532422582216288382594093241870259598560623972055918524006249941752209745875]) [5, 1] [true, true]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [59483945594303280021200586354077201614525881746116164748645585860442048816892687370064809665094888574006639706171518851904310757281114092960047391980601485845466000022908584697188555832523197719394772056598543977395790109599980301165997526576575736895424545011480245279462898541668978041537283659178098087780916694209914885546042069932002025046963795602381471986259834307021658889079453324890514450426056506831560860136187943955309651403165534087535074422367067833823223677248448812212875074009584727824546780809884435279684349435816060890111103624285498828675573783886111471152545212170271534617810598573906299344006785918428518192665066512338845, 560936105538267488015407478288268176192341760510039886591518171593874082538913182270053389097914594937487804557411866654063270897253394621142227752813998266515706681009788295107826036208327469720194730425657552907391264614545008661745047519590107268102591848322225407234571131448237190812902947007536168254342855366647371227991012840403346345682484770789148008590961841337675141978189256572405070950038578474368518905779022173882220067138897343161875684447378957888093513802492806807787857051173605981194678298454933750797498652541477783781422661209615725171300177018892198327124253260886480776777107928255450992584313868519068396080944675]) [5, 1] [true, true]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [85016493513042794363655305710876244080176726018752448207299770597947323658476166374095848510046150956437067446491075374442125429524860554194619495971441165177730881753089256056413819544200641808972097959711946751994474404980669264704322920654725857141635469453598795527519932101519690441552583062615945413056063915240595711955103806643081430786927393551896793347690872223813755740727487702416220026798476556144763545328840581708851630183299050810035241013828839319569587614290945390686805456042201979307751496748449072255337275063914932338005341698234228229280899145956008612439533109402533653185313386394427679408239404166499686168731211035257783, 799080760455920970996356881592863743270245388221432086293338050446399289336273166164537039937715222444900442433254697234612131416833683250507471748492858258486733370297752355925732032867486900789698073085605322166773858874003450959197240250600697082510383248541618103086186542214062626316151782964468669377341422231658620515171984125694238348439168049582205302990033276636958775936117310067618665211951552872878483117159183757470477625059295257320802880055256651309938277838876833057465689989726279463851024114449115727568437317747498799975922782570639634610666413574833707386461953798198957153379226947234019495590445654840590791908510225]) [5, 1] [false, false]

#time def tailRows014 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows015 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows016 : List Int :=
  decoded (raw_ints% [12933119688267300919943323134609051749911305949749522243591377173883151907004710578766693494816384812806005840416999177142563061247234658032338408521194263092047443471998407450100830227642415434726155415844720031531564327627626562499636085482335091686537383452616157680997863178784688118962612662792250452469247949446462313776110752649069561395185637032853033509368216014455052970924429054695386929811684864325759044703950464528192051472753973365145215199809938013619281472618159433419355172331735694367211599649496419615211787854935941936381356561703637664890228207207528112448486647884040595748368239806421657987543727179504990559256024907114105, 241743620223022762189403615517731801856497354872209571529813459061011602803651712323105974099425122698687184232125695056310252403340328075134268429346023253332183043027872707985414781598696312568067647678689443234484090994313804548922525870004333297735262960805125335709587025923602223977194321477646494810787494045111417596345519446506131495703287330583082914584271036137183701344138182933931936194433650419597170950079707297204602745604126684167442239135632635767862776355967335524820107846711695394929705720230270454652850250196444355813543534672823438022809459733564990141504037089056974735460802202033456741518666011527616038600107725]) [6, 1] [true, true]

#time def tailRows017 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows018 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows019 : List Int :=
  decoded (raw_ints% [20108946928545673998980908503766475595652884487505133032146654686834401261039537473120251194673177014347919200415160676923091532870840380925981060941108339114472073432731112690114112477808454151592970955917805913741253342632968261521161382028560243535943979159205320912366508560640541517320091844046966468048022313439234009600855953257719359925577640121015692526249156818364397481816481798102036728163558684512586306393250221124390364386435425278115970122188277092570596212439213474602403097043553800250036505374997154174238846485987665048877110927509790141839038449214239874230283011645682970668702244951972365056584154455732805644919222989, 36857021511889873004463991275420966760034485523309544679047020924826355008614629367307844668972998573706701004967568379646470271492317566388152819810587586673609436102262067773193458405432468099025989135601399794250534922183248079784116843449612222041445101557857251268816113900620253420246686224612110299069393193159207381300767001227032253324153890964605611817744817089285703136312724629329736311407130391319475543909222198574207953953676459537722069754725413980058323586110558101234109107523661813305455262642700621074187197003396128360125937149994760806783402327435576219707660723883967034902319524428760485714849154963893167925]) [6, 3] [true, false]

#time def tailRows020 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows021 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows022 : List Int :=
  decoded (raw_ints% [7618365296101749885947296753531709453010524483622942201703230421231809666831539992236587252223821541824448549836170568668086140092692348307039719712766053801271146769522370678146502972974919383648303660753689641155747381643818365136360517213699873891575558013835172703220304922178517057404642704474215791778821376094064281185894783766795906336786491146301255630972940776284785119200973144288357636517370964890846910059117854803954666309255666325352413226767114863370029011544579067931335687802516885344597981738522643241338726737710460524198353978757855146854702142526591432293747374320077293154592415139891744871787137375415192755015539611, 887985379904590460192969625048408387650746485297939560691769270523736059081498000667268798552650604419994619614220763776322756744871110422707109137946989899921172221990581576272830877408301831386490508492592403518166999031866541706024881458615159936633133878579353709781574935832770974401331830112536020681261819138598731602960899222876915318783909135777985912392137830374722257223883213977503582989610963582945720407846110148536539712202484440006494238872881417640552791662331306380452203916521767610357285298267534544556291003627007604880648839862816503675593491122363961041169467558526445744968566362960010950162311738103470475]) [6, 7] [true, false]

#time def tailRows023 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows024 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows025 : List Int :=
  decoded (raw_ints% [3612399778693857315175388943233187370233969705943036893755971974793985112320198663653223371454699258683795098095498001793330087734274791386517578427422068981282272835767094638490865930236524162716844251544323652393965847526976810447923228663460722470252737556320368271729756032180730302835778019869228689989995363851131865120152288296731392278732175607284540049367353791727108222979543286728534020999853267631531692534011744216032259689848561095520127040264242471358891163259393721021243412978095736385805533149033240962952399897415408205020615330209105736472055792015180320158022971166340080186370461903526643242632745784253366563034279151, 48979158202951032631189918852308455506496240424304081573716390982772331079419135253590750380389471861952158659531163558425605516278431035000495512277851843459452303674610428999591054288789058802296378145997937808652614429639886421193664009520752635319498687853287848754210312384702939002293790222653741508656125502455008035952932192238009372760934789220904997812347842451867700057376517537038145433683894933489937200809195710853362844611537360356411755712408236653347933172110509345922137490235595502117289759248464241484856700197376782230113891748316145221445970525242081422786173504490042661442493667118009780069209507401040962975]) [6, 0] [true, false]

#time def tailRows026 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows027 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows028 : List Int :=
  decoded (raw_ints% [3214633370734165582634637966205536505622759907734343207916197924168297656213844047147878107267352186551721585862395671171726252264526206475891312229671995799400707312133772547818875265958391164075767280187739982313693146953988097040875101224533315574482281560644828903450794485261610340455344428002962913525205338352560956016575917370330650100068593847221516365246222055694852169542295805587127183511426118326624377690644504428933707238582636946912979353200963608351397470244387818146646738719506182881501237040813517785319550880061689600068566202476221598189092728448259109679386347511769964665100662042806456075192296717446567262240022081, 21006836640519499248559170081071981354575096368954459449257297601109843682305369124043964682319391075429997581338729717546872783470894900991980672358586876313096654710044172629389791887890918966317298554826973480008074278238022475215859554845493199594030594857181876788063764891020431122141996456780408130377992640748294807501270469253606430883439500657121600415228314647498903570523960200077486855096325288166003487778007030709545310358298666813827838789563758593297368456773632692343848596159089743869248599523952770043904796707622158272528290987462375855708431184381584765948051771418700799258497463631323629696626123353218314925]) [5, 0] [true, false]

#time def tailRows029 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows030 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows031 : List Int :=
  decoded (raw_ints% [1510651609002703699585592676935772533626114391741637977103606819809481655842364520293489548974121342334021995582467365576205257714244962918139534393018794367081955801954298418018206789845102722032923254380078601669267644866801777901117236019067775260896066269821229256050600858797374816450452984730323115360688078790885755871481396721186036303074982947302850353493347354053899276862262323600788819460725926683663978572017435419712566519655923446277844255568822610820965200167904499404683886855110499063831747217695263580540067523754684398978312076201737988935899978635357918191109495992707703148502549316006024955229995486803859132773363957, 4493848409762764516789327736788103294264699580127329439148227090880133699607047986383847494456430448726349458662327018302461440341318110647881053404202388053649776235149624100935710789020373467160256115495329303391362163559283059580292482536314235034674338650284010263425290657589303117856022076492382016571437859580209238236218218163977996343172226680760780712756613677442862460068921933333321744106606933448274493604795181535806841396456834261377006484521771350177587377118126090596744292354904206520317902101550478240303129044224654295454918974571731694087134371551467776154330270089583232073112920438978428767271042809308283325]) [5, 1] [true, false]

#time def tailRows032 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows033 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows034 : List Int :=
  decoded (raw_ints% [665407747554602747970396916392226793614175968821636452187612641889179493820717217782329958349647910918625953314607889018144955819910364764251196999930171508067266286264161047606770866267139584213528773124302889403779747006897902098060919447013458789314771043731459557775383999348770361834966703528124574373538578949237225840484816744776006146330327258851114619411442521234888122560976191490991962064487126430304311356141777491115710291076667360038494681951409888680414890216683797313729827078810639007597314567987050962335432686467655277259303910285432809548201107399132571638414536170672001496966838919107711208698288411516677908795935887, 1887095234490378635908974986851801996466024725938142293861907137810480945601418416069071662014488409136239611480384623582249892943189597764753875247340630636115479960950209650747544408764809696405216161041626211609097459238089188153462024834153689346955710038219262608516296192672138371248720699493042876103957734913683351257086229934096250394116869935157659380906712506992424383499513175412071644395840988783757770242095517764923666562058795273683434691459837820752921366367094659505728516812132723542638756097455560879486239353139175393515416518534933240115764122718414180341698800908424840050844975160863057729148105039025946825]) [5, 1] [true, false]

#time def tailRows035 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows036 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows037 : List Int :=
  decoded (raw_ints% [300584296183682205920087843352371000932550544489575712995280407868671737549648761617357340991092769307851074480306168891056583254930148467021516252619913423233691598595348587131595067736755224817292243921576555868089250098144389744996580702060155951007056603087133737934081232527644310652156850983074346356740971940249737107919637882385774244812649701327621686282969506869510806435470358891194290810440422478597068423806059509452393870236725899641928847695602488930022305299169358456127259195741372643965719581392574864499440907784376264968451734219397281761804015138081046519924748797614810899902527463258530455670811844023949290677950579, 386269113861070807014445365412836890765487149386036994901627310237224723508913794041659047843542394533466849728958531767150438697409896786623513816565374012642716472040621913826281876308833353452306692466795487705408052856054564715492708655037182564097938975494014069577309110801773186518933103963232078380167545771516178101835782692664816713769088286159847136340599798794091021209858778146804255693591368563613010844260399086842469115886795159518714899321777930401811744036451943909171499707308801579349153899226799179536749848631060301740734451323233733273130500365195310401380272246790523546704009908701739969227248946415060775]) [5, 2] [true, false]

#time def tailRows038 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows039 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows040 : List Int :=
  decoded (raw_ints% [31573726399771863169989151990902691630258687318001827740519015779285171992852873728621239674273039594086111917919264340554937081723761664246410031182161823011140337931511510732120069569794599245663179213765679633640738735059449715754979277304344221076629994635648968058038699761394540413211608540464354317371879564543233887063513311897838141553580615401661398044105789700080591114607011434821751284399008354509534665152648812166736289791040642162800128631285584066496505130768670711658942892332229529449407219745080604820436157258309692207431827988138217682296490702822604547856441574464294021080236765392134727182655956515286589820430651, 154136151745611231451980267072993371378193217062099565446824476167629157874014710195984651664873447730962368541747181588025429807333852818425935031257557590631687729600577437746859345238472223274110076368492473245019370666780212492084379875889557275152593659928509861364920197280313076472509763615477706943025187115775729006335550770775720817319221590972330043674825681722138124794359439130553537812948234457700770017015604756855137082744470544627900400750508124827752305528345124267067284601628043439993096962446927290388583356123894722490860900164326417214624806173628647531361572348786009821581215050531972341781714684005777525]) [7, 2] [true, false]

#time def tailRows041 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows042 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows043 : List Int :=
  decoded (raw_ints% [13496331032858117421978545552191340681467109253039158707724601484583799520748017943222723176886616015280094110834897263219509939183523188219277551941767424545380231836204534723161090740014086550953067584769743250345437132520005177197938175882225142007437897701168089650477237417291936773852488249207213570706135223439943948305140073617537800012481357295310213774641124043784994649749414751504008974783360345981385754625877156165418096000723755572501482450943730355781236986539857685033882401302483648934549691856573553245960529792901227586201728901227604666491525450156830117111131209673738222108393799354291812962492074142966494638085559, 924448967791092081936941338242297730949509911513880527318089271858740898922691620293702843384270283357322586305344469739412524464535960455073219259307511370145358243191325166266986124551355175141157269990798500166052319250893908428926707592064805314868572067483112171178420992404580540669951108278837749401368161357521504382303922909977720229987673133628029656584597628446444032429067236378607301620141926541546955860485286094300960125249882271226358091621332873341114817343969546350847046788837840138377414129879838281711542358047907911681784810319723008317446625181462241108532652719513225259236731421805864693307526329529275]) [7, 8] [true, false]

#time def tailRows044 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows045 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows046 : List Int :=
  decoded (raw_ints% [5297001357814334953326866498864738551131776706334848736668398778717411621721461047031232254409890040713769942950641579647151112965981404673889988101290589442471509440602869451145332359871360043556173681608089041455423302157589126835644066096183353427139766053602536401037559337519641094839987415692458198682498161421074133137663923536329153907486024759541478469586363434740650148774815488100732409627158848102057940670116868035214623911138181361573647263457569068881624732423219597708779995969521141057136194158904503575065559321731752573411808097321485139201707029305740139629877506360300577371290449782226741713445897408745599223041305, 5509900406749311219495358372635750489559855088001268547764013421744648337034380166942591560317423169314625397726724446855212900223764790551587842282466264794940055549199143666233074560166143937590558649516873101475932549873720111457089262150388712372474231986433076458753342964048098386008566332574177037590340937192284434713115669188926229632083216531251097014343115630216297497346312636944728510082854135376888790740791669031447897814077192856953226103918282996781264054556904184912211242504628990783288961216910464795349256683892417247450877540977313846903970389048094391951589974096664312666935316982262353328963578906419275]) [7, 4] [true, false]

#time def tailRows047 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows048 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows049 : List Int :=
  decoded (raw_ints% [2116888351712465427333605287083459493034264694128580383320026678887635554008098535472197240990584041233438730373204368515820828666961215321731318445613989392688383453648107663165384893283794376460608799531428307331513248559132580997834383842938979569453544098436094489784601785347070733238079666888160875304231081518420802120614556473082853828570031840598980853863780406890711204646183718336646017306956016586592270680442056462275309230743948370668187926233464034932453453677803576416383699242900489942187063441366684645390556312196060978116388765071587955709575363328974123808689309174431938396363243539558202815209091802759134536836101, 31173422475849186132042960586280809757939400461286707886079464696228485958869859728762726419168814532835620924131954921832069801177881737103445962708677011349894029186627584532603185961973775588821250035491182849225679170814758172067491319061891075539576119290928716288307913495398918029820242529715561639122107981495278189174808272795860132136608625773831781309521755490239388719991457846249068302489687745243587819101164901469917784491498833329616557516719354741218606535787466876024040684652083655176717391414810689744837949596825070315931799325410279752505115446031026709999235289564029905552423009163248338726561316507021775]) [7, 0] [true, false]

#time def tailRows050 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows051 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows052 : List Int :=
  decoded (raw_ints% [3045921403503635456616560175210311346922611023241842889842425177718196342603333971573376034290493459967145767607168876140601925302144819759381926752463019416392023349639642243566270955776745062094152895128081701139816166404979763277885890507684266111824176839713278529499451357583422481971754260339143441306720674753195273179746492914589545959585154550188301991262361756233020922759298228655461123076237427519732655442767213533395454417192138565706178381985452809416775261775385919182618386323970655165705789528211593007903911958972486701024176567416972918534164180988797758403174419688355331839067271708929681421603506502401328246440717, 10668391831778728963556641873107930840657154636922198992361942022158590395980871497551003317082079335636851764292706730041226583408803857983328218464154592205770936346872886614762962147644120086155487341815739736150929717235090624619913261306433208933862262918551719845674590287087957061146857993599282612576494630512351138949467783354482046766533726396582604379889966948112659651502816854216611122866684725266316576988212699746982526109723857729177851224605995531105283125823730886461726710233122889549171706023986406752598201167582904735110533323381664348561276670478164822541554454053739617396460857126923488962730879553169725]) [5, 0] [true, false]

#time def tailRows053 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows054 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows055 : List Int :=
  decoded (raw_ints% [1124857274162654398510166832894096408270227393566467487712375558396218093003517639520379268740695481449957224757747032770130367221748858453823839923495257424571468967686598437282484550571535549873771339528126432619622607068815985091193119277378171522202494782439611373994315379328906331169290277694064583784381483421147560356664790634774893657831264670501778820558252246208534601378645326175538635654512104405448945845213805071914557734677283263769364075165511947413903939827492235198059697641500923745933988168740078886426640638326283182625861765352460924539055278413892082326237738122434734232504320453709824314220783934730343968479857, 1702624633212971133528883839477774160504755040484536632736466759955961392016132899704608511757338101506012049677241106022233060136787096618736455478088120342720453665193995352825286264620069066585508612713320322016459110538288909347376187103801450471140524759874376833287029614549950016310370681333647858134217305300212296530963559226140926617767588744036950902331897101184000023904263814229478037881463902216171117421183021027556854776106173167808736691556617652784328953277811825731322656315103687404811560680204756702900266998772454642787393141306106842907559180154855871689748302071315520024741578531028888284956460553659175]) [5, 1] [true, false]

#time def tailRows056 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows057 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows058 : List Int :=
  decoded (raw_ints% [362583302764440923183905222384591412371871356641672429146310793818442875816658964186587485374594356719861944733253715143320948133970621914237590434638555055938791016075170005895583291916634312314709102170437978479422836544794767777611665463459332592371119759986735111760797794956598251144168376467869617979533668341154812997014110296426868244871016481913083263824954614328026588249421417740187701294559437444311499328014862800643498756448372171679678570677066366908358210113821280459803638183401745293333391182710102808988738046040895144361396729621206660460143192539648624231643831437190592598932357054037814375190200753012013532657195, 525755160694122192745148114982638686495407663016488574236282755916738902680050409823752774194537967134971602425959737565357154124034449998840648566307570542606009090738875229323592206103306034867917992885751733287989283866522086232401015258013589844086137148237018612753345151373872141520404553242562484279706208022060411287855382327433440289820174666592698477923146472626494724507731417839924947316077634719024629484946739416652643990730627908880348942212075129037248233782065334932151535642638046187392232545938347915629824124953182657903032939308184531268342903017456366300929769542067604767851836033102872425025732500826575]) [5, 1] [true, false]

#time def tailRows059 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows060 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows061 : List Int :=
  decoded (raw_ints% [122143068038553851096097767475597769256663596822123732328232038175486044493859188728200978701055815783789580681693700058450363867239241186040019663009535778510718153589200921937867231435755618638836920199574264308659903324752491728746077238011508840715622987087750161169432850072619625379623577444003157471989017744087433234377433181567791025931286233640847947362311056955539101122544869761428884218313757077360452210741554594212913550803347281000684752465966664855380675106818685470720716499553597178023398177070641930144147656947567808531939843314977193694710651329979241232546557726179224471904965912715547449143435859209878002243551, 147286642846147298568441813751453228205504464554003964483217992481342382022434132810064418280729174841412205149924351731274022034808675375332531448385444770405054520241187694813921895915647635884963620800117873964466785937846533059801109467094335922040195877365902537860075113367479985222695695044789591711162682361364115202087896488078193535922183449271489799786920246487278592279414158212489940924272431606774206820999239860352958251792927083042026093539483082607440173319954804613759099096801483875656438681554297491727886951247244720923970584129191178856361020615620947190271162622906923647239726169464747295510889732928625]) [5, 1] [true, false]

#time def tailRows062 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows063 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows064 : List Int :=
  decoded (raw_ints% [17088737610515377637639233234647679883075956393237150228103065615238754848314731511592603782045788892809649904473437822058175811602533554060653558407029206514249305255573383263204808613339778505537917509142762583996108025039547711540571633219985101122731316495775288473767549224760133347410735330278463707709903173123382701280972775034391082456960056423793446032419850317196789030264597475411456672680668649287144986272225731763021443074911191427377799151368506564955586073563466351794460696378072726052087999903762319429002591685303160297593890663329981121555796296265882800782220297586147463733820635918823610123838157389629664481857, 40100754876420950338410687491531360975403242887940717900768802450888250693592162171585739818215316643891565507624550205653439089830230575857603411985327769671735203104369672224888604686444585465704976498034596648953030090607154384075890743734667803716818145043881262315483092876058761083138434684304021175263341191557388934500852885632642768258963763564388894656053679942799098462372975495358449607359265451021803814269398054561589693665891195082985599291669113585181532820670558769124741805357779254589578558422688905215391441251229798348074508860451135703953263551515447856738256833295690302650391294868110545204521025208275]) [6, 1] [true, false]

#time def tailRows065 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows066 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows067 : List Int :=
  decoded (raw_ints% [5169364212522419788524539455443723602558685046078108424181958136849435802912615615776744423857587046313545576671508938109643820551752173431005681150406136657959654557798192123453241979918656021294645131532530827618283739960692873123346599349309382606431502215733110010989622221545846224905175728168109005577809199714757430988260420499301815742515050954831840591930643987789937613412990586430370191306180381000303660564391392639256895434507790451627179372755430098937476633057390124089467946887444086176998205017277405409156184860582211394353589769043587098558295136715262651936198555871891661338516897319643022426809419672794822699445, 2355738519658989516549069674533298248914949895513077245941078240836138355277851420516925131080722150516214402001516337027524947240317569398487790189463386193340746782232059439489029483649274791139701947334142121463971821876206832158595101097712060873932834528705740823344300664133028182765859959129329019016469271590104709439203342608096290449380228655305783986819341884262924435026260364779201315523767211449753526393980631307168132863306292437149371428292336093195487397588590924328665796980060508534660302197353587539802635224116620909762501968659843934720603694587092150674293882564120786781192146289695248896223032801475]) [6, 3] [true, false]

#time def tailRows068 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows069 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows070 : List Int :=
  decoded (raw_ints% [1192592870495421789851267151983126862298457267800290360545618596329682147875355606478342529593501193244139430462217761960844201556562471109797993105707274135622990987219941269088060913618691592228573912251095804558236059333941072809432704208900609116606098631173503480825883383968278809281612591167179925733891720847816228956007904052805365916506470235077450547306244525360347950570251680564998905714756636330836669101881526462780787531623456830712975326782909324568487482835022445397743234006778688586461337721562612096551735873031173319359217942080382458709962621421839653682499833150190373609211485454669272343754492750069875973955, 273688127357662595283075531671498158040220699474966602774705581158554953937528216777065900483405516155025264690542796820465230834405904801961328398968585801547600682547312181703933400702268222596414574931113604455619957064448826805164873168914548898697088754362748225924944571526956792455402248422564712413076222115947932299937573681242079760715273953905154961803388118684135363578709485263687877071356384211677402601558805106833201262808572479884463472016497658290472718314631017031403819298491212380630687154046081239523502282907921390768567367667230583014258539351141934988018587103250834465711610646764093204010433358825]) [6, 4] [true, false]

#time def tailRows071 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows072 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows073 : List Int :=
  decoded (raw_ints% [317453440219426809443984130674444902731429871468451284010823987621819723116895455885347226432446260977132341885626321527695419204167878174522956831093956634026444430781902626136544384968602754861275646125965667345127196565501252897277939450140968225109148215732521243019647409345167794638840252705826042080507669997463084307134303041188158377099424662863755286360144587906414632481700044029289316370019980151095109175538185543637232488141748579217224417754050377819828575698421570632865711730688014982931864330698947954783410505664461158012867581677533611022345495732737237343047236941387688675782638187940745171270794247707136976823, 790151058325941935815924421757724724491009201800803933447628859871970769785470041595237494385110768011271933206869825157247953685853389326293099898806077174586435738062093740710321655395756722475798208600856347094554384849133162303630713211787801183836360592612037550479007095798986557838604832305742885627588376228509921145926048922278075057130601537295176124132101734624066478647704435110164399645528216395784284653295273544767298957032009783590015169572456788189051523739100388154600994075739048250944061786960999659874020433666188488001813312239219602080271565206444779016954437299327509146207295111491382903049538872625]) [6, 0] [true, false]

#time def tailRows074 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows075 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows076 : List Int :=
  decoded (raw_ints% [109333823068055802757453697884181264371925810032379973995544175757505752723562331520658971734934673490911053459718581057549962073206455471170616641574927857413405502707691983314670731204180886831276277409371911826385741905041156058761272726888457454121644375011803891414529569853811318027739463408956279420938292598228831405447067984770270117888478861479857773603160231996823689682039080757635594084328781880112097084663529936228052543506321244976173958636022163740921558090909573318746136682359846659110401518494870083636771782152426299694548566218240543940259369899175724374157771916768101675008141695434946520660440668855060469463, 148929156031450377655528202775552885963189519948565081691177594114770309270530566164150633279166917873102378218699307164985531181620736124481671738729413398915559267081349074167080325625957057122126626516584353388970515628855803511191473940465894739146443922426912507374494589555474677131731399787838391143433796447439592416676979761685146998340261354466558006196148701735436902340529449337036461761117616329198847569954202332835761535095360326103603864349458052135506470361734979078302554289798850961030444297561341803117771361906831181872230656260871225855988112531036219610531642470628972642342670559178421918354872932675]) [5, 0] [true, false]

#time def tailRows077 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows078 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows079 : List Int :=
  decoded (raw_ints% [24906754737705018855953759103837863032438820310411871030746301427612133532085490453140826721303350069625916188693483420804380707680782674307741481396581640838573084403888843824607786595923167288473639772531289486252643226983951044265561827411074349788223087982276997612230264453571050104551593538834503528267227336722350021553700500484601124014435739342788470813606485496311399073137200621674680544117400230134135994552880721227859860843546505945893047011624986173244000606711996702114906334153295394526922406850408619909189618469196201569649590269079000364748087609878140318155017794413166573273635858560265722455524842167083646851, 8118576372450951568327140839913826083152448872703253857763619690575838758908367784379902316942650021489783110541352313917556826645165655148314031193614357542168659400554577427282999389288609130775774781770982604240313527159757268457368495332984487568560662477914176568334629557461838910000075214910617875935725031837961991564252817307053056470200831764801633938658562125268334906624825815238552970571539236861966210969265380244653822709900106726627463590172248423852794988556744969260050893832769548424198606400583117659014946656337636273149778341799233301596496947707586653234278748252185865737233533697373730054823960975]) [5, 1] [true, false]

#time def tailRows080 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows081 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows082 : List Int :=
  decoded (raw_ints% [2465204426309397414521048485461039883743496723353452471309737491793627299760542487302722395748644957283346808442324073677016191925316887418281210200083942882402766229498897245563919447198807825199013327961173327072148726179757497786183720152430280920263223673449319437596105358082325702039708133991913763638124235794462349319658679661347479364191177728502570250760998257499781752581875367668630297811775766186131578554339348581236920945900696516445522431206185366059440556627751954237054627169392688813034018938558638925514657520432637700468528671952682767047285622091136941208474378441159983673917427769628555846260992680029381513, 1133946480793201682397351005843962023317604531110980159980598211619617725321967867357776182860646613807538471485564819570743349252060225653636803468965690422290092831218783459761426820291621763377777026408852222741086601133725001360893960121173424461628412373207136114981953006139488722036057157307484315072498423834133183755160857048574685839020982183447391862399699330996773477670680244464728681649274944310245459067073744105065616431809999054663110389161491851568935067406065091482714043857800636471740404483616556974356636294883005801040566006132854983974324009720472310285233179078145906733130994563407126524825996075]) [5, 1] [true, false]

#time def tailRows083 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows084 : List Int :=
  decoded (raw_ints% [0, 0]) [0, 0] [false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026, tailRows027, tailRows028, tailRows029, tailRows030, tailRows031, tailRows032, tailRows033, tailRows034, tailRows035, tailRows036, tailRows037, tailRows038, tailRows039, tailRows040, tailRows041, tailRows042, tailRows043, tailRows044, tailRows045, tailRows046, tailRows047, tailRows048, tailRows049, tailRows050, tailRows051, tailRows052, tailRows053, tailRows054, tailRows055, tailRows056, tailRows057, tailRows058, tailRows059, tailRows060, tailRows061, tailRows062, tailRows063, tailRows064, tailRows065, tailRows066, tailRows067, tailRows068, tailRows069, tailRows070, tailRows071, tailRows072, tailRows073, tailRows074, tailRows075, tailRows076, tailRows077, tailRows078, tailRows079, tailRows080, tailRows081, tailRows082, tailRows083, tailRows084]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01 ++ chartRows000_p02

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01 ++ chartRows001_p02

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01 ++ chartRows002_p02

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01 ++ chartRows003_p02

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01 ++ chartRows004_p02

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01 ++ chartRows005_p02

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01 ++ chartRows006_p02

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01 ++ chartRows007_p02

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01 ++ chartRows008_p02

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01 ++ chartRows009_p02

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01 ++ chartRows010_p02

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01 ++ chartRows011_p02

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01 ++ chartRows012_p02

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01 ++ chartRows013_p02

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01 ++ chartRows014_p02

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01 ++ chartRows015_p02

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01 ++ chartRows016_p02

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01 ++ chartRows017_p02

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01 ++ chartRows018_p02

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01 ++ chartRows019_p02

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01 ++ chartRows020_p02

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01 ++ chartRows021_p02

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p02 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01 ++ chartRows022_p02

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01 ++ chartRows023_p02

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01 ++ chartRows024_p02

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01 ++ chartRows025_p02

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01 ++ chartRows026_p02

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01 ++ chartRows027_p02

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01 ++ chartRows028_p02

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01 ++ chartRows029_p02

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01 ++ chartRows030_p02

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01 ++ chartRows031_p02

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01 ++ chartRows032_p02

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01 ++ chartRows033_p02

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01 ++ chartRows034_p02

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01 ++ chartRows035_p02

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01 ++ chartRows036_p02

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01 ++ chartRows037_p02

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01 ++ chartRows038_p02

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01 ++ chartRows039_p02

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01 ++ chartRows040_p02

#time def chartRows041_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041 : List Int := chartRows041_p00 ++ chartRows041_p01 ++ chartRows041_p02

#time def chartRows042_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042 : List Int := chartRows042_p00 ++ chartRows042_p01 ++ chartRows042_p02

#time def chartRows043_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043 : List Int := chartRows043_p00 ++ chartRows043_p01 ++ chartRows043_p02

#time def chartRows044_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044 : List Int := chartRows044_p00 ++ chartRows044_p01 ++ chartRows044_p02

#time def chartRows045_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045 : List Int := chartRows045_p00 ++ chartRows045_p01 ++ chartRows045_p02

#time def chartRows046_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046 : List Int := chartRows046_p00 ++ chartRows046_p01 ++ chartRows046_p02

#time def chartRows047_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047 : List Int := chartRows047_p00 ++ chartRows047_p01 ++ chartRows047_p02

#time def chartRows048_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048 : List Int := chartRows048_p00 ++ chartRows048_p01 ++ chartRows048_p02

#time def chartRows049_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049 : List Int := chartRows049_p00 ++ chartRows049_p01 ++ chartRows049_p02

#time def chartRows050_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050 : List Int := chartRows050_p00 ++ chartRows050_p01 ++ chartRows050_p02

#time def chartRows051_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051_p02 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051 : List Int := chartRows051_p00 ++ chartRows051_p01 ++ chartRows051_p02

#time def chartRows052_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052 : List Int := chartRows052_p00 ++ chartRows052_p01 ++ chartRows052_p02

#time def chartRows053_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053 : List Int := chartRows053_p00 ++ chartRows053_p01 ++ chartRows053_p02

#time def chartRows054_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054 : List Int := chartRows054_p00 ++ chartRows054_p01 ++ chartRows054_p02

#time def chartRows055_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055 : List Int := chartRows055_p00 ++ chartRows055_p01 ++ chartRows055_p02

#time def chartRows056_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056 : List Int := chartRows056_p00 ++ chartRows056_p01 ++ chartRows056_p02

#time def chartRows057_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057 : List Int := chartRows057_p00 ++ chartRows057_p01 ++ chartRows057_p02

#time def chartRows058_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058 : List Int := chartRows058_p00 ++ chartRows058_p01 ++ chartRows058_p02

#time def chartRows059_p00 : List Int :=
  decoded (raw_ints% [4179948839976999111891518679841385, 50249653545189029186547486317161079, 101519035291729949961517456245681239, 2340075830687481850128978976592151, 47089432906563921663078451248678775, 94999010621065468999496958589247703, 756541962156357987200831033319319, 45569501883814065486289528363976777, 91902392828221629162167148579336233, 756192677943565482485562188898199, 45576348982251205688676789182040137, 91902043544008836657451879734915113, 2341179730692789836334530448740631, 47081887239701196451260652741773175, 94999415952645191976271972372553943, 4177909672598566792708458657774185, 50258708443636785361345850079521399, 101518505355936548605314961479068759, 6469528823354712347544409665618409, 55437706584898330036677570057321545, 112165943851889827745567829802461353, 9532158277118086462646639952186135, 63197766090346210056434669410758217, 128167630952362626555758879420265897, 13801311335895551838791115172198039, 74502023139134502961970849961693815, 151501100565376264857196634544650071, 20041275226952598622720601843719145, 90800388762137313734016899755154295, 185343687128224415318708351560567255, 29378442171712435352143377121102185, 114584573593039700207412053649132105]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows059_p01 : List Int :=
  decoded (raw_ints% [234763404526889449293572330525388585, 43970644764475338139083399461433495, 149557273105562184438303653997358665, 308112491463077222784799107107924265, 67099013350430728301348627394078231, 202525863121990376485578852571999095, 419182149577983289225231133963435991, 105626633810325647497835241007891305, 283755299806423641041000908785515127, 591907796738739665024415002365405527, 170245837305206718710922893777315561, 413779130742641671481249334587781705, 867780267854272031233173137150612393, 285628293030206244191328856346918935, 624246974416837078462846696340146249, 1323654398189684994135424887274846889, 491135132515953924917982230752579479, 985035716803054159863907047281619575, 2100417823735845163244735974374345303, 888443533741562907426313360721862889, 1606517239448744928298811157845305207, 3479996489993361995589031565848787671, 1643781263089755393201290581452737129, 2761922784286179974716533768725345353, 6012221286824680296216635508023387689, 3247065849422004731527436046074325399, 4894079765628255714701392320750779465, 10903068399336440420945362135550450217, 6519724624740182798963642992455164695, 9256054483130189437771405860873996151, 20669858873498627951436441174079940311, 14293544818345707772080000297072075881]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows059_p02 : List Int :=
  decoded (raw_ints% [17933529015108621312628678305661108855, 41483128316584518522480084463607180887, 31441518585442467335267294912166487017, 37843144119821604981931406455018147913, 87218191720372693629827379672845743785, 78301396760953121943125056806490627351, 80816566185993555983163268129994082889, 196961107066768282908219731391502858153, 190814860300957318261185922922838839447, 194445937641727848868181520067999402615, 466077364128678723112530711120832324951, 560143930544650206382543799640722390505, 462446286787908192505535113975671761783, 1217036154974286247756260433684393554903, 1533402111977975398550918700490387252073, 1314733798731028261633269119349444183625, 3310582197496911852689722933815503197481, 5673860341805754465383534803623239994007, 3529250510743858989607372514956446265929, 10517844651280641716624176437929130443561, 17765519141627033031204145719517191424023, 12662454482342537192400338726595924171639, 33957224134713429213211856961069561861591, 1651546627057921079272015233211291, 20363658289350325129805625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 30] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false]

#time def chartRows059 : List Int := chartRows059_p00 ++ chartRows059_p01 ++ chartRows059_p02

#time def chartRows060_p00 : List Int :=
  decoded (raw_ints% [34780605565279667155044429179155, 1622985015865069380197817776110095, 1639519449299543884097663514073747, 9746628794815198450981058713677, 1516931460472899719377331535320779, 1530971722989723755983650420860729, 12515790709811032599058133002339, 1467038955148026204982120836691263, 739734708550325964790334026501841, 12520091162059478001261783132259, 1466868297633655588981099003311423, 739736858776450187491435851566801, 9743232587279959350733530634317, 1517119319796264116987167969220299, 1530966739064079690387067608803129, 34793141047922884617555522529555, 1622760019030134938592835493460495, 1639525951509045297025112776399507, 108262645678227883449003486322315, 1795464448179647193927612149456739, 454343719820779737427306826945233, 160026582489575822038438117555441, 2055810601743046472388849438749755, 32588501678920666487447951744667, 116702559859716941938952762099495, 2435570778137950482081364619678503, 2479095809659932361113012553413119, 665343799432664815168661064559, 2989431080620782007900471535545715, 3053156954688890630357272542666317, 504830988618616399795713855162265, 3798194879376048023546782479895335]) [2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 7, 2, 0, 1, 10, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows060_p01 : List Int :=
  decoded (raw_ints% [1949321984308515707759670431441395, 760489935610602225959612334831327, 5008755035095247607083326956194775, 2581982446423125020637333526438191, 147338904189606149344477735907565, 6840154621818456927385231819220643, 7103166061973701461990101274968229, 934502948204200844382537798320717, 9723599969162644386106614505236855, 10150883191898952345510998758870183, 3079509533664969635985765403159175, 14316178207452063682445534205786379, 1887424827746540458782729969833849, 5202315192560907425089075141174765, 22041638103822522930049676117873555, 5845305837049550182834170075751183, 4615129892041635784036039804602209, 35125438977695693382801834770485439, 37813798324842379724497835053383915, 4193273015862427860745143428553229, 58962677240155609202337994554691227, 63817150172375362735550488376801249, 32473396838900379235031053874681621, 102217807231494539154724129627337103, 56531819537362726706781057982847893, 64060995895581490053607226554524123, 188856264595757126142462210053417711, 104799015904603661351100198197450765, 34392904131751627278054814410944935, 358461790813820499369153035845433595, 411230644231795321868026880593205393, 148776577564327654811658001988238727]) [2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows060_p02 : List Int :=
  decoded (raw_ints% [739142730703783162591339240628536671, 846355415887457140603562142213462587, 725416776013994670225305905308493059, 1548674411328441737862417051751343411, 467331336757526780113046012874608275, 1740332772625310370077211965693598313, 3640809834759761843492562861862508907, 541884361958676520094337740312565559, 2498420388946556501735124391509610651, 8510005501829683218171264914525736663, 11072248446187835534302162671213344087, 1686174635726725908683220324494626285, 23628172946332213857373557993939394115, 29558486309894755807238174050189575669, 48751541166261171250323231980564677649, 62467593845084912296034315298353777783, 45899712280984867163513584313355631799, 150883580710661094396493805335240533847, 218634337611376898858666485916198104711, 145717273219445999986922102971258237547, 49777563471467074598512884413952451853, 666001916687729289882009536639315913171, 1238759142693026287946544161900996238589, 1709080660430103218407752372432057, 20363658289350325129805625]) [0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 0, 25] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true]

#time def chartRows060 : List Int := chartRows060_p00 ++ chartRows060_p01 ++ chartRows060_p02

#time def chartRows061_p00 : List Int :=
  decoded (raw_ints% [4716167559297041234218016148577, 52941442385759450166278957073929, 107041472221886918693393375250915, 2628282050721903934061642453079, 49383862276830427292896402028409, 99697022611867973525113716649259, 847225494610218206682939025679, 47684878284315642298155672167771, 96221515066535851384369135170501, 846999500098965860958914111759, 47689411287609990879530523977051, 96221289072024599038645110256581, 2628995647236140279376965210199, 49378877284513574020073500391289, 99697284219359705178980989578539, 4714851691326900745290299575393, 52947402582082271438284454397449, 107041131557922746203648254364131, 7353744948789335668200121446921, 58808580667167375510654099542075, 119109728198038982617138675386445, 10945013457738714472172556571655, 67654892479660942774684697291291, 137408486604567032757511353405021, 16042173041036335877183449776879, 80698607582644804454999212685385, 164395673103342083106867359753555, 23661339852778719499279024034105, 99739238561733614529051596845049, 204099185997157138483329833564539, 35302502716981704335670814053185, 128021287288202243453557260753595]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows061_p01 : List Int :=
  decoded (raw_ints% [263063028566917562318279671651829, 53996301435528440381076911066335, 170344243995697023200393224951419, 352361832719427707035027396771349, 84362423399174481375109978960231, 236013890159259124215711082886265, 490720557554130628791214286797915, 136682271261107790209097085981745, 339069090794045985950613182871881, 711765252214412900375421351739891, 227055038919594569010771180824729, 509378432681474704633905254849755, 1075502562395115259595289618546365, 395463693852105020557706804279703, 793179168633235123972155544521339, 1698021295166814849163767603650797, 706219421280120190626244442876351, 1300305820385684745749318863409161, 2799704410299040060347718850806851, 1340944788631725721981494864970569, 2205618011193475505224644430274041, 4846868620210885972955458158653771, 2599959990248241197783713067005969, 3982195397649136189712308593350299, 8787773399090852892720666090630309, 5472253604111738429297536177629231, 7405537991689957900792070564285979, 16859986993450832519801915335265509, 11640290784879931087376041481970167, 14926702605872613048307380948608761, 33972531382442502036475492994864907, 27793130517492970971734138823500929]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows061_p02 : List Int :=
  decoded (raw_ints% [30686119561449820075544153528226313, 73405952684815404095585673300336003, 65645223709772046668898764151250857, 70512963640858554991775658595610619, 166844306912080421736218576275087789, 184406703924408448224975441496395431, 161976566980993913413341681830728027, 416896234546260916630092781922734077, 490867476617018218744429555351615503, 439326371489675451441726541588401481, 1092170415087687583599497778770745011, 1732945408802919518814941995804956121, 1143711520215030350902200792533959033, 3315983300507625321158869329927316635, 5300124500875981401567785928998770017, 3905217189095514489071610533198313723, 10349053210186526241541597254731042773, 27259171948384428080163050841877023487, 11743960521966993154037772650531499067, 42908349659446935723272434025606836277, 98356857879640930173654529731062247943, 58423561085864370649397712216952360697, 168524379487472293977090014598546107707, 27939409945295989981902847849873, 656892202882268552574375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 25] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false]

#time def chartRows061 : List Int := chartRows061_p00 ++ chartRows061_p01 ++ chartRows061_p02

#time def chartRows062_p00 : List Int :=
  decoded (raw_ints% [313517825912104134897397746195, 27229883895186420951172470170093, 27532659715594589459380442085039, 349527363050629153422951055191, 25327292928705924888409232030425, 25579533685844914612944948989877, 223884716111846400642828997865, 24433664990781387723788861728565, 12328297121815904952728108940815, 223931884821632576309432620265, 24431754064258539285837916038965, 12328320706170798040561410752015, 349452921823748412615435452247, 25329392530067918029026592209625, 25579479140810725482663125028789, 313586410152329083666126178835, 27227377438848526586761399656941, 27532730625067538642558500648623, 1967443453147025605162768698381, 30346775092505183367684611070985, 3844314964852985072798221757793, 2938838629017089701375928802975, 35097151251436629007412474450465, 8915200450246998972231117890925, 543276117901462271135664041365, 42102129608573542173188326282885, 42945849373216783759385712697595, 3223360499700452047162170625379, 52481987024283421683753723774145, 53738779315829386022795366279273, 9748142923298639603513271509955, 67889013606177158550485691285917]) [3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 3, 4, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows062_p01 : List Int :=
  decoded (raw_ints% [34966821619264464860316489519993, 15016524298596643835247709001877, 91474558717477980097806809813965, 47349155230212106579696979775909, 11960537930569789589596394725905, 127955110800563733891476527293425, 133635910620160436173834458005505, 610228507372294390332137247405, 187158862162036296814577967621205, 196611610953126856334284031291235, 66715513073396828006255188695481, 284173608687871097816503662629105, 75595437124587631330449000955159, 116964114833429983463310021993035, 454020914455623608839598722403129, 15189418012661791774730037953411, 54387672128517230299092095197671, 752030068021591031669743750601245, 820576179752676241451039617292871, 207042568589676276558919096393245, 1324223668511899293625072245565865, 1452212005446097715765246190870045, 853073155512302319506407278660975, 2408370616739001244141096521747205, 1359685149068876294194745831158755, 1782481860833217082251985588855617, 4736516290561108571650701360209765, 2677462657241635995073942264917051, 2081400429050774990694316213548235, 9538298060071869573149038877169673, 11300208033418039053788502545786189, 2417291299478114848049565790086157]) [2, 1, 0, 2, 2, 0, 1, 7, 0, 1, 1, 0, 3, 1, 0, 6, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows062_p02 : List Int :=
  decoded (raw_ints% [21387719722967308497205231068595645, 25132174089432048427375398133227287, 26542422809780211066713695207212645, 48214958851721707141942091518548185, 3833985131070294930392959781299035, 69598259308492608451190128659266295, 127557410962088152764060011897446225, 39371111053849384601047795091815875, 14984166486772806518633046389860809, 326607996085692140946702606155613365, 466829367312255051153510051264302739, 362018876429795679406197778942151895, 1086544066115547769956574980848538001, 1430613783960211314264034351386379473, 3624432723696721745541754371639092251, 3222759007524057576196284837692828525, 2889542130258262209309092140454887757, 12958079811535281856226225787178692845, 15584274960902434752123592467404907005, 11180798397874264010193082219863780305, 81457289771103043665092567346468376965, 55055078253665185001101187986407599905, 198234256149489897206797524919843007385, 28786731019243005998970033069819, 656892202882268552574375]) [0, 1, 1, 0, 5, 1, 0, 3, 5, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 24] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true]

#time def chartRows062 : List Int := chartRows062_p00 ++ chartRows062_p01 ++ chartRows062_p02

#time def chartRows063_p00 : List Int :=
  decoded (raw_ints% [91610339208456281933607562935, 955018532506383198831375089765, 1932801211402751651765833114401, 50769256156177985393968666105, 886172339687912171000850461701, 1790421616038117384438256885361, 16317869768356029094859747273, 853480020194027228043437757555, 1723334490113583369949428471983, 16315101637599085747796422601, 853536600151200112811130967155, 1723331721982826426602365147311, 50777990432217820714442020345, 886110223469225399539030602757, 1790424814052643333064603590257, 91594255730516690024902651575, 955092581015635754240015007845, 1932797060215377843803948262177, 144058291545762921389444973735, 1069298734930258779588835905907, 2168449607491657455218295887487, 216942479858943231239045883769, 1243209164107161597018904955315, 2529450378896363607846786744991, 322544941548673100552292428777, 1503183694648145242066927673445, 3068937800303979939638125057537, 484476074266329321859545742375, 1888299047204507798123489812869, 3875958816118982362049963228689, 737916011533848684703392864215, 2472135843180803885786019158195]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows063_p01 : List Int :=
  decoded (raw_ints% [5098350901919160368612901835279, 1157874519474575786761505786985, 3364131070272205167530275541299, 6994141432927584840077800486479, 1859895705352378001427761984793, 4787884882129955459309030732165, 10011911657754538628267068258257, 3118563666142136893129229345879, 7083922480976961170385799510885, 14990371029249053522824059588929, 5369375132827119719369484362695, 11025012214414229245567489423923, 23478309828218310135322773297503, 9785932996048554803456127045785, 17822672746631200609124768236275, 38633617957093984658148384705983, 18285243192585370620401454111625, 30596878206511338852479743515493, 66704794145727910082005965863393, 36874469907666811694991079993671, 54393159131801941849927676459525, 121864507245980092397398499968689, 75667340966444277816003894475383, 104345818021844962242461903502835, 234406318120091181908393474437743, 172829727690934609408264864247305, 205727841064690497481935465410291, 482903386777470069132662233160431, 394636144552098199166347954082105, 450005273403714181058991631997445, 1050369259020502877707275051489841, 1058346170903457390864468100850935]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows063_p02 : List Int :=
  decoded (raw_ints% [995000130168886895814631373574501, 2503351574476058467738091106422881, 2732423798827778311305538540365287, 2566697615210628962787927833699315, 6294121544207294169908097747639103, 9180549328108400323525841742931641, 6459847727824443518425708454305075, 18207094671143472804739478030936031, 27362593922407934818077870892109865, 20927796271427429609839611319562597, 54750237921659807946343190665977537, 133238781256491379926175430314654055, 61185035572640313154581450238524805, 215351613100559122690596491872741457, 471774733037845259754691641258862615, 287405358784410189462190471948870707, 820365127394895762371463563446258127, 5742673226810482494065187329370834089, 1004734501648330832663964732756250035, 7034813087243223516191342534075954831, 25200405328114375230044934250623277657, 11772751812405375177592565130690538885, 37977891642168081240301464114070066577, 253051443826400991712430084667, 22651455271802363881875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 24] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false]

#time def chartRows063 : List Int := chartRows063_p00 ++ chartRows063_p01 ++ chartRows063_p02

#time def chartRows064_p00 : List Int :=
  decoded (raw_ints% [6105207267355467771872940245, 245410484160765528416225101999, 248404666476229528598623898447, 845623439196476078102714941, 226978019722271657693530933915, 229429264427946784430056298429, 2159952305677736009904857699, 218350534106478293916938223887, 110252162304348619897664860601, 2160251265785420382782325347, 218338210499560713653911503119, 110252311784402462084103594425, 845505562583504545747969597, 226991539169619975448067525275, 229428919335258380916973270973, 6106074985276619603973128405, 245394388502232859117846530223, 248405113806479656490903284559, 19336972921924973753984815459, 275840139051832932279852552515, 69988559174739467363208589207, 29239669242365596434516347657, 322742280189932754133785792059, 41066359857906054955166939993, 21974082098322480869992694557, 392798816021295318017917943143, 401718712302258997815837256715, 16608103868454736893475045903, 498534936976512601093727348515, 512099291972722907129722829441, 102866501638171866092862814345, 658528477916571108313518677591]) [2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows064_p01 : List Int :=
  decoded (raw_ints% [340699104542356860398242913699, 162676534787028895354308878543, 910000943529200065465178605895, 473470622754957241121828760143, 66935013301299517325964628931, 1309234617064686689730754191763, 1377357833502141446901824914553, 226256511307616954265776581319, 1980961156349992342680612668791, 2097610909322573424737236592915, 807589180880953929598142565199, 3119286707525622323856966842315, 209857069551172578929183270047, 1480048627069513956243945327605, 5211317879873808061073182929587, 1411337730192307287177255053389, 1459477589754565183403209781263, 9039481215803678148832748152735, 10044354727347873471759385103687, 183637371183884275803651000299, 16887138597910329528298861179691, 18839705784741300664282636675781, 13114147211932194262766292521461, 32545064727340865451700076191007, 18915124437278895876382880603405, 29407112364139072494346503095483, 69343727445639106579364031265535, 40175754225314529254939278411877, 4810832333784091315424448938195, 150173514183897155429086088572939, 186731938155313592051016242930357, 97743355492140962871268440381881]) [2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 1, 0, 3, 2, 0, 1, 6, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows064_p02 : List Int :=
  decoded (raw_ints% [377236996807820950766528763310015, 459191966480140978840344306705239, 640024535379273854789145310577851, 932120358121024858399233611627987, 323675803210924189843006624511713, 1881121904415168298112645940908897, 2937335138324916369923110005621419, 119245301644941841008556804672925, 4450812336662284266491660321924353, 8456607975781698050849817375263575, 14598596230377875743369784334291203, 7799240329483987744493312967662305, 38543833831623190501856392581016243, 54697182221638395254326356848789129, 367246742939694007407744875061570529, 133244453247525501962742824857860455, 226570443239634176820022241890504439, 1604516387230285562501567847597191207, 1507530805590399220132835892827298359, 1212452008324623961774678603219885307, 3637118960730880862314610803490753899, 6551310002168667751969014215246625283, 10519055439043989963207518159926053775, 260615081010940464142369778937, 22651455271802363881875]) [0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 0, 22] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, false, true]

#time def chartRows064 : List Int := chartRows064_p00 ++ chartRows064_p01 ++ chartRows064_p02

#time def chartRows065_p00 : List Int :=
  decoded (raw_ints% [8682323710983520233441788185, 83536485053896002422659220645, 169262575272678244893215685811, 4779499851481717628799784623, 77043766507798722237114676981, 155800751710213007030974113003, 1531329728995523775336050647, 73977485350932567165059651399, 149489922129735765626838277733, 1531155366896977351479275479, 73981107049807674686442575687, 149489747767637219202981502565, 4780049685661540868321007279, 77039796084726521868018202357, 155800952820195737422781785323, 8681312406175549710408925465, 83541206421130756423084590245, 169262314912032828001511718067, 13788131099563638664160729489, 94402420897077621288836053287, 191731758417772016376081373021, 21053063611300881190813108191, 111117468620258033751406049223, 226572953128636536231055210701, 31830965143313705909356376343, 136508548119679383670462269669, 279456981883251123331224695235, 48854436905214577522538572353, 174779398906885445570118801909, 360142383931779406763119643931, 76249873980022755446589454425, 234217421930108538715539414375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows065_p01 : List Int :=
  decoded (raw_ints% [485246694817016739732247670709, 123364626018410733178300727943, 327279146866930956463297710759, 684861194815450228357137853077, 204810822198488707883397157407, 480946673966930005072140870261, 1013036643032349669418835738427, 358070207903799896068210821321, 736900791263908372230092025573, 1575917673134638273370443717155, 643610049564835876921892216961, 1197087089774529797208562512903, 2577597930603274046360546755437, 1241289645246325081221256766415, 2024120890393580126073876459495, 4462497625414435004503695738813, 2450686351212344221509275954631, 3679666380267179959651076045733, 8154473621873104307234228459859, 5341989626752896441010693148849, 6925493592818268569092428368757, 15947149599838344969754197563339, 11757004943815277713092919940617, 14363645633772972841672462343431, 33046144170406519123857810652805, 30021985113063975457940636508087, 30439503480448823995278268249991, 74825134227285772294891367101509, 74951067594591020668796985272335, 74407615859900923757553735359605, 179798186934940768421628988881931, 238974485409190875306379087332857]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows065_p02 : List Int :=
  decoded (raw_ints% [180341638669630865332872238794661, 493723739938722664396805061487123, 692151835422889788027014970371313, 552356586678282674370311910025319, 1424850060770803327730199119191293, 3180449756141194368788661641632319, 1564645309515410441386902179537287, 5297451652334887484545875731194925, 11025800552536207006792698042504439, 6913256098960671411947635193289957, 19503701961012288860127235415331683, 125382310086383092776935070310841505, 23616246414587824454972298264546165, 155911812599931588643855003768677627, 545236559702766367368964468111640889, 257677876271726856965817775814972967, 826530682389081048789754542191160021, 4727079166702151998010949207766603929, 1114089365820120559192901234487827943, 3355311924610304581852230197463803019, 27885885028697235233674872178106189697, 9196480457132577139056080639718234891, 35968276120009691813538051583336596645, 44486224745915441281664368499, 7550485090600787960625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 22] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows065 : List Int := chartRows065_p00 ++ chartRows065_p01 ++ chartRows065_p02

#time def chartRows066_p00 : List Int :=
  decoded (raw_ints% [290595397391340085646481089, 42972683113558554778756709383, 43552379481668134860184342409, 639459842982840204272621327, 39482549491516273571268278011, 39948696616571733766467251043, 406789384239746487167233243, 37857004369695833144575738767, 19131493773183153435377387573, 406827917798486046459305179, 37855391954557287622599345039, 19131513039962523215023423541, 639399103155714781151538959, 39484316040889777330412959483, 39948652204034962038809230179, 290623312651663924888966337, 42970584779803005871811656711, 43552436911559703000224038793, 3722868246228159393901394207, 48784262045743022926859882267, 3100018228687573362077322731, 5711133300128230010684838229, 57862057764715643447417233539, 14758573301339390799455849033, 2187720316249500902159382417, 71628795246255942969599235183, 73496307770483796817145764029, 6763780053513150198122742423, 92865582824707657881967352211, 95774749142508100822028778543, 21552336221062856656246627737, 125739035674361144554581174567]) [4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 5, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows066_p01 : List Int :=
  decoded (raw_ints% [65427322735298628937260445563, 35168189577045720128874656079, 179074927708959084506953863159, 93787585634352917329821087471, 30115964995374160169423311029, 266411793982544025070079798883, 282975290836499875127363453079, 26532572561610009780327942549, 420002647671952365862340351391, 449337511073688234587521845333, 200040224768087860634087742867, 690932954968304181555326879667, 188877006522054033585730339599, 386972843475696752077562120649, 1220163546744303808398691322859, 167815136791500093381821402739, 51450903389389656499350951913, 2238824328871091189865575362263, 2552708392037932003121748573169, 888228397299734541278631432253, 4513021363665241824357152245291, 5152379640867635589668626668283, 4421364440433882333256733935117, 9344651507268967520094626820287, 5675100437950493502741311733953, 10840002762667851807162319124419, 22198479125400771157384087985759, 13305784039501360572950838263721, 16813689843913425958550969824859, 52704662557940374748743903317963, 71078950529497424870165935301579, 2996657165633055871461069339733]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 4, 5, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 6] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows066_p02 : List Int :=
  decoded (raw_ints% [156707997876708178825791846584631, 200599359517582064674022093822753, 427438662772324604107306334909447, 436276779758971526295760778803787, 90491381448770557083510330950457, 1464764877681016216116803086993469, 1866462648966006595255017186222419, 654033648010876319223048017376643, 4017598077800107901354349326362807, 6295336290483036390762973126777663, 20151291780924953098426392461951269, 34766447424076872621051593189248483, 66148031893767733016924606408027331, 105754578940279129945946976145899463, 575211852254754279031151232797739903, 284426915683098017359175718640765527, 199962189233160701921550535136671737, 3417580475282459542164478096777209801, 2234699377125249383107680324782932281, 2196358353001767612519365199924146589, 2984060409975371922993942686399372289, 13385894985446740151298736668468073677, 1842176361335250921215323123826758401, 45877142660798855545356191121, 7550485090600787960625]) [0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 21] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows066 : List Int := chartRows066_p00 ++ chartRows066_p01 ++ chartRows066_p02

#time def chartRows067_p00 : List Int :=
  decoded (raw_ints% [999071269505249270463780825, 8807861046173361927118345167, 17872291436413273945027306807, 545561495269438081177719751, 8065359120734662747445180815, 16327658671638586593385806231, 174165751777032919262607015, 7716738055634485764762905665, 15607931424592115592945479465, 174152005787642060928767655, 7717027617180596908919966785, 15607917678602724734611640105, 545604819757713320645358535, 8065042067209769886620440975, 16327674504148080116185766295, 998991661779862297915766745, 8808237256696023550210683855, 17872270985685655734746891575, 1605169077668934102152081785, 10063025390769494482451974465, 20476431725134452134814740105, 2491789626323565482694024775, 12018575412033891754514847425, 24573390429126951719660846665, 3843526967438005036335164135, 15046604643416625447840024015, 30908707022888522238690035575, 6054735577744428360845298681, 19705629346909901827185175695, 40806969568070955635870498391, 9730704185684969612560678425, 27156075798905482169530621377]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows067_p01 : List Int :=
  decoded (raw_ints% [56592409331500353609276475497, 16344803146914553573206661479, 39167037718279841052306532545, 82667916664099876795043815401, 28241901095306631588087763335, 59845682092734589315943944335, 127254620906321061956338240215, 52028138827574340002982055065, 95650839908893104228482059215, 207524660829202033547408058615, 98579929071579831372022555449, 163901959747883269321908054465, 358132728728356204922412669129, 204588051886924730232115145735, 292810698052052766972527170113, 661300709686860766526550370313, 432582850767843937671062338471, 573078063521732729786138345935, 1298471612341629434429727854519, 1048748110934940913663058382265, 1157976399587740642314651847055, 2779802574044414285763848575255, 2522998262914248583951116551385, 2670574285391614557112255110465, 6351548947893603783378023508905, 7609243267220217323804445772327, 6203972925416237810216884949825, 16483790478028069691133585832617, 21345651655723744822254639418695, 17889060819832049204721146655119, 45438685400972031837192671023639, 92211459856528766441879963571033]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows067_p02 : List Int :=
  decoded (raw_ints% [48895276236863727454726163787215, 158995796913224543101327274013367, 312127982677368925891490270967545, 202311980532889582088481073797185, 563335239447122235434697508551945, 3299559144916169079307779849172935, 673151241591601579237706705722305, 4175022367040660240633967628692425, 14199515925482833742898729003088487, 6801430270365227740704040772143055, 21674097437439663062840476480953847, 111828325772669235881961196227735175, 29072183092557269065035164711899279, 75954712409746739076221990743692841, 669609602334380703241524393717482087, 216855221274973244023218351683327295, 857392640516796678199707580688910103, 1078581596100418229472535626871179495, 1310147021576204137418013622723064895, 448420646750759151968696347535212695, 10903022865007357350306941143664707335, 1940307970925863214921852902059031695, 11533183814357016427810780423000674135, 1179460169119907700968192977, 1510097018120157592125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 21] [true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows067 : List Int := chartRows067_p00 ++ chartRows067_p01 ++ chartRows067_p02

#time def chartRows068_p00 : List Int :=
  decoded (raw_ints% [33639544641842341008458645, 1135041740613794115939054125, 1152137054428725697048165441, 9175945711865892374515485, 1034674189676287914123442177, 1048154182297577445533186211, 11620078788613587408917993, 988226609223939837946806365, 499915160330750144313103139, 11620850800826327941339625, 988193874521833564487770205, 499915546336856514579313955, 9175337546326210416895005, 1034710012427245149712164865, 1048153293659844198767547555, 33641778631078566695275925, 1134999275263052931158090285, 1152138201107306173825679425, 109196998249627163490871985, 1303844241475873683274372265, 332154689154772617676775815, 170430337619681157960606435, 1571787268261561585121578225, 100515380780524924509911355, 133652270081229396083451049, 1985565591954598315116798005, 2045980970270538742286090213, 53063902402608117660630185, 2641005428911396753789186617, 2737796729653862475738033791, 700438036098955747535374635, 3683610468838058080256963925]) [2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 5, 2, 0, 1, 4, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows068_p01 : List Int :=
  decoded (raw_ints% [1931372992486841582279224953, 1187289455858541921045906045, 5442757573307219743930685157, 2875236738465590416569865293, 133600483329829380071628147, 8432768292272225764440588105, 9075370666066992835331686983, 1982295349684196417455424211, 13993188506416300068514886565, 15177569098712655751388585757, 8021436192302070598476370885, 24291131089745797104083981793, 3395449498797889898096975633, 16602205651021621855415623415, 46078933275624582462420370105, 12946809458426702909666949841, 19586138531069933612359479015, 90699953693832284525746475453, 107561720546868300718802380809, 23092723004184416402667175937, 202768041524184051361296202225, 239104889625745833554190042587, 270577961739092387456188068031, 460183521760782946968421290445, 301026871690787943310523407183, 745922393444862089993963210385, 1285079888480553601186048474349, 809277049282765182035599046391, 779862030076539602408632682555, 3443873095540231306944274131985, 5483924612316550863699692033387, 5210572374905506678911238099985]) [2, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows068_p02 : List Int :=
  decoded (raw_ints% [13762872369705187239724171395229, 19024517482433722631156698963577, 105993024187658550978385147194969, 45128452094784284738234178931865, 33859671604975821741841080589629, 453489249802062520681685113683851, 437734969120339391153264760175105, 86865120051203044828429322904667, 1695761549459959921950068499932635, 1859085451303034367464974633667269, 2243112888708232964591017302944083, 320024427975361571549149449180345, 13128357426559339984447283239285975, 26116199378051293387636719050351433, 30211044318144988756333098009629395, 80067168110389527949117284356501051, 8193359225164722605224592894132059, 319794175035608003287873444924905509, 107715819846020615040885108799231605, 166809250451711773416878678573135393, 7687206690684789464730431562062475, 1199109532032042485202376495343120985, 591915022413553234403787349574676495, 1219416143712410379065082731, 1510097018120157592125]) [0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 7, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 0, 18] [true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, false, true]

#time def chartRows068 : List Int := chartRows068_p00 ++ chartRows068_p01 ++ chartRows068_p02

#time def chartRows069_p00 : List Int :=
  decoded (raw_ints% [6338341151454375010992163, 50761281970479399113778291, 103186535957325478531126169, 3427374628528334822001765, 46086912835391704406355715, 93420820177342768698132241, 1089542441737868455568813, 43906532713422729469774761, 88903903107076565420561663, 1089481718444020618923437, 43907827951915967495218089, 88903842383782717583916287, 3427565930508473415021669, 46085496150310770707621635, 93420890032735211617861393, 6337989940194335189116963, 50762959812932914325261427, 103186445903438020222000025, 10327090624119719394927995, 58761476030699441085855561, 119851526467752074806044983, 16357680680344832689599221, 71417141061172353115117417, 146536297772216626890572199, 25850020396201472145568013, 91476837391389106465054003, 188743998848762931725739433, 42051912336496076882176651, 123117181853575297406253443, 256645931581460480753484097, 70044192467836742957859971, 175580662064381260229407305]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows069_p01 : List Int :=
  decoded (raw_ints% [368742036385793300593520719, 123344644867034705676970077, 263205566789248783321973385, 562130873720664749228350767, 223922946717296305102050261, 422269951798450671583347459, 909398465304995760007371105, 441591413654223616352880851, 711051460223841393526073907, 1574912825676515681462302217, 894044229598628635827617131, 1305452779106897904289109161, 2910548468929367933642800199, 2051646697129271627404725221, 2499139919421098665181308169, 5856239395657268196875142551, 4737544619401503187864928957, 5408746173365441159098559603, 12645430712188043012144796729, 13466724766521752719287650555, 11974229158224105040911166083, 30849700098111298919297376241, 36446348612923653125075177011, 32342195706408946597673860713, 80762773477556704763660203807, 147390397275378890605970768781, 84866926384071411291061520105, 264599519365859248494706149599, 485520803793982789496717028293, 327122990257166727809615398275, 897510720435220928597393946673, 4744013475420353879628488485123]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows069_p02 : List Int :=
  decoded (raw_ints% [1055908533972036990284495576691, 6127044999649557597722599460089, 20170002625439993289351300345051, 9815149941097874487066592368521, 31041061100509904766702388290263, 142849162146253276125095761117867, 41395913784852023568987096266793, 91638098420303378069042072482553, 870785896876659773080320386431763, 275883174351408677763124929867213, 1105273157443216427274458220032183, 1166066003571443970367089118846699, 1700175879968467522591653676596733, 809993050748432229987689487617247, 13013591462455939971764056171906915, 2056248832791479262971053307826185, 13369664415278951712143455803136367, 1360288153953665113526706597155011, 24327007044943412420936458667217097, 25022967723781226570380805377888271, 121065614445467057868278639899423691, 664327475115850964082359886483837, 97402934875639496411424541118690431, 27381219277194963385529583, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18] [true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows069 : List Int := chartRows069_p00 ++ chartRows069_p01 ++ chartRows069_p02

#time def chartRows070_p00 : List Int :=
  decoded (raw_ints% [430109274257525019349135, 26245399222929609517865875, 26692165524871263883699209, 464573472749125257175389, 23698057632752718094739463, 24042581482342913291951891, 292459699639158663360983, 22528811440936607460462763, 11410487418602752057120065, 292473510970444451676119, 22528218834196083441295531, 11410494324268394951277633, 464551721619394527068253, 23698705484818385267167239, 24042565602746023408367891, 430129232914072625399695, 26244632607151239657841555, 26692185977641102964103177, 2838773601602169377332323, 30580773211443547273562359, 3906434563862445355379285, 4524753251655751696066001, 37599727013559917167170847, 9653750841039370979108151, 456557419467115264936011, 48679786218066554057826363, 50444675327287079851474781, 5995997099963008960190809, 66819401859455294123075551, 69741588238686942010832575, 20682028533911636434161245, 96647763017770625739352835]) [3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 3, 5, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows070_p01 : List Int :=
  decoded (raw_ints% [51207805486262298182687719, 36756534466132110880828171, 149547515995101839859720531, 79927086986284171840182427, 35316361446372013449058067, 243673900882299069262665519, 267243431331444481459309159, 17471139623266045701438949, 432078407566077947452185067, 477645271210316873968936885, 311690706086185400665405847, 802750368826812531708711887, 232276273570657660061463581, 704004142189256739850435845, 1678841231910819550113808455, 121549996409879548797606001, 484971866374513328434794599, 3618766937583839491110455267, 4588691550245382834351310257, 2574067365198735037874678799, 9438391093903032805070522039, 11676713746140906223839846251, 20107399591583355057091160977, 24211305859173719794107885659, 18466124034060865678340182413, 65246340535891503958258995519, 89867989460236453033435165947, 61142994097798295186015260661, 305713163641282142586490411465, 285196668002739735627143867735, 798958656014052379503270339771, 645485493241372890743875236997]) [2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 3, 1, 0, 5, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows070_p02 : List Int :=
  decoded (raw_ints% [2535573298590493593725358457667, 3992326956262108227651752110689, 17263140405637707918331515364917, 10612964559864705987529147659687, 167013616818907939495379098535, 106326980555287053444403534441159, 66516988323960338079600703002001, 33569748109333717372609828028079, 15987764915745961434603908574993, 414694957661283507790084990104949, 112703853666654231458011577953531, 758925362766893193910892032063685, 445091488979910427827724371397775, 1533048991193099847840603754773783, 24277692628093263129894959836731, 5656707944473862043497051266404531, 1513311012049396486266246429532211, 13506502698507902244472981551899021, 347980718467537375308144532050851, 5252079183518601267535191826335665, 3827786515131018737366555149342081, 48369302849557746934394874941191553, 31666234095807142254276475503254513, 28412602621901363961095749, 65656392092180764875]) [0, 1, 1, 0, 7, 1, 0, 3, 4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 17] [true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, true, true, false, true, false, false, true]

#time def chartRows070 : List Int := chartRows070_p00 ++ chartRows070_p01 ++ chartRows070_p02

#time def chartRows071_p00 : List Int :=
  decoded (raw_ints% [3765932040461730242021661, 27110015153718886064951423, 55235607853957384253033403, 2011729450170635068350483, 24359660659776767946060319, 49457946363325018942661259, 636279753565536554481379, 23086556253377615928250457, 46809937159588847319829397, 636254493821773628873443, 23087101152645694837097561, 46809911899845084394221461, 2011808996904979815395859, 24359065241021163185997343, 49457975390571837838490763, 3765786111321370666136349, 27110719146455654467889279, 55235570498798188320022971, 6242067640897736210912781, 31890637463663904518270041, 65243424251017295197072101, 10139078711695538168948499, 39594854428251126889714841, 81624570603610569576933381, 16510183479166362776734339, 52168794887054980856167039, 108273832794472470522616219, 27977739730230349439396621, 72615221386583852443183519, 152761756003869182738747179, 48735365930522325364266429, 108124274347515679734960281]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows071_p01 : List Int :=
  decoded (raw_ints% [229474861664621857542410229, 91295971306672463555796099, 170085953247628503171716377, 369506198901816646462472757, 176497918080048588296366643, 290716216960860606846552479, 637300088288537698314635499, 382282452602509872277692861, 523081789407725679764449663, 1196080458971096158888695003, 843709831696123055116585517, 1055281122165880351401938201, 2422072743269729086282973381, 2251480166764991193424229683, 2210501452799971789997620697, 5517262741730843334823788581, 5851978226924946926653973283, 5558241455695862738250397567, 13620721135420781454901991547, 22047025745863480953244731693, 13914457906649865643305567263, 41519725108209209334800696523, 70394017613914077607948602717, 49652292947422824644739860953, 133960768467986767895994030933, 631532938959391995587951448867, 154702493134478020859202772697, 835887725041292841091894082517, 2647186825509151851239042150227, 1312718170866206815820642758687, 4114607489509836687918887681611, 16651716803610281079840002970787]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true]

#time def chartRows071_p02 : List Int :=
  decoded (raw_ints% [5449076144152781723337287073151, 9889922488591292540682073138949, 103745044190938751344401963577011, 31990715436354355343859363182887, 130286683483140324964924039686747, 110638967933067479388851045023827, 202041012237724720965466640080871, 123392759741011596920474958239931, 1411523720011760179030470943420611, 189287220429780603433842726864767, 1398769928203816061498847030204507, 103624374045445552488729677687373, 2621006427785795637095475246760351, 2913918022261021793018047651312491, 11988652107391205938589533767098371, 396535968520671708411302082239513, 8971109711084738593082756438098507, 7679851030599226313024195989180733, 21356297786996616240083592287436391, 28639612849075170844696486194377611, 75576530266372977122728874515640691, 14963166092677780917637089896121953, 39257066386698579965008192332082347, 7375192486802389311881883, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 17] [true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows071 : List Int := chartRows071_p00 ++ chartRows071_p01 ++ chartRows071_p02

#time def chartRows072_p00 : List Int :=
  decoded (raw_ints% [258041433789429411119825, 7037824102413853921371855, 7175330039746688328956695, 134408174947860310625, 6280670241921805092062235, 6383979229874611590557045, 86010927100944896433235, 5936752333240982256731855, 3011350180240224388981905, 86013827684032621796275, 5936626533518025506329295, 3011351630531768251663425, 8601837799009631263271, 6280807643977112743916955, 6383975898315877325547797, 258049807904645307229505, 7037661771791258308027983, 7175334323693476140431479, 869409889484590800720803, 8345206107214275201752995, 2140210957246839388902823, 1422528317379614569767945, 10515301329729621510911195, 1356597754481445365762505, 1191515241444373256633745, 14035319376732733480824775, 14658340836119924009135475, 1019717473836250508695937, 20047423261284607563981155, 21120241214353672557186713, 7456069465977070638526585, 30350798958112741619959767]) [2, 0, 1, 12, 0, 1, 1, 0, 2, 1, 0, 2, 6, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows072_p01 : List Int :=
  decoded (raw_ints% [16327590287837872615248523, 14079166930658815412287487, 49871701125192890118087495, 27095208486155815640655559, 7400433245031304225064185, 86667466680748003269109715, 97871316883095663593855345, 31883768645862005816978595, 168278633045693757719114455, 191240587154944892128069275, 164617211208164599978077039, 341737615847644049804938475, 26226583478427093983756469, 418491393088177709525143765, 826747477878352157631422611, 250683484987793953310831077, 759337234528627526191506163, 2015703188200354887905513535, 2939899802096608575151480399, 595675471829026093309716065, 6901445354107372367163471915, 9223978045786072374012221245, 40848798644342344664498066885, 21077318286729189873816427615, 27419090232380312892494008325, 169848890241275581068728092619, 170296639931476751025155739455, 132767934675189275759107088077, 125157665776026304086070294275, 700472879251831514148728798091, 565876566616556300101620085427, 3159307891266611792679037492987]) [2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 1, 0, 3, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true]

#time def chartRows072_p02 : List Int :=
  decoded (raw_ints% [3834748664901364979729093677345, 7885753675357990318148257425601, 5874203818770762612421404582075, 24573990250881062827283571145805, 2082541409780112822771231957375, 81736168459608284138118056597025, 19662066610181685469956524650955, 2477506457476831108107954167175, 6695730823869596432113819043925, 302370683587552073725188655242295, 174407836746606072461800228034475, 165267629590236371219271283534525, 73227913201138456926867077002355, 473271219966600219551057268015775, 473514151099379066206984835654255, 2341911389856229865783151881310105, 803927944713462385317563618904065, 3974242419126260207359952211301655, 1820828691196377807901072265614665, 946436189299978185258920068919635, 1092497235941151287776858331743675, 13555058286648810963656656963896515, 10237103741490821728985225676115625, 7691412907325547151196345, 65656392092180764875]) [0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 0, 15] [false, true, true, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows072 : List Int := chartRows072_p00 ++ chartRows072_p01 ++ chartRows072_p02

#time def chartRows073_p00 : List Int :=
  decoded (raw_ints% [1144283840079327772016195, 7307086463131001717385055, 14933201685638241271637105, 601861690697621234100725, 6481831382427911782235855, 13187056154861292265520185, 189175838862301298582605, 6103363081735759249183605, 12396018625301369732836855, 189170487774690029695117, 6103479704703309185070645, 12396013274213758463949367, 601878536156833910595125, 6481704057285139308573839, 13187062298145282404239609, 1144252957885261667687555, 7307236777016977006260895, 14933193792187377982522289, 1937991170369686450018955, 8770209973055662643948949, 18015437920442326100228799, 3251523048122248628548293, 11183219117756349906298805, 23204952138934261178796047, 5500093095402255010690573, 15273256069300159901045535, 31956568282458764818034913, 9837269214858364157950875, 22183405308560859927679951, 47293930592719383986676361, 18155419673908979336801795, 34947794499016888216947285]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows073_p01 : List Int :=
  decoded (raw_ints% [75286619481486727481429031, 37054068387158259513050205, 58494244656378818601283541, 130496107542553966331281031, 77841189984633094890320197, 109055931273333407243047695, 245391365914345320734651433, 194210796838592361441385299, 214176624625645008381923935, 517443352737570777066356929, 482246319068235582493941275, 497477524950518130125818293, 1193900468644398721001683503, 1683272193927089735908855125, 1178669262762116173369806485, 3359418981639724039404479903, 5183863226477693378668615645, 3864021912804697601943528543, 10226554402044507153981950673, 42367421156783169704027800491, 11546395715717502930707037775, 57777838785305370236678366809, 174614203020698746081369379539, 88598864226371037009999129525, 274759462962787286022075546839, 960412684225281491052322171475, 360774801757114995093445796853, 511039018241795458948877245097, 6148767188150052456532741074475, 1832226504224191945094645213425, 7620218890617129406533940491047, 4872941950698957599690912832675]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false]

#time def chartRows073_p02 : List Int :=
  decoded (raw_ints% [11936759574542989917972036352097, 8896044128068224263375768732847, 75417551561911408846671597851691, 7913657397173723254287180451925, 71394449384542142182986741951519, 19265663281908054062800761505125, 138898343549279827775371159351285, 166077664228361605092459101308335, 579334354865484167299171322763475, 46444983960989831379888703462175, 393991027355214508143911459950015, 460122699920543860355500036493765, 1019770366181688506822971486175665, 1433448082141242535798582819207255, 3313171874039109676951268050864675, 873800415880097889331111369525355, 1419601091977323280797185195163655, 3896474731483300648903486591657085, 5606573381896530847079564615553685, 8629247697499733606651939837685415, 15334634595911216166021070915108891, 6919149047086503408475861813788815, 2808912166928181910465644485766391, 4019371381429392260913325, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 15] [false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows073 : List Int := chartRows073_p00 ++ chartRows073_p01 ++ chartRows073_p02

#time def chartRows074_p00 : List Int :=
  decoded (raw_ints% [39696263813383230213409, 3815644892530454235746441, 3902926537845526999435175, 83367341631847346426793, 3355067962146468079709365, 3418621744074766464874317, 51604012408415299601453, 3148706159475675464332097, 1600141524201328236209639, 51605250967668063218237, 3148651912512806881303553, 1600142143480954618018031, 83365392429102030223185, 3355127163346347717205045, 3418620322787781359700669, 39697156884816680638099, 3815575051945623123089033, 3902928362724518865251831, 549615272385263002226281, 4625436183660481497624213, 596265111273539414072863, 929966931177987636812691, 6014036141486675131994157, 1562425773437891487905469, 409098171067526989232787, 8345303908372432044874977, 8816062709199661545365715, 1478675505657790608525633, 12559606878567106959718749, 13409806404785350719348129, 5862006059473416533685759, 20174707953634756913080041]) [4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows074_p01 : List Int :=
  decoded (raw_ints% [11114581737787174235042577, 12000416370580165584180201, 36007631116460773094461785, 20045792952813965293975557, 14454674428356258677193723, 68176373435955419249800845, 81001351132920613526518761, 17503192946322628036586523, 151645026543310842512011569, 179923471774923643027252299, 234688211390835143368440981, 348227460577117467835185213, 121156113737762324635509843, 708268077619365351347072319, 1090397872106651415985775493, 44611898248789056039298521, 172073245488074636637259053, 3181299771054578873223474489, 7642192677199003516996914687, 11237384985567875842698368555, 23115773294580204905554934277, 35623306503953143574785941493, 114755637409640255328423597013, 93080379655597585614810422929, 28328780467275680034120459205, 746769087892351198125063437931, 435906776343980816408139453775, 459091143118271406760863976677, 244533112438641507667293761701, 2893995971913807206885443328795, 1175885149251610996312203867883, 135290596384991848894949862673]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 6, 6, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 7] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false]

#time def chartRows074_p02 : List Int :=
  decoded (raw_ints% [1520358123165151244930210639833, 7971779244265150348299174866591, 3017325904987698091681345638081, 31740396702644106110221721515493, 613990728684135211539290991117, 62989599921411166988446602351893, 13589661743115943611655593192157, 10081142674632785531876986249517, 13776782115724102077635363549635, 220218002983000561843564687892079, 158421299082838717426496001548501, 170864846126103292892189614885653, 206838852108469689630510223602003, 128201264706471460047341774024265, 429544009958740733813108100312663, 1146700766025825781293952231193145, 449737483458709389822414552054117, 1502682826468080088034408930606271, 1511337187726493245621922177648649, 86831924795960287288235863092687, 1193591571289682021647757136523953, 4864030539846494570843683491231939, 4063529818639364705906394929839551, 4220496648352592841142447, 65656392092180764875]) [0, 1, 1, 0, 6, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 0, 14] [true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows074 : List Int := chartRows074_p00 ++ chartRows074_p01 ++ chartRows074_p02

#time def chartRows075_p00 : List Int :=
  decoded (raw_ints% [716190059151948200304235, 3987867309624416205324485, 8184011183223915973607189, 369079623437021129732917, 3479953814447551567978469, 7098741500634946643570037, 115097562884795288495893, 3249708062750373945858651, 6614564314313130225341227, 115095261753486070595701, 3249758688677960990986683, 6614562013181821007441035, 369086865202059425732821, 3479898586257346087050053, 7098744140137366503769557, 716176791196643291193355, 3987932419082079842452325, 8184007796536069220695733, 1247284932822982025847083, 4912252168650632669436763, 10147469520555694537736171, 2185634474638856280085429, 6482502284728043894146491, 13580388928017532843668683, 3886786573298035919220501, 9283521117928345229607621, 19652809975954425042974613, 7497653373469061485980747, 14256075431324115732587493, 31037249922721522448175861, 14956701827114276999193195, 24278827864866468201569115]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows075_p01 : List Int :=
  decoded (raw_ints% [53491605123304860933349803, 34769834620758722477596149, 44169479085552669730973883, 103218141571177860410139147, 82010943073358286781328469, 93818497106383913156761413, 219998919265294869669063765, 263594243112313696723499403, 208191365232269243293630821, 565604105450966853173891637, 778275714799191792751174827, 621006983331011306603760219, 1607474063362472342648565867, 5741024133285760621205178165, 1764742794830652828795980475, 8126773911447424756604918859, 23183025044106306283829147797, 12103055249902532549014116549, 37050823088839491661639244821, 109249314707787127746978713653, 48130792883043265396454276069, 49015466574841329801510321035, 724294354969264842817014394901, 206395574165671722944943310757, 882559136251893300365503429589, 374310523684067303058944644981, 1400457917055486420237574513733, 1232542967537090840123573179509, 7911828960290613175595488713685, 542225473202462883172945979205, 7053596516437589638530860179157, 3506391909249089027998861907723]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false]

#time def chartRows075_p02 : List Int :=
  decoded (raw_ints% [14423200003525739930953402913637, 18471817385977291842125210800565, 54331002206802603996648653099989, 7555009291700640939170669794651, 32352792911576223126524580391701, 52089803447353770080212623034699, 94238804410079468062343903286341, 138773598565732597203385856526389, 278740090309678439553563756150293, 96624597603006899221254576274747, 87876688296592072269965276589205, 374436877233504845075949918836555, 463241376209277411044783609014245, 741053655839775356899478951576053, 1160953145097256985073609304399509, 652249156864002790930645261398363, 45462612023976783098180433986901, 1957639157530407236995454946169611, 1858664913985236559102434999784773, 3164054914651641005167244684556021, 4119914200997292676757911338805077, 3263029158196811683060264630940859, 1001779871184755565404788291920555, 69532822206061438858683, 65656392092180764875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 14] [true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows075 : List Int := chartRows075_p00 ++ chartRows075_p01 ++ chartRows075_p02

#time def chartRows076_p00 : List Int :=
  decoded (raw_ints% [6315057964017873016203, 262391996278160983119909, 269606461994062434341003, 6495776869299274579771, 226300463997820901432473, 231354676399392393116649, 3969411032306125672299, 210425781323766786481741, 26799213953560964785601, 3969478038943124026407, 210422819868596398743277, 53598444658781179159729, 6495671448390812948497, 226303693479539282587369, 231354599570849466562317, 3157577254831663955427, 262388191455722902331253, 269606560506284404102727, 45348166183041585803231, 327346165634152529161033, 170107672363989650774687, 80230477567700981501681, 443780856187889245544177, 232896994239360934427143, 9457279271404275046129, 648268075904956455167757, 697340934388891251094031, 147225340774165271445507, 1049046729557762848496433, 1143108084279690194723109, 660459771352464516534249, 1826070802098278626731813]) [3, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows076_p01 : List Int :=
  decoded (raw_ints% [524504634295121313537093, 1515162641780884133231931, 3690885814967620914633429, 534205118789229237989319, 2331001247666224737355119, 7886721369221815159659537, 10450806087427167511856721, 3360518316513753606123621, 22338895796297418813474381, 28554881848814631411061443, 93822308000693322318267507, 61655014433441872857637473, 67909631557781484076911717, 374395549747769512405532101, 397628127799070708086544409, 302018560432012901438811521, 404329167694083388964920333, 1559237213424519922479765877, 638884000164538240576526189, 5477431964560680884975915903, 6071638555306263515352180919, 13211064600062233566388039327, 4141582442755781045424118077, 42260218503060927157327561347, 625760815200869196591117283, 112305230020179461362936936271, 10494691215716860666344291389, 24105616594126857029361325323, 30317989468320311614176600333, 406960701577656918294420183737, 269363675333327512708735438229, 45331223481828307657248169671]) [3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 6, 1, 0, 3, 2, 0, 1, 5] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, true, false, true, true]

#time def chartRows076_p02 : List Int :=
  decoded (raw_ints% [253038606962279353579757094053, 395299921439284786578882075841, 759115792384280092080645643769, 2494237601259354771769462675207, 939857644766408900587749217173, 3506392026875760494819767646361, 2783424562574841014742825481023, 433780472479331300781811784123, 629584135665838318501507045313, 11531330506243687207509607910237, 9410626057161129644395447577111, 6892289429983362494451822787777, 17363267778731985177305399968993, 662720282521111203503858364061, 24737535320508887293526936405359, 43606984933623212748104974391979, 9464848474488625269731680904213, 46233767206102373805097013987427, 81586873503303563996802345652443, 511348812886281705229895188587, 49932950498936240866641067004907, 141328083890786282472283081557729, 129736506191613840971022501962457, 294866693850133926405815, 65656392092180764875]) [0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 0, 10] [true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows076 : List Int := chartRows076_p00 ++ chartRows076_p01 ++ chartRows076_p02

#time def chartRows077_p00 : List Int :=
  decoded (raw_ints% [1341623336388758567111135, 6364088249587132168281191, 13140465122564777192443301, 672169031373159057777873, 5434753536588886457050975, 11126672754802859567554293, 207469715090037382384345, 5019750186840814052725445, 10247034008339663127392075, 207466834893029886120625, 5019814106408811692282285, 10247031128142655631128355, 672178092868412126406249, 5434683856626873824966695, 11126676055904097643655229, 1341606743666428232681015, 6364170292145635945094783, 13140460892438938002742493, 2425985862462948732253231, 8117897343959730290328725, 16908053498568314967676739, 4522840962135206493829785, 11216142017071533409601245, 23856880323166470193759755, 8617032639605873264014225, 17163579268230143277988295, 36996753924907549951603765, 18669964150724154648549599, 28450207296283279937629695, 64283750715237577864167589, 41619835035980411082486615, 54503507569678452575087493]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows077_p01 : List Int :=
  decoded (raw_ints% [124573549901942143595203803, 122414818144891008183849441, 111689877368244102102602925, 288608203082813562861539859, 344013747088591563990596505, 299333143859460468942786375, 755036768316296135035985805, 2265135183463143135102925095, 799717371545427230083795935, 3364185698868030834129507405, 8920259202800080850864070815, 4829603510785746739148636565, 14549580085131254820096503315, 35040379810214311779729029495, 18640235777145588931811937565, 11570540522282976108768455365, 243350788242503134753747159935, 65251156109642876820309422425, 289961708575000422642244644795, 58058087515239196998056162575, 468061340707860680575682382305, 475254409302264360397935642155, 2331058375889277351779322085895, 50865018920835517175802902725, 1913862054102252188379442606315, 1489883835620714764439400779409, 4194055411070694022982961789485, 5734804265612244304598165471619, 14098870094575211939853925782455, 3030632690162265046054604461543, 6874181993342252870816359531427, 16065035972530579014248095300969]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true]

#time def chartRows077_p02 : List Int :=
  decoded (raw_ints% [24003684778079729856724889775425, 37038088060448043824918380614851, 63965125835088241089859165726095, 29099439254898892982441586140395, 10862001802109618250692689810275, 98383816676406134788217741760505, 103926566892096752322993441676765, 173210944313603994128769597296875, 236398299572652215414482959226639, 167668194097913376593993897380615, 35196461417357913502504379830741, 453119836494936128110419017850945, 368870032253207678505972476776513, 654321674650230430022397597246843, 746331318977650994403403628310839, 738571478891958879626844138321275, 361110192167515563729412986786949, 1727952380857461394968118167509185, 1123792605702094310300834779845165, 2113173507667596825642108809033075, 2074374311089228341976568326199175, 2717333282822963910309392196697095, 1766751577435829878633658650343085, 3620522114738383939888609, 1510097018120157592125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10] [false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows077 : List Int := chartRows077_p00 ++ chartRows077_p01 ++ chartRows077_p02

#time def chartRows078_p00 : List Int :=
  decoded (raw_ints% [387312893425857282822695, 3389468601703922895252615, 876408624521193167784583, 193662471135990903102195, 2847174607613907881378659, 1462329566761462242606721, 7262061106518714537497, 2614818717159959282843835, 2672900173534783865811271, 29048581714158554933879, 2614788652205309016178755, 2672900848110951259379053, 193660349113252365558465, 2847207370873227722314867, 731164590163130183701319, 387316778101098482346305, 3389430048658318478412615, 1752817743933435791355023, 183281713208984419114525, 4396474483277621651700087, 4626079118803907741514451, 690239718373746741046091, 6321937460002069184245015, 6739685408387338900064733, 2899245935371823679613993, 9918392230267595580068815, 2754852695126664015442727, 6279812271632709021142805, 17918921201489363902700987, 10099234493755594381263853, 1102243071849215843940295, 35037641316798431664640035]) [1, 0, 3, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 5, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows078_p01 : List Int :=
  decoded (raw_ints% [44114170408731351286715231, 24102306735676187502093855, 88462477799839177914879867, 109954673029671179793947661, 298444364090753749811018097, 227856095202207931681390875, 114150912647944326152288367, 1158035025765249588887899945, 1282239934162854177158952255, 956541520223890321654035755, 1024226043587553624683670205, 4859996198263206287232990655, 1025786108137184266538709365, 14651906980292686176315176125, 15105376763238003817779771025, 34426504243072771117903742435, 2877217019086769842540994425, 112355259644078283123288418345, 15213275296142843406998275065, 260963454240079465625721547165, 3596508686890924447615793325, 101493785037297430920134720665, 24186593815290031500201640981, 931498557316239579379597770315, 657443774836994579467604116343, 735488223697460204750160094905, 770374493402390083558836718067, 620039922035605578031102945619, 1821893984176404996503677697375, 4952407232263442058621682988925, 978227588401732746008775208201, 6233282027888786634106885413905]) [1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false]

#time def chartRows078_p02 : List Int :=
  decoded (raw_ints% [6517201443303229902455874071433, 249238845052725326784053441863, 2572461928033380721084519163913, 19980720879291704477805858666695, 17021607430127760172013068953283, 10777073236993931617369698005509, 34642189405230861634896432551175, 5757308668273419821611749597917, 44342001924667075153689921273655, 66235865016659748461151725377377, 15034709932595379641704391921689, 63741628591108299052768095000485, 142725818293437438979863252543445, 20369606531970147333869696979963, 4979814719396686076305779423655, 188730649347773447749920654624563, 182356486547861958826813642597519, 83002683601339062883648156625041, 494690465789338378787276513684395, 175705190365877787501302270904397, 500510343145044829549517386835119, 475290819462939055319264598375765, 122702629995461291953877857295201, 3892947391510629953961027, 1510097018120157592125]) [0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 6, 0, 1, 2, 0, 1, 1, 0, 3, 0, 9] [false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows078 : List Int := chartRows078_p00 ++ chartRows078_p01 ++ chartRows078_p02

#time def chartRows079_p00 : List Int :=
  decoded (raw_ints% [4633546666406968547364341, 18103113212338650472531069, 37741789182773486364952335, 2226809186139534028992963, 15005129304027867345056925, 30881433330226983788595031, 677746367050740123618241, 13649494840059582414545143, 27976877777036709635983827, 677740032210126791134261, 13649636569926387097820443, 27976871442196096303499847, 2226829111148533034554323, 15004974904479835996813665, 30881440585554756129188431, 4633510199846909159955221, 18103294792223453166929089, 37741779896550198323697975, 8838328889824213134265335, 24271995304173654316724107, 51213618986221320617918531, 18160924400341012040819965, 35779952571871879435459759, 78212872276386545793003831, 38300121816268499977462491, 60593844104855678398364037, 134673918492996057811286287, 102673800352699689917255725, 112380196204408879390384741, 275647840661964247706004503, 272419448178678285155900047, 265941444810255058232875487]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows079_p01 : List Int :=
  decoded (raw_ints% [650741089193342222779160275, 1580397441708521937865832741, 657219092561765449702184835, 2503557979080542445800893063, 6031192548397314585978862499, 3426736328227298933964540969, 10115147969186378969645588303, 18992307395965626685304125691, 12719604189356394621659909833, 2845966878381933129679674889, 140728907590842484371673218041, 34557878463703954436643710413, 162567181865190044186657018621, 6098455734590309625084743763, 268738210992328574121686526249, 309394545190622838183414980425, 1158298168682650801815155028907, 46754789932884573686813197939, 842805167757437654006655304719, 981849784492094375043543542301, 2047858126372973029508623531565, 2982953120932182830865353875927, 6050065058973203982134758506145, 1916944779051304176400273886663, 2085262153548926776225861087917, 8142006328725980731393171352427, 10052271991573434934760893480725, 16277333541248111489753790946489, 23811527599445913203586662236531, 14367067878400657286386068818191, 607812270528179017560300062385, 42339768084798735927894674918645]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false]

#time def chartRows079_p02 : List Int :=
  decoded (raw_ints% [37570783207318391472412430992337, 65543483413716470113921037092791, 76604323372666904399007764789097, 70312468291196814569403281019099, 31278928125848301642807947222339, 170260773300177990060474142314275, 115637863538015417325603098585857, 215586168546996592816673959881033, 210937405501229778183559303160955, 270209078309159165551545003609451, 174909536345944804693588799034353, 575060334757686640992267396858893, 306236947464444139041515507736053, 611088203912971614482237900985495, 511318720431329457550708531465041, 879911591206214116432989790108335, 674829818239328797923796766379347, 1705781423285429568188675547061627, 716400493398214776059901555194029, 1542270325477430227815587312147321, 1109935687965843136253846514699587, 2531651255364645019944361304014919, 2138116060797016659750416344509361, 10593833962295113728079169, 7550485090600787960625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 9] [true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows079 : List Int := chartRows079_p00 ++ chartRows079_p01 ++ chartRows079_p02

#time def chartRows080_p00 : List Int :=
  decoded (raw_ints% [5532937747349079086649675, 9822055874443323375097945, 41058512593018077449784471, 2655865955421624458525499, 7940731548391175806469453, 32869708890247373904609297, 774608581414822550517607, 3583094959510849458286223, 29439234353410926895566191, 774614543521560875614057, 3583061483488176627975923, 29439240315517665220662641, 2655847205104097907713349, 7940804462543259792186503, 32869702064143324003990047, 5532972055777795592219925, 9821970172080451163665195, 41058521325025217503923321, 11397819316480496004627993, 3368444129580263846101607, 57989312697283509100771239, 23570092621382782469285913, 5304947372140236792073297, 92957224635146787574685145, 60418596277104208707080101, 37043869139703837853692341, 176945913533633778751051159, 155361515833254958101485429, 81638385765665155875373289, 392726025643992945559616689, 841538095371762015403008105, 96202692486479397977588885]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows080_p01 : List Int :=
  decoded (raw_ints% [1389625636849009919064110223, 3151809528589397123602287129, 461588240568713585639190697, 5382973260810169058069405457, 8705949763787910619736153451, 3344214913562355919557464899, 171166974388344438064460865, 67348849818451825255291043547, 7782773282650483448457772057, 76225966556628080313091657863, 12545369642131626106307397943, 8000579363111183666966697331, 156120186017211531674690099353, 508784648968925469193232885545, 1270508932798881847172823125, 340119093309582311412235388249, 487875694577047107678737964501, 444780014064035999857499306897, 1336779436855554888284206238295, 2445883396023792835534669059483, 467547551652264998123972794501, 621228264591190839571724856687, 3580078186087097704856261326983, 1000551690979878417838584876293, 6647189846702081379962655243153, 8880731418349176465079350485001, 1556265317217416353366144266241, 1346536614440002619739566085135, 17098881157750301831585672291365, 6879628036389419629402180732415, 24633075961659475676925456691231, 26396397374314938510377640624523]) [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0] [true, false, true, false, false, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true]

#time def chartRows080_p02 : List Int :=
  decoded (raw_ints% [13986350523315469124853383758883, 15335559745094838998133488358073, 63960501553377453470124922802247, 4879192334481379720243864973027, 75021339182597552982369075068697, 67166543129675494166474156162169, 12493537757515496086317884760841, 71815297606299512286019841708775, 202399785422021157071974342767429, 47649773791749975285498696270061, 197751030945397138952428657220823, 150190647567405757731382886868075, 152425634391959172726702803724065, 249960168800012538293020113120177, 565360518996043472233834130285623, 51270436887827891222942095299007, 465590997763436691672196904033521, 299308541610649324874658210698041, 206467442302042149753565663280779, 731642975148830839031372823621103, 1431985881295484083791265751628789, 196767667834993542428774020100027, 999651447757302569634551138705727, 23295725170183578268217073, 7550485090600787960625]) [1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 9] [true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows080 : List Int := chartRows080_p00 ++ chartRows080_p01 ++ chartRows080_p02

#time def chartRows081_p00 : List Int :=
  decoded (raw_ints% [21079504996450081821460763, 64228103147805928604947343, 136258014773030979608639279, 9460709941221491002878123, 50950406628774969182231173, 105717799835359406784300393, 2821671549933098342177563, 45306683265362946599191097, 93435418344204817439244707, 2821654681443178535388013, 45307063528908772497876047, 93435401475714897632455157, 9460762984850201556838173, 50949992628249303669967123, 105717819142008277724681343, 21079407962122939457928413, 64228589498609175611552393, 136257990088981418739447929, 43652924748000490969368757, 93108808552495182585823949, 200990322799104849166745099, 107722214311664762863612141, 151534438994610157550289907, 352365461858770102999725997, 268393985180334783833817413, 308553237175824708313048231, 728481661350769649697155551, 1352930229596128320790676309, 688322409355279725217924733, 2349805876127232754321649273, 4960749693464113673912703637, 3014413696368081349894400849]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows081_p01 : List Int :=
  decoded (raw_ints% [8663485799187474749025029219, 11796627309017002595485567619, 10609821796283507073043332007, 1827608183634585827452165237, 96295574916295424847485893027, 20578840921665923841076734389, 106264594041677841615519295409, 31877000505464748526721255491, 181981328036307342621928454047, 234437169463438014989726443927, 662153665605859515771115438597, 84332841932595420894519245371, 395839495636956752254667739179, 712995436227314026604501460637, 1142326003175411688920302423147, 1770988597470130294630284638413, 2905648204466454035538566942107, 1341658030522032632314483675903, 421664170769009714303780843057, 4638303873713641880836098041323, 4668970405757496382156831461067, 7965616248949105630678445826487, 9652271794516282462876598310277, 7934949716905251129357712406743, 2951648328146465048637945557533, 20278204046070301039112453613773, 14635573183275068543596365159487, 26978827512440118453351106366517, 26273499710931765938322214398883, 32621458375235350948867194820803, 20983531847578653554141345581407, 70292432016483941589289183132323]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, true, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true]

#time def chartRows081_p02 : List Int :=
  decoded (raw_ints% [37911426238588463333048063638279, 75582399879837053973470051949799, 61155215704395906828131409707669, 107963405657732532229711171443843, 84719616191925088734627825374453, 207658920065759840752223055013773, 84399005170203350323214755777059, 184094519578230658845726639346989, 124536169693447705364245639100859, 307354434473787149274734938583703, 267217269950542794233704055259903, 544441127854489255943322257066091, 164673334216692060405276522424659, 401760027597394167073863840907047, 223676770876454263591663139034549, 781527821235191362611909575548479, 722524384575429159425522958938589, 1299937882773070679772010712345949, 282680207536216466778049755644439, 801090269074095783938150892441909, 351149665953104999973485088635619, 1818347944310949996932111849143419, 1749878485894061463736676516152239, 78668759884740530715050021, 22651455271802363881875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows081 : List Int := chartRows081_p00 ++ chartRows081_p01 ++ chartRows081_p02

#time def chartRows082_p00 : List Int :=
  decoded (raw_ints% [26557766042749367254950415, 4502745780146426069068421, 153382398858180998391124371, 11951154285692782859486763, 13695175083272203507769805, 114873478529738848276687193, 3319718514383510620778255, 24070811955478625693060605, 99602605729662554796422175, 3319734453399947929135505, 24070631652160896394761355, 99602621668678992104779425, 11951104170589118345505813, 13695273204439286811098055, 114873460292668058379420743, 26557857699518301144359665, 1125679244460937960633349, 153382422162775477869286221, 64402363956938486132025277, 53948404108396874766555775, 244342643819232265145671163, 156025691965829053448118085, 100424099779688500872292445, 464770699741999804725814525, 730329404633973952633602425, 52493524018556482053668465, 1351125796341802810807535035, 2614576303779597314578112525, 415376752206831226752947435, 4696031504755374078019249985, 5221842157481277292178987255, 2824550399853823242792786385]) [0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows082_p01 : List Int :=
  decoded (raw_ints% [2088765651053694100418375255, 45667403505479503018442591495, 4391088653067614838673092385, 48800480011907086210203203495, 21836800460132077386147278755, 21421426552812839887824902555, 116304683977518666614793073745, 282929065213039957225352420585, 6556972278299923056205092785, 144787580775389213224412068085, 340559248615071949879273332373, 240086212107414277449702615475, 768275894603501120329037821043, 1121747221910599435254877390355, 314331359501872257654452961233, 12912078692026365046566236939, 1962654140850736154376986514943, 27551906556349536181411711715, 3097313441453361954678430142237, 3373311921727154056948127753285, 824161390674431948361266776855, 1686655660576944052107288903895, 7819950308080708776189999912225, 2491650911923968899142952978405, 9506606569230918781030838761615, 8310613576170701240382692556703, 6171627526731844879467466358515, 9015943301140926316838146117137, 25007113263722491895454641226075, 2909481332123366170619869789149, 24301783538752266818999187665641, 17440859318129340709850597351393]) [0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0] [true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false]

#time def chartRows082_p02 : List Int :=
  decoded (raw_ints% [2354435717123830876998396858445, 31868037484345418004603231540323, 68683246744093952904907916425325, 11621896653882608368610857773095, 54256068577877875610155282236395, 31690471667120592806831116543595, 49847761007103305888920741557765, 91248843654851235708232082118125, 168391091788716134008444382487159, 5017143753309496109555064692625, 108832719800985491107043416912629, 49570326121140792085631856056445, 59271665390806414059761820464697, 227653485468560833029855943343343, 377748442634243864243076228156729, 29501751107902807647411597285945, 199665283286823823298852140869831, 63736298339098719024212592250935, 259205111852631036123552587227335, 513677427581968968517715776775625, 788683472938668495658415801060115, 17117273615597955688400497482495, 338742343695798246164912616535425, 89970082450465182823037393, 22651455271802363881875]) [4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 9] [false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows082 : List Int := chartRows082_p00 ++ chartRows082_p01 ++ chartRows082_p02

#time def chartRows083_p00 : List Int :=
  decoded (raw_ints% [1107100429612165832687165155, 2358436961757127572556983815, 5207868666656526234783510187, 433208243740894524201040515, 1742331275287232829539361217, 3667559993303465877895304517, 125150433686898538040196841, 1492020474275338524154902785, 3109201315875672815654067161, 125149996144563611319809191, 1492030407913435753458967535, 3109200878333337888933679511, 433209619299551009146794765, 1742320466564465746794521167, 3667560493777452509400283467, 1107097914355640483130283405, 2358449646512537771752557065, 5207868027432644001677361637, 2647419544006331497367042375, 3956516295275746713055087977, 8962385485794615982174687417, 11523550245523372128845426679, 7653288734525200766486641815, 23133355275324319608387156471, 40173643005946592244605972445, 27003616786322490970745941335, 74830548526794283981838555595, 65127055456634971737439084035, 88000574746418385255698586705, 49877136076105904489005444005, 624266166744835948525583321865, 103250494126947452504132226735]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true]

#time def chartRows083_p01 : List Int :=
  decoded (raw_ints% [639516086125365015774016961895, 392350563815669762181018943545, 1160531758743253511795468057025, 1656132816685870726480619227305, 3440293731687689035276376936205, 887951621758286976866170113825, 1391810351186148546614738765355, 4621474961803664533534811286861, 5720055704632124558757285815385, 9453579044677502115425926988421, 12162864102476589824118459266265, 8354998301849042090203452459897, 1912189904004576824842279009017, 23520377220448972230195746905065, 18605672500321055089479632717145, 33771051418920985229471927162313, 32647686044244492150604212326685, 38685756139048902370188041350233, 24643742595125465309063461740693, 84930791003874127247752668392189, 46689699588167929211728791936225, 92934734452993154089293418978181, 71590879980795672480200387051561, 131175825868699352125317295434145, 106274645476071608856845700318809, 249213873171805948657520417216025, 96492060373423415748671982166897, 214530107676530012280875103948777, 132388543778323406057174084126605, 367251920474912545189723538997905, 331355437070012554881221437038197, 633303899787659887483530498570125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false]

#time def chartRows083_p02 : List Int :=
  decoded (raw_ints% [168285027183223396365676186086313, 434337006495970738659483145658533, 206619452485685245139124001371129, 899355879100407229777337458142345, 861021453797945381003889642857529, 1445763896986964900454380708027593, 244953877788147093912571816655945, 791361895674704764589615066541193, 259257562730781402690769822383325, 1992171914873522571131423957912841, 1977868229930888262353225952185461, 3035680897959939238160237897789565, 273561247673415711468967828110705, 1317070230759832378497781767987429, 205408356884125053485184688773705, 4079189881046355905189051837666289, 4147342771835646563172834977003289, 5958561967793276683023280135938297, 137255466094834395501401549436705, 2016627552841755173335629847708713, 123965466715837176302246501335923, 7837934054540197460857508434210305, 8099154987350869032661156484982933, 3157484548134346033735337671, 656892202882268552574375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false]

#time def chartRows083 : List Int := chartRows083_p00 ++ chartRows083_p01 ++ chartRows083_p02

#time def chartRows084_p00 : List Int :=
  decoded (raw_ints% [770168873050577917775753555, 712446257624691591995469233, 3157843417102032768950189671, 308069847582281121680452259, 481391014401035833591748825, 2079604696469173729493983857, 77016967043711593496926151, 202188205021205235157508487, 1694517881843181014316605447, 77017174476024711431395001, 202187023678662120047411337, 1694518089275494132251074297, 308069195520007371408002909, 481393584518435181746411975, 2079604459271526215090472207, 770170065123441858132287405, 712443242877331611502825583, 3157843719914975444630762521, 3157681605502315553631740521, 312890912410469259969674845, 7085695390540732856394790447, 10705293823709164777679468705, 483765606047455895641820763, 20948670819752213187705999673, 13400836201008924525987041019, 11956857473351041817558168085, 18253128442452453439398427359, 146023074682559438190363202155, 9530711352629277360852474915, 141170782441115909276951815815, 114369324401988769430491931055, 67033108604604198186402517035]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows084_p01 : List Int :=
  decoded (raw_ints% [401563181525664116897806949025, 704007005970508794048832843905, 61950017877309023395672202985, 188074500042855907720533963825, 1057281268930569549842895359109, 569940788761300397676027809835, 1949362774943934251612262166839, 2180642342357175508989946220235, 933381233175951503051550953139, 826001701517328292465211305713, 4724725177159070807576405209071, 50334423549871097228559950325, 6079365817998918024101140123593, 5121206084190168171944927618745, 947835985995779826131213563983, 5682884910967820659732617713919, 15352604427300878690898258741821, 3510504530594293060631009208345, 14790925600523226203110568646647, 9735796887689573057082231609299, 11561260483317759386373404485889, 20407733140134531836926595779169, 41070767746012977469588978418359, 3112646178547639998225611200477, 30398831493568018689744614248489, 15199420763048643660728879412521, 14754753631347609041607786966235, 56270178476532352498604713254327, 96022515744666022289887436856845, 8974128405953363664277657011567, 54951758031182313452011603015039, 18557710527234854432167883128931]) [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0] [false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true]

#time def chartRows084_p02 : List Int :=
  decoded (raw_ints% [66513008481970804206671862924375, 132416563248613481309731156742953, 203114965034680611367356198258407, 2395895530320372691972556529341, 89256112313301984489792924644385, 13159594686580900799359031980849, 8537622284544362947542770958377, 279211482661401695057790090921943, 397479402774415611623990051031893, 3576012565299410031468805863485, 131427514799594817365558992090799, 13462623135096750747627420131365, 260877446221705804463305715697861, 542369540709107179737176463254057, 730719446253924641873737353025503, 8519317850198080389548112997425, 174887282409720711388933469640081, 82341575989734777946458177402447, 234921000016109418705215818663821, 987948304653380131209129000068031, 1276030923992584989359782790582517, 65302940289338617167361951407597, 205741043349470080204195613112039, 1964006145076305343362971613, 656892202882268552574375]) [1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 8] [true, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true]

#time def chartRows084 : List Int := chartRows084_p00 ++ chartRows084_p01 ++ chartRows084_p02

#time def chartRows085_p00 : List Int :=
  decoded (raw_ints% [53718802044552238191975789435, 53716354736241305400284204235, 142051797054449008376724812087, 13131173700493551583766794403, 34616640273655464784464818417, 75201821309403218600982228249, 3581246683952737265838456219, 27454007335254202232750615429, 58489400924956929751376977627, 3581240577269598341634069669, 27454146905749990252787905979, 58489394818273790827172591077, 13131192894837997742168164253, 34616488489793398916018754767, 75201828290381386910974824999, 53718766961233839624505007685, 53716532695425985737124234485, 142051788146453224277647996937, 177869122876461093236585642705, 142054022412261078165028770137, 373639677984148157138738647327, 158769713630759520494907392719, 409454778448348172210295519895, 392739087229849729880416897313, 2097426766263479523805277694755, 175485404849257962824786015301, 1863457392664389314419768190161, 1980439120659188381841976987947, 3785398754078610875400259869615, 5941323279587057220067022872863, 8648748602896680008381724747765, 4136363646167634726508739991195]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, true, true]

#time def chartRows085_p01 : List Int :=
  decoded (raw_ints% [726986202650434406472724886955, 14615131812883931947919354365557, 13512098451714749141363189625915, 23990866618431046362773804000277, 22887852627566888934716228258235, 25093899979600229169329968739919, 15718145803748089375976930107599, 56845387837403210453266059180531, 32263606803419028728069266890555, 64015094661222010012005357331167, 45578726760845958894726179507985, 88596875695206191737202149621143, 75281755737779261570545237003713, 164732111013500437072107538502065, 58893846718272889061383092125415, 135029082036567134396288481006337, 71526185916133883878390034584747, 240867346331794682407012927382987, 228235007133933687590005984923655, 398631577737035969803893705072019, 84158525113994878695396977044079, 241922756519236166092277754733111, 84686088984936235753787236109541, 556395809142277257200774482761051, 555868245271335900142384223695589, 851751954382787596986547906627493, 85213652855877592812177495175003, 380569798096387932597950919041445, 52053754975259856875467136635635, 1147108099623297936772321330493935, 1180267997503915672709031689033303, 1659933446833788685512034091008011]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true]

#time def chartRows085_p02 : List Int :=
  decoded (raw_ints% [18893857094642120938756778096267, 531719204305132869678469538610343, 83671789219359895693871461868111, 2172758794044279434251746851522087, 2275324440358281450884375091486465, 3012646838331993523045844992882833, 186237435533361912326499701832489, 653650608754352176467598439528257, 412639952832014810250043153588717, 3852534882619707611839943134243579, 4078937399918360509763486585999807, 5165230002461937208811786146040795, 639042470130667708173586605344945, 673652649711561888798256406452271, 1067647584174771282500549726540491, 6477925122304166805783629157838011, 6906530236348270380110592279033557, 8452273387551817780522115298509877, 1496252698218874856827512847736037, 478095567028776117910973292935829, 2235038274983995574109886845192693, 10426621652799468755260601439181743, 11165407229564589472542975436638399, 97885299549500623284350300761, 20363658289350325129805625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8] [false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, false]

#time def chartRows085 : List Int := chartRows085_p00 ++ chartRows085_p01 ++ chartRows085_p02

#time def chartRows086_p00 : List Int :=
  decoded (raw_ints% [14803857849709820671489174583, 88340245338074107726552404527, 243056111942980213315575930385, 7162554564727481894951720013, 40589739558270909266980147957, 6267485414839693088357854527, 2387515975740786947887211471, 31039808820254252566938644423, 33427258213521793969072184719, 2387518879649277407826623921, 31039675655307761475431302073, 33427261117430284429011597169, 7162550001442711172189786163, 40589884338851362198245140107, 6267484999995623022652224177, 191001010373696901691774460983, 88340075666849450852949591377, 448860930385098527794163923951, 105049882793692600335721303159, 115795447356274131945009800545, 534812057965102829150217081775, 1919556110761255152899816611425, 8354903563421574741385855891, 1489793935589844924085320832809, 2139206653756259866258109706391, 1687965216048706889009797010335, 5548556700107359943243247150625, 3275662447672279109959991889755, 2155916460883103015740881418173, 568219229259530794790686538753, 6317348532424748352499208719455, 4863359679295851330910186769175]) [0, 1, 0, 3, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 5, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 1, 1] [false, true, false, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, true, true, false, false, true]

#time def chartRows086_p01 : List Int :=
  decoded (raw_ints% [9024791750837496667668514070457, 7119548892982851198973909159035, 10478780603966393689257536020737, 8222591390279393821193813630877, 21115123405784431577864942165187, 9375738106669851067037631548895, 20012080908487888955645037693345, 22690887745519271757003682198725, 31751466207602469466472348309637, 59563520883025369310016277518339, 107886744246532402958359039638259, 6657574819424710344983025324915, 71014111109026305405346444318645, 25947426598354952884824121472587, 38067639019464966745943345664311, 152953428757203755478881362484317, 233899413357485954934107748949029, 12632276959505532194858070822757, 106893411198637152340050507937299, 3289997468918606125499714483861, 157764135318556021442221057620407, 81908208670112170693039849737721, 56640066084577396820347979453903, 527712916168892307140787112687, 17330960483980614536577911826973, 2039537234550234351154170182241, 295356393358063153120562778010817, 39025050518829240029617115822679, 202045249536012651857232837174217, 33160308668972641925607510028543, 37786898522494754334147693154537, 135724638872314962298210556096621]) [1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 2, 1, 2, 3, 1, 3, 4, 1, 4, 2, 1, 2, 0] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, true, false, true, true, true, true, false]

#time def chartRows086_p02 : List Int :=
  decoded (raw_ints% [512824604785987454308368570686051, 1095053231106344587063732677411637, 1352715254665499114506312656386397, 51282165101671160186301523034039, 121937384686839565144369422878139, 328971813551215503803633676294731, 419945324939755830098972042850173, 1803624452903554183454315755559267, 2152574870247464706900478301625587, 226407483347873183431030630226653, 19978603792695019642528869771589, 327495070174927698680844256657287, 1312684220367953046702534215925241, 1413771807195007561952347842355875, 1643544019039829530466420503270841, 428582657001982213930657883087921, 97722858330105730166771595742321, 583746455464691150971783231473451, 1974403817711706014230306790616441, 2129567616174414951271432139001971, 2425045013875606738699752162529761, 738910253927400088012908579858981, 288269057763499363543463207945661, 114126127046635196322043377901, 20363658289350325129805625]) [1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 9] [true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false]

#time def chartRows086 : List Int := chartRows086_p00 ++ chartRows086_p01 ++ chartRows086_p02

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040, chartRows041, chartRows042, chartRows043, chartRows044, chartRows045, chartRows046, chartRows047, chartRows048, chartRows049, chartRows050, chartRows051, chartRows052, chartRows053, chartRows054, chartRows055, chartRows056, chartRows057, chartRows058, chartRows059, chartRows060, chartRows061, chartRows062, chartRows063, chartRows064, chartRows065, chartRows066, chartRows067, chartRows068, chartRows069, chartRows070, chartRows071, chartRows072, chartRows073, chartRows074, chartRows075, chartRows076, chartRows077, chartRows078, chartRows079, chartRows080, chartRows081, chartRows082, chartRows083, chartRows084, chartRows085, chartRows086]

#time def graph : KernelGraph 87 85 2 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 23.2338 s provisional ×3 model; 38723 exact original rank units.
#time theorem checked : chart.check 89 87 basis.matrix = true := by decide +kernel
end C009

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027
