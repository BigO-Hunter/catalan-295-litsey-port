module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table002
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceSparse
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Retained exact sparse source values for the actual small/large check classes.
Odd raw magnitudes and explicit binary exponents preserve every integer.
Exact required sparse source bank. Source generation only; kernel build awaits Sean. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6

#time def treeT_J009_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [142075692044742501432067366310625]) 0) 34 true) (.node 5 (sourceLit (List.headD (raw_ints% [167723701791877168706296072019475]) 0) 34 true) (.node 4 (sourceLit (List.headD (raw_ints% [373264828628543388579117300600375]) 0) 33 true) (.node 3 (sourceLit (List.headD (raw_ints% [213527969779136561239787708200875]) 0) 34 true) .empty .empty) .empty) (.node 6 (sourceLit (List.headD (raw_ints% [613677727418390385766783126734375]) 0) 32 true) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [13854262273608282101176331381540175]) 0) 31 false) (.node 9 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 37 true) (.node 8 (sourceLit (List.headD (raw_ints% [265555089319230748749989789386875]) 0) 33 true) .empty .empty) .empty) (.node 11 (sourceLit (List.headD (raw_ints% [28117597692624432220587154170375]) 0) 36 true) .empty .empty)))

#time def treeT_J009_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [177304988447068722372861910520625]) 0) 33 true) (.node 15 (sourceLit (List.headD (raw_ints% [47529320481951429516531639027525]) 0) 35 true) (.node 14 (sourceLit (List.headD (raw_ints% [197478605706007958696105117751375]) 0) 33 true) (.node 13 (sourceLit (List.headD (raw_ints% [51406921033990123554810857624625]) 0) 35 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [91712244222196574625591466899375]) 0) 34 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [166491125197156722418414758174375]) 0) 33 true) (.node 18 (sourceLit (List.headD (raw_ints% [1373453025918301914118678805034375]) 0) 30 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [323362002359197411696798905067875]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [53679050140464825148393657961625]) 0) 35 true) treeT_J009_part000 treeT_J009_part001)

#time def treeT_J009_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [2220142848293423294339994843272325]) 0) 29 true) (.node 24 (sourceLit (List.headD (raw_ints% [290920172862134810071260776575125]) 0) 32 true) (.node 23 (sourceLit (List.headD (raw_ints% [149126220787270066367311079247375]) 0) 33 true) (.node 22 (sourceLit (List.headD (raw_ints% [612131686814383097021272671683625]) 0) 31 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [142011102378468340748941063328475]) 0) 33 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [265552214896915280981634364301925]) 0) 32 true) (.node 27 (sourceLit (List.headD (raw_ints% [135685796088323439435490584295725]) 0) 33 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [130016101446301889821463970183675]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [232002435038757367361147873443341]) 0) 32 true) (.node 33 (sourceLit (List.headD (raw_ints% [240496305338766575256742755846675]) 0) 32 true) (.node 32 (sourceLit (List.headD (raw_ints% [245037592469477684991006709710075]) 0) 32 true) (.node 31 (sourceLit (List.headD (raw_ints% [124897713082460731189379901194325]) 0) 33 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [1889247589726704442173350468231175]) 0) 29 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [224206132084334821337508174157575]) 0) 32 true) (.node 36 (sourceLit (List.headD (raw_ints% [456046035801610122189666667978425]) 0) 31 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [882165025417260214947739809462075]) 0) 30 true) .empty .empty)))

#time def treeT_J009_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [509574342843602040477749102791965]) 0) 31 true) treeT_J009_part003 treeT_J009_part004)

#time def treeT_J009_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [157207309324225889760576649274625]) 0) 33 true) treeT_J009_part002 treeT_J009_part005)

#time def treeT_J009_part007 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [142075692044742501432067366310625]) 0) 35 true) (.node 46 (sourceLit (List.headD (raw_ints% [167723701791877168706296072019475]) 0) 35 true) (.node 45 (sourceLit (List.headD (raw_ints% [373264828628543388579117300600375]) 0) 34 true) (.node 44 (sourceLit (List.headD (raw_ints% [213527969779136561239787708200875]) 0) 35 true) .empty .empty) .empty) (.node 47 (sourceLit (List.headD (raw_ints% [613677727418390385766783126734375]) 0) 33 true) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 38 true) (.node 49 (sourceLit (List.headD (raw_ints% [265555089319230748749989789386875]) 0) 34 true) .empty .empty) (.node 51 (sourceLit (List.headD (raw_ints% [13854262273608282101176331381540175]) 0) 32 false) .empty .empty)))

#time def treeT_J009_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [91712244222196574625591466899375]) 0) 35 true) (.node 55 (sourceLit (List.headD (raw_ints% [197478605706007958696105117751375]) 0) 34 true) (.node 54 (sourceLit (List.headD (raw_ints% [51406921033990123554810857624625]) 0) 36 true) (.node 53 (sourceLit (List.headD (raw_ints% [53679050140464825148393657961625]) 0) 36 true) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [47529320481951429516531639027525]) 0) 36 true) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [1373453025918301914118678805034375]) 0) 31 true) (.node 58 (sourceLit (List.headD (raw_ints% [177304988447068722372861910520625]) 0) 34 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [166491125197156722418414758174375]) 0) 34 true) .empty .empty)))

#time def treeT_J009_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [28117597692624432220587154170375]) 0) 37 true) treeT_J009_part007 treeT_J009_part008)

#time def treeT_J009_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [142011102378468340748941063328475]) 0) 34 true) (.node 64 (sourceLit (List.headD (raw_ints% [149126220787270066367311079247375]) 0) 34 true) (.node 63 (sourceLit (List.headD (raw_ints% [612131686814383097021272671683625]) 0) 32 true) (.node 62 (sourceLit (List.headD (raw_ints% [157207309324225889760576649274625]) 0) 34 true) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [290920172862134810071260776575125]) 0) 33 true) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [135685796088323439435490584295725]) 0) 34 true) (.node 67 (sourceLit (List.headD (raw_ints% [2220142848293423294339994843272325]) 0) 30 true) .empty .empty) (.node 69 (sourceLit (List.headD (raw_ints% [265552214896915280981634364301925]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [1889247589726704442173350468231175]) 0) 30 true) (.node 73 (sourceLit (List.headD (raw_ints% [245037592469477684991006709710075]) 0) 33 true) (.node 72 (sourceLit (List.headD (raw_ints% [124897713082460731189379901194325]) 0) 34 true) (.node 71 (sourceLit (List.headD (raw_ints% [509574342843602040477749102791965]) 0) 32 true) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [240496305338766575256742755846675]) 0) 33 true) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [456046035801610122189666667978425]) 0) 32 true) (.node 76 (sourceLit (List.headD (raw_ints% [232002435038757367361147873443341]) 0) 33 true) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [224206132084334821337508174157575]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [130016101446301889821463970183675]) 0) 34 true) treeT_J009_part010 treeT_J009_part011)

#time def treeT_J009_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [323362002359197411696798905067875]) 0) 33 true) treeT_J009_part009 treeT_J009_part012)

#time def treeT_J009_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [217018795273875795219049667862225]) 0) 32 true) treeT_J009_part006 treeT_J009_part013)

#time def treeT_J009_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [110833916830715354520303861676875]) 0) 36 true) (.node 87 (sourceLit (List.headD (raw_ints% [528819115122766173393116921767275]) 0) 34 true) (.node 86 (sourceLit (List.headD (raw_ints% [2372440901609956722866155278068625]) 0) 32 true) (.node 85 (sourceLit (List.headD (raw_ints% [686388177324669076252854760784025]) 0) 34 true) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [961800365517550022783576464081875]) 0) 33 true) .empty .empty)) (.node 91 (sourceLit (List.headD (raw_ints% [96849503163484155426466864364625]) 0) 36 true) (.node 90 (sourceLit (List.headD (raw_ints% [18103143702715974081176168011730175]) 0) 31 true) .empty .empty) (.node 92 (sourceLit (List.headD (raw_ints% [14068978474170141401769906013386675]) 0) 33 false) .empty .empty)))

#time def treeT_J009_part016 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [4496130604302278861919175076525625]) 0) 30 true) (.node 96 (sourceLit (List.headD (raw_ints% [303244967189819342766618768603375]) 0) 34 true) (.node 95 (sourceLit (List.headD (raw_ints% [158098363654009064702711791470975]) 0) 35 true) (.node 94 (sourceLit (List.headD (raw_ints% [661386196541429243678193409634625]) 0) 33 true) .empty .empty) .empty) (.node 97 (sourceLit (List.headD (raw_ints% [583164139264154149891644313919775]) 0) 33 true) .empty .empty)) (.node 100 (sourceLit (List.headD (raw_ints% [262522755889776125605469974991625]) 0) 34 true) (.node 99 (sourceLit (List.headD (raw_ints% [542728828591118167073032883908125]) 0) 33 true) .empty .empty) (.node 101 (sourceLit (List.headD (raw_ints% [508757191464400999913082383422875]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part017 : IntSourceTree :=
  (.node 93 (sourceLit (List.headD (raw_ints% [173533860507005334209886375738375]) 0) 35 true) treeT_J009_part015 treeT_J009_part016)

#time def treeT_J009_part018 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [432358613425549923560273669018175]) 0) 33 true) (.node 105 (sourceLit (List.headD (raw_ints% [454493780770611924720303253661025]) 0) 33 true) (.node 104 (sourceLit (List.headD (raw_ints% [933343200766631383971284566792125]) 0) 32 true) (.node 103 (sourceLit (List.headD (raw_ints% [479703016509633492674995517851125]) 0) 33 true) .empty .empty) .empty) (.node 106 (sourceLit (List.headD (raw_ints% [7089302683294890627940350007131675]) 0) 29 true) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [412727082906991867920498366999225]) 0) 33 true) (.node 108 (sourceLit (List.headD (raw_ints% [1689038418499592732376726114668475]) 0) 31 true) .empty .empty) (.node 110 (sourceLit (List.headD (raw_ints% [1614843376331720207375325811623435]) 0) 31 true) .empty .empty)))

#time def treeT_J009_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [716600776962547159991841900126375]) 0) 32 true) (.node 114 (sourceLit (List.headD (raw_ints% [5951955369296581477538864242491225]) 0) 29 true) (.node 113 (sourceLit (List.headD (raw_ints% [758685399320919274258296453707925]) 0) 32 true) (.node 112 (sourceLit (List.headD (raw_ints% [774111093217726395964491495873855]) 0) 32 true) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [729982786316308933665823149943359]) 0) 32 true) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [2766203260995620762569593534365325]) 0) 30 true) (.node 117 (sourceLit (List.headD (raw_ints% [703803608070694648107083319615789]) 0) 32 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [679805733063463490130983028768075]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [395166692702746828096475979540375]) 0) 33 true) treeT_J009_part018 treeT_J009_part019)

#time def treeT_J009_part021 : IntSourceTree :=
  (.node 102 (sourceLit (List.headD (raw_ints% [1974764332059196196553118568859375]) 0) 31 true) treeT_J009_part017 treeT_J009_part020)

#time def treeT_J009_part022 : IntSourceTree :=
  (.node 131 (sourceLit (List.headD (raw_ints% [15978702988162128091176249696635175]) 0) 33 true) (.node 129 (sourceLit (List.headD (raw_ints% [87030659524789909254198334336875]) 0) 37 true) (.node 128 (sourceLit (List.headD (raw_ints% [193371711539011835980524777728325]) 0) 36 true) (.node 127 (sourceLit (List.headD (raw_ints% [879381587095783168549686075667125]) 0) 34 true) .empty .empty) .empty) (.node 130 (sourceLit (List.headD (raw_ints% [79592141616688207608540357043125]) 0) 37 true) .empty .empty)) (.node 133 (sourceLit (List.headD (raw_ints% [14283694674732000702363480645233175]) 0) 34 false) (.node 132 (sourceLit (List.headD (raw_ints% [34365952735429861602939855097125]) 0) 38 true) .empty .empty) (.node 134 (sourceLit (List.headD (raw_ints% [61063469736507605327537759056875]) 0) 37 true) .empty .empty)))

#time def treeT_J009_part023 : IntSourceTree :=
  (.node 140 (sourceLit (List.headD (raw_ints% [188118851696980722327309062866875]) 0) 35 true) (.node 138 (sourceLit (List.headD (raw_ints% [202929575408542713759391201699575]) 0) 35 true) (.node 137 (sourceLit (List.headD (raw_ints% [3305198796369105752203551589125]) 0) 41 true) (.node 136 (sourceLit (List.headD (raw_ints% [55284521586028817593090076221725]) 0) 37 true) .empty .empty) .empty) (.node 139 (sourceLit (List.headD (raw_ints% [1561338789191988473900248135745625]) 0) 32 true) .empty .empty)) (.node 142 (sourceLit (List.headD (raw_ints% [175774941070087555076252867074125]) 0) 35 true) (.node 141 (sourceLit (List.headD (raw_ints% [726729021199907090725080994898625]) 0) 33 true) .empty .empty) (.node 143 (sourceLit (List.headD (raw_ints% [681316322622406549765922948587875]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part024 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [231953795417710642491044145941625]) 0) 35 true) treeT_J009_part022 treeT_J009_part023)

#time def treeT_J009_part025 : IntSourceTree :=
  (.node 149 (sourceLit (List.headD (raw_ints% [1157933988705762170413457386064625]) 0) 32 true) (.node 147 (sourceLit (List.headD (raw_ints% [2434579917500733666800177581929675]) 0) 31 true) (.node 146 (sourceLit (List.headD (raw_ints% [156241339196071791985681095166275]) 0) 35 true) (.node 145 (sourceLit (List.headD (raw_ints% [80302878488062071737502973777125]) 0) 36 true) .empty .empty) .empty) (.node 148 (sourceLit (List.headD (raw_ints% [148336408668613242062391542361225]) 0) 35 true) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [552634516744059083448788354415735]) 0) 33 true) (.node 150 (sourceLit (List.headD (raw_ints% [141355490730344989049517198407775]) 0) 35 true) .empty .empty) (.node 152 (sourceLit (List.headD (raw_ints% [135134489810143048453548039173025]) 0) 35 true) .empty .empty)))

#time def treeT_J009_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [239798737993179913384787572729107]) 0) 34 true) (.node 156 (sourceLit (List.headD (raw_ints% [248990175638775783152337638250009]) 0) 34 true) (.node 155 (sourceLit (List.headD (raw_ints% [2031353889784938517682756887130025]) 0) 31 true) (.node 154 (sourceLit (List.headD (raw_ints% [259094546991076349500776848930625]) 0) 34 true) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [977155518123484197794017132274325]) 0) 32 true) .empty .empty)) (.node 167 (sourceLit (List.headD (raw_ints% [1545838787008401456793117833290925]) 0) 34 true) (.node 159 (sourceLit (List.headD (raw_ints% [942019117789180273810926862451625]) 0) 32 true) .empty .empty) (.node 168 (sourceLit (List.headD (raw_ints% [2555725982865582651415167838586625]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [132268375187062177743371196540945]) 0) 35 true) treeT_J009_part025 treeT_J009_part026)

#time def treeT_J009_part028 : IntSourceTree :=
  (.node 144 (sourceLit (List.headD (raw_ints% [165288397861181713153842219301875]) 0) 35 true) treeT_J009_part024 treeT_J009_part027)

#time def treeT_J009_part029 : IntSourceTree :=
  (.node 126 (sourceLit (List.headD (raw_ints% [259332237766395953773279344382275]) 0) 36 true) treeT_J009_part021 treeT_J009_part028)

#time def treeT_J009_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [882165025417260214947739809462075]) 0) 31 true) treeT_J009_part014 treeT_J009_part029)

#time def treeT_J009_part031 : IntSourceTree :=
  (.node 174 (sourceLit (List.headD (raw_ints% [57796164895469432053132115990567325]) 0) 33 false) (.node 172 (sourceLit (List.headD (raw_ints% [46026384450494397584122405406657025]) 0) 33 true) (.node 171 (sourceLit (List.headD (raw_ints% [221519063303268675007694563807875]) 0) 36 true) (.node 170 (sourceLit (List.headD (raw_ints% [6963219283542865696638781216610175]) 0) 31 false) .empty .empty) .empty) (.node 173 (sourceLit (List.headD (raw_ints% [376321383259872451437151305815625]) 0) 35 true) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [624570214481023227197557815163125]) 0) 34 true) (.node 175 (sourceLit (List.headD (raw_ints% [330409394238051777917590280984025]) 0) 35 true) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [1185940551488768013087238125175425]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part032 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [926496512051066947935027418741875]) 0) 33 true) (.node 181 (sourceLit (List.headD (raw_ints% [996193622111444778705390119512125]) 0) 33 true) (.node 180 (sourceLit (List.headD (raw_ints% [1036293277412436222689308185762375]) 0) 33 true) (.node 179 (sourceLit (List.headD (raw_ints% [1080707774677223543002096729688475]) 0) 33 true) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [3839067837540060529247529390329625]) 0) 31 true) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [867813402118841780510434500753975]) 0) 33 true) (.node 184 (sourceLit (List.headD (raw_ints% [1791922089722994815092407227559375]) 0) 32 true) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [13468234209648999736860411279812325]) 0) 29 true) .empty .empty)))

#time def treeT_J009_part033 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [9041963665625578299106572232530375]) 0) 30 true) treeT_J009_part031 treeT_J009_part032)

#time def treeT_J009_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [1436426973758509937830661921789085]) 0) 32 true) (.node 190 (sourceLit (List.headD (raw_ints% [3016892578491328474278503732635065]) 0) 31 true) (.node 189 (sourceLit (List.headD (raw_ints% [773964186441914068578633971890575]) 0) 33 true) (.node 188 (sourceLit (List.headD (raw_ints% [3180121416501874601223629049190875]) 0) 31 true) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [735677233140013084299661607721825]) 0) 33 true) .empty .empty)) (.node 194 (sourceLit (List.headD (raw_ints% [10978396654647377273612648914749735]) 0) 29 true) (.node 193 (sourceLit (List.headD (raw_ints% [1403466437641369500998472173060475]) 0) 32 true) .empty .empty) (.node 195 (sourceLit (List.headD (raw_ints% [1342773589612301862340391641501641]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part035 : IntSourceTree :=
  (.node 209 (sourceLit (List.headD (raw_ints% [1859480706667263377381581163891625]) 0) 34 true) (.node 199 (sourceLit (List.headD (raw_ints% [1238584170881975816947317553064781]) 0) 32 true) (.node 198 (sourceLit (List.headD (raw_ints% [5051040883992252819782543523829275]) 0) 30 true) (.node 197 (sourceLit (List.headD (raw_ints% [1288117797039511617111617786384283]) 0) 32 true) .empty .empty) .empty) (.node 208 (sourceLit (List.headD (raw_ints% [1159095363930377784832068277834275]) 0) 35 true) .empty .empty)) (.node 211 (sourceLit (List.headD (raw_ints% [38920625259867121878991280609880525]) 0) 32 false) (.node 210 (sourceLit (List.headD (raw_ints% [98158682315310054916102668368325]) 0) 38 true) .empty .empty) (.node 212 (sourceLit (List.headD (raw_ints% [152787157832408951801814853613625]) 0) 37 true) .empty .empty)))

#time def treeT_J009_part036 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [657376556411195678845457493501825]) 0) 33 true) treeT_J009_part034 treeT_J009_part035)

#time def treeT_J009_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [817572100143024412325175092312025]) 0) 33 true) treeT_J009_part033 treeT_J009_part036)

#time def treeT_J009_part038 : IntSourceTree :=
  (.node 218 (sourceLit (List.headD (raw_ints% [780081400671682585568455721776275]) 0) 34 true) (.node 216 (sourceLit (List.headD (raw_ints% [219840351065994142731410128540575]) 0) 36 true) (.node 215 (sourceLit (List.headD (raw_ints% [58260072486304853338114204282450575]) 0) 34 false) (.node 214 (sourceLit (List.headD (raw_ints% [254194443786857240782075787701875]) 0) 36 true) .empty .empty) .empty) (.node 217 (sourceLit (List.headD (raw_ints% [413037491513400459056530513459125]) 0) 35 true) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [704470071283262098347478603954725]) 0) 34 true) (.node 219 (sourceLit (List.headD (raw_ints% [5919286087241601351306075961039125]) 0) 31 true) .empty .empty) (.node 221 (sourceLit (List.headD (raw_ints% [1345857533624965354653535376626125]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [8599074374647532403260056115952975]) 0) 30 true) (.node 225 (sourceLit (List.headD (raw_ints% [1149499061818498241192383437342375]) 0) 33 true) (.node 224 (sourceLit (List.headD (raw_ints% [595919716328703521627342980138125]) 0) 34 true) (.node 223 (sourceLit (List.headD (raw_ints% [2476435192295247429715683493153875]) 0) 32 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [555330723726698196539072310421425]) 0) 34 true) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [1011093713898056215405085831563125]) 0) 33 true) (.node 228 (sourceLit (List.headD (raw_ints% [520899282805797928200392007589575]) 0) 34 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [491253204981224090479599575075025]) 0) 34 true) .empty .empty)))

#time def treeT_J009_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [644643739971269668552884385363875]) 0) 34 true) treeT_J009_part038 treeT_J009_part039)

#time def treeT_J009_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [844793238334750296035716365001623]) 0) 33 true) (.node 234 (sourceLit (List.headD (raw_ints% [885277343659216801996918475199225]) 0) 33 true) (.node 233 (sourceLit (List.headD (raw_ints% [907353473010261226857177135625305]) 0) 33 true) (.node 232 (sourceLit (List.headD (raw_ints% [465408253519726987392565529375775]) 0) 34 true) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [6915688875077500238247135140489685]) 0) 30 true) .empty .empty)) (.node 238 (sourceLit (List.headD (raw_ints% [808520321053151790342042640926069]) 0) 33 true) (.node 237 (sourceLit (List.headD (raw_ints% [1652350707521298517587812841732975]) 0) 32 true) .empty .empty) (.node 239 (sourceLit (List.headD (raw_ints% [3167002648413892272160689798926025]) 0) 31 true) .empty .empty)))

#time def treeT_J009_part042 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [299036481396375025199075660198128125]) 0) 33 true) (.node 252 (sourceLit (List.headD (raw_ints% [42473504855180759731556843008268775]) 0) 34 false) (.node 251 (sourceLit (List.headD (raw_ints% [563750395219211764321126783138725]) 0) 36 true) (.node 250 (sourceLit (List.headD (raw_ints% [36714910590219079734744079838876175]) 0) 31 true) .empty .empty) .empty) (.node 253 (sourceLit (List.headD (raw_ints% [845975879399399162977367523093375]) 0) 35 true) .empty .empty)) (.node 256 (sourceLit (List.headD (raw_ints% [117144715187090729903425966380064275]) 0) 34 false) (.node 255 (sourceLit (List.headD (raw_ints% [686368380909377185210712869823475]) 0) 35 true) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [2331505065567138270615323931473775]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part043 : IntSourceTree :=
  (.node 249 (sourceLit (List.headD (raw_ints% [220796464420767366847830646013625]) 0) 38 true) treeT_J009_part041 treeT_J009_part042)

#time def treeT_J009_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [1911623545003210307380927023803595]) 0) 32 true) treeT_J009_part040 treeT_J009_part043)

#time def treeT_J009_part045 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [7538759890653299785810735756486275]) 0) 37 true) treeT_J009_part037 treeT_J009_part044)

#time def treeT_J009_part046 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [1652078447834011726276510122713625]) 0) 33 true) (.node 261 (sourceLit (List.headD (raw_ints% [1821686663021603614684524296306775]) 0) 33 true) (.node 260 (sourceLit (List.headD (raw_ints% [3846699532416728905927459589514375]) 0) 32 true) (.node 259 (sourceLit (List.headD (raw_ints% [2039617828009506799271726157416625]) 0) 33 true) .empty .empty) .empty) (.node 262 (sourceLit (List.headD (raw_ints% [6927792431459662307980753622679375]) 0) 31 true) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [1515865463195972305998937419798525]) 0) 33 true) (.node 264 (sourceLit (List.headD (raw_ints% [3160948294867500044338959758748375]) 0) 32 true) .empty .empty) (.node 266 (sourceLit (List.headD (raw_ints% [23315735768542943981295858715143675]) 0) 29 true) .empty .empty)))

#time def treeT_J009_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [2386820116247910676931192125818105]) 0) 32 true) (.node 270 (sourceLit (List.headD (raw_ints% [5071857132693121248962182919869935]) 0) 31 true) (.node 269 (sourceLit (List.headD (raw_ints% [1309632944781277644222934058467725]) 0) 33 true) (.node 268 (sourceLit (List.headD (raw_ints% [1354738239536414450509106766690525]) 0) 33 true) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [1229335586784883277618736692578275]) 0) 33 true) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [18056914481680981985817019425260025]) 0) 29 true) (.node 273 (sourceLit (List.headD (raw_ints% [2319799590516446398142052061945725]) 0) 32 true) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [2198335785024565345647282259295259]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [1403750794763768373831114149373675]) 0) 33 true) treeT_J009_part046 treeT_J009_part047)

#time def treeT_J009_part049 : IntSourceTree :=
  (.node 291 (sourceLit (List.headD (raw_ints% [18908883962521550403433840112189175]) 0) 34 true) (.node 279 (sourceLit (List.headD (raw_ints% [1995497113330631344420853010639495]) 0) 32 true) (.node 278 (sourceLit (List.headD (raw_ints% [8167764776178135320919959210034525]) 0) 30 true) (.node 277 (sourceLit (List.headD (raw_ints% [2091055156299489567031247673622209]) 0) 32 true) .empty .empty) .empty) (.node 290 (sourceLit (List.headD (raw_ints% [343434246526224678779558623658925]) 0) 38 true) .empty .empty)) (.node 293 (sourceLit (List.headD (raw_ints% [72628544417793958874799786034213875]) 0) 35 false) (.node 292 (sourceLit (List.headD (raw_ints% [102740809346700703129827982381275]) 0) 39 true) .empty .empty) (.node 294 (sourceLit (List.headD (raw_ints% [147945358903135480548822933847875]) 0) 38 true) .empty .empty)))

#time def treeT_J009_part050 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [333786939181561175231061888365475]) 0) 36 true) (.node 298 (sourceLit (List.headD (raw_ints% [387855916223863921261717052424375]) 0) 36 true) (.node 297 (sourceLit (List.headD (raw_ints% [14694719084825516295310312111690425]) 0) 38 false) (.node 296 (sourceLit (List.headD (raw_ints% [116632007460845760619825685320725]) 0) 38 true) .empty .empty) .empty) (.node 299 (sourceLit (List.headD (raw_ints% [2868287425997612432301326166953625]) 0) 33 true) .empty .empty)) (.node 302 (sourceLit (List.headD (raw_ints% [294260730762583486532909977735725]) 0) 36 true) (.node 301 (sourceLit (List.headD (raw_ints% [1250420999395881775636962106444125]) 0) 34 true) .empty .empty) (.node 303 (sourceLit (List.headD (raw_ints% [1112839309791103719566267532381375]) 0) 34 true) .empty .empty)))

#time def treeT_J009_part051 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [89324138470669969634297466120144675]) 0) 36 true) treeT_J009_part049 treeT_J009_part050)

#time def treeT_J009_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [4286182649432717522865305166482385]) 0) 31 true) treeT_J009_part048 treeT_J009_part051)

#time def treeT_J009_part053 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [1698382765174772685613127701817925]) 0) 33 true) (.node 307 (sourceLit (List.headD (raw_ints% [3679165348473852894508950649797675]) 0) 32 true) (.node 306 (sourceLit (List.headD (raw_ints% [240133684867318527364966277344275]) 0) 36 true) (.node 305 (sourceLit (List.headD (raw_ints% [125715577065562612696661020087875]) 0) 37 true) .empty .empty) .empty) (.node 308 (sourceLit (List.headD (raw_ints% [220712877989492611407680535446025]) 0) 36 true) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [790058396922477735395313974016585]) 0) 34 true) (.node 310 (sourceLit (List.headD (raw_ints% [204594934950013388435833620848175]) 0) 36 true) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [190981833316289072556542790800625]) 0) 36 true) .empty .empty)))

#time def treeT_J009_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [320633708811584444172301258174035]) 0) 35 true) (.node 316 (sourceLit (List.headD (raw_ints% [338385636672453762402891473573409]) 0) 35 true) (.node 315 (sourceLit (List.headD (raw_ints% [2785306401650870436892471071192585]) 0) 32 true) (.node 314 (sourceLit (List.headD (raw_ints% [358630561714307399036283396686625]) 0) 35 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [1316915970955709502638746162374705]) 0) 33 true) .empty .empty)) (.node 331 (sourceLit (List.headD (raw_ints% [2183723576990585665915342206132675]) 0) 36 true) (.node 319 (sourceLit (List.headD (raw_ints% [1250190531941060762189817352777125]) 0) 33 true) .empty .empty) (.node 332 (sourceLit (List.headD (raw_ints% [80291272780223860538424523232647125]) 0) 34 true) .empty .empty)))

#time def treeT_J009_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [46233332601176545314812968443525]) 0) 38 true) treeT_J009_part053 treeT_J009_part054)

#time def treeT_J009_part056 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [7541088607221896394279391181814351225]) 0) 30 false) (.node 336 (sourceLit (List.headD (raw_ints% [831737822952450486977805695341221675]) 0) 34 true) (.node 335 (sourceLit (List.headD (raw_ints% [1680757361540790503570454071742525]) 0) 35 true) (.node 334 (sourceLit (List.headD (raw_ints% [880064836738726696197473948471839125]) 0) 33 false) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [5132943411926990409053519929052625]) 0) 33 true) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [7626450171573720823277845078300125]) 0) 32 true) (.node 339 (sourceLit (List.headD (raw_ints% [4166076831572315940915746681373375]) 0) 33 true) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [3518904363883375189012465917540825]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [2438388163113328064008346288134725]) 0) 33 true) (.node 345 (sourceLit (List.headD (raw_ints% [2708769462825260512597731150503475]) 0) 33 true) (.node 344 (sourceLit (List.headD (raw_ints% [5741766183461329712191180500302625]) 0) 32 true) (.node 343 (sourceLit (List.headD (raw_ints% [3056093244367324058250049521057975]) 0) 33 true) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [41050639689025113719394583569848325]) 0) 29 true) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [2221773103050604138299954508668675]) 0) 33 true) (.node 348 (sourceLit (List.headD (raw_ints% [1162213554468719221999921941553575]) 0) 34 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [8515204988705060235942838694673465]) 0) 31 true) .empty .empty)))

#time def treeT_J009_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [13078943558874446102210640080426625]) 0) 31 true) treeT_J009_part056 treeT_J009_part057)

#time def treeT_J009_part059 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [2441730019695023337177127913107425]) 0) 35 true) treeT_J009_part055 treeT_J009_part058)

#time def treeT_J009_part060 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [264039682876327051162291785643875]) 0) 36 true) treeT_J009_part052 treeT_J009_part059)

#time def treeT_J009_part061 : IntSourceTree :=
  (.node 258 (sourceLit (List.headD (raw_ints% [17392435791232051080511380628853625]) 0) 30 true) treeT_J009_part045 treeT_J009_part060)

#time def treeT_J009_part062 : IntSourceTree :=
  (.node 169 (sourceLit (List.headD (raw_ints% [275909506247308317440745693779775]) 0) 36 true) treeT_J009_part030 treeT_J009_part061)

#time def treeT_J009_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [6855042957170764224704579118287955]) 0) 31 true) (.node 354 (sourceLit (List.headD (raw_ints% [29286018101923800416551460260909575]) 0) 29 true) (.node 353 (sourceLit (List.headD (raw_ints% [3791619075604803923667317243674275]) 0) 32 true) (.node 352 (sourceLit (List.headD (raw_ints% [3933647059131911206231319666314575]) 0) 32 true) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [3539753202404353038933252087690741]) 0) 32 true) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [3134642227654719762335967120145065]) 0) 32 true) (.node 358 (sourceLit (List.headD (raw_ints% [12902890759113216721299979387960755]) 0) 30 true) (.node 357 (sourceLit (List.headD (raw_ints% [3323115030459770631415015903552335]) 0) 32 true) .empty .empty) .empty) (.node 372 (sourceLit (List.headD (raw_ints% [1772760339603782853396030276607575]) 0) 37 true) .empty .empty)))

#time def treeT_J009_part064 : IntSourceTree :=
  (.node 378 (sourceLit (List.headD (raw_ints% [3581519747031534724006651719355125]) 0) 34 true) (.node 376 (sourceLit (List.headD (raw_ints% [1214229331697407461091151330459625]) 0) 36 true) (.node 375 (sourceLit (List.headD (raw_ints% [1237361390621406574734663812952417825]) 0) 34 false) (.node 374 (sourceLit (List.headD (raw_ints% [1849948584082481414981836177715925]) 0) 36 true) .empty .empty) .empty) (.node 377 (sourceLit (List.headD (raw_ints% [949295575631054617340288192234745075]) 0) 35 true) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [2830929074846071239991499127911475]) 0) 34 true) (.node 379 (sourceLit (List.headD (raw_ints% [7552561756925886844008596486482165725]) 0) 31 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [5125608172781957272003920865411875]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part065 : IntSourceTree :=
  (.node 373 (sourceLit (List.headD (raw_ints% [19114977149752227426653038658357625]) 0) 38 true) treeT_J009_part063 treeT_J009_part064)

#time def treeT_J009_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [26333978295129702141358780970657625]) 0) 30 true) (.node 385 (sourceLit (List.headD (raw_ints% [3730316950412327909044604178896625]) 0) 33 true) (.node 384 (sourceLit (List.headD (raw_ints% [1999934512862015853600882378482475]) 0) 34 true) (.node 383 (sourceLit (List.headD (raw_ints% [8627586319710031223945569950901125]) 0) 32 true) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [1748234723355986403137866041126375]) 0) 34 true) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [2950471452700104202386560064396375]) 0) 33 true) (.node 388 (sourceLit (List.headD (raw_ints% [1555536651155357618377624146350625]) 0) 34 true) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [1403393363250550584556620025275975]) 0) 34 true) .empty .empty)))

#time def treeT_J009_part067 : IntSourceTree :=
  (.node 396 (sourceLit (List.headD (raw_ints% [2186210655714537989321686193397105]) 0) 33 true) (.node 394 (sourceLit (List.headD (raw_ints% [2357096828747574327522183656927775]) 0) 33 true) (.node 393 (sourceLit (List.headD (raw_ints% [2454180415894261756157304676121775]) 0) 33 true) (.node 392 (sourceLit (List.headD (raw_ints% [1280256039150174647128430077790025]) 0) 34 true) .empty .empty) .empty) (.node 395 (sourceLit (List.headD (raw_ints% [18144792495320318668981575976139235]) 0) 30 true) .empty .empty)) (.node 398 (sourceLit (List.headD (raw_ints% [2040580195213432854725810870856195]) 0) 33 true) (.node 397 (sourceLit (List.headD (raw_ints% [4221211015259345219427086793538545]) 0) 32 true) .empty .empty) (.node 399 (sourceLit (List.headD (raw_ints% [7902128631348973672540709976852255]) 0) 31 true) .empty .empty)))

#time def treeT_J009_part068 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [5354971401015149294361582798607125]) 0) 32 true) treeT_J009_part066 treeT_J009_part067)

#time def treeT_J009_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [2341861440833041242880826006597925]) 0) 34 true) treeT_J009_part065 treeT_J009_part068)

#time def treeT_J009_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [68296005447609391904057835484838036025]) 0) 30 true) (.node 416 (sourceLit (List.headD (raw_ints% [3306460604195263636447133321246057325]) 0) 34 false) (.node 415 (sourceLit (List.headD (raw_ints% [5719036974789135156356890639121175]) 0) 35 true) (.node 414 (sourceLit (List.headD (raw_ints% [2103423374322869251503268422606727125]) 0) 33 true) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [14294725895231528968404901358301375]) 0) 33 true) .empty .empty)) (.node 420 (sourceLit (List.headD (raw_ints% [3780094103548730282415937165780232925]) 0) 33 false) (.node 419 (sourceLit (List.headD (raw_ints% [10160002156553822955110860196047125]) 0) 33 true) .empty .empty) (.node 421 (sourceLit (List.headD (raw_ints% [7804811935500909770953530594105075]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part071 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [4554550730310617548543117876370775]) 0) 33 true) (.node 425 (sourceLit (List.headD (raw_ints% [5290968588622802901805798363426425]) 0) 33 true) (.node 424 (sourceLit (List.headD (raw_ints% [11513406455958732735699959401499625]) 0) 32 true) (.node 423 (sourceLit (List.headD (raw_ints% [6311352518964840913273254505333725]) 0) 33 true) .empty .empty) .empty) (.node 426 (sourceLit (List.headD (raw_ints% [78319502724169379370032750154843675]) 0) 29 true) .empty .empty)) (.node 429 (sourceLit (List.headD (raw_ints% [4000373501570826335210542076733825]) 0) 33 true) (.node 428 (sourceLit (List.headD (raw_ints% [17036269859379948365359405438229025]) 0) 31 true) .empty .empty) (.node 430 (sourceLit (List.headD (raw_ints% [15088566632895773383149641820497535]) 0) 31 true) .empty .empty)))

#time def treeT_J009_part072 : IntSourceTree :=
  (.node 422 (sourceLit (List.headD (raw_ints% [27925921823381212073820726842868375]) 0) 31 true) treeT_J009_part070 treeT_J009_part071)

#time def treeT_J009_part073 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [705609346134347152767312303615705]) 0) 35 true) (.node 434 (sourceLit (List.headD (raw_ints% [49247755206692575780482289374987225]) 0) 29 true) (.node 433 (sourceLit (List.headD (raw_ints% [6450429237596593253360123378645925]) 0) 32 true) (.node 432 (sourceLit (List.headD (raw_ints% [6776295742898387382491845930899675]) 0) 32 true) .empty .empty) .empty) (.node 435 (sourceLit (List.headD (raw_ints% [5888634112585944271155482540020359]) 0) 32 true) .empty .empty)) (.node 438 (sourceLit (List.headD (raw_ints% [20866797362961545034116714960347605]) 0) 30 true) (.node 437 (sourceLit (List.headD (raw_ints% [5421727592398381325871728870036085]) 0) 32 true) .empty .empty) (.node 439 (sourceLit (List.headD (raw_ints% [5027678553199011656567276363279715]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part074 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [3664536540853875857559680534067825]) 0) 35 true) (.node 458 (sourceLit (List.headD (raw_ints% [5356603074099997122199124819473125]) 0) 35 true) (.node 457 (sourceLit (List.headD (raw_ints% [132992380619572445430856922296275075]) 0) 40 false) (.node 456 (sourceLit (List.headD (raw_ints% [2252403821545863847632869654330775]) 0) 37 true) .empty .empty) .empty) (.node 459 (sourceLit (List.headD (raw_ints% [37924283602267639374033215985660100875]) 0) 32 true) .empty .empty)) (.node 462 (sourceLit (List.headD (raw_ints% [2731475247333934264036352293753575]) 0) 35 true) (.node 461 (sourceLit (List.headD (raw_ints% [7565313815270242522103878252425877725]) 0) 33 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [9649167751835590424937578445983625]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part075 : IntSourceTree :=
  (.node 455 (sourceLit (List.headD (raw_ints% [1670392382472137913118966117779572475]) 0) 35 true) treeT_J009_part073 treeT_J009_part074)

#time def treeT_J009_part076 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [3569390080586871400871878860111375]) 0) 33 true) treeT_J009_part072 treeT_J009_part075)

#time def treeT_J009_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [11740352697135239489991114299753175]) 0) 35 true) treeT_J009_part069 treeT_J009_part076)

#time def treeT_J009_part078 : IntSourceTree :=
  (.node 469 (sourceLit (List.headD (raw_ints% [11135326953979739960586285309436275]) 0) 32 true) (.node 467 (sourceLit (List.headD (raw_ints% [25992762214519838614336984592093025]) 0) 31 true) (.node 466 (sourceLit (List.headD (raw_ints% [1771366932633408249333966161150025]) 0) 35 true) (.node 465 (sourceLit (List.headD (raw_ints% [972886188193300603331919402825375]) 0) 36 true) .empty .empty) .empty) (.node 468 (sourceLit (List.headD (raw_ints% [1499507039577629965082746865010075]) 0) 35 true) .empty .empty)) (.node 471 (sourceLit (List.headD (raw_ints% [4866797615940312044394029510945205]) 0) 33 true) (.node 470 (sourceLit (List.headD (raw_ints% [1298490069160137875326961025728925]) 0) 35 true) .empty .empty) (.node 472 (sourceLit (List.headD (raw_ints% [1144567020718348376871724391160675]) 0) 35 true) .empty .empty)))

#time def treeT_J009_part079 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [1690573698592474235572958999589945]) 0) 34 true) (.node 476 (sourceLit (List.headD (raw_ints% [1851211728435703140916898173311627]) 0) 34 true) (.node 475 (sourceLit (List.headD (raw_ints% [15551481355686128555750356699423995]) 0) 31 true) (.node 474 (sourceLit (List.headD (raw_ints% [2046666204424509462918969860859075]) 0) 34 true) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [7068538522890209224849910064312735]) 0) 32 true) .empty .empty)) (.node 496 (sourceLit (List.headD (raw_ints% [9988030134083815288922997792364347225]) 0) 34 true) (.node 479 (sourceLit (List.headD (raw_ints% [6482334365806285680788002491747675]) 0) 32 true) .empty .empty) (.node 497 (sourceLit (List.headD (raw_ints% [57782196394236114155846927580283425]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part080 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [1080528831751031406583635313694475]) 0) 35 true) treeT_J009_part078 treeT_J009_part079)

#time def treeT_J009_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [15540449459706633199017563844694875]) 0) 33 true) (.node 501 (sourceLit (List.headD (raw_ints% [21511480391330097089523913678437525]) 0) 33 true) (.node 500 (sourceLit (List.headD (raw_ints% [5213047213227046207056144143930041725]) 0) 36 true) (.node 499 (sourceLit (List.headD (raw_ints% [32692822436246154022482138359737875]) 0) 33 true) .empty .empty) .empty) (.node 502 (sourceLit (List.headD (raw_ints% [60550436443985321388904846746249890175]) 0) 31 false) .empty .empty)) (.node 505 (sourceLit (List.headD (raw_ints% [11954703435788497336883690143978575]) 0) 33 true) (.node 504 (sourceLit (List.headD (raw_ints% [27083264551383628964050354382434875]) 0) 32 true) .empty .empty) (.node 506 (sourceLit (List.headD (raw_ints% [170739361453315575082938616968452325]) 0) 29 true) .empty .empty)))

#time def treeT_J009_part082 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [12690894720862860795084272112881145]) 0) 32 true) (.node 510 (sourceLit (List.headD (raw_ints% [29452741183023186459195499417247565]) 0) 31 true) (.node 509 (sourceLit (List.headD (raw_ints% [7995682815050213385451432843346775]) 0) 33 true) (.node 508 (sourceLit (List.headD (raw_ints% [34949254569659728863314563745957025]) 0) 31 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [6818530472694231601743809345720025]) 0) 33 true) .empty .empty)) (.node 514 (sourceLit (List.headD (raw_ints% [89059935257439444262223030777905575]) 0) 29 true) (.node 513 (sourceLit (List.headD (raw_ints% [11862643093896980776587466879924875]) 0) 32 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [10484695522810131432196276346852241]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part083 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [9616384730756648446128611412829425]) 0) 33 true) treeT_J009_part081 treeT_J009_part082)

#time def treeT_J009_part084 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [340664400956493760146452812347609389625]) 0) 30 false) treeT_J009_part080 treeT_J009_part083)

#time def treeT_J009_part085 : IntSourceTree :=
  (.node 539 (sourceLit (List.headD (raw_ints% [416512968161029038894519244318929591375]) 0) 31 false) (.node 519 (sourceLit (List.headD (raw_ints% [8496911035540782228016395633439845]) 0) 32 true) (.node 518 (sourceLit (List.headD (raw_ints% [35681510820160128764682565554154275]) 0) 30 true) (.node 517 (sourceLit (List.headD (raw_ints% [9387966235087243801463456516456931]) 0) 32 true) .empty .empty) .empty) (.node 538 (sourceLit (List.headD (raw_ints% [47068990246036119911448677941337175]) 0) 34 true) .empty .empty)) (.node 541 (sourceLit (List.headD (raw_ints% [90974069226902981835002184555306545325]) 0) 33 true) (.node 540 (sourceLit (List.headD (raw_ints% [25363749354538402307362777291602225]) 0) 34 true) .empty .empty) (.node 542 (sourceLit (List.headD (raw_ints% [16048529896662228561451209090930375]) 0) 34 true) .empty .empty)))

#time def treeT_J009_part086 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [6617370651601388515963117682809275]) 0) 34 true) (.node 546 (sourceLit (List.headD (raw_ints% [8411969570521680838215757821678525]) 0) 34 true) (.node 545 (sourceLit (List.headD (raw_ints% [19300175045837224137394999159831875]) 0) 33 true) (.node 544 (sourceLit (List.headD (raw_ints% [11229031453603808139345191717843625]) 0) 34 true) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [118753837024275897854264647784266275]) 0) 30 true) .empty .empty)) (.node 550 (sourceLit (List.headD (raw_ints% [5398702676729937634797510791888925]) 0) 34 true) (.node 549 (sourceLit (List.headD (raw_ints% [11906963807839994451364139218260375]) 0) 33 true) .empty .empty) (.node 551 (sourceLit (List.headD (raw_ints% [19719145951142562370407440395357155]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part087 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [60569734779488992569754721903141857425]) 0) 32 false) treeT_J009_part085 treeT_J009_part086)

#time def treeT_J009_part088 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [12744674650332493442373806476683975]) 0) 32 true) (.node 555 (sourceLit (List.headD (raw_ints% [57956972546067187150722317379057585]) 0) 30 true) (.node 554 (sourceLit (List.headD (raw_ints% [7769310685047961850749527158206725]) 0) 33 true) (.node 553 (sourceLit (List.headD (raw_ints% [8368779393858735168749730858103245]) 0) 33 true) .empty .empty) .empty) (.node 556 (sourceLit (List.headD (raw_ints% [6782272065938725150362480000228987]) 0) 33 true) .empty .empty)) (.node 559 (sourceLit (List.headD (raw_ints% [22716842088547557403106560570658925]) 0) 31 true) (.node 558 (sourceLit (List.headD (raw_ints% [6006818837902295330317538517277041]) 0) 33 true) .empty .empty) (.node 580 (sourceLit (List.headD (raw_ints% [499921723572661778207417550621810258975]) 0) 32 false) .empty .empty)))

#time def treeT_J009_part089 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [446866240013475597313701356146167675]) 0) 29 true) (.node 584 (sourceLit (List.headD (raw_ints% [121166552823529368768473494160666149725]) 0) 32 false) (.node 583 (sourceLit (List.headD (raw_ints% [48653670126942281046787272519026625]) 0) 33 true) (.node 582 (sourceLit (List.headD (raw_ints% [788342990259209176068922323188702252775]) 0) 31 true) .empty .empty) .empty) (.node 585 (sourceLit (List.headD (raw_ints% [32961422378626735220497076727395925]) 0) 33 true) .empty .empty)) (.node 588 (sourceLit (List.headD (raw_ints% [41902291227308084495475042019154625]) 0) 32 true) (.node 587 (sourceLit (List.headD (raw_ints% [24031493551330074906734419873884675]) 0) 33 true) .empty .empty) (.node 589 (sourceLit (List.headD (raw_ints% [18473799791355340678401037887890325]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part090 : IntSourceTree :=
  (.node 581 (sourceLit (List.headD (raw_ints% [79943517026823512139927195487971375]) 0) 33 true) treeT_J009_part088 treeT_J009_part089)

#time def treeT_J009_part091 : IntSourceTree :=
  (.node 552 (sourceLit (List.headD (raw_ints% [4529396431257534848000360563398675]) 0) 34 true) treeT_J009_part087 treeT_J009_part090)

#time def treeT_J009_part092 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [9906606586611351333611858270498355]) 0) 32 true) treeT_J009_part084 treeT_J009_part091)

#time def treeT_J009_part093 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [2155709003051412529836186063425625]) 0) 35 true) treeT_J009_part077 treeT_J009_part092)

#time def treeT_J009_part094 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [20592547217381715970801832285974659]) 0) 32 true) (.node 593 (sourceLit (List.headD (raw_ints% [24372528356163298007415417627264525]) 0) 32 true) (.node 592 (sourceLit (List.headD (raw_ints% [26747397181422263945730608677833165]) 0) 32 true) (.node 591 (sourceLit (List.headD (raw_ints% [14776280234225518937446233821835675]) 0) 33 true) .empty .empty) .empty) (.node 594 (sourceLit (List.headD (raw_ints% [178741005346040081137768356681398265]) 0) 29 true) .empty .empty)) (.node 597 (sourceLit (List.headD (raw_ints% [17741122028667656799986463484459017]) 0) 32 true) (.node 596 (sourceLit (List.headD (raw_ints% [38143759372844484483498600838060875]) 0) 31 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [66275886382499818774307886259317525]) 0) 30 true) .empty .empty)))

#time def treeT_J009_part095 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [3068681601013131797785164863214675]) 0) 37 true) (.node 624 (sourceLit (List.headD (raw_ints% [4678079834167309113430260100147875]) 0) 37 true) (.node 623 (sourceLit (List.headD (raw_ints% [106114090629837271079834630636480513775]) 0) 35 true) (.node 622 (sourceLit (List.headD (raw_ints% [7986873391270160447309498299630125]) 0) 37 true) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [3787057906205475187269090286244561925]) 0) 38 false) .empty .empty)) (.node 628 (sourceLit (List.headD (raw_ints% [2176765362466085798846412773884425]) 0) 37 true) (.node 627 (sourceLit (List.headD (raw_ints% [41014050373649962432429588545237675]) 0) 33 true) .empty .empty) (.node 629 (sourceLit (List.headD (raw_ints% [14997663709734045022055451400447125]) 0) 34 true) .empty .empty)))

#time def treeT_J009_part096 : IntSourceTree :=
  (.node 599 (sourceLit (List.headD (raw_ints% [15530364316068399093253758435668319]) 0) 32 true) treeT_J009_part094 treeT_J009_part095)

#time def treeT_J009_part097 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [15098004099996611748380754912792585]) 0) 33 true) (.node 633 (sourceLit (List.headD (raw_ints% [8973934466583754285635194247915]) 0) 44 true) (.node 632 (sourceLit (List.headD (raw_ints% [1280860475370998011180734157304625]) 0) 37 true) (.node 631 (sourceLit (List.headD (raw_ints% [5760477916069275847663771741684785]) 0) 35 true) .empty .empty) .empty) (.node 634 (sourceLit (List.headD (raw_ints% [2075402208889417019583236308632225]) 0) 36 true) .empty .empty)) (.node 637 (sourceLit (List.headD (raw_ints% [6349771180627997760281198590344225]) 0) 34 true) (.node 636 (sourceLit (List.headD (raw_ints% [1726284393930373852554919035718209]) 0) 36 true) .empty .empty) (.node 638 (sourceLit (List.headD (raw_ints% [1466787898845670183708615620897747]) 0) 36 true) .empty .empty)))

#time def treeT_J009_part098 : IntSourceTree :=
  (.node 667 (sourceLit (List.headD (raw_ints% [74166317681090142622390855748984925]) 0) 33 true) (.node 665 (sourceLit (List.headD (raw_ints% [116737132314727156409271246477336075]) 0) 33 true) (.node 664 (sourceLit (List.headD (raw_ints% [1818992002900925706045827584344354370125]) 0) 32 true) (.node 663 (sourceLit (List.headD (raw_ints% [206926278393702853267116673069137375]) 0) 33 true) .empty .empty) .empty) (.node 666 (sourceLit (List.headD (raw_ints% [3878394162194420067360862154470577578875]) 0) 29 false) .empty .empty)) (.node 669 (sourceLit (List.headD (raw_ints% [51182691807559404884684170876411275]) 0) 33 true) (.node 668 (sourceLit (List.headD (raw_ints% [122153910267291765234243312161796075]) 0) 32 true) .empty .empty) (.node 670 (sourceLit (List.headD (raw_ints% [174159650076047951201169608078318565]) 0) 31 true) .empty .empty)))

#time def treeT_J009_part099 : IntSourceTree :=
  (.node 639 (sourceLit (List.headD (raw_ints% [5444880536744032671400165711082325]) 0) 34 true) treeT_J009_part097 treeT_J009_part098)

#time def treeT_J009_part100 : IntSourceTree :=
  (.node 630 (sourceLit (List.headD (raw_ints% [1634387139328175380450440887000175]) 0) 37 true) treeT_J009_part096 treeT_J009_part099)

#time def treeT_J009_part101 : IntSourceTree :=
  (.node 676 (sourceLit (List.headD (raw_ints% [82640273427128409503547438464279805]) 0) 31 true) (.node 674 (sourceLit (List.headD (raw_ints% [409374763855992839725619733549959175]) 0) 29 true) (.node 673 (sourceLit (List.headD (raw_ints% [57602542067580574708151568440231475]) 0) 32 true) (.node 672 (sourceLit (List.headD (raw_ints% [65420249475686149616889739189123395]) 0) 32 true) .empty .empty) .empty) (.node 675 (sourceLit (List.headD (raw_ints% [45820323467079628655861729590256541]) 0) 32 true) .empty .empty)) (.node 678 (sourceLit (List.headD (raw_ints% [136916791397596109554690468631697675]) 0) 30 true) (.node 677 (sourceLit (List.headD (raw_ints% [37499978577104306481770945658523671]) 0) 32 true) .empty .empty) (.node 679 (sourceLit (List.headD (raw_ints% [31406848446993046785421941433059585]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part102 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [38107594692934001841080643780409875]) 0) 34 true) (.node 708 (sourceLit (List.headD (raw_ints% [56752194781361456231619553557909525]) 0) 34 true) (.node 707 (sourceLit (List.headD (raw_ints% [3878722274597409267060321591178939480275]) 0) 30 false) (.node 706 (sourceLit (List.headD (raw_ints% [92187679506622102026989927571618675]) 0) 34 true) .empty .empty) .empty) (.node 709 (sourceLit (List.headD (raw_ints% [92158582847823675190132409360901825]) 0) 33 true) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [27277224421308109147522001303732925]) 0) 34 true) (.node 711 (sourceLit (List.headD (raw_ints% [128075826747493744419859434144840285]) 0) 32 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [47041631688122620839908861369393475]) 0) 33 true) .empty .empty)))

#time def treeT_J009_part103 : IntSourceTree :=
  (.node 705 (sourceLit (List.headD (raw_ints% [1940177855899500912038438473504180351725]) 0) 33 true) treeT_J009_part101 treeT_J009_part102)

#time def treeT_J009_part104 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [93357747103643848183489142943039075]) 0) 31 true) (.node 717 (sourceLit (List.headD (raw_ints% [57241188704616418462422644102902905]) 0) 32 true) (.node 716 (sourceLit (List.headD (raw_ints% [32010048315636637835422377304510869]) 0) 33 true) (.node 715 (sourceLit (List.headD (raw_ints% [288590731056019945738573694247618495]) 0) 30 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [25765675386338945012102020691341695]) 0) 33 true) .empty .empty)) (.node 747 (sourceLit (List.headD (raw_ints% [294584400345398265485568854537489775]) 0) 33 true) (.node 746 (sourceLit (List.headD (raw_ints% [65964085550978449252590893306604348834075]) 0) 29 true) .empty .empty) (.node 748 (sourceLit (List.headD (raw_ints% [3878966582417943850590790077803263072425]) 0) 31 false) .empty .empty)))

#time def treeT_J009_part105 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [1095957450163931027151463830270632025]) 0) 29 true) (.node 752 (sourceLit (List.headD (raw_ints% [190731404019301339222829129100557175]) 0) 32 true) (.node 751 (sourceLit (List.headD (raw_ints% [114906270547459914127354700559469575]) 0) 33 true) (.node 750 (sourceLit (List.headD (raw_ints% [563109012706541450319889666808896035]) 0) 31 true) .empty .empty) .empty) (.node 753 (sourceLit (List.headD (raw_ints% [160615253302884298472024441989631925]) 0) 32 true) .empty .empty)) (.node 756 (sourceLit (List.headD (raw_ints% [102975228814445768117513127891669345]) 0) 32 true) (.node 755 (sourceLit (List.headD (raw_ints% [118176974118781325550080982294438159]) 0) 32 true) .empty .empty) (.node 757 (sourceLit (List.headD (raw_ints% [90540214685442244859918563559519805]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part106 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [175826087317886420041794043355226825]) 0) 33 true) treeT_J009_part104 treeT_J009_part105)

#time def treeT_J009_part107 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [40999324396465238551485677971173675]) 0) 33 true) treeT_J009_part103 treeT_J009_part106)

#time def treeT_J009_part108 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [37524108224276093236967874562169925]) 0) 33 true) treeT_J009_part100 treeT_J009_part107)

#time def treeT_J009_part109 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [68859246312476209100356699787408475]) 0) 35 true) (.node 788 (sourceLit (List.headD (raw_ints% [118916102782018404626974650489790125]) 0) 35 true) (.node 787 (sourceLit (List.headD (raw_ints% [34921403912787929259825607448891644157175]) 0) 31 true) (.node 759 (sourceLit (List.headD (raw_ints% [71655853098362733262986141332307195]) 0) 32 true) .empty .empty) .empty) (.node 789 (sourceLit (List.headD (raw_ints% [3879150899583639497941170342621984876075]) 0) 32 false) .empty .empty)) (.node 792 (sourceLit (List.headD (raw_ints% [43814523063075902489916349627868325]) 0) 35 true) (.node 791 (sourceLit (List.headD (raw_ints% [217516592979523852950015116332027875]) 0) 33 true) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [35922443082794679595730066932790925]) 0) 35 true) .empty .empty)))

#time def treeT_J009_part110 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [113827485567845694980600770624243245]) 0) 32 true) (.node 797 (sourceLit (List.headD (raw_ints% [148709268924275117772603611680435785]) 0) 32 true) (.node 796 (sourceLit (List.headD (raw_ints% [43083462901572343857329302494963645]) 0) 34 true) (.node 795 (sourceLit (List.headD (raw_ints% [403683359553955540706445068011506765]) 0) 31 true) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [32387269649551649923908271434089055]) 0) 34 true) .empty .empty)) (.node 829 (sourceLit (List.headD (raw_ints% [775502734938260816974003160563094175]) 0) 33 true) (.node 828 (sourceLit (List.headD (raw_ints% [73721774407993802370242004975586551386775]) 0) 31 true) .empty .empty) (.node 830 (sourceLit (List.headD (raw_ints% [15517166707347264533215001260154748400335]) 0) 31 false) .empty .empty)))

#time def treeT_J009_part111 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [59807964453209529960269382009229125]) 0) 34 true) treeT_J009_part109 treeT_J009_part110)

#time def treeT_J009_part112 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [75177032684877443147232985029959355]) 0) 34 true) (.node 834 (sourceLit (List.headD (raw_ints% [3502115264433787961101984737126606375]) 0) 29 true) (.node 833 (sourceLit (List.headD (raw_ints% [540417115706330141366637152056261275]) 0) 32 true) (.node 832 (sourceLit (List.headD (raw_ints% [679334967898794072577231336227554325]) 0) 32 true) .empty .empty) .empty) (.node 835 (sourceLit (List.headD (raw_ints% [360286741506894914132074073779394841]) 0) 32 true) .empty .empty)) (.node 838 (sourceLit (List.headD (raw_ints% [868661433154865704036138209251960715]) 0) 30 true) (.node 837 (sourceLit (List.headD (raw_ints% [254127488527136505998715856400189355]) 0) 32 true) .empty .empty) (.node 839 (sourceLit (List.headD (raw_ints% [187442304098050466128280030140405245]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part113 : IntSourceTree :=
  (.node 874 (sourceLit (List.headD (raw_ints% [420801186799911081446098388037803025]) 0) 33 true) (.node 872 (sourceLit (List.headD (raw_ints% [348338653826197953695666198484061575]) 0) 34 true) (.node 871 (sourceLit (List.headD (raw_ints% [15517601740533223580920901290387412456085]) 0) 32 false) (.node 870 (sourceLit (List.headD (raw_ints% [637784242313308398773289760988277225]) 0) 34 true) .empty .empty) .empty) (.node 873 (sourceLit (List.headD (raw_ints% [535645195567615354194311068496390625]) 0) 33 true) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [274119815703750226417415468789467551]) 0) 33 true) (.node 875 (sourceLit (List.headD (raw_ints% [2694748545325876879689094601103592845]) 0) 30 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [452706992554744427405260268559239055]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part114 : IntSourceTree :=
  (.node 869 (sourceLit (List.headD (raw_ints% [38800462653788720934091587659104268131425]) 0) 33 true) treeT_J009_part112 treeT_J009_part113)

#time def treeT_J009_part115 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [435967699952349758675498897739798225]) 0) 33 true) treeT_J009_part111 treeT_J009_part114)

#time def treeT_J009_part116 : IntSourceTree :=
  (.node 913 (sourceLit (List.headD (raw_ints% [2246292114903253488198692435816231325]) 0) 32 true) (.node 911 (sourceLit (List.headD (raw_ints% [2115169269300883836417660146213310675]) 0) 33 true) (.node 910 (sourceLit (List.headD (raw_ints% [325920867937657032005947702532988893451735]) 0) 31 true) (.node 879 (sourceLit (List.headD (raw_ints% [641006462019174314074936668003474225]) 0) 31 true) .empty .empty) .empty) (.node 912 (sourceLit (List.headD (raw_ints% [31035882816034345955914379812111052466495]) 0) 32 false) .empty .empty)) (.node 915 (sourceLit (List.headD (raw_ints% [1322918005692749411652319478371817259]) 0) 32 true) (.node 914 (sourceLit (List.headD (raw_ints% [13638530993729903373115969454757893625]) 0) 29 true) .empty .empty) (.node 916 (sourceLit (List.headD (raw_ints% [2093332283846857334511230720863918005]) 0) 31 true) .empty .empty)))

#time def treeT_J009_part117 : IntSourceTree :=
  (.node 953 (sourceLit (List.headD (raw_ints% [969888076913434799102142941349360901785]) 0) 38 false) (.node 951 (sourceLit (List.headD (raw_ints% [85359617419547563896717150955844076476955]) 0) 34 true) (.node 919 (sourceLit (List.headD (raw_ints% [569969492814082358475317223987639735]) 0) 32 true) (.node 918 (sourceLit (List.headD (raw_ints% [2752994507283089715205943939221951725]) 0) 30 true) .empty .empty) .empty) (.node 952 (sourceLit (List.headD (raw_ints% [441707653868671470680498486932312275]) 0) 36 true) .empty .empty)) (.node 955 (sourceLit (List.headD (raw_ints% [2735945612101006623356718713413575195]) 0) 32 true) (.node 954 (sourceLit (List.headD (raw_ints% [456372732025835601688148511944607075]) 0) 35 true) .empty .empty) (.node 956 (sourceLit (List.headD (raw_ints% [262199547497249796308726002395587427]) 0) 35 true) .empty .empty)))

#time def treeT_J009_part118 : IntSourceTree :=
  (.node 917 (sourceLit (List.headD (raw_ints% [842351774287864399670946018757680849]) 0) 32 true) treeT_J009_part116 treeT_J009_part117)

#time def treeT_J009_part119 : IntSourceTree :=
  (.node 996 (sourceLit (List.headD (raw_ints% [8850450164557169158915644132790382775]) 0) 31 true) (.node 994 (sourceLit (List.headD (raw_ints% [993179029290350964183967487911200321321465]) 0) 29 false) (.node 959 (sourceLit (List.headD (raw_ints% [527997011315978850282751817804619375]) 0) 33 true) (.node 958 (sourceLit (List.headD (raw_ints% [163249706264957798380011676306417401]) 0) 35 true) .empty .empty) .empty) (.node 995 (sourceLit (List.headD (raw_ints% [5979045706720620215358056712741895941]) 0) 32 true) .empty .empty)) (.node 998 (sourceLit (List.headD (raw_ints% [10372007823053813541641819679215479875]) 0) 30 true) (.node 997 (sourceLit (List.headD (raw_ints% [3352840985668132341268670019571717983]) 0) 32 true) .empty .empty) (.node 999 (sourceLit (List.headD (raw_ints% [2042025807425242415604869596915038681]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [248299705880740981344904957607546691501255]) 0) 33 false) (.node 1038 (sourceLit (List.headD (raw_ints% [2699842160608301147748623314346048379]) 0) 33 true) (.node 1037 (sourceLit (List.headD (raw_ints% [7209824873265056251809673680485703825]) 0) 32 true) (.node 1036 (sourceLit (List.headD (raw_ints% [4930247516731621030123152703159546233]) 0) 33 true) .empty .empty) .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [8260019777789898140510812407997002375]) 0) 31 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [47306591163066636472835569764670150725]) 0) 30 true) (.node 1077 (sourceLit (List.headD (raw_ints% [16368149081258351779223940793066466949]) 0) 32 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [8757342835007962175389623660469154835]) 0) 32 true) .empty .empty)))

#time def treeT_J009_part121 : IntSourceTree :=
  (.node 1035 (sourceLit (List.headD (raw_ints% [993189973072799368210460914786053975622245]) 0) 30 false) treeT_J009_part119 treeT_J009_part120)

#time def treeT_J009_part122 : IntSourceTree :=
  (.node 957 (sourceLit (List.headD (raw_ints% [820312645646056453552985226152339475]) 0) 33 true) treeT_J009_part118 treeT_J009_part121)

#time def treeT_J009_part123 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [189352949228033206150899313532011245]) 0) 33 true) treeT_J009_part115 treeT_J009_part122)

#time def treeT_J009_part124 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [321012718239335238144690684191525565]) 0) 30 true) treeT_J009_part108 treeT_J009_part123)

#time def treeT_J009_part125 : IntSourceTree :=
  (.node 590 (sourceLit (List.headD (raw_ints% [65802969279696769151717614328835435]) 0) 31 true) treeT_J009_part093 treeT_J009_part124)

#time def treeT_J009_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [2044183372415330937354601240992525]) 0) 33 true) treeT_J009_part062 treeT_J009_part125)

#time def treeT_J009 : IntSourceTree := treeT_J009_part126

#time def treeT_J010_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [538697466904725233178550715613375]) 0) 32 true) (.node 5 (sourceLit (List.headD (raw_ints% [317029633243294524137942992259625]) 0) 33 true) (.node 4 (sourceLit (List.headD (raw_ints% [176037839522303984945671502640375]) 0) 34 true) (.node 3 (sourceLit (List.headD (raw_ints% [1607166179224453657560862574087625]) 0) 31 true) .empty .empty) .empty) (.node 6 (sourceLit (List.headD (raw_ints% [145229623637777622929826348683175]) 0) 34 true) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [28117597692624432220587154170375]) 0) 36 true) (.node 9 (sourceLit (List.headD (raw_ints% [59359372906651579132350658804125]) 0) 35 true) (.node 8 (sourceLit (List.headD (raw_ints% [126008493363242825877446135356125]) 0) 34 true) .empty .empty) .empty) (.node 11 (sourceLit (List.headD (raw_ints% [13944238586224680284282210274885375]) 0) 31 false) .empty .empty)))

#time def treeT_J010_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [338731379196161866281778713427125]) 0) 32 true) (.node 15 (sourceLit (List.headD (raw_ints% [181411407024508283141483886796875]) 0) 33 true) (.node 14 (sourceLit (List.headD (raw_ints% [47081136773586364751643603136875]) 0) 35 true) (.node 13 (sourceLit (List.headD (raw_ints% [97985567716721506223258264533125]) 0) 34 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [43780307456268171887120018471475]) 0) 35 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [1273479345233415044001035590206375]) 0) 30 true) (.node 18 (sourceLit (List.headD (raw_ints% [164073177768186636621997367381625]) 0) 33 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [154652136694999066746588587997375]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [12780726223920196463903251895625]) 0) 37 true) treeT_J010_part000 treeT_J010_part001)

#time def treeT_J010_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [133013471116828522438353173993955]) 0) 33 true) (.node 24 (sourceLit (List.headD (raw_ints% [139346186807226785594932938666375]) 0) 33 true) (.node 23 (sourceLit (List.headD (raw_ints% [571233362897838468336782265617625]) 0) 31 true) (.node 22 (sourceLit (List.headD (raw_ints% [146495843536559439390829161971625]) 0) 33 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [272175107733718521924202673794875]) 0) 32 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [127354656031249533592353649726725]) 0) 33 true) (.node 27 (sourceLit (List.headD (raw_ints% [2081717751960503012638642699664325]) 0) 29 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [249485016215415605427013133347425]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [1783393104295647756166434123119175]) 0) 29 true) (.node 33 (sourceLit (List.headD (raw_ints% [461957587246330937761426265249775]) 0) 31 true) (.node 32 (sourceLit (List.headD (raw_ints% [117641558839202813196970313021325]) 0) 33 true) (.node 31 (sourceLit (List.headD (raw_ints% [479582238638135979442456138343565]) 0) 31 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [226863530699918365695245953824675]) 0) 32 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [431052615630388404660255864271425]) 0) 31 true) (.node 36 (sourceLit (List.headD (raw_ints% [219148676093557626917450888679741]) 0) 32 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [212047170919956688485362377759575]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [122259522772474460243370962136675]) 0) 33 true) treeT_J010_part003 treeT_J010_part004)

#time def treeT_J010_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [300867924205097865920329181731575]) 0) 32 true) treeT_J010_part002 treeT_J010_part005)

#time def treeT_J010_part007 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [538697466904725233178550715613375]) 0) 33 true) (.node 46 (sourceLit (List.headD (raw_ints% [317029633243294524137942992259625]) 0) 34 true) (.node 45 (sourceLit (List.headD (raw_ints% [176037839522303984945671502640375]) 0) 35 true) (.node 44 (sourceLit (List.headD (raw_ints% [1607166179224453657560862574087625]) 0) 32 true) .empty .empty) .empty) (.node 47 (sourceLit (List.headD (raw_ints% [145229623637777622929826348683175]) 0) 35 true) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [59359372906651579132350658804125]) 0) 36 true) (.node 49 (sourceLit (List.headD (raw_ints% [126008493363242825877446135356125]) 0) 35 true) .empty .empty) (.node 51 (sourceLit (List.headD (raw_ints% [28117597692624432220587154170375]) 0) 37 true) .empty .empty)))

#time def treeT_J010_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [43780307456268171887120018471475]) 0) 36 true) (.node 55 (sourceLit (List.headD (raw_ints% [47081136773586364751643603136875]) 0) 36 true) (.node 54 (sourceLit (List.headD (raw_ints% [97985567716721506223258264533125]) 0) 35 true) (.node 53 (sourceLit (List.headD (raw_ints% [12780726223920196463903251895625]) 0) 38 true) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [181411407024508283141483886796875]) 0) 34 true) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [164073177768186636621997367381625]) 0) 34 true) (.node 58 (sourceLit (List.headD (raw_ints% [338731379196161866281778713427125]) 0) 33 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [1273479345233415044001035590206375]) 0) 31 true) .empty .empty)))

#time def treeT_J010_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [13944238586224680284282210274885375]) 0) 32 false) treeT_J010_part007 treeT_J010_part008)

#time def treeT_J010_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [272175107733718521924202673794875]) 0) 33 true) (.node 64 (sourceLit (List.headD (raw_ints% [571233362897838468336782265617625]) 0) 32 true) (.node 63 (sourceLit (List.headD (raw_ints% [146495843536559439390829161971625]) 0) 34 true) (.node 62 (sourceLit (List.headD (raw_ints% [300867924205097865920329181731575]) 0) 33 true) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [139346186807226785594932938666375]) 0) 34 true) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [2081717751960503012638642699664325]) 0) 30 true) (.node 67 (sourceLit (List.headD (raw_ints% [133013471116828522438353173993955]) 0) 34 true) .empty .empty) (.node 69 (sourceLit (List.headD (raw_ints% [127354656031249533592353649726725]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [226863530699918365695245953824675]) 0) 33 true) (.node 73 (sourceLit (List.headD (raw_ints% [117641558839202813196970313021325]) 0) 34 true) (.node 72 (sourceLit (List.headD (raw_ints% [479582238638135979442456138343565]) 0) 32 true) (.node 71 (sourceLit (List.headD (raw_ints% [122259522772474460243370962136675]) 0) 34 true) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [461957587246330937761426265249775]) 0) 32 true) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [219148676093557626917450888679741]) 0) 33 true) (.node 76 (sourceLit (List.headD (raw_ints% [1783393104295647756166434123119175]) 0) 30 true) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [431052615630388404660255864271425]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [249485016215415605427013133347425]) 0) 33 true) treeT_J010_part010 treeT_J010_part011)

#time def treeT_J010_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [154652136694999066746588587997375]) 0) 34 true) treeT_J010_part009 treeT_J010_part012)

#time def treeT_J010_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [834809071408629592260435128754075]) 0) 30 true) treeT_J010_part006 treeT_J010_part013)

#time def treeT_J010_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [419978721091422074913849398005125]) 0) 34 true) (.node 87 (sourceLit (List.headD (raw_ints% [1997539599041630959924993222463625]) 0) 32 true) (.node 86 (sourceLit (List.headD (raw_ints% [558921734451438316852859661878325]) 0) 34 true) (.node 85 (sourceLit (List.headD (raw_ints% [40316767061911222919466236932125]) 0) 38 true) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [454910001187867665841859259376575]) 0) 34 true) .empty .empty)) (.node 91 (sourceLit (List.headD (raw_ints% [17743238452250381348752652438349375]) 0) 31 true) (.node 90 (sourceLit (List.headD (raw_ints% [48945447835309196828429490592875]) 0) 37 true) .empty .empty) (.node 92 (sourceLit (List.headD (raw_ints% [43454469161328667977271056445125]) 0) 37 true) .empty .empty)))

#time def treeT_J010_part016 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [536411741532104113571922928161975]) 0) 33 true) (.node 96 (sourceLit (List.headD (raw_ints% [144544239638077287119454394076025]) 0) 35 true) (.node 95 (sourceLit (List.headD (raw_ints% [602473134709263766644582229468125]) 0) 33 true) (.node 94 (sourceLit (List.headD (raw_ints% [157410482809136778670808427193125]) 0) 35 true) .empty .empty) .empty) (.node 97 (sourceLit (List.headD (raw_ints% [1112559876999904398850092380947875]) 0) 32 true) .empty .empty)) (.node 100 (sourceLit (List.headD (raw_ints% [501640574377747479741400881529125]) 0) 33 true) (.node 99 (sourceLit (List.headD (raw_ints% [4146222721905174816507423824627625]) 0) 30 true) .empty .empty) (.node 101 (sourceLit (List.headD (raw_ints% [60788213814269823630044150529675]) 0) 36 true) .empty .empty)))

#time def treeT_J010_part017 : IntSourceTree :=
  (.node 93 (sourceLit (List.headD (raw_ints% [14140209721658123296728726803951625]) 0) 33 false) treeT_J010_part015 treeT_J010_part016)

#time def treeT_J010_part018 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [6627885695518489688935842861771675]) 0) 29 true) (.node 105 (sourceLit (List.headD (raw_ints% [870291618061958414749361857440375]) 0) 32 true) (.node 104 (sourceLit (List.headD (raw_ints% [446637187339010971968383709220125]) 0) 33 true) (.node 103 (sourceLit (List.headD (raw_ints% [1835710030742944459025851188234975]) 0) 31 true) .empty .empty) .empty) (.node 106 (sourceLit (List.headD (raw_ints% [424371276112078619941378580671545]) 0) 33 true) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [1582747719529671801784616432969475]) 0) 31 true) (.node 108 (sourceLit (List.headD (raw_ints% [404699228436064556161059046249095]) 0) 33 true) .empty .empty) (.node 110 (sourceLit (List.headD (raw_ints% [387159101352523674126043636770225]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [688305446706115835863532926618959]) 0) 32 true) (.node 114 (sourceLit (List.headD (raw_ints% [714268940013704139880516550345925]) 0) 32 true) (.node 113 (sourceLit (List.headD (raw_ints% [1456371367306212980008398288124485]) 0) 31 true) (.node 112 (sourceLit (List.headD (raw_ints% [371396532250695027776513535525375]) 0) 33 true) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [5607928291645647248016386120877225]) 0) 29 true) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [664547533454273819184441176959389]) 0) 32 true) (.node 117 (sourceLit (List.headD (raw_ints% [676170244332629675753089129423875]) 0) 32 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [2613611853634477645021611785417325]) 0) 30 true) .empty .empty)))

#time def treeT_J010_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [1516297891085188863973648928435835]) 0) 31 true) treeT_J010_part018 treeT_J010_part019)

#time def treeT_J010_part021 : IntSourceTree :=
  (.node 102 (sourceLit (List.headD (raw_ints% [472112703243436827595525190017875]) 0) 33 true) treeT_J010_part017 treeT_J010_part020)

#time def treeT_J010_part022 : IntSourceTree :=
  (.node 131 (sourceLit (List.headD (raw_ints% [69773297977993961436271827015375]) 0) 37 true) (.node 129 (sourceLit (List.headD (raw_ints% [164450753912312419982206562010225]) 0) 36 true) (.node 128 (sourceLit (List.headD (raw_ints% [729421066068452863373221253425125]) 0) 34 true) (.node 127 (sourceLit (List.headD (raw_ints% [206846055406830346961516656597575]) 0) 36 true) .empty .empty) .empty) (.node 130 (sourceLit (List.headD (raw_ints% [301259975278118916649148080396875]) 0) 35 true) .empty .empty)) (.node 133 (sourceLit (List.headD (raw_ints% [7668435734352117878341951137375]) 0) 40 true) (.node 132 (sourceLit (List.headD (raw_ints% [15843738519237530816517431356617375]) 0) 33 true) .empty .empty) (.node 134 (sourceLit (List.headD (raw_ints% [14336180857091566309175243333017875]) 0) 34 false) .empty .empty)))

#time def treeT_J010_part023 : IntSourceTree :=
  (.node 140 (sourceLit (List.headD (raw_ints% [1436371688335879886253194117210625]) 0) 32 true) (.node 138 (sourceLit (List.headD (raw_ints% [386914248901871266284156833760375]) 0) 34 true) (.node 137 (sourceLit (List.headD (raw_ints% [50381966090904557616167187802275]) 0) 37 true) (.node 136 (sourceLit (List.headD (raw_ints% [210530863842377741751549171335625]) 0) 35 true) .empty .empty) .empty) (.node 139 (sourceLit (List.headD (raw_ints% [186169281881958738474962780390175]) 0) 35 true) .empty .empty)) (.node 142 (sourceLit (List.headD (raw_ints% [671743496823219312160377226743225]) 0) 33 true) (.node 141 (sourceLit (List.headD (raw_ints% [173494218841374206497406146765875]) 0) 35 true) .empty .empty) (.node 143 (sourceLit (List.headD (raw_ints% [162808429853438694102348014023125]) 0) 35 true) .empty .empty)))

#time def treeT_J010_part024 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [55164673017775206959582412028125]) 0) 37 true) treeT_J010_part022 treeT_J010_part023)

#time def treeT_J010_part025 : IntSourceTree :=
  (.node 149 (sourceLit (List.headD (raw_ints% [138672286202407511284352698261185]) 0) 35 true) (.node 147 (sourceLit (List.headD (raw_ints% [145678902497625048751512703338795]) 0) 35 true) (.node 146 (sourceLit (List.headD (raw_ints% [149529127582059973206289795911375]) 0) 35 true) (.node 145 (sourceLit (List.headD (raw_ints% [153645500265892093186725385276875]) 0) 35 true) .empty .empty) .empty) (.node 148 (sourceLit (List.headD (raw_ints% [2273083971778993338148600081053675]) 0) 31 true) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [132449789290024606941336337316775]) 0) 35 true) (.node 150 (sourceLit (List.headD (raw_ints% [1083777687098840590930590166274625]) 0) 32 true) .empty .empty) (.node 152 (sourceLit (List.headD (raw_ints% [518357826223526442265596395046135]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [921287873034870946845922394576325]) 0) 32 true) (.node 156 (sourceLit (List.headD (raw_ints% [1912267593674999745924975998879025]) 0) 31 true) (.node 155 (sourceLit (List.headD (raw_ints% [243702704656892887092635298260625]) 0) 34 true) (.node 154 (sourceLit (List.headD (raw_ints% [497206890029941021123486011437355]) 0) 33 true) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [234578385306279104473041018969609]) 0) 34 true) .empty .empty)) (.node 167 (sourceLit (List.headD (raw_ints% [5787315702861285914354819494083375]) 0) 32 true) (.node 159 (sourceLit (List.headD (raw_ints% [226250181267158565349539399599907]) 0) 34 true) .empty .empty) (.node 168 (sourceLit (List.headD (raw_ints% [1199858442066775109850273993404025]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [126877486705746107289771611252025]) 0) 35 true) treeT_J010_part025 treeT_J010_part026)

#time def treeT_J010_part028 : IntSourceTree :=
  (.node 144 (sourceLit (List.headD (raw_ints% [632238333922552995344534461308675]) 0) 33 true) treeT_J010_part024 treeT_J010_part027)

#time def treeT_J010_part029 : IntSourceTree :=
  (.node 126 (sourceLit (List.headD (raw_ints% [973106912737864609284976589568375]) 0) 34 true) treeT_J010_part021 treeT_J010_part028)

#time def treeT_J010_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [212047170919956688485362377759575]) 0) 33 true) treeT_J010_part014 treeT_J010_part029)

#time def treeT_J010_part031 : IntSourceTree :=
  (.node 174 (sourceLit (List.headD (raw_ints% [333369404189398765543076445598875]) 0) 35 true) (.node 172 (sourceLit (List.headD (raw_ints% [96092126794659254895272597585625]) 0) 37 true) (.node 171 (sourceLit (List.headD (raw_ints% [8102919243350576015979913865649375]) 0) 31 false) (.node 170 (sourceLit (List.headD (raw_ints% [57752653038501611576888535708675]) 0) 38 true) .empty .empty) .empty) (.node 173 (sourceLit (List.headD (raw_ints% [45827686760133184929763589517186375]) 0) 33 true) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [296773144504124368557204902148975]) 0) 35 true) (.node 175 (sourceLit (List.headD (raw_ints% [57947196563075529003345555561539625]) 0) 33 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [2255933944478139469174694360422125]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part032 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [3538237943842810038257166625710825]) 0) 31 true) (.node 181 (sourceLit (List.headD (raw_ints% [950065977821721297212840912973225]) 0) 33 true) (.node 180 (sourceLit (List.headD (raw_ints% [987713680677922428058301361592275]) 0) 33 true) (.node 179 (sourceLit (List.headD (raw_ints% [8235033242954705704585594855704375]) 0) 30 true) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [915841047487556824383723984109125]) 0) 33 true) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [1658661717628253566628775987794325]) 0) 32 true) (.node 184 (sourceLit (List.headD (raw_ints% [855830251488498580850400402964875]) 0) 33 true) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [804792726015058125552424501543455]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part033 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [1075811173376841730145427081510825]) 0) 33 true) treeT_J010_part031 treeT_J010_part032)

#time def treeT_J010_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [688201782069501827754177163008825]) 0) 33 true) (.node 190 (sourceLit (List.headD (raw_ints% [722219188266736416148777949319255]) 0) 33 true) (.node 189 (sourceLit (List.headD (raw_ints% [2963420224028314874512583729137875]) 0) 31 true) (.node 188 (sourceLit (List.headD (raw_ints% [760731991544935833851042580461265]) 0) 33 true) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [2818812857310173499748711736662665]) 0) 31 true) .empty .empty)) (.node 194 (sourceLit (List.headD (raw_ints% [1315770847278233576755829229686475]) 0) 32 true) (.node 193 (sourceLit (List.headD (raw_ints% [2690491242481998558116372872244595]) 0) 31 true) .empty .empty) (.node 195 (sourceLit (List.headD (raw_ints% [10302692189312465427935166245118135]) 0) 29 true) .empty .empty)))

#time def treeT_J010_part035 : IntSourceTree :=
  (.node 209 (sourceLit (List.headD (raw_ints% [870956934242150269885860869383575]) 0) 35 true) (.node 199 (sourceLit (List.headD (raw_ints% [4756691130644489929745767371193275]) 0) 30 true) (.node 198 (sourceLit (List.headD (raw_ints% [1212079548995959016599886974797483]) 0) 32 true) (.node 197 (sourceLit (List.headD (raw_ints% [618048674671185035085943434727575]) 0) 33 true) .empty .empty) .empty) (.node 208 (sourceLit (List.headD (raw_ints% [4328473570724380187608376987233125]) 0) 33 true) .empty .empty)) (.node 211 (sourceLit (List.headD (raw_ints% [161237314176012484871282315819325]) 0) 37 true) (.node 210 (sourceLit (List.headD (raw_ints% [368801717883682367591722514224125]) 0) 36 true) .empty .empty) (.node 212 (sourceLit (List.headD (raw_ints% [39790396281825637649014776578884125]) 0) 32 false) .empty .empty)))

#time def treeT_J010_part036 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [1261316190549027260877549459466041]) 0) 32 true) treeT_J010_part034 treeT_J010_part035)

#time def treeT_J010_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [12511842634985186881469251014884325]) 0) 29 true) treeT_J010_part033 treeT_J010_part036)

#time def treeT_J010_part038 : IntSourceTree :=
  (.node 218 (sourceLit (List.headD (raw_ints% [1482105446674396936606380692901375]) 0) 33 true) (.node 216 (sourceLit (List.headD (raw_ints% [58368258290760284486848653904210875]) 0) 34 false) (.node 215 (sourceLit (List.headD (raw_ints% [223040058153848351623911621542625]) 0) 36 true) (.node 214 (sourceLit (List.headD (raw_ints% [30081933808612375619469416425102125]) 0) 35 true) .empty .empty) .empty) (.node 217 (sourceLit (List.headD (raw_ints% [196009212322315253324870526544425]) 0) 36 true) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [5362289866282945932079206621283125]) 0) 31 true) (.node 219 (sourceLit (List.headD (raw_ints% [703472609612924253195501520730475]) 0) 34 true) .empty .empty) (.node 221 (sourceLit (List.headD (raw_ints% [640725242995174015063489068060525]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [513434921019808028049399094865865]) 0) 34 true) (.node 225 (sourceLit (List.headD (raw_ints% [548539250956714394476949632411125]) 0) 34 true) (.node 224 (sourceLit (List.headD (raw_ints% [2273761275997704047568097703093475]) 0) 32 true) (.node 223 (sourceLit (List.headD (raw_ints% [590224187780679436179027956062875]) 0) 34 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [1060545207300013673803616804148825]) 0) 33 true) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [483387419140120811282337183938895]) 0) 34 true) (.node 228 (sourceLit (List.headD (raw_ints% [7965674691427200205172050852776975]) 0) 30 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [939821268464737141790996781431625]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [1228388458820223282265304599203225]) 0) 33 true) treeT_J010_part038 treeT_J010_part039)

#time def treeT_J010_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [6478157001962465936085214247360085]) 0) 30 true) (.node 234 (sourceLit (List.headD (raw_ints% [1696077462422116515869400849369885]) 0) 32 true) (.node 233 (sourceLit (List.headD (raw_ints% [434446808658009613174633940504775]) 0) 34 true) (.node 232 (sourceLit (List.headD (raw_ints% [1782097204863120615217518946570395]) 0) 32 true) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [828365437964447802570558633165225]) 0) 33 true) .empty .empty)) (.node 238 (sourceLit (List.headD (raw_ints% [1550906825649869193497851344333975]) 0) 32 true) (.node 237 (sourceLit (List.headD (raw_ints% [792159419936469051931467421526823]) 0) 33 true) .empty .empty) (.node 239 (sourceLit (List.headD (raw_ints% [759579186461641885900808175597669]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part042 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [713324737526613768567400242979125]) 0) 35 true) (.node 252 (sourceLit (List.headD (raw_ints% [226382501557365714847292034053025]) 0) 37 true) (.node 251 (sourceLit (List.headD (raw_ints% [31706229187906247541850154775993375]) 0) 31 true) (.node 250 (sourceLit (List.headD (raw_ints% [639946322088143823578306726548875]) 0) 36 true) .empty .empty) .empty) (.node 253 (sourceLit (List.headD (raw_ints% [21404520760489705644694591524017625]) 0) 35 false) .empty .empty)) (.node 256 (sourceLit (List.headD (raw_ints% [595387088111269037938441584021525]) 0) 35 true) (.node 255 (sourceLit (List.headD (raw_ints% [298602667031974533959100886962356625]) 0) 33 true) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [469202000270560415363963925594109125]) 0) 32 false) .empty .empty)))

#time def treeT_J010_part043 : IntSourceTree :=
  (.node 249 (sourceLit (List.headD (raw_ints% [102800317489965516742993246199625]) 0) 39 true) treeT_J010_part041 treeT_J010_part042)

#time def treeT_J010_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [457319609686687202266105274685705]) 0) 34 true) treeT_J010_part040 treeT_J010_part043)

#time def treeT_J010_part045 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [65418383857250783381904793036125]) 0) 38 true) treeT_J010_part037 treeT_J010_part044)

#time def treeT_J010_part046 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [6288869726718976219865270167914975]) 0) 31 true) (.node 261 (sourceLit (List.headD (raw_ints% [3462157910639503337653524795336675]) 0) 32 true) (.node 260 (sourceLit (List.headD (raw_ints% [1826176757773774584723704721329625]) 0) 33 true) (.node 259 (sourceLit (List.headD (raw_ints% [15478653903835645281116496230717625]) 0) 30 true) .empty .empty) .empty) (.node 262 (sourceLit (List.headD (raw_ints% [1647059924493139235870232288132975]) 0) 33 true) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [2888860834367154528507419418392625]) 0) 32 true) (.node 264 (sourceLit (List.headD (raw_ints% [1505066499634219163865711421286625]) 0) 33 true) .empty .empty) (.node 266 (sourceLit (List.headD (raw_ints% [1389364277811799452355374028101045]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [1141076656677246981310243935733995]) 0) 33 true) (.node 270 (sourceLit (List.headD (raw_ints% [1211330488293746828980570786436325]) 0) 33 true) (.node 269 (sourceLit (List.headD (raw_ints% [1250563616849721332664866780909775]) 0) 33 true) (.node 268 (sourceLit (List.headD (raw_ints% [1293007692534296278346553799002195]) 0) 33 true) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [4699757290407723634579262514790335]) 0) 31 true) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [2159803621985843328641242294351725]) 0) 32 true) (.node 273 (sourceLit (List.headD (raw_ints% [4437897576970483902753702914036985]) 0) 31 true) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [16834547209441398825975247344800025]) 0) 29 true) .empty .empty)))

#time def treeT_J010_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [21425603998615250680246486717878075]) 0) 29 true) treeT_J010_part046 treeT_J010_part047)

#time def treeT_J010_part049 : IntSourceTree :=
  (.node 291 (sourceLit (List.headD (raw_ints% [239354503956065669353512205364775]) 0) 38 true) (.node 279 (sourceLit (List.headD (raw_ints% [7650563474554463618237043383478525]) 0) 30 true) (.node 278 (sourceLit (List.headD (raw_ints% [1956558130749917191125982711309809]) 0) 32 true) (.node 277 (sourceLit (List.headD (raw_ints% [4005962303277725795741440508449785]) 0) 31 true) .empty .empty) .empty) (.node 290 (sourceLit (List.headD (raw_ints% [1276003361955765900296169424969875]) 0) 36 true) .empty .empty)) (.node 293 (sourceLit (List.headD (raw_ints% [40241029425028732866346810254225]) 0) 40 true) (.node 292 (sourceLit (List.headD (raw_ints% [17874156367432971297716232838719375]) 0) 34 true) .empty .empty) (.node 294 (sourceLit (List.headD (raw_ints% [72890975329591786908858599473137375]) 0) 35 false) .empty .empty)))

#time def treeT_J010_part050 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [2529091009388174837259322402358625]) 0) 33 true) (.node 298 (sourceLit (List.headD (raw_ints% [117671026429308703075142576571752625]) 0) 35 false) (.node 297 (sourceLit (List.headD (raw_ints% [99844468947238446153392764369275]) 0) 38 true) (.node 296 (sourceLit (List.headD (raw_ints% [89242731330683704611487385216641875]) 0) 36 true) .empty .empty) .empty) (.node 299 (sourceLit (List.headD (raw_ints% [339215903541819517464249955617375]) 0) 36 true) .empty .empty)) (.node 302 (sourceLit (List.headD (raw_ints% [1116884725909640027694110098066725]) 0) 34 true) (.node 301 (sourceLit (List.headD (raw_ints% [296362878694650142415053913317275]) 0) 36 true) .empty .empty) (.node 303 (sourceLit (List.headD (raw_ints% [264208934178114949922801083017525]) 0) 36 true) .empty .empty)))

#time def treeT_J010_part051 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [122571169843191354235872155359125]) 0) 38 true) treeT_J010_part049 treeT_J010_part050)

#time def treeT_J010_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [2052145561308763949404685073194859]) 0) 32 true) treeT_J010_part048 treeT_J010_part051)

#time def treeT_J010_part053 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [202405068348543866766054153765825]) 0) 36 true) (.node 307 (sourceLit (List.headD (raw_ints% [218982339197997856076493733308795]) 0) 36 true) (.node 306 (sourceLit (List.headD (raw_ints% [228539453383392606837975326780475]) 0) 36 true) (.node 305 (sourceLit (List.headD (raw_ints% [239131812169376192347190447218875]) 0) 36 true) .empty .empty) .empty) (.node 308 (sourceLit (List.headD (raw_ints% [3364982326797012618768608966275275]) 0) 32 true) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [188502719651764906678616377937655]) 0) 36 true) (.node 310 (sourceLit (List.headD (raw_ints% [1561305965234705523538736780387925]) 0) 33 true) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [729415021386150754840435892054985]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [1227527738813928301121794582057905]) 0) 33 true) (.node 316 (sourceLit (List.headD (raw_ints% [2589097551869733222472508274359985]) 0) 32 true) (.node 315 (sourceLit (List.headD (raw_ints% [332859546005348881517670915296625]) 0) 35 true) (.node 314 (sourceLit (List.headD (raw_ints% [685455028637091846721075516166775]) 0) 34 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [314996535343073724368304412917009]) 0) 35 true) .empty .empty)) (.node 331 (sourceLit (List.headD (raw_ints% [49957985977262770077104688422078625]) 0) 31 true) (.node 319 (sourceLit (List.headD (raw_ints% [299244736072068826306293633928035]) 0) 35 true) .empty .empty) (.node 332 (sourceLit (List.headD (raw_ints% [731035514266896962566756787406075]) 0) 37 true) .empty .empty)))

#time def treeT_J010_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [176657462004809342033902498807305]) 0) 36 true) treeT_J010_part053 treeT_J010_part054)

#time def treeT_J010_part056 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [4329709788843058230764635576433625]) 0) 33 true) (.node 336 (sourceLit (List.headD (raw_ints% [1365751629379792629835512901724475]) 0) 35 true) (.node 335 (sourceLit (List.headD (raw_ints% [881730469668708829229969682747455625]) 0) 33 false) (.node 334 (sourceLit (List.headD (raw_ints% [1862101145675225134878795613291275]) 0) 35 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [3324969402852438962931560252526649125]) 0) 32 true) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [3601277698895337694704294568548375]) 0) 33 true) (.node 339 (sourceLit (List.headD (raw_ints% [7546424345379592642090241396822885625]) 0) 30 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [6654206126913196011383764814097825]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [37080496067533256670275196937923525]) 0) 29 true) (.node 345 (sourceLit (List.headD (raw_ints% [5141356067075389816086925511250375]) 0) 32 true) (.node 344 (sourceLit (List.headD (raw_ints% [2722276447215620034899105906993775]) 0) 33 true) (.node 343 (sourceLit (List.headD (raw_ints% [11581285887835264223240491401152625]) 0) 31 true) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [2436744716898219625199673127400955]) 0) 33 true) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [528604677486822821525935546341375]) 0) 35 true) (.node 348 (sourceLit (List.headD (raw_ints% [2210709734633669418877345933938525]) 0) 33 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [2027150605282955039276295673816875]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [3094746134621263042770630324943425]) 0) 33 true) treeT_J010_part056 treeT_J010_part057)

#time def treeT_J010_part059 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [4909834640990334617801353045342125]) 0) 38 true) treeT_J010_part055 treeT_J010_part058)

#time def treeT_J010_part060 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [1003777112680318043074293116205375]) 0) 34 true) treeT_J010_part052 treeT_J010_part059)

#time def treeT_J010_part061 : IntSourceTree :=
  (.node 258 (sourceLit (List.headD (raw_ints% [2060336223780202323052501343199975]) 0) 33 true) treeT_J010_part045 treeT_J010_part060)

#time def treeT_J010_part062 : IntSourceTree :=
  (.node 169 (sourceLit (List.headD (raw_ints% [1038863411045483651832593108845125]) 0) 34 true) treeT_J010_part030 treeT_J010_part061)

#time def treeT_J010_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [3273607174776818154878049571551141]) 0) 32 true) (.node 354 (sourceLit (List.headD (raw_ints% [3493235162168055616443637667482035]) 0) 32 true) (.node 353 (sourceLit (List.headD (raw_ints% [7232742765207928174693271358842775]) 0) 31 true) (.node 352 (sourceLit (List.headD (raw_ints% [1874966857750991525547618111268485]) 0) 33 true) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [27034574623332479364173585689873575]) 0) 29 true) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [11989880346468389199711669929447955]) 0) 30 true) (.node 358 (sourceLit (List.headD (raw_ints% [3083386434739262398766887895362335]) 0) 32 true) (.node 357 (sourceLit (List.headD (raw_ints% [6350427904201207094148592588990155]) 0) 31 true) .empty .empty) .empty) (.node 372 (sourceLit (List.headD (raw_ints% [21538639492469115113760242932798875]) 0) 32 false) .empty .empty)))

#time def treeT_J010_part064 : IntSourceTree :=
  (.node 378 (sourceLit (List.headD (raw_ints% [3795653508569673775232130558813659625]) 0) 33 true) (.node 376 (sourceLit (List.headD (raw_ints% [1238701394991443647675919223614023125]) 0) 34 false) (.node 375 (sourceLit (List.headD (raw_ints% [1371816466302459717935306991854775]) 0) 36 true) (.node 374 (sourceLit (List.headD (raw_ints% [151448329585437140793680248198611375]) 0) 35 true) .empty .empty) .empty) (.node 377 (sourceLit (List.headD (raw_ints% [966373753590838845221941844247375]) 0) 36 true) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [7556540709417145341439278686432320125]) 0) 31 false) (.node 379 (sourceLit (List.headD (raw_ints% [2972846174675780160907635753964125]) 0) 34 true) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [2415826184116737125044078915279275]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part065 : IntSourceTree :=
  (.node 373 (sourceLit (List.headD (raw_ints% [570071396566782031101369546389175]) 0) 38 true) treeT_J010_part063 treeT_J010_part064)

#time def treeT_J010_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [1560815360106228200893698194165775]) 0) 34 true) (.node 385 (sourceLit (List.headD (raw_ints% [1765749198538115265510344118118275]) 0) 34 true) (.node 384 (sourceLit (List.headD (raw_ints% [7566177437113992050943318936331125]) 0) 32 true) (.node 383 (sourceLit (List.headD (raw_ints% [2037910397908803243079425992873325]) 0) 34 true) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [3313040440008248961383122897006575]) 0) 33 true) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [1401089461239493951813129318875225]) 0) 34 true) (.node 388 (sourceLit (List.headD (raw_ints% [23620566760345206195200761072822425]) 0) 30 true) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [2667531454659877048668747590343075]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part067 : IntSourceTree :=
  (.node 396 (sourceLit (List.headD (raw_ints% [16678184415853546474283552592433635]) 0) 30 true) (.node 394 (sourceLit (List.headD (raw_ints% [4490922650659560787808969294175675]) 0) 32 true) (.node 393 (sourceLit (List.headD (raw_ints% [1168337009731754157412008116039265]) 0) 34 true) (.node 392 (sourceLit (List.headD (raw_ints% [4873030345925317534368888160093125]) 0) 32 true) .empty .empty) .empty) (.node 395 (sourceLit (List.headD (raw_ints% [2161796978146660090372954006295535]) 0) 33 true) .empty .empty)) (.node 398 (sourceLit (List.headD (raw_ints% [3895372426573350491905003424874345]) 0) 32 true) (.node 397 (sourceLit (List.headD (raw_ints% [2013621033404523257404831919883105]) 0) 33 true) .empty .empty) (.node 399 (sourceLit (List.headD (raw_ints% [1886407490450987093541713359650195]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part068 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [1273139726675895412561830162066255]) 0) 34 true) treeT_J010_part066 treeT_J010_part067)

#time def treeT_J010_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [4420436675093915955995544617964375]) 0) 33 true) treeT_J010_part065 treeT_J010_part068)

#time def treeT_J010_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [11132270268610363292786433931524375]) 0) 33 true) (.node 416 (sourceLit (List.headD (raw_ints% [4121514235830046241905715065694625]) 0) 35 true) (.node 415 (sourceLit (List.headD (raw_ints% [2093317106352205955579411668336346625]) 0) 33 true) (.node 414 (sourceLit (List.headD (raw_ints% [7259041199393287362743117128935525]) 0) 35 true) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [13234580562783988144338914041438834125]) 0) 32 false) .empty .empty)) (.node 420 (sourceLit (List.headD (raw_ints% [8290106999807782948926248447308125]) 0) 33 true) (.node 419 (sourceLit (List.headD (raw_ints% [68276880482494373045804330337841439625]) 0) 30 true) .empty .empty) (.node 421 (sourceLit (List.headD (raw_ints% [3781597457772029268725331225623208975]) 0) 33 false) .empty .empty)))

#time def treeT_J010_part071 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [68936798012730710093984735766286875]) 0) 29 true) (.node 425 (sourceLit (List.headD (raw_ints% [9990998807152594285799712361411875]) 0) 32 true) (.node 424 (sourceLit (List.headD (raw_ints% [5429365144419592937418598064499525]) 0) 33 true) (.node 423 (sourceLit (List.headD (raw_ints% [23782207512916063424723865542562375]) 0) 31 true) .empty .empty) .empty) (.node 426 (sourceLit (List.headD (raw_ints% [4626252077254241436841703345072145]) 0) 33 true) .empty .empty)) (.node 429 (sourceLit (List.headD (raw_ints% [15162891920556041050785792331360425]) 0) 31 true) (.node 428 (sourceLit (List.headD (raw_ints% [4032551705791243384697446842724575]) 0) 33 true) .empty .empty) (.node 430 (sourceLit (List.headD (raw_ints% [3577207239675020767976221601684025]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part072 : IntSourceTree :=
  (.node 422 (sourceLit (List.headD (raw_ints% [6568558601845685457405685336173675]) 0) 33 true) treeT_J010_part070 treeT_J010_part071)

#time def treeT_J010_part073 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [5373580737809822206613766453630999]) 0) 32 true) (.node 434 (sourceLit (List.headD (raw_ints% [5853460915685977642852427260832085]) 0) 32 true) (.node 433 (sourceLit (List.headD (raw_ints% [12259378618493341962782281281529725]) 0) 31 true) (.node 432 (sourceLit (List.headD (raw_ints% [3217592048952590124699702536996535]) 0) 33 true) .empty .empty) .empty) (.node 435 (sourceLit (List.headD (raw_ints% [44820187787220493240769923016937225]) 0) 29 true) .empty .empty)) (.node 438 (sourceLit (List.headD (raw_ints% [4971097698878830630852439784170085]) 0) 32 true) (.node 437 (sourceLit (List.headD (raw_ints% [1290969563956542422516870000430435]) 0) 34 true) .empty .empty) (.node 439 (sourceLit (List.headD (raw_ints% [19173099066118414735528357469546805]) 0) 30 true) .empty .empty)))

#time def treeT_J010_part074 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [37916710595955759193621804512136879875]) 0) 32 true) (.node 458 (sourceLit (List.headD (raw_ints% [8515117035676830959785522300126246875]) 0) 34 false) (.node 457 (sourceLit (List.headD (raw_ints% [1577570241119603698341886610723625]) 0) 37 true) (.node 456 (sourceLit (List.headD (raw_ints% [1666009250671824801627665445975184875]) 0) 35 true) .empty .empty) .empty) (.node 459 (sourceLit (List.headD (raw_ints% [4079712046967291565939399088780125]) 0) 35 true) .empty .empty)) (.node 462 (sourceLit (List.headD (raw_ints% [7567615352219152453406657995864382325]) 0) 33 false) (.node 461 (sourceLit (List.headD (raw_ints% [2937140407845522911941084766014425]) 0) 35 true) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [2265324101968441107163129671650175]) 0) 35 true) .empty .empty)))

#time def treeT_J010_part075 : IntSourceTree :=
  (.node 455 (sourceLit (List.headD (raw_ints% [2943612366545413822403905068540375]) 0) 37 true) treeT_J010_part073 treeT_J010_part074)

#time def treeT_J010_part076 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [13549561205809095835619348994431535]) 0) 31 true) treeT_J010_part072 treeT_J010_part075)

#time def treeT_J010_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [178653348004159822883403540383746875]) 0) 33 false) treeT_J010_part069 treeT_J010_part076)

#time def treeT_J010_part078 : IntSourceTree :=
  (.node 469 (sourceLit (List.headD (raw_ints% [1315731122275874716442158761924675]) 0) 35 true) (.node 467 (sourceLit (List.headD (raw_ints% [1532718358574006617974002575453185]) 0) 35 true) (.node 466 (sourceLit (List.headD (raw_ints% [1669489591786086331104147366101325]) 0) 35 true) (.node 465 (sourceLit (List.headD (raw_ints% [1831807972940738835954126973190625]) 0) 35 true) .empty .empty) .empty) (.node 468 (sourceLit (List.headD (raw_ints% [22658115626192751949391987346732225]) 0) 31 true) .empty .empty)) (.node 471 (sourceLit (List.headD (raw_ints% [1152033756499562677707195719808885]) 0) 35 true) (.node 470 (sourceLit (List.headD (raw_ints% [9827829011236286953448297150674275]) 0) 32 true) .empty .empty) (.node 472 (sourceLit (List.headD (raw_ints% [4338265429941889150625230417169205]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part079 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [6432384085078988888229956578569135]) 0) 32 true) (.node 476 (sourceLit (List.headD (raw_ints% [14071001685683473383243185212251795]) 0) 31 true) (.node 475 (sourceLit (List.headD (raw_ints% [1845831968769658776239736627268275]) 0) 34 true) (.node 474 (sourceLit (List.headD (raw_ints% [3884227983916890587486655993677025]) 0) 33 true) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [1679979852202649474604467266873947]) 0) 34 true) .empty .empty)) (.node 496 (sourceLit (List.headD (raw_ints% [19427384696533264337325525482628375]) 0) 35 true) (.node 479 (sourceLit (List.headD (raw_ints% [1542345104213921768655363212259945]) 0) 34 true) .empty .empty) (.node 497 (sourceLit (List.headD (raw_ints% [39890728573533184970381561177041792125]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part080 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [1024627519610417983643847210478635]) 0) 35 true) treeT_J010_part078 treeT_J010_part079)

#time def treeT_J010_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [60564705025266135690677987832457620975]) 0) 31 false) (.node 501 (sourceLit (List.headD (raw_ints% [20849154026863894231173567868880044425]) 0) 34 true) (.node 500 (sourceLit (List.headD (raw_ints% [24347589375930549578588944262932875]) 0) 33 true) (.node 499 (sourceLit (List.headD (raw_ints% [340760625624152963758941043941881339625]) 0) 30 false) .empty .empty) .empty) (.node 502 (sourceLit (List.headD (raw_ints% [16928564660918497838122992791941725]) 0) 33 true) .empty .empty)) (.node 505 (sourceLit (List.headD (raw_ints% [22441061344451548461761380851050625]) 0) 32 true) (.node 504 (sourceLit (List.headD (raw_ints% [12693227671327935919886439308701875]) 0) 33 true) .empty .empty) (.node 506 (sourceLit (List.headD (raw_ints% [10028211706271669250791312440452855]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part082 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [5998678003043911296957863221474545]) 0) 33 true) (.node 510 (sourceLit (List.headD (raw_ints% [6948641738531976963561048493713375]) 0) 33 true) (.node 509 (sourceLit (List.headD (raw_ints% [30153339331829462847998182362104025]) 0) 31 true) (.node 508 (sourceLit (List.headD (raw_ints% [8229195162800809559094573760900905]) 0) 33 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [25761754839136051978173839608265565]) 0) 31 true) .empty .empty)) (.node 514 (sourceLit (List.headD (raw_ints% [10540579398080710095449128106826075]) 0) 32 true) (.node 513 (sourceLit (List.headD (raw_ints% [22446744821041771242219562055823915]) 0) 31 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [79475107698120005558803068780727575]) 0) 29 true) .empty .empty)))

#time def treeT_J010_part083 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [144757869735888340287346127094682725]) 0) 29 true) treeT_J010_part081 treeT_J010_part082)

#time def treeT_J010_part084 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [39349977447216955054153937611631625]) 0) 33 true) treeT_J010_part080 treeT_J010_part083)

#time def treeT_J010_part085 : IntSourceTree :=
  (.node 539 (sourceLit (List.headD (raw_ints% [31190553353282371922275139434071375]) 0) 34 true) (.node 519 (sourceLit (List.headD (raw_ints% [32285973614513496370311295159006275]) 0) 30 true) (.node 518 (sourceLit (List.headD (raw_ints% [8468741118742365165983298350821491]) 0) 32 true) (.node 517 (sourceLit (List.headD (raw_ints% [8907123429857303693175705210530055]) 0) 32 true) .empty .empty) .empty) (.node 538 (sourceLit (List.headD (raw_ints% [56920962644886846889952605777294285875]) 0) 33 true) .empty .empty)) (.node 541 (sourceLit (List.headD (raw_ints% [18473308560239503754706774730904025]) 0) 34 true) (.node 540 (sourceLit (List.headD (raw_ints% [416594046816064482146184652966155099375]) 0) 31 false) .empty .empty) (.node 542 (sourceLit (List.headD (raw_ints% [90964231459674729378100929471384560025]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part086 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [99441638483502836388562152401218275]) 0) 30 true) (.node 546 (sourceLit (List.headD (raw_ints% [15763102977307203137344791386645325]) 0) 33 true) (.node 545 (sourceLit (List.headD (raw_ints% [9029611725446458247978185362320625]) 0) 34 true) (.node 544 (sourceLit (List.headD (raw_ints% [60580921055341937762051768379063852225]) 0) 32 false) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [6962774989123656014843307289546485]) 0) 34 true) .empty .empty)) (.node 550 (sourceLit (List.headD (raw_ints% [10162755160296587947274942605714875]) 0) 33 true) (.node 549 (sourceLit (List.headD (raw_ints% [5597732918249060126210256237051555]) 0) 34 true) .empty .empty) (.node 551 (sourceLit (List.headD (raw_ints% [4644574225532851608146657054095605]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part087 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [12397916456981615623796733448641375]) 0) 34 true) treeT_J010_part085 treeT_J010_part086)

#time def treeT_J010_part088 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [6033115307942149054095192030767307]) 0) 33 true) (.node 555 (sourceLit (List.headD (raw_ints% [6848915460541392542969654852289525]) 0) 33 true) (.node 554 (sourceLit (List.headD (raw_ints% [14678288853207990067246250068469865]) 0) 32 true) (.node 553 (sourceLit (List.headD (raw_ints% [3949422963823075329670168800517275]) 0) 34 true) .empty .empty) .empty) (.node 556 (sourceLit (List.headD (raw_ints% [51333104326753058792316698356223985]) 0) 30 true) .empty .empty)) (.node 559 (sourceLit (List.headD (raw_ints% [5384050910314521628672571926301601]) 0) 33 true) (.node 558 (sourceLit (List.headD (raw_ints% [11381862774635618498121453842490975]) 0) 32 true) .empty .empty) (.node 580 (sourceLit (List.headD (raw_ints% [100414624037198938110511613473352625]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part089 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [26090235195514163741121429008829645]) 0) 33 true) (.node 584 (sourceLit (List.headD (raw_ints% [36898438156598526575300494485863625]) 0) 33 true) (.node 583 (sourceLit (List.headD (raw_ints% [788278556702663970715485423603534101175]) 0) 31 true) (.node 582 (sourceLit (List.headD (raw_ints% [56964669580039517180704106131674375]) 0) 33 true) .empty .empty) .empty) (.node 585 (sourceLit (List.headD (raw_ints% [121184283172028327072565298138978755075]) 0) 32 false) .empty .empty)) (.node 588 (sourceLit (List.headD (raw_ints% [19621904793693814500278655397285035]) 0) 33 true) (.node 587 (sourceLit (List.headD (raw_ints% [359661425537942160107687197277967675]) 0) 29 true) .empty .empty) (.node 589 (sourceLit (List.headD (raw_ints% [34644149575836686770281985019557125]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part090 : IntSourceTree :=
  (.node 581 (sourceLit (List.headD (raw_ints% [499990662923520059070878924441675277075]) 0) 32 false) treeT_J010_part088 treeT_J010_part089)

#time def treeT_J010_part091 : IntSourceTree :=
  (.node 552 (sourceLit (List.headD (raw_ints% [17085223979252273676923378773927155]) 0) 32 true) treeT_J010_part087 treeT_J010_part090)

#time def treeT_J010_part092 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [9393075012347448003304126564515201]) 0) 32 true) treeT_J010_part084 treeT_J010_part091)

#time def treeT_J010_part093 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [8108015037901035686890273303115625]) 0) 33 true) treeT_J010_part077 treeT_J010_part092)

#time def treeT_J010_part094 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [155377513953207835517136932314790265]) 0) 29 true) (.node 593 (sourceLit (List.headD (raw_ints% [45894151095967323465473953039884705]) 0) 31 true) (.node 592 (sourceLit (List.headD (raw_ints% [12579618899087495135628764994907875]) 0) 33 true) (.node 591 (sourceLit (List.headD (raw_ints% [55540286443236651600025701237453435]) 0) 31 true) .empty .empty) .empty) (.node 594 (sourceLit (List.headD (raw_ints% [21054804312503892541912222297312125]) 0) 32 true) .empty .empty)) (.node 597 (sourceLit (List.headD (raw_ints% [33518857467038451405965287935163875]) 0) 31 true) (.node 596 (sourceLit (List.headD (raw_ints% [18002586829818122168574492844642899]) 0) 32 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [15663720113026231050397469772247737]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part095 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [7575002892187852142231415183147837525]) 0) 37 false) (.node 624 (sourceLit (List.headD (raw_ints% [106107434719750738559692148997824744175]) 0) 35 true) (.node 623 (sourceLit (List.headD (raw_ints% [5570844140382237694613421585379125]) 0) 37 true) (.node 622 (sourceLit (List.headD (raw_ints% [147738723595798697112244963478264959275]) 0) 35 false) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [3483603303894008540915288640442875]) 0) 37 true) .empty .empty)) (.node 628 (sourceLit (List.headD (raw_ints% [32527473381804915464890630609593675]) 0) 33 true) (.node 627 (sourceLit (List.headD (raw_ints% [2390932525798813465784765214910395]) 0) 37 true) .empty .empty) (.node 629 (sourceLit (List.headD (raw_ints% [1753021484430594296758549895029185]) 0) 37 true) .empty .empty)))

#time def treeT_J010_part096 : IntSourceTree :=
  (.node 599 (sourceLit (List.headD (raw_ints% [58768928582571451614660335580921525]) 0) 30 true) treeT_J010_part094 treeT_J010_part095)

#time def treeT_J010_part097 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [1775736106495312499867820930627825]) 0) 36 true) (.node 633 (sourceLit (List.headD (raw_ints% [1078774491908052475744824524298825]) 0) 37 true) (.node 632 (sourceLit (List.headD (raw_ints% [4806882807998047240387790307940785]) 0) 35 true) (.node 631 (sourceLit (List.headD (raw_ints% [1349714463616426491641664925049655]) 0) 37 true) .empty .empty) .empty) (.node 634 (sourceLit (List.headD (raw_ints% [3901982780344916674778462871426855]) 0) 35 true) .empty .empty)) (.node 637 (sourceLit (List.headD (raw_ints% [1496183940234496639309912601734449]) 0) 36 true) (.node 636 (sourceLit (List.headD (raw_ints% [13005551203306847090602529244820785]) 0) 33 true) .empty .empty) (.node 638 (sourceLit (List.headD (raw_ints% [5534248673100708226960958523168225]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part098 : IntSourceTree :=
  (.node 667 (sourceLit (List.headD (raw_ints% [3878761142225718238982592260968970780475]) 0) 29 false) (.node 665 (sourceLit (List.headD (raw_ints% [1818903238688040144027639682104174661875]) 0) 32 true) (.node 664 (sourceLit (List.headD (raw_ints% [141368574335633079652328996246268375]) 0) 33 true) (.node 663 (sourceLit (List.headD (raw_ints% [5515917711768222278307324254908012797975]) 0) 31 false) .empty .empty) .empty) (.node 666 (sourceLit (List.headD (raw_ints% [85385070529094109568167807485342355]) 0) 33 true) .empty .empty)) (.node 669 (sourceLit (List.headD (raw_ints% [95465743951382975089280537418817575]) 0) 32 true) (.node 668 (sourceLit (List.headD (raw_ints% [56887936031868216404833831479847605]) 0) 33 true) .empty .empty) (.node 670 (sourceLit (List.headD (raw_ints% [40654397567314753954993620186441075]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part099 : IntSourceTree :=
  (.node 639 (sourceLit (List.headD (raw_ints% [1284958650338963677715612230743267]) 0) 36 true) treeT_J010_part097 treeT_J010_part098)

#time def treeT_J010_part100 : IntSourceTree :=
  (.node 630 (sourceLit (List.headD (raw_ints% [12240697207770049411503521206921125]) 0) 34 true) treeT_J010_part096 treeT_J010_part099)

#time def treeT_J010_part101 : IntSourceTree :=
  (.node 676 (sourceLit (List.headD (raw_ints% [38820968578031877827195776935447501]) 0) 32 true) (.node 674 (sourceLit (List.headD (raw_ints% [47986763169611465905756547257812675]) 0) 32 true) (.node 673 (sourceLit (List.headD (raw_ints% [107926098759970188226935336814220415]) 0) 31 true) (.node 672 (sourceLit (List.headD (raw_ints% [30611243936638152596904512606681085]) 0) 33 true) .empty .empty) .empty) (.node 675 (sourceLit (List.headD (raw_ints% [344076281930941498854506315227847175]) 0) 29 true) .empty .empty)) (.node 678 (sourceLit (List.headD (raw_ints% [32214165974477661407519733483254631]) 0) 32 true) (.node 677 (sourceLit (List.headD (raw_ints% [70525552159416325318854946023402405]) 0) 31 true) .empty .empty) (.node 679 (sourceLit (List.headD (raw_ints% [118327028956651211648090337160461675]) 0) 30 true) .empty .empty)))

#time def treeT_J010_part102 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [70984349535842876266273495004975325]) 0) 33 true) (.node 708 (sourceLit (List.headD (raw_ints% [3879021362012772678306311386013847529875]) 0) 30 false) (.node 707 (sourceLit (List.headD (raw_ints% [66257610322703601841889685766059195]) 0) 34 true) (.node 706 (sourceLit (List.headD (raw_ints% [1940103284963045778303342325034540062275]) 0) 33 true) .empty .empty) .empty) (.node 709 (sourceLit (List.headD (raw_ints% [42863764156423462030765432319614125]) 0) 34 true) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [101855806417099761060928315609758285]) 0) 32 true) (.node 711 (sourceLit (List.headD (raw_ints% [29856681858383342021860300786043835]) 0) 34 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [21981048001373732790945916412290485]) 0) 34 true) .empty .empty)))

#time def treeT_J010_part103 : IntSourceTree :=
  (.node 705 (sourceLit (List.headD (raw_ints% [113499747904481011325006687122725375]) 0) 34 true) treeT_J010_part101 treeT_J010_part102)

#time def treeT_J010_part104 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [21934496771765951985794835637308495]) 0) 33 true) (.node 717 (sourceLit (List.headD (raw_ints% [26851497056155904712716476121571909]) 0) 33 true) (.node 716 (sourceLit (List.headD (raw_ints% [240031872304486722129686081269280895]) 0) 30 true) (.node 715 (sourceLit (List.headD (raw_ints% [33780874317648965906813979812790075]) 0) 33 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [48388557467013492411011111930729505]) 0) 32 true) .empty .empty)) (.node 747 (sourceLit (List.headD (raw_ints% [65962066261043183144689546662074252773275]) 0) 29 true) (.node 746 (sourceLit (List.headD (raw_ints% [368613921088829935731858941005559145]) 0) 33 true) .empty .empty) (.node 748 (sourceLit (List.headD (raw_ints% [208142505258946190962724911584389175]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part105 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [127861620841378396421810784040511205]) 0) 32 true) (.node 752 (sourceLit (List.headD (raw_ints% [88815483496895215490536690537494255]) 0) 33 true) (.node 751 (sourceLit (List.headD (raw_ints% [427563927405658871146157321966518035]) 0) 31 true) (.node 750 (sourceLit (List.headD (raw_ints% [130800659058379094168068109092015425]) 0) 33 true) .empty .empty) .empty) (.node 753 (sourceLit (List.headD (raw_ints% [299497126908428856016777925624812725]) 0) 31 true) .empty .empty)) (.node 756 (sourceLit (List.headD (raw_ints% [96302528692563985800060142315712799]) 0) 32 true) (.node 755 (sourceLit (List.headD (raw_ints% [883287502344432178404815826257042025]) 0) 29 true) .empty .empty) (.node 757 (sourceLit (List.headD (raw_ints% [84753160072535198405415567622939245]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part106 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [3879212293500675444256489947088685165025]) 0) 31 false) treeT_J010_part104 treeT_J010_part105)

#time def treeT_J010_part107 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [76710236517210854828707633842805575]) 0) 32 true) treeT_J010_part103 treeT_J010_part106)

#time def treeT_J010_part108 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [140310868881084138984030638073284565]) 0) 31 true) treeT_J010_part100 treeT_J010_part107)

#time def treeT_J010_part109 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [3879354262199747130009022494078695115675]) 0) 32 false) (.node 788 (sourceLit (List.headD (raw_ints% [34920543811527977911497929024044050151575]) 0) 31 true) (.node 787 (sourceLit (List.headD (raw_ints% [151178155383063166944984627619749975]) 0) 35 true) (.node 759 (sourceLit (List.headD (raw_ints% [268781430779456727639998558285374365]) 0) 30 true) .empty .empty) .empty) (.node 789 (sourceLit (List.headD (raw_ints% [82639370551261364465979739632387525]) 0) 35 true) .empty .empty)) (.node 792 (sourceLit (List.headD (raw_ints% [162854060494279555042614503178379875]) 0) 33 true) (.node 791 (sourceLit (List.headD (raw_ints% [50471988599997876073103904152985795]) 0) 35 true) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [33417217747760741349795387062601885]) 0) 35 true) .empty .empty)))

#time def treeT_J010_part110 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [26628662739190002728775667682862255]) 0) 34 true) (.node 797 (sourceLit (List.headD (raw_ints% [34725515818204040543671833097070445]) 0) 34 true) (.node 796 (sourceLit (List.headD (raw_ints% [321627815019972728137564872493880565]) 0) 31 true) (.node 795 (sourceLit (List.headD (raw_ints% [47040373261864715257498402113860565]) 0) 34 true) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [121117762678056904399820023315148985]) 0) 32 true) .empty .empty)) (.node 829 (sourceLit (List.headD (raw_ints% [73720299916556631267252347995176785468175]) 0) 31 true) (.node 828 (sourceLit (List.headD (raw_ints% [1001282737805559144597152109373610625]) 0) 33 true) .empty .empty) (.node 830 (sourceLit (List.headD (raw_ints% [530314305351711821559769807967084775]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part111 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [111393445195609000594035145891003575]) 0) 33 true) treeT_J010_part109 treeT_J010_part110)

#time def treeT_J010_part112 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [280020457402353736259927074595171721]) 0) 32 true) (.node 834 (sourceLit (List.headD (raw_ints% [406813863122793465174915408961118955]) 0) 32 true) (.node 833 (sourceLit (List.headD (raw_ints% [1003335357045807584324138099802226275]) 0) 31 true) (.node 832 (sourceLit (List.headD (raw_ints% [314960425303087793094294542686392105]) 0) 33 true) .empty .empty) .empty) (.node 835 (sourceLit (List.headD (raw_ints% [2681302743915055840604308842255072375]) 0) 29 true) .empty .empty)) (.node 838 (sourceLit (List.headD (raw_ints% [202612304295486366906028493773530555]) 0) 32 true) (.node 837 (sourceLit (List.headD (raw_ints% [29609331868429691216518663108867665]) 0) 35 true) .empty .empty) (.node 839 (sourceLit (List.headD (raw_ints% [700160670644998507558561628235817515]) 0) 30 true) .empty .empty)))

#time def treeT_J010_part113 : IntSourceTree :=
  (.node 874 (sourceLit (List.headD (raw_ints% [780548466654589583136067808020219125]) 0) 32 true) (.node 872 (sourceLit (List.headD (raw_ints% [15518170320847382738017321362643103740485]) 0) 32 false) (.node 871 (sourceLit (List.headD (raw_ints% [429370328151716069413561999661113185]) 0) 34 true) (.node 870 (sourceLit (List.headD (raw_ints% [38799827089378189198630685244627740291925]) 0) 33 true) .empty .empty) .empty) (.node 873 (sourceLit (List.headD (raw_ints% [248125989807566310394703768561188335]) 0) 34 true) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [2038047113875110384329179097267311245]) 0) 30 true) (.node 875 (sourceLit (List.headD (raw_ints% [312733116599064034659918604733397825]) 0) 33 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [210569425765945655172583408401030831]) 0) 33 true) .empty .empty)))

#time def treeT_J010_part114 : IntSourceTree :=
  (.node 869 (sourceLit (List.headD (raw_ints% [836003996703036415665192630108835575]) 0) 34 true) treeT_J010_part112 treeT_J010_part113)

#time def treeT_J010_part115 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [15517844612726394178907236133636746980735]) 0) 31 false) treeT_J010_part111 treeT_J010_part114)

#time def treeT_J010_part116 : IntSourceTree :=
  (.node 913 (sourceLit (List.headD (raw_ints% [62073684618746576759653609588672217188215]) 0) 31 false) (.node 911 (sourceLit (List.headD (raw_ints% [325916461327751907767952718090658669316135]) 0) 31 true) (.node 910 (sourceLit (List.headD (raw_ints% [2813701681460433841101000712468257525]) 0) 33 true) (.node 879 (sourceLit (List.headD (raw_ints% [149354978817106361448477158407806045]) 0) 33 true) .empty .empty) .empty) (.node 912 (sourceLit (List.headD (raw_ints% [1402520887303776484559953455958060635]) 0) 33 true) .empty .empty)) (.node 915 (sourceLit (List.headD (raw_ints% [9807472722558377489572776086068433625]) 0) 29 true) (.node 914 (sourceLit (List.headD (raw_ints% [1578194055337737017982714739528387725]) 0) 32 true) .empty .empty) (.node 916 (sourceLit (List.headD (raw_ints% [970912008993902402379747344338419579]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part117 : IntSourceTree :=
  (.node 953 (sourceLit (List.headD (raw_ints% [288598724374052543541312421849218075]) 0) 36 true) (.node 951 (sourceLit (List.headD (raw_ints% [596082838327179442921859678201786085]) 0) 36 true) (.node 919 (sourceLit (List.headD (raw_ints% [2120891707089546732957267063178051725]) 0) 30 true) (.node 918 (sourceLit (List.headD (raw_ints% [639665398768296253784305139830592769]) 0) 32 true) .empty .empty) .empty) (.node 952 (sourceLit (List.headD (raw_ints% [85358657912149822626492509863325443264155]) 0) 34 true) .empty .empty)) (.node 955 (sourceLit (List.headD (raw_ints% [316365234684668245830699033698747475]) 0) 35 true) (.node 954 (sourceLit (List.headD (raw_ints% [15518616291803307837309186414120059351835]) 0) 34 false) .empty .empty) (.node 956 (sourceLit (List.headD (raw_ints% [1942356402170816776310899247200280595]) 0) 32 true) .empty .empty)))

#time def treeT_J010_part118 : IntSourceTree :=
  (.node 917 (sourceLit (List.headD (raw_ints% [1564297803980235324864880487525428605]) 0) 31 true) treeT_J010_part116 treeT_J010_part117)

#time def treeT_J010_part119 : IntSourceTree :=
  (.node 996 (sourceLit (List.headD (raw_ints% [4090931745960789530911437194841540021]) 0) 32 true) (.node 994 (sourceLit (List.headD (raw_ints% [7656965124631944375339282759646590675]) 0) 32 true) (.node 959 (sourceLit (List.headD (raw_ints% [122577604987797473083956995355696681]) 0) 35 true) (.node 958 (sourceLit (List.headD (raw_ints% [605833128381708584900200950549347475]) 0) 33 true) .empty .empty) .empty) (.node 995 (sourceLit (List.headD (raw_ints% [993201250148134259965277503279769866951065]) 0) 29 false) .empty .empty)) (.node 998 (sourceLit (List.headD (raw_ints% [2401704934143530735044350603918962223]) 0) 32 true) (.node 997 (sourceLit (List.headD (raw_ints% [6205127804703031780378716501275693775]) 0) 31 true) .empty .empty) (.node 999 (sourceLit (List.headD (raw_ints% [7572438347017790625445948145611507875]) 0) 30 true) .empty .empty)))

#time def treeT_J010_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [21475084997612296037154509304564863079]) 0) 32 true) (.node 1038 (sourceLit (List.headD (raw_ints% [4993461547939614610578314600176998825]) 0) 32 true) (.node 1037 (sourceLit (List.headD (raw_ints% [3330589162732832783704273258904151273]) 0) 33 true) (.node 1036 (sourceLit (List.headD (raw_ints% [993209019573742943232382746876758668073445]) 0) 30 false) .empty .empty) .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [1911394514192340842708522622496175499]) 0) 33 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [10920651716787800399772742431697642869]) 0) 32 true) (.node 1077 (sourceLit (List.headD (raw_ints% [248303806175386911566040781398314985941805]) 0) 33 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [32375254036499126259180568655804482725]) 0) 30 true) .empty .empty)))

#time def treeT_J010_part121 : IntSourceTree :=
  (.node 1035 (sourceLit (List.headD (raw_ints% [6391504185893271392016486624851600775]) 0) 33 true) treeT_J010_part119 treeT_J010_part120)

#time def treeT_J010_part122 : IntSourceTree :=
  (.node 957 (sourceLit (List.headD (raw_ints% [190085645806989186801790983984347187]) 0) 35 true) treeT_J010_part118 treeT_J010_part121)

#time def treeT_J010_part123 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [352631547216818155064478586426733655]) 0) 32 true) treeT_J010_part115 treeT_J010_part122)

#time def treeT_J010_part124 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [75191822250145957443346171003033005]) 0) 32 true) treeT_J010_part108 treeT_J010_part123)

#time def treeT_J010_part125 : IntSourceTree :=
  (.node 590 (sourceLit (List.headD (raw_ints% [15442289934464263541279976454492845]) 0) 33 true) treeT_J010_part093 treeT_J010_part124)

#time def treeT_J010_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [7790690431469920553730631728313065]) 0) 31 true) treeT_J010_part062 treeT_J010_part125)

#time def treeT_J010 : IntSourceTree := treeT_J010_part126

#time def treeT_J011_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [128188655339217360977955346155675]) 0) 34 true) (.node 5 (sourceLit (List.headD (raw_ints% [150476387074463592017864998849125]) 0) 34 true) (.node 4 (sourceLit (List.headD (raw_ints% [1334510686447489466330926533647625]) 0) 31 true) (.node 3 (sourceLit (List.headD (raw_ints% [189934665446201692141343176583625]) 0) 34 true) .empty .empty) .empty) (.node 6 (sourceLit (List.headD (raw_ints% [276131309326749895453452586193625]) 0) 33 true) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [53679050140464825148393657961625]) 0) 35 true) (.node 9 (sourceLit (List.headD (raw_ints% [28306941784830657353385720865125]) 0) 36 true) (.node 8 (sourceLit (List.headD (raw_ints% [480271289881090049343564421233375]) 0) 32 true) .empty .empty) .empty) (.node 11 (sourceLit (List.headD (raw_ints% [12780726223920196463903251895625]) 0) 37 true) .empty .empty)))

#time def treeT_J011_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [162340503601152491084576821990275]) 0) 33 true) (.node 15 (sourceLit (List.headD (raw_ints% [43429500709609165761956959738125]) 0) 35 true) (.node 14 (sourceLit (List.headD (raw_ints% [90120505425078308399317801828125]) 0) 34 true) (.node 13 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 35 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [167778632385660073579987084774875]) 0) 33 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [152712532235813128654083365696625]) 0) 33 true) (.node 18 (sourceLit (List.headD (raw_ints% [314673541598194437643843180447125]) 0) 32 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [1187377610672268457296845261646375]) 0) 30 true) .empty .empty)))

#time def treeT_J011_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [14018599175163852336435829195005375]) 0) 31 false) treeT_J011_part000 treeT_J011_part001)

#time def treeT_J011_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [255815778167100670450406511368475]) 0) 32 true) (.node 24 (sourceLit (List.headD (raw_ints% [535669602970408356437225390777625]) 0) 31 true) (.node 23 (sourceLit (List.headD (raw_ints% [137200769919162932871626796956625]) 0) 33 true) (.node 22 (sourceLit (List.headD (raw_ints% [281392531863886137975333750271575]) 0) 32 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [130825702657946654618997437402625]) 0) 33 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [1960537532948518927647560015024325]) 0) 29 true) (.node 27 (sourceLit (List.headD (raw_ints% [125148408825185324614412711288955]) 0) 33 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [120051383903295135612980362929225]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [214834611900934651376278187334675]) 0) 32 true) (.node 33 (sourceLit (List.headD (raw_ints% [222502391454485429930037374147025]) 0) 32 true) (.node 32 (sourceLit (List.headD (raw_ints% [453196223208107186742784908623565]) 0) 31 true) (.node 31 (sourceLit (List.headD (raw_ints% [115443135453050355462622561125675]) 0) 33 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [437170724266606920376886625209775]) 0) 31 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [207788030561184118949536886994741]) 0) 32 true) (.node 36 (sourceLit (List.headD (raw_ints% [1689911221057831462030456052111175]) 0) 29 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [408945413513337254019990779911425]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [235382145899365733466844027807425]) 0) 32 true) treeT_J011_part003 treeT_J011_part004)

#time def treeT_J011_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [144427555715862909575465986480875]) 0) 33 true) treeT_J011_part002 treeT_J011_part005)

#time def treeT_J011_part007 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [128188655339217360977955346155675]) 0) 35 true) (.node 46 (sourceLit (List.headD (raw_ints% [150476387074463592017864998849125]) 0) 35 true) (.node 45 (sourceLit (List.headD (raw_ints% [1334510686447489466330926533647625]) 0) 32 true) (.node 44 (sourceLit (List.headD (raw_ints% [189934665446201692141343176583625]) 0) 35 true) .empty .empty) .empty) (.node 47 (sourceLit (List.headD (raw_ints% [276131309326749895453452586193625]) 0) 34 true) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [28306941784830657353385720865125]) 0) 37 true) (.node 49 (sourceLit (List.headD (raw_ints% [480271289881090049343564421233375]) 0) 33 true) .empty .empty) (.node 51 (sourceLit (List.headD (raw_ints% [53679050140464825148393657961625]) 0) 36 true) .empty .empty)))

#time def treeT_J011_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [167778632385660073579987084774875]) 0) 34 true) (.node 55 (sourceLit (List.headD (raw_ints% [90120505425078308399317801828125]) 0) 35 true) (.node 54 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 36 true) (.node 53 (sourceLit (List.headD (raw_ints% [14018599175163852336435829195005375]) 0) 32 false) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [43429500709609165761956959738125]) 0) 36 true) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [314673541598194437643843180447125]) 0) 33 true) (.node 58 (sourceLit (List.headD (raw_ints% [162340503601152491084576821990275]) 0) 34 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [152712532235813128654083365696625]) 0) 34 true) .empty .empty)))

#time def treeT_J011_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [12780726223920196463903251895625]) 0) 38 true) treeT_J011_part007 treeT_J011_part008)

#time def treeT_J011_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [130825702657946654618997437402625]) 0) 34 true) (.node 64 (sourceLit (List.headD (raw_ints% [137200769919162932871626796956625]) 0) 34 true) (.node 63 (sourceLit (List.headD (raw_ints% [281392531863886137975333750271575]) 0) 33 true) (.node 62 (sourceLit (List.headD (raw_ints% [144427555715862909575465986480875]) 0) 34 true) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [535669602970408356437225390777625]) 0) 32 true) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [125148408825185324614412711288955]) 0) 34 true) (.node 67 (sourceLit (List.headD (raw_ints% [255815778167100670450406511368475]) 0) 33 true) .empty .empty) (.node 69 (sourceLit (List.headD (raw_ints% [1960537532948518927647560015024325]) 0) 30 true) .empty .empty)))

#time def treeT_J011_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [437170724266606920376886625209775]) 0) 32 true) (.node 73 (sourceLit (List.headD (raw_ints% [453196223208107186742784908623565]) 0) 32 true) (.node 72 (sourceLit (List.headD (raw_ints% [115443135453050355462622561125675]) 0) 34 true) (.node 71 (sourceLit (List.headD (raw_ints% [235382145899365733466844027807425]) 0) 33 true) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [222502391454485429930037374147025]) 0) 33 true) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [1689911221057831462030456052111175]) 0) 30 true) (.node 76 (sourceLit (List.headD (raw_ints% [214834611900934651376278187334675]) 0) 33 true) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [207788030561184118949536886994741]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [120051383903295135612980362929225]) 0) 34 true) treeT_J011_part010 treeT_J011_part011)

#time def treeT_J011_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [1187377610672268457296845261646375]) 0) 31 true) treeT_J011_part009 treeT_J011_part012)

#time def treeT_J011_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [201284454099813365147338586689575]) 0) 32 true) treeT_J011_part006 treeT_J011_part013)

#time def treeT_J011_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [49940856777193351812284812645275]) 0) 37 true) (.node 87 (sourceLit (List.headD (raw_ints% [473716892958637007093504649240825]) 0) 34 true) (.node 86 (sourceLit (List.headD (raw_ints% [66148711070046223179842121715875]) 0) 37 true) (.node 85 (sourceLit (List.headD (raw_ints% [609262274710343176547507707485375]) 0) 34 true) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [1728779184732909114284056268315625]) 0) 32 true) .empty .empty)) (.node 91 (sourceLit (List.headD (raw_ints% [43833157345741118242868189834625]) 0) 37 true) (.node 90 (sourceLit (List.headD (raw_ints% [372913189600160399046777105310125]) 0) 34 true) .empty .empty) (.node 92 (sourceLit (List.headD (raw_ints% [17454058384153601145933023304549375]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part016 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [1027555517487086150996053497751875]) 0) 32 true) (.node 96 (sourceLit (List.headD (raw_ints% [553185411014966393614555329850125]) 0) 33 true) (.node 95 (sourceLit (List.headD (raw_ints% [144021150574553715708624068064375]) 0) 35 true) (.node 94 (sourceLit (List.headD (raw_ints% [14198840186014008953234464798661625]) 0) 33 false) .empty .empty) .empty) (.node 97 (sourceLit (List.headD (raw_ints% [532531507752594161106734533819725]) 0) 33 true) .empty .empty)) (.node 100 (sourceLit (List.headD (raw_ints% [3847399054898842545004645625507625]) 0) 30 true) (.node 99 (sourceLit (List.headD (raw_ints% [496649482168796835684223922264475]) 0) 33 true) .empty .empty) (.node 101 (sourceLit (List.headD (raw_ints% [466422573227389605040867476305625]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part017 : IntSourceTree :=
  (.node 93 (sourceLit (List.headD (raw_ints% [157628956761682423054806773379375]) 0) 35 true) treeT_J011_part015 treeT_J011_part016)

#time def treeT_J011_part018 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [398154401806601293861577038321545]) 0) 33 true) (.node 105 (sourceLit (List.headD (raw_ints% [417977377018705076867509750423875]) 0) 33 true) (.node 104 (sourceLit (List.headD (raw_ints% [1715470651940680747365444611394975]) 0) 31 true) (.node 103 (sourceLit (List.headD (raw_ints% [440509452944288705430237148966875]) 0) 33 true) .empty .empty) .empty) (.node 106 (sourceLit (List.headD (raw_ints% [815523427773716042424044270186775]) 0) 32 true) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [380542251397446162844670482226595]) 0) 33 true) (.node 108 (sourceLit (List.headD (raw_ints% [6225567368398702526765448348766875]) 0) 29 true) .empty .empty) (.node 110 (sourceLit (List.headD (raw_ints% [1489773241149787460713871959409475]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [5304820367207879263999729951245225]) 0) 29 true) (.node 114 (sourceLit (List.headD (raw_ints% [1375614168565821826594253009284485]) 0) 31 true) (.node 113 (sourceLit (List.headD (raw_ints% [701042692169917413770943114858375]) 0) 32 true) (.node 112 (sourceLit (List.headD (raw_ints% [1429860943986818680991967313835835]) 0) 31 true) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [675174953917007068343871309253425]) 0) 32 true) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [640482903772247104005232636099875]) 0) 32 true) (.node 117 (sourceLit (List.headD (raw_ints% [651550417042554486555575862343959]) 0) 32 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [629867668144923110650808961289389]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [364762400160130186989298890591225]) 0) 33 true) treeT_J011_part018 treeT_J011_part019)

#time def treeT_J011_part021 : IntSourceTree :=
  (.node 102 (sourceLit (List.headD (raw_ints% [56624067425523894957594469460925]) 0) 36 true) treeT_J011_part017 treeT_J011_part020)

#time def treeT_J011_part022 : IntSourceTree :=
  (.node 131 (sourceLit (List.headD (raw_ints% [265555089319230748749989789386875]) 0) 35 true) (.node 129 (sourceLit (List.headD (raw_ints% [624253947425909532470245923541125]) 0) 34 true) (.node 128 (sourceLit (List.headD (raw_ints% [172764118809709823057774651542575]) 0) 36 true) (.node 127 (sourceLit (List.headD (raw_ints% [782248067793989675424021361260375]) 0) 34 true) .empty .empty) .empty) (.node 130 (sourceLit (List.headD (raw_ints% [71574771769556046271183904425425]) 0) 37 true) .empty .empty)) (.node 133 (sourceLit (List.headD (raw_ints% [15736328779658726741184426249777375]) 0) 33 true) (.node 132 (sourceLit (List.headD (raw_ints% [3881553890227615222370617242375]) 0) 41 true) .empty .empty) (.node 134 (sourceLit (List.headD (raw_ints% [55383146970320851343580758214375]) 0) 37 true) .empty .empty)))

#time def treeT_J011_part023 : IntSourceTree :=
  (.node 140 (sourceLit (List.headD (raw_ints% [171968474966491853515070278283925]) 0) 35 true) (.node 138 (sourceLit (List.headD (raw_ints% [185095502075720835011078855914725]) 0) 35 true) (.node 137 (sourceLit (List.headD (raw_ints% [192703389314653160017284122537625]) 0) 35 true) (.node 136 (sourceLit (List.headD (raw_ints% [50295824932472274973333554163125]) 0) 37 true) .empty .empty) .empty) (.node 139 (sourceLit (List.headD (raw_ints% [356440987944445856676105158652375]) 0) 34 true) .empty .empty)) (.node 142 (sourceLit (List.headD (raw_ints% [160997508755763347732700744912375]) 0) 35 true) (.node 141 (sourceLit (List.headD (raw_ints% [1330010722113287043853900181930625]) 0) 32 true) .empty .empty) (.node 143 (sourceLit (List.headD (raw_ints% [624592546944496181346177761103225]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part024 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [14379081196864165570033100402317875]) 0) 34 false) treeT_J011_part022 treeT_J011_part023)

#time def treeT_J011_part025 : IntSourceTree :=
  (.node 149 (sourceLit (List.headD (raw_ints% [2132514917725091799558944166871275]) 0) 31 true) (.node 147 (sourceLit (List.headD (raw_ints% [139926912401653842993409439704575]) 0) 35 true) (.node 146 (sourceLit (List.headD (raw_ints% [143575837180379211124256156510625]) 0) 35 true) (.node 145 (sourceLit (List.headD (raw_ints% [589900524485136195464109610308675]) 0) 33 true) .empty .empty) .empty) (.node 148 (sourceLit (List.headD (raw_ints% [136502996490707984623582163516295]) 0) 35 true) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [1019008949351055993780183903794625]) 0) 32 true) (.node 150 (sourceLit (List.headD (raw_ints% [130245433747075513615845059648685]) 0) 35 true) .empty .empty) (.node 152 (sourceLit (List.headD (raw_ints% [124659632353539915763338164732775]) 0) 35 true) .empty .empty)))

#time def treeT_J011_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [221881193240685183803019487674609]) 0) 34 true) (.node 156 (sourceLit (List.headD (raw_ints% [230170171008036208483796560959375]) 0) 34 true) (.node 155 (sourceLit (List.headD (raw_ints% [469221722149607453108683192037355]) 0) 33 true) (.node 154 (sourceLit (List.headD (raw_ints% [239270150357715991920452870355675]) 0) 34 true) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [1807454573075023900984636949567025]) 0) 31 true) .empty .empty)) (.node 167 (sourceLit (List.headD (raw_ints% [1361426657584881331025066185304175]) 0) 34 true) (.node 159 (sourceLit (List.headD (raw_ints% [872020394031156953990474492288325]) 0) 32 true) .empty .empty) (.node 168 (sourceLit (List.headD (raw_ints% [4529205357619008289108114621767375]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [488332360389355747124591202606135]) 0) 33 true) treeT_J011_part025 treeT_J011_part026)

#time def treeT_J011_part028 : IntSourceTree :=
  (.node 144 (sourceLit (List.headD (raw_ints% [151654341512562886279305176005125]) 0) 35 true) treeT_J011_part024 treeT_J011_part027)

#time def treeT_J011_part029 : IntSourceTree :=
  (.node 126 (sourceLit (List.headD (raw_ints% [229392943817939792264821354318125]) 0) 36 true) treeT_J011_part021 treeT_J011_part028)

#time def treeT_J011_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [408945413513337254019990779911425]) 0) 32 true) treeT_J011_part014 treeT_J011_part029)

#time def treeT_J011_part031 : IntSourceTree :=
  (.node 174 (sourceLit (List.headD (raw_ints% [45671497745331462435603317298216375]) 0) 33 true) (.node 172 (sourceLit (List.headD (raw_ints% [8956295525938217185933350044169375]) 0) 31 false) (.node 171 (sourceLit (List.headD (raw_ints% [99316386193370974299499619016225]) 0) 37 true) (.node 170 (sourceLit (List.headD (raw_ints% [875594705251658665893714741772125]) 0) 34 true) .empty .empty) .empty) (.node 173 (sourceLit (List.headD (raw_ints% [339209941187452325408632233644625]) 0) 35 true) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [58069510198471628673746956939121625]) 0) 33 false) (.node 175 (sourceLit (List.headD (raw_ints% [299044025188013095040021997650625]) 0) 35 true) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [1076934890086518638039939199400275]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part032 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [847470617101818076431368810332125]) 0) 33 true) (.node 181 (sourceLit (List.headD (raw_ints% [909325226504545223079694749965775]) 0) 33 true) (.node 180 (sourceLit (List.headD (raw_ints% [7558712559323424868630719451368375]) 0) 30 true) (.node 179 (sourceLit (List.headD (raw_ints% [984114534436969844404406925053325]) 0) 33 true) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [877018182709095884193144426243225]) 0) 33 true) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [795257355081798013366931657617125]) 0) 33 true) (.node 184 (sourceLit (List.headD (raw_ints% [3281269723615288703403977477430825]) 0) 31 true) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [1544078670166828739432394171047925]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part033 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [2055698711547364409280492462850125]) 0) 32 true) treeT_J011_part031 treeT_J011_part032)

#time def treeT_J011_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [2646174853417405294128768301342665]) 0) 31 true) (.node 190 (sourceLit (List.headD (raw_ints% [2775256594300396138404016374333075]) 0) 31 true) (.node 189 (sourceLit (List.headD (raw_ints% [711481720528217714143986825903765]) 0) 33 true) (.node 188 (sourceLit (List.headD (raw_ints% [11685077419012989376390959933418725]) 0) 29 true) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [677201069816473921937461586598255]) 0) 33 true) .empty .empty)) (.node 194 (sourceLit (List.headD (raw_ints% [2531044714549024150402476611564595]) 0) 31 true) (.node 193 (sourceLit (List.headD (raw_ints% [1293511425486721238442467520866025]) 0) 32 true) .empty .empty) (.node 195 (sourceLit (List.headD (raw_ints% [1238986248944720867019751653591975]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part035 : IntSourceTree :=
  (.node 209 (sourceLit (List.headD (raw_ints% [3280697462767189224167622774685125]) 0) 33 true) (.node 199 (sourceLit (List.headD (raw_ints% [1145181877780558359773346940107483]) 0) 32 true) (.node 198 (sourceLit (List.headD (raw_ints% [583485834651388398489702156733575]) 0) 33 true) (.node 197 (sourceLit (List.headD (raw_ints% [1189810951021735181314796625331041]) 0) 32 true) .empty .empty) .empty) (.node 208 (sourceLit (List.headD (raw_ints% [1015898419965461684909516882219025]) 0) 35 true) .empty .empty)) (.node 211 (sourceLit (List.headD (raw_ints% [305019807966213958571862476192625]) 0) 36 true) (.node 210 (sourceLit (List.headD (raw_ints% [174071752295476896219795773369175]) 0) 37 true) .empty .empty) (.node 212 (sourceLit (List.headD (raw_ints% [68263955071550052520534681077225]) 0) 38 true) .empty .empty)))

#time def treeT_J011_part036 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [9710274741579559235478132193950135]) 0) 29 true) treeT_J011_part034 treeT_J011_part035)

#time def treeT_J011_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [750452295636432395132472213763455]) 0) 33 true) treeT_J011_part033 treeT_J011_part036)

#time def treeT_J011_part038 : IntSourceTree :=
  (.node 218 (sourceLit (List.headD (raw_ints% [706743885935076968017781487570825]) 0) 34 true) (.node 216 (sourceLit (List.headD (raw_ints% [198452375323068545093354889324375]) 0) 36 true) (.node 215 (sourceLit (List.headD (raw_ints% [30025289471097814002818208850267125]) 0) 35 true) (.node 214 (sourceLit (List.headD (raw_ints% [228443647246810622721470717215875]) 0) 36 true) .empty .empty) .empty) (.node 217 (sourceLit (List.headD (raw_ints% [58454916977100934993781525184196875]) 0) 34 false) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [640177584503986137374266368485475]) 0) 34 true) (.node 219 (sourceLit (List.headD (raw_ints% [1342816735658472695928282145545375]) 0) 33 true) .empty .empty) (.node 221 (sourceLit (List.headD (raw_ints% [4898691115096850780922919087507125]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [984371020560213367458756412229625]) 0) 33 true) (.node 225 (sourceLit (List.headD (raw_ints% [2101468674645016312475758256813475]) 0) 32 true) (.node 224 (sourceLit (List.headD (raw_ints% [544161934076692303872758458321875]) 0) 34 true) (.node 223 (sourceLit (List.headD (raw_ints% [1129443818473695587040111091383225]) 0) 33 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [508105680721039591118419344595875]) 0) 34 true) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [7420047583562805777273071599676175]) 0) 30 true) (.node 228 (sourceLit (List.headD (raw_ints% [477446302655016425885307886730865]) 0) 34 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [450990853034066686912296706606395]) 0) 34 true) .empty .empty)))

#time def treeT_J011_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [587330208993018527614293260141025]) 0) 34 true) treeT_J011_part038 treeT_J011_part039)

#time def treeT_J011_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [778645906928648450052158531673225]) 0) 33 true) (.node 234 (sourceLit (List.headD (raw_ints% [814971124771289254601561780154675]) 0) 33 true) (.node 233 (sourceLit (List.headD (raw_ints% [1669510132638693799879585896130395]) 0) 32 true) (.node 232 (sourceLit (List.headD (raw_ints% [427881805109394090410785257132705]) 0) 34 true) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [1592601270249809244185110227489885]) 0) 32 true) .empty .empty)) (.node 238 (sourceLit (List.headD (raw_ints% [746048564540364813708757649981823]) 0) 33 true) (.node 237 (sourceLit (List.headD (raw_ints% [6095365595429511433508858294816085]) 0) 30 true) .empty .empty) (.node 239 (sourceLit (List.headD (raw_ints% [1461922944574396639968334134645975]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part042 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [21525112707646783275976379960485125]) 0) 35 false) (.node 252 (sourceLit (List.headD (raw_ints% [28477563235775910534532548520497375]) 0) 31 true) (.node 251 (sourceLit (List.headD (raw_ints% [248827118397582818140091927722125]) 0) 37 true) (.node 250 (sourceLit (List.headD (raw_ints% [300637844689441319784238504114125]) 0) 37 true) .empty .empty) .empty) (.node 253 (sourceLit (List.headD (raw_ints% [753013339957348514919922663590975]) 0) 35 true) .empty .empty)) (.node 256 (sourceLit (List.headD (raw_ints% [298271825967254140696292627741258625]) 0) 33 true) (.node 255 (sourceLit (List.headD (raw_ints% [614730563799229395845860871212875]) 0) 35 true) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [2098303115082578083453739029789725]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part043 : IntSourceTree :=
  (.node 249 (sourceLit (List.headD (raw_ints% [770251895900428742418537204424425]) 0) 36 true) treeT_J011_part041 treeT_J011_part042)

#time def treeT_J011_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [878123822474670072311916235269225]) 0) 33 true) treeT_J011_part040 treeT_J011_part043)

#time def treeT_J011_part045 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [40428953085255670668302202543724125]) 0) 32 false) treeT_J011_part037 treeT_J011_part044)

#time def treeT_J011_part046 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [1501850218870256034025804230231975]) 0) 33 true) (.node 261 (sourceLit (List.headD (raw_ints% [1651385111511399326417370723976125]) 0) 33 true) (.node 260 (sourceLit (List.headD (raw_ints% [13926355211212138266221794877357625]) 0) 30 true) (.node 259 (sourceLit (List.headD (raw_ints% [1842861009303338027666719025229975]) 0) 33 true) .empty .empty) .empty) (.node 262 (sourceLit (List.headD (raw_ints% [3144654749678659012536630235020675]) 0) 32 true) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [1381390381224971202124102175670375]) 0) 33 true) (.node 264 (sourceLit (List.headD (raw_ints% [5754280824174275992916911253634975]) 0) 31 true) .empty .empty) (.node 266 (sourceLit (List.headD (raw_ints% [2658858679123203885519122342579025]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [4378815726379955284366561580811135]) 0) 31 true) (.node 270 (sourceLit (List.headD (raw_ints% [1161197747315602409717263806335775]) 0) 33 true) (.node 269 (sourceLit (List.headD (raw_ints% [1198303490091847989397244721019695]) 0) 33 true) (.node 268 (sourceLit (List.headD (raw_ints% [19814795238913838382289245257929275]) 0) 29 true) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [1126762342319792825711725239827325]) 0) 33 true) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [4146995816005751049115866972956985]) 0) 31 true) (.node 273 (sourceLit (List.headD (raw_ints% [2129543015388431484843814536195615]) 0) 32 true) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [2020898250140436151386495467026725]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [1281970427247725969341205164620045]) 0) 33 true) treeT_J011_part046 treeT_J011_part047)

#time def treeT_J011_part049 : IntSourceTree :=
  (.node 291 (sourceLit (List.headD (raw_ints% [897531570791551320565091540263875]) 0) 36 true) (.node 279 (sourceLit (List.headD (raw_ints% [1839012380380900895061683659819809]) 0) 32 true) (.node 278 (sourceLit (List.headD (raw_ints% [3761422256823957839550049667881785]) 0) 31 true) (.node 277 (sourceLit (List.headD (raw_ints% [1924772676692858618893837501361859]) 0) 32 true) .empty .empty) .empty) (.node 290 (sourceLit (List.headD (raw_ints% [298090071802475923099370715527625]) 0) 38 true) .empty .empty)) (.node 293 (sourceLit (List.headD (raw_ints% [17226629080257895300708687766055375]) 0) 34 true) (.node 292 (sourceLit (List.headD (raw_ints% [45140790831508191404889311661225]) 0) 40 true) .empty .empty) (.node 294 (sourceLit (List.headD (raw_ints% [131142423177634473049612986593775]) 0) 38 true) .empty .empty)))

#time def treeT_J011_part050 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [300670856199837972573113164186125]) 0) 36 true) (.node 298 (sourceLit (List.headD (raw_ints% [347889807286875278858989385554725]) 0) 36 true) (.node 297 (sourceLit (List.headD (raw_ints% [89181685736088768922518538231363875]) 0) 36 true) (.node 296 (sourceLit (List.headD (raw_ints% [104069547119040212688126495472125]) 0) 38 true) .empty .empty) .empty) (.node 299 (sourceLit (List.headD (raw_ints% [117759462816003329263865244020492625]) 0) 35 false) .empty .empty)) (.node 302 (sourceLit (List.headD (raw_ints% [266013725629595199700769365958775]) 0) 36 true) (.node 301 (sourceLit (List.headD (raw_ints% [2256916024028821871324718947462625]) 0) 33 true) .empty .empty) (.node 303 (sourceLit (List.headD (raw_ints% [1007605465602481712748259571818725]) 0) 34 true) .empty .empty)))

#time def treeT_J011_part051 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [73075514886391380554770968771237375]) 0) 35 false) treeT_J011_part049 treeT_J011_part050)

#time def treeT_J011_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [15771345582417388671483631445888025]) 0) 29 true) treeT_J011_part048 treeT_J011_part051)

#time def treeT_J011_part053 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [3098686913837758151254043414563275]) 0) 32 true) (.node 307 (sourceLit (List.headD (raw_ints% [209310957320373814757545741293675]) 0) 36 true) (.node 306 (sourceLit (List.headD (raw_ints% [218321175125982902751420707768625]) 0) 36 true) (.node 305 (sourceLit (List.headD (raw_ints% [913203037382314920110288249205375]) 0) 34 true) .empty .empty) .empty) (.node 308 (sourceLit (List.headD (raw_ints% [201131031148177385863974319472295]) 0) 36 true) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [1444271672156534747122611377402325]) 0) 33 true) (.node 310 (sourceLit (List.headD (raw_ints% [186828159264445325621237003603325]) 0) 36 true) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [174720134302599683825234995673655]) 0) 36 true) .empty .empty)))

#time def treeT_J011_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [294681028038123451296269962845009]) 0) 35 true) (.node 316 (sourceLit (List.headD (raw_ints% [310563085802946925333584233838375]) 0) 35 true) (.node 315 (sourceLit (List.headD (raw_ints% [638598636438985451232689186366775]) 0) 34 true) (.node 314 (sourceLit (List.headD (raw_ints% [328642972654285557560563189010235]) 0) 35 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [2418994996746969309493693287767985]) 0) 32 true) .empty .empty)) (.node 331 (sourceLit (List.headD (raw_ints% [943533168812320874257390934388375]) 0) 37 true) (.node 319 (sourceLit (List.headD (raw_ints% [1149749656124780599790857766617905]) 0) 33 true) .empty .empty) (.node 332 (sourceLit (List.headD (raw_ints% [28964457294883373981633310056390625]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [677326398435315371121743921170185]) 0) 34 true) treeT_J011_part053 treeT_J011_part054)

#time def treeT_J011_part056 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [3323508978083195449880125917340069125]) 0) 32 true) (.node 336 (sourceLit (List.headD (raw_ints% [882875945058385185134460377911157625]) 0) 33 false) (.node 335 (sourceLit (List.headD (raw_ints% [1483548207042922172947946914287525]) 0) 35 true) (.node 334 (sourceLit (List.headD (raw_ints% [9687935446976169644171266931635125]) 0) 37 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [4562147900535995528586356680426275]) 0) 33 true) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [7550531975435425211153597412188885625]) 0) 30 false) (.node 339 (sourceLit (List.headD (raw_ints% [3723375907286666434077111143645625]) 0) 33 true) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [3159348587686008234752439903001875]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [2211168374768000474681526159677955]) 0) 33 true) (.node 345 (sourceLit (List.headD (raw_ints% [2449362757949283718488080911970025]) 0) 33 true) (.node 344 (sourceLit (List.headD (raw_ints% [10367406625465431411055241895464625]) 0) 31 true) (.node 343 (sourceLit (List.headD (raw_ints% [2754369391203267161186505625108425]) 0) 33 true) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [4646765619935315475363183651063975]) 0) 32 true) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [2019793008278990184426344390537025]) 0) 33 true) (.node 348 (sourceLit (List.headD (raw_ints% [33768809835101858195642464513251525]) 0) 29 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [484372291630538935384194902056875]) 0) 35 true) .empty .empty)))

#time def treeT_J011_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [5883009346436628472762245554829825]) 0) 32 true) treeT_J011_part056 treeT_J011_part057)

#time def treeT_J011_part059 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [2135997273259175734992993282727425]) 0) 35 true) treeT_J011_part055 treeT_J011_part058)

#time def treeT_J011_part060 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [239422071198390932538261442977525]) 0) 36 true) treeT_J011_part052 treeT_J011_part059)

#time def treeT_J011_part061 : IntSourceTree :=
  (.node 258 (sourceLit (List.headD (raw_ints% [469695034528354844359532693936425125]) 0) 32 false) treeT_J011_part045 treeT_J011_part060)

#time def treeT_J011_part062 : IntSourceTree :=
  (.node 169 (sourceLit (List.headD (raw_ints% [30705815508129117811372459724325]) 0) 39 true) treeT_J011_part030 treeT_J011_part061)

#time def treeT_J011_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [25098967149677680207408476481585575]) 0) 29 true) (.node 354 (sourceLit (List.headD (raw_ints% [6690226558959294888832035765765975]) 0) 31 true) (.node 353 (sourceLit (List.headD (raw_ints% [3461501282294758397563705325361345]) 0) 32 true) (.node 352 (sourceLit (List.headD (raw_ints% [7175357650872322692614329438407465]) 0) 31 true) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [3237389312328132769582515557137035]) 0) 32 true) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [2875884068229074325678635745700335]) 0) 32 true) (.node 358 (sourceLit (List.headD (raw_ints% [5914557730163919398424723483190155]) 0) 31 true) (.node 357 (sourceLit (List.headD (raw_ints% [3044236696154292186443510240052141]) 0) 32 true) .empty .empty) .empty) (.node 372 (sourceLit (List.headD (raw_ints% [762970005486288108637833687743475]) 0) 38 true) .empty .empty)))

#time def treeT_J011_part064 : IntSourceTree :=
  (.node 378 (sourceLit (List.headD (raw_ints% [3170588671388494413150399138207375]) 0) 34 true) (.node 376 (sourceLit (List.headD (raw_ints% [1067270018566761322195440932399025]) 0) 36 true) (.node 375 (sourceLit (List.headD (raw_ints% [150578998462200737708141104224318375]) 0) 35 true) (.node 374 (sourceLit (List.headD (raw_ints% [1611427580548637842794541336352325]) 0) 36 true) .empty .empty) .empty) (.node 377 (sourceLit (List.headD (raw_ints% [1239602688002740260824534530836613125]) 0) 34 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [2520692482487314543784658486901125]) 0) 34 true) (.node 379 (sourceLit (List.headD (raw_ints% [3794546829347208766935586893422039625]) 0) 33 true) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [7559559639531540498638896287978736125]) 0) 31 false) .empty .empty)))

#time def treeT_J011_part065 : IntSourceTree :=
  (.node 373 (sourceLit (List.headD (raw_ints% [39942059026148207221201441007830875]) 0) 32 false) treeT_J011_part063 treeT_J011_part064)

#time def treeT_J011_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [2972277961372324957302817720714575]) 0) 33 true) (.node 385 (sourceLit (List.headD (raw_ints% [6714594475936171730614088898643125]) 0) 32 true) (.node 384 (sourceLit (List.headD (raw_ints% [1796681106409703431033459853198325]) 0) 34 true) (.node 383 (sourceLit (List.headD (raw_ints% [3867798415231665047265726411192375]) 0) 33 true) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [1576078057445352107482398080895525]) 0) 34 true) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [21374062179750825590626290854998425]) 0) 30 true) (.node 388 (sourceLit (List.headD (raw_ints% [1406644250175290931225628881788775]) 0) 34 true) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [1272480371221208881941396376123725]) 0) 34 true) .empty .empty)))

#time def treeT_J011_part067 : IntSourceTree :=
  (.node 396 (sourceLit (List.headD (raw_ints% [1995136969116345068248178621783535]) 0) 33 true) (.node 394 (sourceLit (List.headD (raw_ints% [2146929391677616167321452569320405]) 0) 33 true) (.node 393 (sourceLit (List.headD (raw_ints% [4466052057131061208127353753726725]) 0) 32 true) (.node 392 (sourceLit (List.headD (raw_ints% [1163607668700933648927126835131255]) 0) 34 true) .empty .empty) .empty) (.node 395 (sourceLit (List.headD (raw_ints% [4135832013203353083901279020298875]) 0) 32 true) .empty .empty)) (.node 398 (sourceLit (List.headD (raw_ints% [1865512584001798381258430388672105]) 0) 33 true) (.node 397 (sourceLit (List.headD (raw_ints% [15422987162689802969433703330513635]) 0) 30 true) .empty .empty) (.node 399 (sourceLit (List.headD (raw_ints% [3615058417914358198843007949954345]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part068 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [2430706660887776735950947839052675]) 0) 33 true) treeT_J011_part066 treeT_J011_part067)

#time def treeT_J011_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [2095293685167627435949362439166775]) 0) 34 true) treeT_J011_part065 treeT_J011_part068)

#time def treeT_J011_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [13240330482105117536476402164032974125]) 0) 32 false) (.node 416 (sourceLit (List.headD (raw_ints% [2087507932755991086799589211705704625]) 0) 33 true) (.node 415 (sourceLit (List.headD (raw_ints% [4962162115151629198230218431121775]) 0) 35 true) (.node 414 (sourceLit (List.headD (raw_ints% [194949026177766921527941711913992875]) 0) 33 false) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [12514172396532185626540698237958125]) 0) 33 true) .empty .empty)) (.node 420 (sourceLit (List.headD (raw_ints% [68263281244990765482122987706941519625]) 0) 30 true) (.node 419 (sourceLit (List.headD (raw_ints% [8958978778267311218524485409183875]) 0) 33 true) .empty .empty) (.node 421 (sourceLit (List.headD (raw_ints% [6923421342263249940386194044602625]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part071 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [4093143855013407955248066163904145]) 0) 33 true) (.node 425 (sourceLit (List.headD (raw_ints% [4737361667689530005645758500823275]) 0) 33 true) (.node 424 (sourceLit (List.headD (raw_ints% [20574980696387888967070569394074375]) 0) 31 true) (.node 423 (sourceLit (List.headD (raw_ints% [5626805349467242582610944131558675]) 0) 33 true) .empty .empty) .empty) (.node 426 (sourceLit (List.headD (raw_ints% [8782423331937027985864994146222275]) 0) 32 true) .empty .empty)) (.node 429 (sourceLit (List.headD (raw_ints% [3606783992422173540476171136618075]) 0) 33 true) (.node 428 (sourceLit (List.headD (raw_ints% [61344084928812540438047702549614875]) 0) 29 true) .empty .empty) (.node 430 (sourceLit (List.headD (raw_ints% [13624105513662202624479172422088425]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part072 : IntSourceTree :=
  (.node 422 (sourceLit (List.headD (raw_ints% [3782721324438988563555829266766782975]) 0) 33 false) treeT_J011_part070 treeT_J011_part071)

#time def treeT_J011_part073 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [41074345061575969135011987843196425]) 0) 29 true) (.node 434 (sourceLit (List.headD (raw_ints% [11173981669564949943677379249140925]) 0) 31 true) (.node 433 (sourceLit (List.headD (raw_ints% [5847360067312710793853309355688695]) 0) 32 true) (.node 432 (sourceLit (List.headD (raw_ints% [12270295636229891194993253274013935]) 0) 31 true) .empty .empty) .empty) (.node 435 (sourceLit (List.headD (raw_ints% [5350328254382331899703294720144585]) 0) 32 true) .empty .empty)) (.node 438 (sourceLit (List.headD (raw_ints% [1188553679065735446376122480915435]) 0) 34 true) (.node 437 (sourceLit (List.headD (raw_ints% [4936311180311088086549204247081999]) 0) 32 true) .empty .empty) (.node 439 (sourceLit (List.headD (raw_ints% [4586166267778119199355085808988085]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part074 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [3219143147889998337369913461141375]) 0) 35 true) (.node 458 (sourceLit (List.headD (raw_ints% [4671791862571845606695149549875375]) 0) 35 true) (.node 457 (sourceLit (List.headD (raw_ints% [1663555310379365673812061871271158875]) 0) 35 true) (.node 456 (sourceLit (List.headD (raw_ints% [1947446048292433938017388749361375]) 0) 37 true) .empty .empty) .empty) (.node 459 (sourceLit (List.headD (raw_ints% [8517438655726163151705994528727506875]) 0) 34 false) .empty .empty)) (.node 462 (sourceLit (List.headD (raw_ints% [2414063828547811252218415802717925]) 0) 35 true) (.node 461 (sourceLit (List.headD (raw_ints% [37911420442261152990380941997460127875]) 0) 32 true) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [7569310447293208792158924259944758325]) 0) 33 false) .empty .empty)))

#time def treeT_J011_part075 : IntSourceTree :=
  (.node 455 (sourceLit (List.headD (raw_ints% [496107023102168396944223920362629625]) 0) 34 false) treeT_J011_part073 treeT_J011_part074)

#time def treeT_J011_part076 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [3227433278973503143537518686669025]) 0) 33 true) treeT_J011_part072 treeT_J011_part075)

#time def treeT_J011_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [10071522814521434003212345721168175]) 0) 35 true) treeT_J011_part069 treeT_J011_part076)

#time def treeT_J011_part078 : IntSourceTree :=
  (.node 469 (sourceLit (List.headD (raw_ints% [19985011374530857423710705847308225]) 0) 31 true) (.node 467 (sourceLit (List.headD (raw_ints% [1452536342641175757140544106376925]) 0) 35 true) (.node 466 (sourceLit (List.headD (raw_ints% [1580641805122088949081680209963875]) 0) 35 true) (.node 465 (sourceLit (List.headD (raw_ints% [6930193110225858618228240247715625]) 0) 33 true) .empty .empty) .empty) (.node 468 (sourceLit (List.headD (raw_ints% [1343249802419058512011218641057685]) 0) 35 true) .empty .empty)) (.node 471 (sourceLit (List.headD (raw_ints% [8762692191886649152577276743983075]) 0) 32 true) (.node 470 (sourceLit (List.headD (raw_ints% [1167151810600482329267387380247175]) 0) 35 true) .empty .empty) (.node 472 (sourceLit (List.headD (raw_ints% [1031912805136284747305195925768885]) 0) 35 true) .empty .empty)))

#time def treeT_J011_part079 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [1535399298154644852645386929204947]) 0) 34 true) (.node 476 (sourceLit (List.headD (raw_ints% [1677595642632993415727558049180525]) 0) 34 true) (.node 475 (sourceLit (List.headD (raw_ints% [3519074828180798429888050114421025]) 0) 33 true) (.node 474 (sourceLit (List.headD (raw_ints% [1850215337817547313265928393184145]) 0) 34 true) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [12825678949443083082789142256341395]) 0) 31 true) .empty .empty)) (.node 496 (sourceLit (List.headD (raw_ints% [4071936025164664674576484893156223125]) 0) 33 false) (.node 479 (sourceLit (List.headD (raw_ints% [5893371014611525372165971897369135]) 0) 32 true) .empty .empty) (.node 497 (sourceLit (List.headD (raw_ints% [49804101148825700390015741741605875]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part080 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [3902121789549414993432949760143605]) 0) 33 true) treeT_J011_part078 treeT_J011_part079)

#time def treeT_J011_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [13685705278915247435136382290184725]) 0) 33 true) (.node 501 (sourceLit (List.headD (raw_ints% [18829723840856736758573113644528375]) 0) 33 true) (.node 500 (sourceLit (List.headD (raw_ints% [340821318228227986336714812626221739625]) 0) 30 false) (.node 499 (sourceLit (List.headD (raw_ints% [28415356122307453635036710989819125]) 0) 33 true) .empty .empty) .empty) (.node 502 (sourceLit (List.headD (raw_ints% [20847070883350070776968385632113455425]) 0) 34 true) .empty .empty)) (.node 505 (sourceLit (List.headD (raw_ints% [10583135304540626600664178612618125]) 0) 33 true) (.node 504 (sourceLit (List.headD (raw_ints% [60575058559042058226238464648952140975]) 0) 31 false) .empty .empty) (.node 506 (sourceLit (List.headD (raw_ints% [18938349108966406487047966844640225]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part082 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [22780473131316705415315853701918365]) 0) 31 true) (.node 510 (sourceLit (List.headD (raw_ints% [26345917235399512222942239272528025]) 0) 31 true) (.node 509 (sourceLit (List.headD (raw_ints% [7139214426930294555613577991843405]) 0) 33 true) (.node 508 (sourceLit (List.headD (raw_ints% [124580566929257956475941943066631525]) 0) 29 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [6109781205830355490601580355308375]) 0) 33 true) .empty .empty)) (.node 514 (sourceLit (List.headD (raw_ints% [20042992646830370003786218832007915]) 0) 31 true) (.node 513 (sourceLit (List.headD (raw_ints% [10663244814867845163029825456613465]) 0) 32 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [9451394448158046606424132425328575]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part083 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [8551990585963303637405375515806855]) 0) 33 true) treeT_J011_part081 treeT_J011_part082)

#time def treeT_J011_part084 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [39857215448174968317469392104371516125]) 0) 32 true) treeT_J011_part080 treeT_J011_part083)

#time def treeT_J011_part085 : IntSourceTree :=
  (.node 539 (sourceLit (List.headD (raw_ints% [56892092759627294620881381161826529875]) 0) 33 true) (.node 519 (sourceLit (List.headD (raw_ints% [7697028117459039621808009624651491]) 0) 32 true) (.node 518 (sourceLit (List.headD (raw_ints% [8071464233180141297284652332679655]) 0) 32 true) (.node 517 (sourceLit (List.headD (raw_ints% [8484453960752859239271260146362201]) 0) 32 true) .empty .empty) .empty) (.node 538 (sourceLit (List.headD (raw_ints% [40460517423682009176625442641855125]) 0) 34 true) .empty .empty)) (.node 541 (sourceLit (List.headD (raw_ints% [416644159112750292317476696621141995375]) 0) 31 false) (.node 540 (sourceLit (List.headD (raw_ints% [21977069826527456960296884067536375]) 0) 34 true) .empty .empty) (.node 542 (sourceLit (List.headD (raw_ints% [14001596183761114254136282039092525]) 0) 34 true) .empty .empty)))

#time def treeT_J011_part086 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [5865490981125186613382938233691485]) 0) 34 true) (.node 546 (sourceLit (List.headD (raw_ints% [7421851694296448702500818192690375]) 0) 34 true) (.node 545 (sourceLit (List.headD (raw_ints% [60588918945262509943474921129447572225]) 0) 32 false) (.node 544 (sourceLit (List.headD (raw_ints% [9855581035857708283558898011824375]) 0) 34 true) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [13128203738401703458485790419132525]) 0) 33 true) .empty .empty)) (.node 550 (sourceLit (List.headD (raw_ints% [4804910805729329897078803231349055]) 0) 34 true) (.node 549 (sourceLit (List.headD (raw_ints% [84610544180196241628520531372015075]) 0) 30 true) .empty .empty) (.node 551 (sourceLit (List.headD (raw_ints% [8791612521756431535182481264272475]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part087 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [90957593980693491900032466788398580025]) 0) 33 true) treeT_J011_part085 treeT_J011_part086)

#time def treeT_J011_part088 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [45884691541323414455827331305593585]) 0) 30 true) (.node 555 (sourceLit (List.headD (raw_ints% [13004842990468773144010118603165865]) 0) 32 true) (.node 554 (sourceLit (List.headD (raw_ints% [6962814139232750536497968670245175]) 0) 33 true) (.node 553 (sourceLit (List.headD (raw_ints% [14976229552217875428449954181631155]) 0) 32 true) .empty .empty) .empty) (.node 556 (sourceLit (List.headD (raw_ints% [6096203162892059774969016326967525]) 0) 33 true) .empty .empty)) (.node 559 (sourceLit (List.headD (raw_ints% [10249557451748757222403332767990175]) 0) 32 true) (.node 558 (sourceLit (List.headD (raw_ints% [5413655364443569533980486287952307]) 0) 33 true) .empty .empty) (.node 580 (sourceLit (List.headD (raw_ints% [1251094802382264700270816911215446217625]) 0) 30 true) .empty .empty)))

#time def treeT_J011_part089 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [121196776239633986293436890225739784675]) 0) 32 false) (.node 584 (sourceLit (List.headD (raw_ints% [788235810404589993426498198956140781175]) 0) 31 true) (.node 583 (sourceLit (List.headD (raw_ints% [42320679456129209581408745866185375]) 0) 33 true) (.node 582 (sourceLit (List.headD (raw_ints% [500032442646150575425350239149595817075]) 0) 32 false) .empty .empty) .empty) (.node 585 (sourceLit (List.headD (raw_ints% [28839188838890206533571413434679375]) 0) 33 true) .empty .empty)) (.node 588 (sourceLit (List.headD (raw_ints% [295521952699596554195603350345609275]) 0) 29 true) (.node 587 (sourceLit (List.headD (raw_ints% [21135416191222491172597897254954645]) 0) 33 true) .empty .empty) (.node 589 (sourceLit (List.headD (raw_ints% [16322749497570451897918174942922535]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part090 : IntSourceTree :=
  (.node 581 (sourceLit (List.headD (raw_ints% [69078555465253091082614422625617125]) 0) 33 true) treeT_J011_part088 treeT_J011_part089)

#time def treeT_J011_part091 : IntSourceTree :=
  (.node 552 (sourceLit (List.headD (raw_ints% [4045955595557785995991188503770605]) 0) 34 true) treeT_J011_part087 treeT_J011_part090)

#time def treeT_J011_part092 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [71536049440209580621405615818276375]) 0) 29 true) treeT_J011_part084 treeT_J011_part091)

#time def treeT_J011_part093 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [1915062121528769575788742139180175]) 0) 35 true) treeT_J011_part077 treeT_J011_part092)

#time def treeT_J011_part094 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [18399862108772955539567742255652125]) 0) 32 true) (.node 593 (sourceLit (List.headD (raw_ints% [21704399949594442804899682573551375]) 0) 32 true) (.node 592 (sourceLit (List.headD (raw_ints% [47552427042734746866143996412261435]) 0) 31 true) (.node 591 (sourceLit (List.headD (raw_ints% [13109862017086964097713632570087845]) 0) 33 true) .empty .empty) .empty) (.node 594 (sourceLit (List.headD (raw_ints% [39861925562041131710013597894516705]) 0) 31 true) .empty .empty)) (.node 597 (sourceLit (List.headD (raw_ints% [15900358690815379860604805161507899]) 0) 32 true) (.node 596 (sourceLit (List.headD (raw_ints% [136541438407290789682756281832377465]) 0) 29 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [29741763074963131861258026640234275]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part095 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [2677167143074219728883824405248625]) 0) 37 true) (.node 624 (sourceLit (List.headD (raw_ints% [4058137302533937662231230981795125]) 0) 37 true) (.node 623 (sourceLit (List.headD (raw_ints% [147747509156711016831345676484498599275]) 0) 35 false) (.node 622 (sourceLit (List.headD (raw_ints% [6884619910186497103559767573315575]) 0) 37 true) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [106103091168731562921246640010698544175]) 0) 35 true) .empty .empty)) (.node 628 (sourceLit (List.headD (raw_ints% [1908740651262163069901869877657895]) 0) 37 true) (.node 627 (sourceLit (List.headD (raw_ints% [7575619027710774249805961001009932325]) 0) 37 false) .empty .empty) (.node 629 (sourceLit (List.headD (raw_ints% [26363926064925039070885352371699275]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part096 : IntSourceTree :=
  (.node 599 (sourceLit (List.headD (raw_ints% [13957593340315238514113935527157737]) 0) 32 true) treeT_J011_part094 treeT_J011_part095)

#time def treeT_J011_part097 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [3357135321446544820750434911418855]) 0) 35 true) (.node 633 (sourceLit (List.headD (raw_ints% [4072024686314608929711755278828785]) 0) 35 true) (.node 632 (sourceLit (List.headD (raw_ints% [1132988302691147262715305508289655]) 0) 37 true) (.node 631 (sourceLit (List.headD (raw_ints% [10170350475320966583803332392735525]) 0) 34 true) .empty .empty) .empty) (.node 634 (sourceLit (List.headD (raw_ints% [1842698226295211533550214237913275]) 0) 36 true) .empty .empty)) (.node 637 (sourceLit (List.headD (raw_ints% [11332093358245921903366118815847985]) 0) 33 true) (.node 636 (sourceLit (List.headD (raw_ints% [1537957368235111970574840741085575]) 0) 36 true) .empty .empty) (.node 638 (sourceLit (List.headD (raw_ints% [1310837915796476290828039859194449]) 0) 36 true) .empty .empty)))

#time def treeT_J011_part098 : IntSourceTree :=
  (.node 667 (sourceLit (List.headD (raw_ints% [64533932387152540151684483713001355]) 0) 33 true) (.node 665 (sourceLit (List.headD (raw_ints% [101021204842195798657827977982764625]) 0) 33 true) (.node 664 (sourceLit (List.headD (raw_ints% [5516156103419342532029559846460095957975]) 0) 31 false) (.node 663 (sourceLit (List.headD (raw_ints% [177987157669838697732503816479913025]) 0) 33 true) .empty .empty) .empty) (.node 666 (sourceLit (List.headD (raw_ints% [1818846234939338993033383130396916491475]) 0) 32 true) .empty .empty)) (.node 669 (sourceLit (List.headD (raw_ints% [44756951342818766338941661142130105]) 0) 33 true) (.node 668 (sourceLit (List.headD (raw_ints% [3879012464140616012454847635867430959675]) 0) 29 false) .empty .empty) (.node 670 (sourceLit (List.headD (raw_ints% [76323390787301791580752263437053575]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part099 : IntSourceTree :=
  (.node 639 (sourceLit (List.headD (raw_ints% [4873051405803593659713673468061025]) 0) 34 true) treeT_J011_part097 treeT_J011_part098)

#time def treeT_J011_part100 : IntSourceTree :=
  (.node 630 (sourceLit (List.headD (raw_ints% [1439729836480140250104921463946685]) 0) 37 true) treeT_J011_part096 treeT_J011_part099)

#time def treeT_J011_part101 : IntSourceTree :=
  (.node 676 (sourceLit (List.headD (raw_ints% [293171882737866947373299386829235975]) 0) 29 true) (.node 674 (sourceLit (List.headD (raw_ints% [90442864400026354040762571028004415]) 0) 31 true) (.node 673 (sourceLit (List.headD (raw_ints% [50806851422638982008879869956986545]) 0) 32 true) (.node 672 (sourceLit (List.headD (raw_ints% [115173180562400718474709321871506965]) 0) 31 true) .empty .empty) .empty) (.node 675 (sourceLit (List.headD (raw_ints% [40566481132673813534039113357572675]) 0) 32 true) .empty .empty)) (.node 678 (sourceLit (List.headD (raw_ints% [60914983791004243365670923886549605]) 0) 31 true) (.node 677 (sourceLit (List.headD (raw_ints% [33314277092708203197790098553230501]) 0) 32 true) .empty .empty) (.node 679 (sourceLit (List.headD (raw_ints% [27989219965172002792383339967064631]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part102 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [33239112650977644338102289430556625]) 0) 34 true) (.node 708 (sourceLit (List.headD (raw_ints% [49264007177055235592469524691738195]) 0) 34 true) (.node 707 (sourceLit (List.headD (raw_ints% [1940056139382711381030278506413075408675]) 0) 33 true) (.node 706 (sourceLit (List.headD (raw_ints% [79603867697602040826757382740775625]) 0) 34 true) .empty .empty) .empty) (.node 709 (sourceLit (List.headD (raw_ints% [3879223375549135412767414718686404553875]) 0) 30 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [23897586328748345803921410209888835]) 0) 34 true) (.node 711 (sourceLit (List.headD (raw_ints% [55982689836659858413145598651582525]) 0) 33 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [82596983071883847037015279640876685]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part103 : IntSourceTree :=
  (.node 705 (sourceLit (List.headD (raw_ints% [6364980832769195035399532966545684311375]) 0) 32 false) treeT_J011_part101 treeT_J011_part102)

#time def treeT_J011_part104 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [41422778167789868726816230014305505]) 0) 32 true) (.node 717 (sourceLit (List.headD (raw_ints% [202515135871899572146370436302452095]) 0) 30 true) (.node 716 (sourceLit (List.headD (raw_ints% [28262822186792917769440387428888075]) 0) 33 true) (.node 715 (sourceLit (List.headD (raw_ints% [63585781828453995474759091736653575]) 0) 32 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [22827573766336392871165779679674909]) 0) 33 true) .empty .empty)) (.node 747 (sourceLit (List.headD (raw_ints% [253881538403255623155345047250101145]) 0) 33 true) (.node 746 (sourceLit (List.headD (raw_ints% [14548807900477729063832449063488285114225]) 0) 32 false) .empty .empty) (.node 748 (sourceLit (List.headD (raw_ints% [65960808924387380205423759841085844037275]) 0) 29 true) .empty .empty)))

#time def treeT_J011_part105 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [239945067887509034107298547535502325]) 0) 31 true) (.node 752 (sourceLit (List.headD (raw_ints% [332688338130878148830455467341153235]) 0) 31 true) (.node 751 (sourceLit (List.headD (raw_ints% [99994957853633053446765303446020425]) 0) 33 true) (.node 750 (sourceLit (List.headD (raw_ints% [3879376022330710016350576223213278661025]) 0) 31 false) .empty .empty) .empty) (.node 753 (sourceLit (List.headD (raw_ints% [140373839207347784422491411722124135]) 0) 32 true) .empty .empty)) (.node 756 (sourceLit (List.headD (raw_ints% [724200626517396980222846080957221225]) 0) 29 true) (.node 755 (sourceLit (List.headD (raw_ints% [103694581316435345427873510857148705]) 0) 32 true) .empty .empty) (.node 757 (sourceLit (List.headD (raw_ints% [79737011654463467879971451162321799]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part106 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [152299077365402176030936437624822675]) 0) 33 true) treeT_J011_part104 treeT_J011_part105)

#time def treeT_J011_part107 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [36065265612277289740478156053680345]) 0) 33 true) treeT_J011_part103 treeT_J011_part106)

#time def treeT_J011_part108 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [32961492750277523905643854276206075]) 0) 33 true) treeT_J011_part100 treeT_J011_part107)

#time def treeT_J011_part109 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [59529982357212265846417074097133025]) 0) 35 true) (.node 788 (sourceLit (List.headD (raw_ints% [102308765613100193781437761279181475]) 0) 35 true) (.node 787 (sourceLit (List.headD (raw_ints% [4122216009965110111215681892475340130725]) 0) 35 false) (.node 759 (sourceLit (List.headD (raw_ints% [63321075100173568692279778751635005]) 0) 32 true) .empty .empty) .empty) (.node 789 (sourceLit (List.headD (raw_ints% [34920016149968257809095587279886124295575]) 0) 31 true) .empty .empty)) (.node 792 (sourceLit (List.headD (raw_ints% [38048685762442353821421946618065795]) 0) 35 true) (.node 791 (sourceLit (List.headD (raw_ints% [3879487987710383336067402514410581826075]) 0) 32 false) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [125045677529497150896720093850138275]) 0) 33 true) .empty .empty)))

#time def treeT_J011_part110 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [100177373913105460053883282401596985]) 0) 32 true) (.node 797 (sourceLit (List.headD (raw_ints% [260842745322748704038237822327384565]) 0) 31 true) (.node 796 (sourceLit (List.headD (raw_ints% [37715879564821213829216561714130315]) 0) 34 true) (.node 795 (sourceLit (List.headD (raw_ints% [88179643029527519316269727899424375]) 0) 33 true) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [28454718944063537504402835741323445]) 0) 34 true) .empty .empty)) (.node 829 (sourceLit (List.headD (raw_ints% [666171047539399374220565652608629125]) 0) 33 true) (.node 828 (sourceLit (List.headD (raw_ints% [593604458199921474441031042077929380770075]) 0) 29 false) .empty .empty) (.node 830 (sourceLit (List.headD (raw_ints% [73719408322267225634541750782985527252175]) 0) 31 true) .empty .empty)))

#time def treeT_J011_part111 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [52154286797535247341006627834221895]) 0) 34 true) treeT_J011_part109 treeT_J011_part110)

#time def treeT_J011_part112 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [2097547950427483637897785211824358775]) 0) 29 true) (.node 834 (sourceLit (List.headD (raw_ints% [760420352348468173066462203265603875]) 0) 31 true) (.node 833 (sourceLit (List.headD (raw_ints% [468405132991729876720259734166928585]) 0) 32 true) (.node 832 (sourceLit (List.headD (raw_ints% [15518284639179664222418440513109668457535]) 0) 31 false) .empty .empty) .empty) (.node 835 (sourceLit (List.headD (raw_ints% [313539713063846633300179511816626455]) 0) 32 true) .empty .empty)) (.node 838 (sourceLit (List.headD (raw_ints% [23755333660287629955986008264929165]) 0) 35 true) (.node 837 (sourceLit (List.headD (raw_ints% [221990024864106242753761042550720721]) 0) 32 true) .empty .empty) (.node 839 (sourceLit (List.headD (raw_ints% [164316676452334731342942907178952555]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part113 : IntSourceTree :=
  (.node 874 (sourceLit (List.headD (raw_ints% [364096559396659382038246478498484795]) 0) 33 true) (.node 872 (sourceLit (List.headD (raw_ints% [300147529479180365681727396094912185]) 0) 34 true) (.node 871 (sourceLit (List.headD (raw_ints% [38799448154988804485304576648698054539125]) 0) 33 true) (.node 870 (sourceLit (List.headD (raw_ints% [547111082824974842527731504414363075]) 0) 34 true) .empty .empty) .empty) (.node 873 (sourceLit (List.headD (raw_ints% [15518534730534723216720233953297368734085]) 0) 32 false) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [238107953934204205641746388388365825]) 0) 33 true) (.node 875 (sourceLit (List.headD (raw_ints% [584061066289413134433922747466755125]) 0) 32 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [1575862459781986229821309567169589645]) 0) 30 true) .empty .empty)))

#time def treeT_J011_part114 : IntSourceTree :=
  (.node 869 (sourceLit (List.headD (raw_ints% [663444490499857990059222216637701629361225]) 0) 30 false) treeT_J011_part112 treeT_J011_part113)

#time def treeT_J011_part115 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [376244901004065073324571289331043775]) 0) 33 true) treeT_J011_part111 treeT_J011_part114)

#time def treeT_J011_part116 : IntSourceTree :=
  (.node 913 (sourceLit (List.headD (raw_ints% [1932775102841713048733559434592368895]) 0) 32 true) (.node 911 (sourceLit (List.headD (raw_ints% [1812199430295834296786354728326408525]) 0) 33 true) (.node 910 (sourceLit (List.headD (raw_ints% [92145487352765651961720495927585894576675]) 0) 34 false) (.node 879 (sourceLit (List.headD (raw_ints% [279907964651496619241892849837269655]) 0) 32 true) .empty .empty) .empty) (.node 912 (sourceLit (List.headD (raw_ints% [325913869879090100104855053702694104770535]) 0) 31 true) .empty .empty)) (.node 915 (sourceLit (List.headD (raw_ints% [1142846524522790894852806402177312725]) 0) 32 true) (.node 914 (sourceLit (List.headD (raw_ints% [62074899342491241335054002275392740540215]) 0) 31 false) .empty .empty) (.node 916 (sourceLit (List.headD (raw_ints% [7247429110203126513044978747643723225]) 0) 29 true) .empty .empty)))

#time def treeT_J011_part117 : IntSourceTree :=
  (.node 953 (sourceLit (List.headD (raw_ints% [85358101152406205830393821913997868376155]) 0) 34 true) (.node 951 (sourceLit (List.headD (raw_ints% [407381397566051412332186560359041632845825]) 0) 33 false) (.node 919 (sourceLit (List.headD (raw_ints% [496005671451581939636878577093342769]) 0) 32 true) (.node 918 (sourceLit (List.headD (raw_ints% [1195777121217384150525533434930723005]) 0) 31 true) .empty .empty) .empty) (.node 952 (sourceLit (List.headD (raw_ints% [378012975204163482776156833057874085]) 0) 36 true) .empty .empty)) (.node 955 (sourceLit (List.headD (raw_ints% [15518870850889382687047109049535051823835]) 0) 34 false) (.node 954 (sourceLit (List.headD (raw_ints% [392169635861263416673828239023471025]) 0) 35 true) .empty .empty) (.node 956 (sourceLit (List.headD (raw_ints% [226184642647146672302765003447236725]) 0) 35 true) .empty .empty)))

#time def treeT_J011_part118 : IntSourceTree :=
  (.node 917 (sourceLit (List.headD (raw_ints% [730441790872710579813224511002742579]) 0) 32 true) treeT_J011_part116 treeT_J011_part117)

#time def treeT_J011_part119 : IntSourceTree :=
  (.node 996 (sourceLit (List.headD (raw_ints% [993214981886030695097528024148990960448665]) 0) 29 false) (.node 994 (sourceLit (List.headD (raw_ints% [1427804517780990534621355152899358634558695]) 0) 31 true) (.node 959 (sourceLit (List.headD (raw_ints% [457934578282943765641820292546726675]) 0) 33 true) (.node 958 (sourceLit (List.headD (raw_ints% [141340300974182853017067284983667187]) 0) 35 true) .empty .empty) .empty) (.node 995 (sourceLit (List.headD (raw_ints% [5131867649257423771928445422198223675]) 0) 32 true) .empty .empty)) (.node 998 (sourceLit (List.headD (raw_ints% [4475789529203756132698135745543410575]) 0) 31 true) (.node 997 (sourceLit (List.headD (raw_ints% [2888512491481636177031015544153045021]) 0) 32 true) .empty .empty) (.node 999 (sourceLit (List.headD (raw_ints% [1765439144135343708636197982645332223]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [24831295000838799741010225449708972430113225]) 0) 29 true) (.node 1038 (sourceLit (List.headD (raw_ints% [2323151287584904764962746404218376273]) 0) 33 true) (.node 1037 (sourceLit (List.headD (raw_ints% [993220653452681116237811247818171434582245]) 0) 30 false) (.node 1036 (sourceLit (List.headD (raw_ints% [4227129078668837082717385408409276775]) 0) 33 true) .empty .empty) .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [3559920372637868601414495160449957225]) 0) 32 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [248306282310552579998485986488479244498205]) 0) 33 false) (.node 1077 (sourceLit (List.headD (raw_ints% [14020003823193712153838526089484062079]) 0) 32 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [7527166006204275351214787634228172869]) 0) 32 true) .empty .empty)))

#time def treeT_J011_part121 : IntSourceTree :=
  (.node 1035 (sourceLit (List.headD (raw_ints% [1489880001184548065369543589097498841854035]) 0) 32 true) treeT_J011_part119 treeT_J011_part120)

#time def treeT_J011_part122 : IntSourceTree :=
  (.node 957 (sourceLit (List.headD (raw_ints% [1417891662605285070805917295118533395]) 0) 32 true) treeT_J011_part118 treeT_J011_part121)

#time def treeT_J011_part123 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [165080586975979167744955371068073831]) 0) 33 true) treeT_J011_part115 treeT_J011_part122)

#time def treeT_J011_part124 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [70800076040447664390349756207951245]) 0) 32 true) treeT_J011_part108 treeT_J011_part123)

#time def treeT_J011_part125 : IntSourceTree :=
  (.node 590 (sourceLit (List.headD (raw_ints% [29132313472398364702789146049743525]) 0) 32 true) treeT_J011_part093 treeT_J011_part124)

#time def treeT_J011_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [1862488205911332384228066817825875]) 0) 33 true) treeT_J011_part062 treeT_J011_part125)

#time def treeT_J011 : IntSourceTree := treeT_J011_part126

#time def treeT_J012_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [244889534112722748541689081559875]) 0) 33 true) (.node 5 (sourceLit (List.headD (raw_ints% [1147060035163326584860345505845125]) 0) 31 true) (.node 4 (sourceLit (List.headD (raw_ints% [158692890232174545229579671949875]) 0) 34 true) (.node 3 (sourceLit (List.headD (raw_ints% [360627462931579334001475820630775]) 0) 33 true) .empty .empty) .empty) (.node 6 (sourceLit (List.headD (raw_ints% [131731321946047303870806896068875]) 0) 34 true) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [51406921033990123554810857624625]) 0) 35 true) (.node 9 (sourceLit (List.headD (raw_ints% [216704313530024664487959582141375]) 0) 33 true) (.node 8 (sourceLit (List.headD (raw_ints% [114799323104634298015770987026925]) 0) 34 true) .empty .empty) .empty) (.node 11 (sourceLit (List.headD (raw_ints% [97985567716721506223258264533125]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [624251866721599573952303082148875]) 0) 31 true) (.node 15 (sourceLit (List.headD (raw_ints% [41712919653893388459112811131875]) 0) 35 true) (.node 14 (sourceLit (List.headD (raw_ints% [10814460651009397007918136219375]) 0) 37 true) (.node 13 (sourceLit (List.headD (raw_ints% [14081082725591906630259356204272875]) 0) 31 false) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [20152661594103225535390304637375]) 0) 36 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [293845691455509673036000844024625]) 0) 32 true) (.node 18 (sourceLit (List.headD (raw_ints% [151313994702084086292189702707775]) 0) 33 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [142846708484015082260894890549125]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 35 true) treeT_J012_part000 treeT_J012_part001)

#time def treeT_J012_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [123327676606580139360174196290525]) 0) 33 true) (.node 24 (sourceLit (List.headD (raw_ints% [129050741602460198894645013139125]) 0) 33 true) (.node 23 (sourceLit (List.headD (raw_ints% [264351563565325876023462747744075]) 0) 32 true) (.node 22 (sourceLit (List.headD (raw_ints% [135501334226140867600676413728375]) 0) 33 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [504427827756381209525461886143875]) 0) 31 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [118205792110957069745131932481455]) 0) 33 true) (.node 27 (sourceLit (List.headD (raw_ints% [241396497299088141106515663075975]) 0) 32 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [1853422875071854423950085141994325]) 0) 29 true) .empty .empty)))

#time def treeT_J012_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [415117706468470110792112386644775]) 0) 31 true) (.node 33 (sourceLit (List.headD (raw_ints% [859529783595173653117924560296505]) 0) 30 true) (.node 32 (sourceLit (List.headD (raw_ints% [109396340250335423802281237648175]) 0) 33 true) (.node 31 (sourceLit (List.headD (raw_ints% [222885435813754874702138625953925]) 0) 32 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [211141745922111921962123372462025]) 0) 32 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [1606599820487092403599086706421175]) 0) 29 true) (.node 36 (sourceLit (List.headD (raw_ints% [204123146113268201006530700031675]) 0) 32 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [197655562924202341572748723329741]) 0) 32 true) .empty .empty)))

#time def treeT_J012_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [113587568341772277631236189556725]) 0) 33 true) treeT_J012_part003 treeT_J012_part004)

#time def treeT_J012_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [1112397350158603304708612850525375]) 0) 30 true) treeT_J012_part002 treeT_J012_part005)

#time def treeT_J012_part007 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [244889534112722748541689081559875]) 0) 34 true) (.node 46 (sourceLit (List.headD (raw_ints% [1147060035163326584860345505845125]) 0) 32 true) (.node 45 (sourceLit (List.headD (raw_ints% [158692890232174545229579671949875]) 0) 35 true) (.node 44 (sourceLit (List.headD (raw_ints% [360627462931579334001475820630775]) 0) 34 true) .empty .empty) .empty) (.node 47 (sourceLit (List.headD (raw_ints% [131731321946047303870806896068875]) 0) 35 true) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [216704313530024664487959582141375]) 0) 34 true) (.node 49 (sourceLit (List.headD (raw_ints% [114799323104634298015770987026925]) 0) 35 true) .empty .empty) (.node 51 (sourceLit (List.headD (raw_ints% [51406921033990123554810857624625]) 0) 36 true) .empty .empty)))

#time def treeT_J012_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [20152661594103225535390304637375]) 0) 37 true) (.node 55 (sourceLit (List.headD (raw_ints% [10814460651009397007918136219375]) 0) 38 true) (.node 54 (sourceLit (List.headD (raw_ints% [14081082725591906630259356204272875]) 0) 32 false) (.node 53 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 36 true) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [41712919653893388459112811131875]) 0) 36 true) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [151313994702084086292189702707775]) 0) 34 true) (.node 58 (sourceLit (List.headD (raw_ints% [624251866721599573952303082148875]) 0) 32 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [293845691455509673036000844024625]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [97985567716721506223258264533125]) 0) 35 true) treeT_J012_part007 treeT_J012_part008)

#time def treeT_J012_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [504427827756381209525461886143875]) 0) 32 true) (.node 64 (sourceLit (List.headD (raw_ints% [264351563565325876023462747744075]) 0) 33 true) (.node 63 (sourceLit (List.headD (raw_ints% [135501334226140867600676413728375]) 0) 34 true) (.node 62 (sourceLit (List.headD (raw_ints% [1112397350158603304708612850525375]) 0) 31 true) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [129050741602460198894645013139125]) 0) 34 true) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [241396497299088141106515663075975]) 0) 33 true) (.node 67 (sourceLit (List.headD (raw_ints% [123327676606580139360174196290525]) 0) 34 true) .empty .empty) (.node 69 (sourceLit (List.headD (raw_ints% [118205792110957069745131932481455]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [211141745922111921962123372462025]) 0) 33 true) (.node 73 (sourceLit (List.headD (raw_ints% [109396340250335423802281237648175]) 0) 34 true) (.node 72 (sourceLit (List.headD (raw_ints% [222885435813754874702138625953925]) 0) 33 true) (.node 71 (sourceLit (List.headD (raw_ints% [113587568341772277631236189556725]) 0) 34 true) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [859529783595173653117924560296505]) 0) 31 true) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [204123146113268201006530700031675]) 0) 33 true) (.node 76 (sourceLit (List.headD (raw_ints% [415117706468470110792112386644775]) 0) 32 true) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [1606599820487092403599086706421175]) 0) 30 true) .empty .empty)))

#time def treeT_J012_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [1853422875071854423950085141994325]) 0) 30 true) treeT_J012_part010 treeT_J012_part011)

#time def treeT_J012_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [142846708484015082260894890549125]) 0) 34 true) treeT_J012_part009 treeT_J012_part012)

#time def treeT_J012_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [389213766009741161233613829616425]) 0) 31 true) treeT_J012_part006 treeT_J012_part013)

#time def treeT_J012_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [762853822920866329678796744098125]) 0) 33 true) (.node 87 (sourceLit (List.headD (raw_ints% [451085250525301918159328212142625]) 0) 34 true) (.node 86 (sourceLit (List.headD (raw_ints% [503040238982650877047511791730625]) 0) 34 true) (.node 85 (sourceLit (List.headD (raw_ints% [4622979371741942759163267624247275]) 0) 31 true) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [412125964679554917467456597248575]) 0) 34 true) .empty .empty)) (.node 91 (sourceLit (List.headD (raw_ints% [335423059343327822752660899749625]) 0) 34 true) (.node 90 (sourceLit (List.headD (raw_ints% [178191725175278472476731116429225]) 0) 35 true) .empty .empty) (.node 92 (sourceLit (List.headD (raw_ints% [158765021314919773851598173547875]) 0) 35 true) .empty .empty)))

#time def treeT_J012_part016 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [493571176309219130840300045688225]) 0) 33 true) (.node 96 (sourceLit (List.headD (raw_ints% [66363023613971950527954785117625]) 0) 36 true) (.node 95 (sourceLit (List.headD (raw_ints% [14247934404207480184095807448800375]) 0) 33 false) (.node 94 (sourceLit (List.headD (raw_ints% [18024101085015661679863560365625]) 0) 38 true) .empty .empty) .empty) (.node 97 (sourceLit (List.headD (raw_ints% [2045374991127577287430916830291125]) 0) 31 true) .empty .empty)) (.node 100 (sourceLit (List.headD (raw_ints% [462409270324321262907863920281975]) 0) 33 true) (.node 99 (sourceLit (List.headD (raw_ints% [954658041987689474868605320273125]) 0) 32 true) .empty .empty) (.node 101 (sourceLit (List.headD (raw_ints% [3589133713129551463867400653868625]) 0) 30 true) .empty .empty)))

#time def treeT_J012_part017 : IntSourceTree :=
  (.node 93 (sourceLit (List.headD (raw_ints% [17216620892526994829403620669332875]) 0) 31 true) treeT_J012_part015 treeT_J012_part016)

#time def treeT_J012_part018 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [767459158213674277944408109211775]) 0) 32 true) (.node 105 (sourceLit (List.headD (raw_ints% [1610384680766225798662240095808725]) 0) 31 true) (.node 104 (sourceLit (List.headD (raw_ints% [412954595302103271508060641774375]) 0) 33 true) (.node 103 (sourceLit (List.headD (raw_ints% [212011446648319357171287525695325]) 0) 34 true) .empty .empty) .empty) (.node 106 (sourceLit (List.headD (raw_ints% [392875289803260656218405856265975]) 0) 33 true) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [5871265038498966091458416076436875]) 0) 29 true) (.node 108 (sourceLit (List.headD (raw_ints% [375104914315363487695564852680645]) 0) 33 true) .empty .empty) (.node 110 (sourceLit (List.headD (raw_ints% [359235600102056001349291540369095]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [640443837575179486841962789816425]) 0) 32 true) (.node 114 (sourceLit (List.headD (raw_ints% [664028976080571468456126528723375]) 0) 32 true) (.node 113 (sourceLit (List.headD (raw_ints% [2706637189424904342116293454966295]) 0) 30 true) (.node 112 (sourceLit (List.headD (raw_ints% [344953933116753686722663520578725]) 0) 33 true) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [1303941860721877195443736733948235]) 0) 31 true) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [618837021528870462453374076796959]) 0) 32 true) (.node 117 (sourceLit (List.headD (raw_ints% [5035283483008429369074711479895225]) 0) 29 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [608693027238675621182736438402375]) 0) 32 true) .empty .empty)))

#time def treeT_J012_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [1407652003444344674545807890086475]) 0) 31 true) treeT_J012_part018 treeT_J012_part019)

#time def treeT_J012_part021 : IntSourceTree :=
  (.node 102 (sourceLit (List.headD (raw_ints% [435885499709919461442903148468125]) 0) 33 true) treeT_J012_part017 treeT_J012_part020)

#time def treeT_J012_part022 : IntSourceTree :=
  (.node 131 (sourceLit (List.headD (raw_ints% [15848100517661043615240032350575]) 0) 39 true) (.node 129 (sourceLit (List.headD (raw_ints% [148663320787460309725842805110825]) 0) 36 true) (.node 128 (sourceLit (List.headD (raw_ints% [657280966937881087776967342725375]) 0) 34 true) (.node 127 (sourceLit (List.headD (raw_ints% [185654458518301786588352447830875]) 0) 36 true) .empty .empty) .empty) (.node 130 (sourceLit (List.headD (raw_ints% [273074754695420832595418580978375]) 0) 35 true) .empty .empty)) (.node 133 (sourceLit (List.headD (raw_ints% [55951179246939526741976458298625]) 0) 37 true) (.node 132 (sourceLit (List.headD (raw_ints% [59359372906651579132350658804125]) 0) 37 true) .empty .empty) (.node 134 (sourceLit (List.headD (raw_ints% [15648851809059450729831488436802875]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part023 : IntSourceTree :=
  (.node 140 (sourceLit (List.headD (raw_ints% [165203087633044950458151119062125]) 0) 35 true) (.node 138 (sourceLit (List.headD (raw_ints% [710561562202988856739306874071125]) 0) 33 true) (.node 137 (sourceLit (List.headD (raw_ints% [23105181009934362496282240240125]) 0) 38 true) (.node 136 (sourceLit (List.headD (raw_ints% [14414786082823053737932258693327875]) 0) 34 false) .empty .empty) .empty) (.node 139 (sourceLit (List.headD (raw_ints% [171128590803567522274055171490225]) 0) 35 true) .empty .empty)) (.node 142 (sourceLit (List.headD (raw_ints% [1238368181485474079579393901671625]) 0) 32 true) (.node 141 (sourceLit (List.headD (raw_ints% [159781280920153090323484514866425]) 0) 35 true) .empty .empty) (.node 143 (sourceLit (List.headD (raw_ints% [150192082741889296921113367369875]) 0) 35 true) .empty .empty)))

#time def treeT_J012_part024 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [25233741519021926351808984511875]) 0) 38 true) treeT_J012_part022 treeT_J012_part023)

#time def treeT_J012_part025 : IntSourceTree :=
  (.node 149 (sourceLit (List.headD (raw_ints% [128449561102203208975216460099595]) 0) 35 true) (.node 147 (sourceLit (List.headD (raw_ints% [134773806598340258429115829987725]) 0) 35 true) (.node 146 (sourceLit (List.headD (raw_ints% [552978426504922294568389104832425]) 0) 33 true) (.node 145 (sourceLit (List.headD (raw_ints% [141951926849821536306707814317625]) 0) 35 true) .empty .empty) .empty) (.node 148 (sourceLit (List.headD (raw_ints% [65757832614323267104736555766975]) 0) 36 true) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [122824015880141861859027675406185]) 0) 35 true) (.node 150 (sourceLit (List.headD (raw_ints% [2008921081713555833754165467221275]) 0) 31 true) .empty .empty) (.node 152 (sourceLit (List.headD (raw_ints% [961881131816834925141530638178625]) 0) 32 true) .empty .empty)))

#time def treeT_J012_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [1714341831260668482737812386737025]) 0) 31 true) (.node 156 (sourceLit (List.headD (raw_ints% [222206038563351771162906086825865]) 0) 34 true) (.node 155 (sourceLit (List.headD (raw_ints% [226443615079229773247001578130675]) 0) 34 true) (.node 154 (sourceLit (List.headD (raw_ints% [923553702914865344499184447334895]) 0) 32 true) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [218160345730955642917716044892375]) 0) 34 true) .empty .empty)) (.node 167 (sourceLit (List.headD (raw_ints% [643437208882003084496066423529225]) 0) 35 true) (.node 159 (sourceLit (List.headD (raw_ints% [210590729302334060440312676733609]) 0) 34 true) .empty .empty) (.node 168 (sourceLit (List.headD (raw_ints% [1073109703466859375239362985398425]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [117778796433209131460191141465275]) 0) 35 true) treeT_J012_part025 treeT_J012_part026)

#time def treeT_J012_part028 : IntSourceTree :=
  (.node 144 (sourceLit (List.headD (raw_ints% [583694223027951552661687355037225]) 0) 33 true) treeT_J012_part024 treeT_J012_part027)

#time def treeT_J012_part029 : IntSourceTree :=
  (.node 126 (sourceLit (List.headD (raw_ints% [1737959668289308087151461059201075]) 0) 33 true) treeT_J012_part021 treeT_J012_part028)

#time def treeT_J012_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [197655562924202341572748723329741]) 0) 33 true) treeT_J012_part014 treeT_J012_part029)

#time def treeT_J012_part031 : IntSourceTree :=
  (.node 174 (sourceLit (List.headD (raw_ints% [4740884770240483132764112241625]) 0) 41 true) (.node 172 (sourceLit (List.headD (raw_ints% [348374195250233621836082861670525]) 0) 35 true) (.node 171 (sourceLit (List.headD (raw_ints% [756875959438355507629013424163875]) 0) 34 true) (.node 170 (sourceLit (List.headD (raw_ints% [416461557974562766426640104014075]) 0) 35 true) .empty .empty) .empty) (.node 173 (sourceLit (List.headD (raw_ints% [9618621160475592700462736342404875]) 0) 31 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [135506908538203460286517090977375]) 0) 36 true) (.node 175 (sourceLit (List.headD (raw_ints% [45545638022326381643758784322406125]) 0) 33 true) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [232681952316296437094347055923537125]) 0) 31 false) .empty .empty)))

#time def treeT_J012_part032 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [814345288188835365236818850280975]) 0) 33 true) (.node 181 (sourceLit (List.headD (raw_ints% [6983863895385325365454270966107375]) 0) 30 true) (.node 180 (sourceLit (List.headD (raw_ints% [906619456104218915284577451639825]) 0) 33 true) (.node 179 (sourceLit (List.headD (raw_ints% [1887588206824265952088622176011375]) 0) 32 true) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [842364747651305261144972970463275]) 0) 33 true) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [3059169103457386622631258744489075]) 0) 31 true) (.node 184 (sourceLit (List.headD (raw_ints% [788582066633011103860846297184625]) 0) 33 true) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [742740124995311634235256658275025]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part033 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [985160408326580068921763329679775]) 0) 33 true) treeT_J012_part031 treeT_J012_part032)

#time def treeT_J012_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [637638193924381208149557882670755]) 0) 33 true) (.node 190 (sourceLit (List.headD (raw_ints% [668360888715569670452440140427665]) 0) 33 true) (.node 189 (sourceLit (List.headD (raw_ints% [10962740110767790287354142199908725]) 0) 29 true) (.node 188 (sourceLit (List.headD (raw_ints% [703085538471358579737361787221155]) 0) 33 true) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [2610190159982766992962523044356075]) 0) 31 true) .empty .empty)) (.node 194 (sourceLit (List.headD (raw_ints% [1220431766850774634906931734721025]) 0) 32 true) (.node 193 (sourceLit (List.headD (raw_ints% [4988411865109775059015951650462705]) 0) 30 true) .empty .empty) (.node 195 (sourceLit (List.headD (raw_ints% [2390272950937584182553001055391345]) 0) 31 true) .empty .empty)))

#time def treeT_J012_part035 : IntSourceTree :=
  (.node 209 (sourceLit (List.headD (raw_ints% [775783061891938755787677375176775]) 0) 35 true) (.node 199 (sourceLit (List.headD (raw_ints% [552824402010996430777537974167325]) 0) 33 true) (.node 198 (sourceLit (List.headD (raw_ints% [1126445744318774680888354282342041]) 0) 32 true) (.node 197 (sourceLit (List.headD (raw_ints% [9185902985046083985351278076960135]) 0) 29 true) .empty .empty) .empty) (.node 208 (sourceLit (List.headD (raw_ints% [1916467868590131250207298351391525]) 0) 34 true) .empty .empty)) (.node 211 (sourceLit (List.headD (raw_ints% [289676753833274417504719845209475]) 0) 36 true) (.node 210 (sourceLit (List.headD (raw_ints% [1320120535439816356238235464846625]) 0) 34 true) .empty .empty) (.node 212 (sourceLit (List.headD (raw_ints% [519438467811749191099610788947375]) 0) 35 true) .empty .empty)))

#time def treeT_J012_part036 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [1171105083058658699134049835228975]) 0) 32 true) treeT_J012_part034 treeT_J012_part035)

#time def treeT_J012_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [1444454547806014900329148310117925]) 0) 32 true) treeT_J012_part033 treeT_J012_part036)

#time def treeT_J012_part038 : IntSourceTree :=
  (.node 218 (sourceLit (List.headD (raw_ints% [234103075440702414807825669671679375]) 0) 32 false) (.node 216 (sourceLit (List.headD (raw_ints% [3747526506571839711355690188483375]) 0) 38 true) (.node 215 (sourceLit (List.headD (raw_ints% [50620414804825803772416811354125]) 0) 38 true) (.node 214 (sourceLit (List.headD (raw_ints% [40916324778594494160125713216010625]) 0) 32 false) .empty .empty) .empty) (.node 217 (sourceLit (List.headD (raw_ints% [89296546518334735293952610497125]) 0) 37 true) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [1226775856292086150256017699762875]) 0) 33 true) (.node 219 (sourceLit (List.headD (raw_ints% [642903226719445024373652986699325]) 0) 34 true) .empty .empty) (.node 221 (sourceLit (List.headD (raw_ints% [587056894263912734637608421906975]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [473192511798631117377024998299575]) 0) 34 true) (.node 225 (sourceLit (List.headD (raw_ints% [504678212933368031247430668549375]) 0) 34 true) (.node 224 (sourceLit (List.headD (raw_ints% [1044996353349719177811950345524725]) 0) 33 true) (.node 223 (sourceLit (List.headD (raw_ints% [541980582167526667302746235723525]) 0) 34 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [1953212250447542033494480534824225]) 0) 32 true) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [446186416266952161786928867021965]) 0) 34 true) (.node 228 (sourceLit (List.headD (raw_ints% [918391886891428763491255863982125]) 0) 33 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [6944897947340678619845811265466175]) 0) 30 true) .empty .empty)))

#time def treeT_J012_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [4507127532414377206295483162764125]) 0) 31 true) treeT_J012_part038 treeT_J012_part039)

#time def treeT_J012_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [1501448796684177097901376708087885]) 0) 32 true) (.node 234 (sourceLit (List.headD (raw_ints% [3141304459280044370017582755792915]) 0) 31 true) (.node 233 (sourceLit (List.headD (raw_ints% [402080601057962945229175599740205]) 0) 34 true) (.node 232 (sourceLit (List.headD (raw_ints% [824154514082966033910496203088725]) 0) 33 true) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [767544536692315088412928578459675]) 0) 33 true) .empty .empty)) (.node 238 (sourceLit (List.headD (raw_ints% [5757219322524747019875653303486085]) 0) 30 true) (.node 237 (sourceLit (List.headD (raw_ints% [734784391596747413298617745444225]) 0) 33 true) .empty .empty) (.node 239 (sourceLit (List.headD (raw_ints% [705264285714106560007728928874823]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part042 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [160617680432506838227904149207275]) 0) 37 true) (.node 252 (sourceLit (List.headD (raw_ints% [810332820082864048182796519167375]) 0) 35 true) (.node 251 (sourceLit (List.headD (raw_ints% [1883365111441277204847457505529375]) 0) 34 true) (.node 250 (sourceLit (List.headD (raw_ints% [1135104565809314745148714646339475]) 0) 35 true) .empty .empty) .empty) (.node 253 (sourceLit (List.headD (raw_ints% [26240652130451566815650281588720875]) 0) 31 true) .empty .empty)) (.node 256 (sourceLit (List.headD (raw_ints% [269456409900402969892817399855625]) 0) 36 true) (.node 255 (sourceLit (List.headD (raw_ints% [43230981400460437901942248769208375]) 0) 34 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [1192048737998687403201403744175281125]) 0) 31 true) .empty .empty)))

#time def treeT_J012_part043 : IntSourceTree :=
  (.node 249 (sourceLit (List.headD (raw_ints% [5799601429529866979400120778762725]) 0) 33 true) treeT_J012_part041 treeT_J012_part042)

#time def treeT_J012_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [422712856955285946734384789615295]) 0) 34 true) treeT_J012_part040 treeT_J012_part043)

#time def treeT_J012_part045 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [236471836756354568352129945073275]) 0) 36 true) treeT_J012_part037 treeT_J012_part044)

#time def treeT_J012_part046 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [2878436956036706475821845462202175]) 0) 32 true) (.node 261 (sourceLit (List.headD (raw_ints% [12644549805288053038642012230098625]) 0) 30 true) (.node 260 (sourceLit (List.headD (raw_ints% [1664993450773561182210034495157475]) 0) 33 true) (.node 259 (sourceLit (List.headD (raw_ints% [470093739088229095567739961519370125]) 0) 32 false) .empty .empty) .empty) (.node 262 (sourceLit (List.headD (raw_ints% [1505862829404345677405460717164625]) 0) 33 true) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [5300801723340366799864344019708725]) 0) 31 true) (.node 264 (sourceLit (List.headD (raw_ints% [1379340262037095565350138645709475]) 0) 33 true) .empty .empty) (.node 266 (sourceLit (List.headD (raw_ints% [1275972726738160490754466015922475]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [1053213233896762578787981275790425]) 0) 33 true) (.node 270 (sourceLit (List.headD (raw_ints% [1116384776352238976695275327660195]) 0) 33 true) (.node 269 (sourceLit (List.headD (raw_ints% [18425800269757930144366045447519275]) 0) 29 true) (.node 268 (sourceLit (List.headD (raw_ints% [1189684508723165889770738205977145]) 0) 33 true) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [1083676946839477906720822055277525]) 0) 33 true) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [1996213041612928926926473063200615]) 0) 32 true) (.node 273 (sourceLit (List.headD (raw_ints% [8198060360217681483551987598956895]) 0) 30 true) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [3892335967622504557482164456194485]) 0) 31 true) .empty .empty)))

#time def treeT_J012_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [2461969953089069166659812759530525]) 0) 32 true) treeT_J012_part046 treeT_J012_part047)

#time def treeT_J012_part049 : IntSourceTree :=
  (.node 291 (sourceLit (List.headD (raw_ints% [52839238248502520477749675070625]) 0) 40 true) (.node 279 (sourceLit (List.headD (raw_ints% [3545921714480761296765501406816785]) 0) 31 true) (.node 278 (sourceLit (List.headD (raw_ints% [1812691822068214972306116699434859]) 0) 32 true) (.node 277 (sourceLit (List.headD (raw_ints% [14837277761900749581070749252446025]) 0) 29 true) .empty .empty) .empty) (.node 290 (sourceLit (List.headD (raw_ints% [1119870223522512655790471328479025]) 0) 36 true) .empty .empty)) (.node 293 (sourceLit (List.headD (raw_ints% [143465245831627369957666643523525]) 0) 38 true) (.node 292 (sourceLit (List.headD (raw_ints% [85245415226845500859240419786375]) 0) 39 true) .empty .empty) (.node 294 (sourceLit (List.headD (raw_ints% [16789244227261515243943998701182875]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part050 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [58915064368065147714749497402391625]) 0) 36 false) (.node 298 (sourceLit (List.headD (raw_ints% [356537953359847454502307353461740125]) 0) 34 true) (.node 297 (sourceLit (List.headD (raw_ints% [45039965845517058649716197339625]) 0) 39 true) (.node 296 (sourceLit (List.headD (raw_ints% [73211193453035155592787770277075375]) 0) 35 false) .empty .empty) .empty) (.node 299 (sourceLit (List.headD (raw_ints% [307356463385171609027766804882225]) 0) 36 true) .empty .empty)) (.node 302 (sourceLit (List.headD (raw_ints% [2034355568218418958086632266833625]) 0) 33 true) (.node 301 (sourceLit (List.headD (raw_ints% [269484139127412111893106518312625]) 0) 36 true) .empty .empty) (.node 303 (sourceLit (List.headD (raw_ints% [240970561809204752525678620360275]) 0) 36 true) .empty .empty)))

#time def treeT_J012_part051 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [54998632813840517227743668926575]) 0) 39 true) treeT_J012_part049 treeT_J012_part050)

#time def treeT_J012_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [1899073063710601654517664478609725]) 0) 32 true) treeT_J012_part048 treeT_J012_part051)

#time def treeT_J012_part053 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [185874523114053431995952334738795]) 0) 36 true) (.node 307 (sourceLit (List.headD (raw_ints% [200695053734882343344360254405725]) 0) 36 true) (.node 306 (sourceLit (List.headD (raw_ints% [836897368223206191592465871221125]) 0) 34 true) (.node 305 (sourceLit (List.headD (raw_ints% [218665512275931883525676994290025]) 0) 36 true) .empty .empty) .empty) (.node 308 (sourceLit (List.headD (raw_ints% [96473629137352525198034805971775]) 0) 37 true) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [173417979849238257490222634511225]) 0) 36 true) (.node 310 (sourceLit (List.headD (raw_ints% [2870225580604312881130058545513275]) 0) 32 true) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [1343199379595989779531147907466325]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [2270014609844000640298773987239985]) 0) 32 true) (.node 316 (sourceLit (List.headD (raw_ints% [298860896367290932447598468513325]) 0) 35 true) (.node 315 (sourceLit (List.headD (raw_ints% [307167126230153459628386121185235]) 0) 35 true) (.node 314 (sourceLit (List.headD (raw_ints% [1264188975234409278383601210790995]) 0) 33 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [291072168028463560304761683291375]) 0) 35 true) .empty .empty)) (.node 331 (sourceLit (List.headD (raw_ints% [7075596676738824041476313122302825]) 0) 34 true) (.node 319 (sourceLit (List.headD (raw_ints% [276856884088527103074596942640009]) 0) 35 true) .empty .empty) (.node 332 (sourceLit (List.headD (raw_ints% [2571378427821297262393182685352625]) 0) 35 true) .empty .empty)))

#time def treeT_J012_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [162783158209699908389701419012555]) 0) 36 true) treeT_J012_part053 treeT_J012_part054)

#time def treeT_J012_part056 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [3892786547966052046678953053243775]) 0) 33 true) (.node 336 (sourceLit (List.headD (raw_ints% [610521715121045305751081302969575]) 0) 36 true) (.node 335 (sourceLit (List.headD (raw_ints% [76809469854983468389830246171574125]) 0) 34 true) (.node 334 (sourceLit (List.headD (raw_ints% [413243302894002641602762424886825]) 0) 37 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [3534806928495812382170612393041693125]) 0) 31 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [3252709963389184562234234382958125]) 0) 33 true) (.node 339 (sourceLit (List.headD (raw_ints% [3322397365967008731586198789213291125]) 0) 32 true) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [7553772788917626960526577679736226625]) 0) 30 false) .empty .empty)))

#time def treeT_J012_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [4233208992696580366079914210238475]) 0) 32 true) (.node 345 (sourceLit (List.headD (raw_ints% [9366723098155531584214816913710875]) 0) 31 true) (.node 344 (sourceLit (List.headD (raw_ints% [2476188726910180475060719280054925]) 0) 33 true) (.node 343 (sourceLit (List.headD (raw_ints% [5258985316836969356524683605132325]) 0) 32 true) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [2222675469676749645656365892717925]) 0) 33 true) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [30968697848566562757027775210029525]) 0) 29 true) (.node 348 (sourceLit (List.headD (raw_ints% [2021436351034951603739025864514455]) 0) 33 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [1857607593472615935239962028160525]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [2805883396634248112884243575837375]) 0) 33 true) treeT_J012_part056 treeT_J012_part057)

#time def treeT_J012_part059 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [17405000465693329624280813341903125]) 0) 31 true) treeT_J012_part055 treeT_J012_part058)

#time def treeT_J012_part060 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [916720301343493649004947558338725]) 0) 34 true) treeT_J012_part052 treeT_J012_part059)

#time def treeT_J012_part061 : IntSourceTree :=
  (.node 258 (sourceLit (List.headD (raw_ints% [1872329080260131460484720206228225]) 0) 33 true) treeT_J012_part045 treeT_J012_part060)

#time def treeT_J012_part062 : IntSourceTree :=
  (.node 169 (sourceLit (List.headD (raw_ints% [1866270044830658021429072626803375]) 0) 33 true) treeT_J012_part030 treeT_J012_part061)

#time def treeT_J012_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [3015600955971853699536513460354035]) 0) 32 true) (.node 354 (sourceLit (List.headD (raw_ints% [3212848021097468141543972345201145]) 0) 32 true) (.node 353 (sourceLit (List.headD (raw_ints% [13293129713318154988946378920504305]) 0) 30 true) (.node 352 (sourceLit (List.headD (raw_ints% [1721474443691049541055580876389175]) 0) 33 true) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [6221175834252769669586645230133475]) 0) 31 true) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [5534136724895241264429594542143155]) 0) 31 true) (.node 358 (sourceLit (List.headD (raw_ints% [2844462866387201992570070233227141]) 0) 32 true) (.node 357 (sourceLit (List.headD (raw_ints% [23416916973112489772221854717259575]) 0) 29 true) .empty .empty) .empty) (.node 372 (sourceLit (List.headD (raw_ints% [5711670033109296027728466405720825]) 0) 35 true) .empty .empty)))

#time def treeT_J012_part064 : IntSourceTree :=
  (.node 378 (sourceLit (List.headD (raw_ints% [4960958741935202200179841806888653625]) 0) 32 false) (.node 376 (sourceLit (List.headD (raw_ints% [37505165827004655995654504112162375]) 0) 37 true) (.node 375 (sourceLit (List.headD (raw_ints% [303246037266321607147275087033675]) 0) 38 true) (.node 374 (sourceLit (List.headD (raw_ints% [49751976443352731351495181462828375]) 0) 32 false) .empty .empty) .empty) (.node 377 (sourceLit (List.headD (raw_ints% [430361851738977071152216513611075]) 0) 37 true) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [3793717880911529913304194768432424125]) 0) 33 true) (.node 379 (sourceLit (List.headD (raw_ints% [2663360694425365610567885833714875]) 0) 34 true) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [2174773406879536114661808309707625]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part065 : IntSourceTree :=
  (.node 373 (sourceLit (List.headD (raw_ints% [1997517444494787782562516111258525]) 0) 36 true) treeT_J012_part063 treeT_J012_part064)

#time def treeT_J012_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [1419895254737220272278924875095025]) 0) 34 true) (.node 385 (sourceLit (List.headD (raw_ints% [1601526677806452940958011302894825]) 0) 34 true) (.node 384 (sourceLit (List.headD (raw_ints% [3425544714149982058514788488454875]) 0) 33 true) (.node 383 (sourceLit (List.headD (raw_ints% [1842001149397429102781529094396275]) 0) 34 true) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [6019133625262706817844953428826375]) 0) 32 true) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [1277938258578737875755216525559275]) 0) 34 true) (.node 388 (sourceLit (List.headD (raw_ints% [2689630926498939962911357314690075]) 0) 33 true) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [19487795526149311232507541027976425]) 0) 30 true) .empty .empty)))

#time def treeT_J012_part067 : IntSourceTree :=
  (.node 396 (sourceLit (List.headD (raw_ints% [3830288663314442210005857482026875]) 0) 32 true) (.node 394 (sourceLit (List.headD (raw_ints% [8236373812380517875411974077340325]) 0) 31 true) (.node 393 (sourceLit (List.headD (raw_ints% [1070341810852249907496775200338955]) 0) 34 true) (.node 392 (sourceLit (List.headD (raw_ints% [2229897887933680169287325073005175]) 0) 33 true) .empty .empty) .empty) (.node 395 (sourceLit (List.headD (raw_ints% [1984179516176854303030427860460205]) 0) 33 true) .empty .empty)) (.node 398 (sourceLit (List.headD (raw_ints% [14336858533736487211026758768299635]) 0) 30 true) (.node 397 (sourceLit (List.headD (raw_ints% [1851312283857999458317466727188535]) 0) 33 true) .empty .empty) (.node 399 (sourceLit (List.headD (raw_ints% [1737035330033093580271682462667105]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part068 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [1163935674075662905279071490115625]) 0) 34 true) treeT_J012_part066 treeT_J012_part067)

#time def treeT_J012_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [7561910211190500636358924208803561125]) 0) 31 false) treeT_J012_part065 treeT_J012_part068)

#time def treeT_J012_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [9878792707681214230191975382310625]) 0) 33 true) (.node 416 (sourceLit (List.headD (raw_ints% [1815446583009527551427119393299825]) 0) 36 true) (.node 415 (sourceLit (List.headD (raw_ints% [203370916153319668131155673805976625]) 0) 33 false) (.node 414 (sourceLit (List.headD (raw_ints% [396068535400196285239938421592925]) 0) 39 true) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [8335468154352408349614388919398477125]) 0) 31 true) .empty .empty)) (.node 420 (sourceLit (List.headD (raw_ints% [7400732814312277880037308951901375]) 0) 33 true) (.node 419 (sourceLit (List.headD (raw_ints% [13244314849837413131945882402990598375]) 0) 32 false) .empty .empty) (.node 421 (sourceLit (List.headD (raw_ints% [68253258883502105573393693974655012625]) 0) 30 true) .empty .empty)))

#time def treeT_J012_part071 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [7805058257828833269609992647414275]) 0) 32 true) (.node 425 (sourceLit (List.headD (raw_ints% [18037634615044324883903490993928125]) 0) 31 true) (.node 424 (sourceLit (List.headD (raw_ints% [4891815870679535936065397097530175]) 0) 33 true) (.node 423 (sourceLit (List.headD (raw_ints% [3783584598253668802857724446204346725]) 0) 33 false) .empty .empty) .empty) (.node 426 (sourceLit (List.headD (raw_ints% [4183431241549062118175679318861375]) 0) 33 true) .empty .empty)) (.node 429 (sourceLit (List.headD (raw_ints% [55099491799399516056135658860052875]) 0) 29 true) (.node 428 (sourceLit (List.headD (raw_ints% [3658144667913929485376673635865645]) 0) 33 true) .empty .empty) (.node 430 (sourceLit (List.headD (raw_ints% [3254145440842335567780904074076575]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part072 : IntSourceTree :=
  (.node 422 (sourceLit (List.headD (raw_ints% [5893210230883896345762989662993125]) 0) 33 true) treeT_J012_part070 treeT_J012_part071)

#time def treeT_J012_part073 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [4921117108735563512585197981486785]) 0) 32 true) (.node 434 (sourceLit (List.headD (raw_ints% [5349886465720531118430229257510495]) 0) 32 true) (.node 433 (sourceLit (List.headD (raw_ints% [22385236493620727719650822247578495]) 0) 30 true) (.node 432 (sourceLit (List.headD (raw_ints% [2934268252611602080060705084073325]) 0) 33 true) .empty .empty) .empty) (.node 435 (sourceLit (List.headD (raw_ints% [10251571790508266081237302924547175]) 0) 31 true) .empty .empty)) (.node 438 (sourceLit (List.headD (raw_ints% [4560786269044795840699796675526999]) 0) 32 true) (.node 437 (sourceLit (List.headD (raw_ints% [37867701639918585587871864995170425]) 0) 29 true) .empty .empty) (.node 439 (sourceLit (List.headD (raw_ints% [137542528263144467915580691033695]) 0) 37 true) .empty .empty)))

#time def treeT_J012_part074 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [4259508182687235761312519292855755625]) 0) 35 false) (.node 458 (sourceLit (List.headD (raw_ints% [6648213448143805274897115363143565375]) 0) 33 true) (.node 457 (sourceLit (List.headD (raw_ints% [692542365635275240137451439844375]) 0) 38 true) (.node 456 (sourceLit (List.headD (raw_ints% [503412242769356916096391706703275625]) 0) 34 false) .empty .empty) .empty) (.node 459 (sourceLit (List.headD (raw_ints% [3607716006627924309812044774297875]) 0) 35 true) .empty .empty)) (.node 462 (sourceLit (List.headD (raw_ints% [37907584547346303104876309091729286875]) 0) 32 true) (.node 461 (sourceLit (List.headD (raw_ints% [2612979703716370882687750321096875]) 0) 35 true) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [2025604540743233621490730284298425]) 0) 35 true) .empty .empty)))

#time def treeT_J012_part075 : IntSourceTree :=
  (.node 455 (sourceLit (List.headD (raw_ints% [1281028104334463533812478599338025]) 0) 38 true) treeT_J012_part073 treeT_J012_part074)

#time def treeT_J012_part076 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [12341600991089971334870595067033425]) 0) 31 true) treeT_J012_part072 treeT_J012_part075)

#time def treeT_J012_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [165368440593804143263030111641163275]) 0) 31 true) treeT_J012_part069 treeT_J012_part076)

#time def treeT_J012_part078 : IntSourceTree :=
  (.node 469 (sourceLit (List.headD (raw_ints% [1190103204667595804810728555153185]) 0) 35 true) (.node 467 (sourceLit (List.headD (raw_ints% [1381767993405920922948377221883175]) 0) 35 true) (.node 466 (sourceLit (List.headD (raw_ints% [6009250494890809033029268782550875]) 0) 33 true) (.node 465 (sourceLit (List.headD (raw_ints% [1645144596436541497553692897317675]) 0) 35 true) .empty .empty) .empty) (.node 468 (sourceLit (List.headD (raw_ints% [639428416416236663337329416590525]) 0) 36 true) .empty .empty)) (.node 471 (sourceLit (List.headD (raw_ints% [1045104883383336331250916291980475]) 0) 35 true) (.node 470 (sourceLit (List.headD (raw_ints% [17805848136625102411814058916038225]) 0) 31 true) .empty .empty) (.node 472 (sourceLit (List.headD (raw_ints% [7881805215222610996295944921023075]) 0) 32 true) .empty .empty)))

#time def treeT_J012_part079 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [11765421553091049188422553113435395]) 0) 31 true) (.node 476 (sourceLit (List.headD (raw_ints% [1605320781798455967807861360630075]) 0) 34 true) (.node 475 (sourceLit (List.headD (raw_ints% [1682853474771838407699900698525145]) 0) 34 true) (.node 474 (sourceLit (List.headD (raw_ints% [7074431340620104922119424085119085]) 0) 32 true) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [1534902412438782027133865627149125]) 0) 34 true) .empty .empty)) (.node 496 (sourceLit (List.headD (raw_ints% [8432778251666180719072709401404375]) 0) 36 true) (.node 479 (sourceLit (List.headD (raw_ints% [1411875469505851130214057106429947]) 0) 34 true) .empty .empty) (.node 497 (sourceLit (List.headD (raw_ints% [16390064038662119007156656226650887125]) 0) 31 false) .empty .empty)))

#time def treeT_J012_part080 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [931963220879676086281964941867185]) 0) 35 true) treeT_J012_part078 treeT_J012_part079)

#time def treeT_J012_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [651424517899999561058344274030213025]) 0) 39 true) (.node 501 (sourceLit (List.headD (raw_ints% [340861782575485194297394928717423372625]) 0) 30 false) (.node 500 (sourceLit (List.headD (raw_ints% [21460995238711116598459049242481625]) 0) 33 true) (.node 499 (sourceLit (List.headD (raw_ints% [39837168642412634231534343855564859875]) 0) 32 true) .empty .empty) .empty) (.node 502 (sourceLit (List.headD (raw_ints% [15010627398847070715739012905781875]) 0) 33 true) .empty .empty)) (.node 505 (sourceLit (List.headD (raw_ints% [60582795564386945027075612938171114725]) 0) 31 false) (.node 504 (sourceLit (List.headD (raw_ints% [11313020455266333035860445176857225]) 0) 33 true) .empty .empty) (.node 506 (sourceLit (List.headD (raw_ints% [8977725529943269862253863859680025]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part082 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [5426570814455088569946625251770475]) 0) 33 true) (.node 510 (sourceLit (List.headD (raw_ints% [6266680196498430870704924367148905]) 0) 33 true) (.node 509 (sourceLit (List.headD (raw_ints% [108594182803157069758220671787121525]) 0) 29 true) (.node 508 (sourceLit (List.headD (raw_ints% [7395999279333437898210344139199755]) 0) 33 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [23270095282160233488757522765043025]) 0) 31 true) .empty .empty)) (.node 514 (sourceLit (List.headD (raw_ints% [9561525068354286262081209812364465]) 0) 32 true) (.node 513 (sourceLit (List.headD (raw_ints% [40669205228160160250716737120606105]) 0) 30 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [18046153571972153607240393415929165]) 0) 31 true) .empty .empty)))

#time def treeT_J012_part083 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [16231943721734402862507082482789225]) 0) 32 true) treeT_J012_part081 treeT_J012_part082)

#time def treeT_J012_part084 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [34443918692976401138604916767729375]) 0) 33 true) treeT_J012_part080 treeT_J012_part083)

#time def treeT_J012_part085 : IntSourceTree :=
  (.node 539 (sourceLit (List.headD (raw_ints% [27228486679720552518980827219133625]) 0) 34 true) (.node 519 (sourceLit (List.headD (raw_ints% [7364060648670426215123971000357155]) 0) 32 true) (.node 518 (sourceLit (List.headD (raw_ints% [7718433030465460376371128341666001]) 0) 32 true) (.node 517 (sourceLit (List.headD (raw_ints% [64872828395182596351831262085154375]) 0) 29 true) .empty .empty) .empty) (.node 538 (sourceLit (List.headD (raw_ints% [29686490934949729556950886952938017875]) 0) 32 false) .empty .empty)) (.node 541 (sourceLit (List.headD (raw_ints% [16235035831278374833083548600287875]) 0) 34 true) (.node 540 (sourceLit (List.headD (raw_ints% [56875201373161577276784421026987882375]) 0) 33 true) .empty .empty) (.node 542 (sourceLit (List.headD (raw_ints% [416676951670177800507147546900881946375]) 0) 31 false) .empty .empty)))

#time def treeT_J012_part086 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [11116516390404509555808447150065025]) 0) 33 true) (.node 546 (sourceLit (List.headD (raw_ints% [60594814065376726645141671475736216475]) 0) 32 false) (.node 545 (sourceLit (List.headD (raw_ints% [8022731262393250040753059382221875]) 0) 34 true) (.node 544 (sourceLit (List.headD (raw_ints% [90952933032421431403242030756764415525]) 0) 33 true) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [6214189543131428016357109415913675]) 0) 34 true) .empty .empty)) (.node 550 (sourceLit (List.headD (raw_ints% [72982486529906864934592553955045075]) 0) 30 true) (.node 549 (sourceLit (List.headD (raw_ints% [5015792869998246288588887028893385]) 0) 34 true) .empty .empty) (.node 551 (sourceLit (List.headD (raw_ints% [4176470429731758208203091783187955]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part087 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [10959418317360603472757552337185025]) 0) 34 true) treeT_J012_part085 treeT_J012_part086)

#time def treeT_J012_part088 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [5471905864561579694746276352416125]) 0) 33 true) (.node 555 (sourceLit (List.headD (raw_ints% [6195818118810609446681408415314175]) 0) 33 true) (.node 554 (sourceLit (List.headD (raw_ints% [26520342546919950406477888950367935]) 0) 31 true) (.node 553 (sourceLit (List.headD (raw_ints% [3562644372695736397382695368036105]) 0) 34 true) .empty .empty) .empty) (.node 556 (sourceLit (List.headD (raw_ints% [11624870444778329736008947973408865]) 0) 32 true) .empty .empty)) (.node 559 (sourceLit (List.headD (raw_ints% [4894682091453758115943014128806107]) 0) 33 true) (.node 558 (sourceLit (List.headD (raw_ints% [41341985289000497974986155858283585]) 0) 30 true) .empty .empty) (.node 580 (sourceLit (List.headD (raw_ints% [87452951480171093477464259634052875]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part089 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [23113199519629730300758373669207475]) 0) 33 true) (.node 584 (sourceLit (List.headD (raw_ints% [32524652814176080855169764171882875]) 0) 33 true) (.node 583 (sourceLit (List.headD (raw_ints% [500059289961377744322615613976749213575]) 0) 32 false) (.node 582 (sourceLit (List.headD (raw_ints% [49929515926266428616595181495369625]) 0) 33 true) .empty .empty) .empty) (.node 585 (sourceLit (List.headD (raw_ints% [788206259823758396253011858992286438925]) 0) 31 true) .empty .empty)) (.node 588 (sourceLit (List.headD (raw_ints% [17460758893192274167218093524454945]) 0) 33 true) (.node 587 (sourceLit (List.headD (raw_ints% [121205860074475187693145850033955222175]) 0) 32 false) .empty .empty) (.node 589 (sourceLit (List.headD (raw_ints% [247134341689787236027649637014959275]) 0) 29 true) .empty .empty)))

#time def treeT_J012_part090 : IntSourceTree :=
  (.node 581 (sourceLit (List.headD (raw_ints% [1250865004546070430725945665149229490625]) 0) 30 true) treeT_J012_part088 treeT_J012_part089)

#time def treeT_J012_part091 : IntSourceTree :=
  (.node 552 (sourceLit (List.headD (raw_ints% [7694145033468811246230788922009975]) 0) 33 true) treeT_J012_part087 treeT_J012_part090)

#time def treeT_J012_part092 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [8541710689439143749014007606714375]) 0) 32 true) treeT_J012_part084 treeT_J012_part091)

#time def treeT_J012_part093 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [7570594741221487587773963680897148325]) 0) 33 false) treeT_J012_part077 treeT_J012_part092)

#time def treeT_J012_part094 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [34994531521867747205715384484806705]) 0) 31 true) (.node 593 (sourceLit (List.headD (raw_ints% [82437115307340819688975885631553495]) 0) 30 true) (.node 592 (sourceLit (List.headD (raw_ints% [11279310904471944262865741880981345]) 0) 33 true) (.node 591 (sourceLit (List.headD (raw_ints% [24856195623873315722917515595001025]) 0) 32 true) .empty .empty) .empty) (.node 594 (sourceLit (List.headD (raw_ints% [18939629913211604916980353131924375]) 0) 32 true) .empty .empty)) (.node 597 (sourceLit (List.headD (raw_ints% [121125098721270679424311905489387465]) 0) 29 true) (.node 596 (sourceLit (List.headD (raw_ints% [16241561785803294037711626054542325]) 0) 32 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [14169190427780858402613977067998499]) 0) 32 true) .empty .empty)))

#time def treeT_J012_part095 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [106100134236141890362269191308502831925]) 0) 35 true) (.node 624 (sourceLit (List.headD (raw_ints% [147753055748449793931464411183378407275]) 0) 35 false) (.node 623 (sourceLit (List.headD (raw_ints% [4871262201113228142979703644773075]) 0) 37 true) (.node 622 (sourceLit (List.headD (raw_ints% [208442744527031028904136651506263929625]) 0) 34 true) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [3062740193972853851802088098707625]) 0) 37 true) .empty .empty)) (.node 628 (sourceLit (List.headD (raw_ints% [3788030518464549756334426827534540225]) 0) 38 false) (.node 627 (sourceLit (List.headD (raw_ints% [2112376247062287785550158031661725]) 0) 37 true) .empty .empty) (.node 629 (sourceLit (List.headD (raw_ints% [1555620752899253484828650811945195]) 0) 37 true) .empty .empty)))

#time def treeT_J012_part096 : IntSourceTree :=
  (.node 599 (sourceLit (List.headD (raw_ints% [26613863991659645544738213857569275]) 0) 31 true) treeT_J012_part094 treeT_J012_part095)

#time def treeT_J012_part097 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [1592976474300124433787368089576275]) 0) 36 true) (.node 633 (sourceLit (List.headD (raw_ints% [964583316472025983185380814118155]) 0) 37 true) (.node 632 (sourceLit (List.headD (raw_ints% [8581025295202252238343363336495525]) 0) 34 true) (.node 631 (sourceLit (List.headD (raw_ints% [1202502606720349509430941495654585]) 0) 37 true) .empty .empty) .empty) (.node 634 (sourceLit (List.headD (raw_ints% [6989596595052608660312249585148195]) 0) 34 true) .empty .empty)) (.node 637 (sourceLit (List.headD (raw_ints% [1346206990155214292870668712765775]) 0) 36 true) (.node 636 (sourceLit (List.headD (raw_ints% [1460603817318088591856652281962365]) 0) 36 true) .empty .empty) (.node 638 (sourceLit (List.headD (raw_ints% [9972889179033772681165718703887985]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part098 : IntSourceTree :=
  (.node 667 (sourceLit (List.headD (raw_ints% [1818808007852745433489452910970000532975]) 0) 32 true) (.node 665 (sourceLit (List.headD (raw_ints% [5516304043774151802059873016860395471725]) 0) 31 false) (.node 664 (sourceLit (List.headD (raw_ints% [123355737621447219720180752460855525]) 0) 33 true) (.node 663 (sourceLit (List.headD (raw_ints% [2167601246177625975555708826026860650575]) 0) 32 true) .empty .empty) .empty) (.node 666 (sourceLit (List.headD (raw_ints% [74894486687501592956908445489436525]) 0) 33 true) .empty .empty)) (.node 669 (sourceLit (List.headD (raw_ints% [3879190385249388737722480721032384149675]) 0) 29 false) (.node 668 (sourceLit (List.headD (raw_ints% [50135281012800934970386963488720255]) 0) 33 true) .empty .empty) (.node 670 (sourceLit (List.headD (raw_ints% [35983372809281557230866202233821605]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part099 : IntSourceTree :=
  (.node 639 (sourceLit (List.headD (raw_ints% [1159313542040887535833870367399049]) 0) 36 true) treeT_J012_part097 treeT_J012_part098)

#time def treeT_J012_part100 : IntSourceTree :=
  (.node 630 (sourceLit (List.headD (raw_ints% [21768981894985046386632135382489275]) 0) 33 true) treeT_J012_part096 treeT_J012_part099)

#time def treeT_J012_part101 : IntSourceTree :=
  (.node 676 (sourceLit (List.headD (raw_ints% [34733685391800687843484152811898475]) 0) 32 true) (.node 674 (sourceLit (List.headD (raw_ints% [42793702340998058006884018971637545]) 0) 32 true) (.node 673 (sourceLit (List.headD (raw_ints% [192155694139131251938011741136303305]) 0) 30 true) (.node 672 (sourceLit (List.headD (raw_ints% [27200772510579240038924385979965375]) 0) 33 true) .empty .empty) .empty) (.node 675 (sourceLit (List.headD (raw_ints% [76839013998973991359280608877564415]) 0) 31 true) .empty .empty)) (.node 678 (sourceLit (List.headD (raw_ints% [28909433257185998969247421740506301]) 0) 32 true) (.node 677 (sourceLit (List.headD (raw_ints% [252789478512160000090991078692977975]) 0) 29 true) .empty .empty) (.node 679 (sourceLit (List.headD (raw_ints% [53169249440610535904587535773534605]) 0) 31 true) .empty .empty)))

#time def treeT_J012_part102 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [3879364537104548618093573778115444063875]) 0) 30 false) (.node 708 (sourceLit (List.headD (raw_ints% [1940024984443611025692154569451105820175]) 0) 33 true) (.node 707 (sourceLit (List.headD (raw_ints% [57995476711003290672507181236142725]) 0) 34 true) (.node 706 (sourceLit (List.headD (raw_ints% [6365105117663286924958026547328418127125]) 0) 32 false) .empty .empty) .empty) (.node 709 (sourceLit (List.headD (raw_ints% [37690314989606907091757756993158695]) 0) 34 true) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [45057681365662365346924299261965025]) 0) 33 true) (.node 711 (sourceLit (List.headD (raw_ints% [26363351955518761155418670268584925]) 0) 34 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [19484105978803032173441339467020135]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part103 : IntSourceTree :=
  (.node 705 (sourceLit (List.headD (raw_ints% [98853816069664388905764047671194525]) 0) 34 true) treeT_J012_part101 treeT_J012_part102)

#time def treeT_J012_part104 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [19634924920858898682576458801313909]) 0) 33 true) (.node 717 (sourceLit (List.headD (raw_ints% [23964029470558973500518803109772275]) 0) 33 true) (.node 716 (sourceLit (List.headD (raw_ints% [53469352921884573889574172366166575]) 0) 32 true) (.node 715 (sourceLit (List.headD (raw_ints% [30049890546597062536585074255027345]) 0) 33 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [173006365079889818641665329061874095]) 0) 30 true) .empty .empty)) (.node 747 (sourceLit (List.headD (raw_ints% [14549018243179319283405506005626836787225]) 0) 32 false) (.node 746 (sourceLit (List.headD (raw_ints% [320520777591155962666147745195341575]) 0) 33 true) .empty .empty) (.node 748 (sourceLit (List.headD (raw_ints% [181846625831212227719641761455850645]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part105 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [113079145489426199380646696764523535]) 0) 32 true) (.node 752 (sourceLit (List.headD (raw_ints% [78252635311495804582750295094374325]) 0) 33 true) (.node 751 (sourceLit (List.headD (raw_ints% [3879488976568460751833221000167313976025]) 0) 31 false) (.node 750 (sourceLit (List.headD (raw_ints% [114777887149146071136164825738813175]) 0) 33 true) .empty .empty) .empty) (.node 753 (sourceLit (List.headD (raw_ints% [528767207711466593612777047055137095]) 0) 30 true) .empty .empty)) (.node 756 (sourceLit (List.headD (raw_ints% [85465876794587562302856144208210905]) 0) 32 true) (.node 755 (sourceLit (List.headD (raw_ints% [195638828758446773951746880032671075]) 0) 31 true) .empty .empty) (.node 757 (sourceLit (List.headD (raw_ints% [602720168237993182142195679165687225]) 0) 29 true) .empty .empty)))

#time def treeT_J012_part106 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [65959989887444941559871426943467770395275]) 0) 29 true) treeT_J012_part104 treeT_J012_part105)

#time def treeT_J012_part107 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [136238921378710382655513744455117745]) 0) 31 true) treeT_J012_part103 treeT_J012_part106)

#time def treeT_J012_part108 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [62219731956066869823611025934956075]) 0) 32 true) treeT_J012_part100 treeT_J012_part107)

#time def treeT_J012_part109 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [34919677212274745088982500360791607229575]) 0) 31 true) (.node 788 (sourceLit (List.headD (raw_ints% [2061130403452866288637207571884742825925]) 0) 36 false) (.node 787 (sourceLit (List.headD (raw_ints% [131262650440076335996820281979599425]) 0) 35 true) (.node 759 (sourceLit (List.headD (raw_ints% [59918557819639641368538896644169745]) 0) 32 true) .empty .empty) .empty) (.node 789 (sourceLit (List.headD (raw_ints% [72078155420802660313942002231345975]) 0) 35 true) .empty .empty)) (.node 792 (sourceLit (List.headD (raw_ints% [3879579091931192076563914848765837906075]) 0) 32 false) (.node 791 (sourceLit (List.headD (raw_ints% [44207267596813654990373077735114125]) 0) 35 true) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [29384264666346386204654477813677095]) 0) 35 true) .empty .empty)))

#time def treeT_J012_part110 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [23655879852095498175125665948634445]) 0) 34 true) (.node 797 (sourceLit (List.headD (raw_ints% [30750923662014294401168670549219315]) 0) 34 true) (.node 796 (sourceLit (List.headD (raw_ints% [35542368959140550015543176916626125]) 0) 34 true) (.node 795 (sourceLit (List.headD (raw_ints% [41514627471414568422030811254748095]) 0) 34 true) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [214856901579051681750265175051906565]) 0) 31 true) .empty .empty)) (.node 829 (sourceLit (List.headD (raw_ints% [593609373171378711450996565345961933832075]) 0) 29 false) (.node 828 (sourceLit (List.headD (raw_ints% [868254577689398460254920494380944755]) 0) 33 true) .empty .empty) (.node 830 (sourceLit (List.headD (raw_ints% [461847356217275211375371192111954625]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part111 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [196264143166378105478631651300009675]) 0) 32 true) treeT_J012_part109 treeT_J012_part110)

#time def treeT_J012_part112 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [246651142976728985073390345829773855]) 0) 32 true) (.node 834 (sourceLit (List.headD (raw_ints% [357069089172115979893824948254309985]) 0) 32 true) (.node 833 (sourceLit (List.headD (raw_ints% [31037161502657248079104931567173758385695]) 0) 30 false) (.node 832 (sourceLit (List.headD (raw_ints% [275405505463013435340234326786538675]) 0) 33 true) .empty .empty) .empty) (.node 835 (sourceLit (List.headD (raw_ints% [589417743907065647962779725167367625]) 0) 31 true) .empty .empty)) (.node 838 (sourceLit (List.headD (raw_ints% [179060704671064460176521573695171721]) 0) 32 true) (.node 837 (sourceLit (List.headD (raw_ints% [1671991445147002018852567643498384775]) 0) 29 true) .empty .empty) (.node 839 (sourceLit (List.headD (raw_ints% [38734585939853010095431569601934205]) 0) 34 true) .empty .empty)))

#time def treeT_J012_part113 : IntSourceTree :=
  (.node 874 (sourceLit (List.headD (raw_ints% [31037554030943580835315888830476358405045]) 0) 31 false) (.node 872 (sourceLit (List.headD (raw_ints% [38799211246524571503181068285258183170625]) 0) 33 true) (.node 871 (sourceLit (List.headD (raw_ints% [373432821023647901394625036641726375]) 0) 34 true) (.node 870 (sourceLit (List.headD (raw_ints% [663448727595928201628961566067545148291225]) 0) 30 false) .empty .empty) .empty) (.node 873 (sourceLit (List.headD (raw_ints% [216636976130320662930925371159184485]) 0) 34 true) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [447248268070503447900607017500863125]) 0) 32 true) (.node 875 (sourceLit (List.headD (raw_ints% [274039834229286843049763325744813795]) 0) 33 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [185149295652700396271053004731335225]) 0) 33 true) .empty .empty)))

#time def treeT_J012_part114 : IntSourceTree :=
  (.node 869 (sourceLit (List.headD (raw_ints% [724098266847793139627036489918252805]) 0) 34 true) treeT_J012_part112 treeT_J012_part113)

#time def treeT_J012_part115 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [73718843401117950929798221721750528435175]) 0) 31 true) treeT_J012_part111 treeT_J012_part114)

#time def treeT_J012_part116 : IntSourceTree :=
  (.node 913 (sourceLit (List.headD (raw_ints% [651824541447050392130002024131304689115695]) 0) 30 true) (.node 911 (sourceLit (List.headD (raw_ints% [5759121648414423066865310842103872474425]) 0) 38 false) (.node 910 (sourceLit (List.headD (raw_ints% [2434545711173897347132774767561056595]) 0) 33 true) (.node 879 (sourceLit (List.headD (raw_ints% [131748944966873463826270241797902831]) 0) 33 true) .empty .empty) .empty) (.node 912 (sourceLit (List.headD (raw_ints% [1218325778631578170238265819780366825]) 0) 33 true) .empty .empty)) (.node 915 (sourceLit (List.headD (raw_ints% [62075697479631068736279740440677884177715]) 0) 31 false) (.node 914 (sourceLit (List.headD (raw_ints% [1376026719870449323553578021019165895]) 0) 32 true) .empty .empty) (.node 916 (sourceLit (List.headD (raw_ints% [849508193940418387125662957149481325]) 0) 32 true) .empty .empty)))

#time def treeT_J012_part117 : IntSourceTree :=
  (.node 953 (sourceLit (List.headD (raw_ints% [250422200625314376826835112155295585]) 0) 36 true) (.node 951 (sourceLit (List.headD (raw_ints% [515278222537562361434537432729832555]) 0) 36 true) (.node 919 (sourceLit (List.headD (raw_ints% [932400954470074574588584736579098005]) 0) 31 true) (.node 918 (sourceLit (List.headD (raw_ints% [561536477939737124907690445230169179]) 0) 32 true) .empty .empty) .empty) (.node 952 (sourceLit (List.headD (raw_ints% [407382996745047647782560962179906021533825]) 0) 33 false) .empty .empty)) (.node 955 (sourceLit (List.headD (raw_ints% [275496721410290620125953673818588025]) 0) 35 true) (.node 954 (sourceLit (List.headD (raw_ints% [170715523869498493241329478240445261880185]) 0) 33 true) .empty .empty) (.node 956 (sourceLit (List.headD (raw_ints% [7759518090987392404965955130961923130105]) 0) 35 false) .empty .empty)))

#time def treeT_J012_part118 : IntSourceTree :=
  (.node 917 (sourceLit (List.headD (raw_ints% [5483980843981053147557144636515425225]) 0) 29 true) treeT_J012_part116 treeT_J012_part117)

#time def treeT_J012_part119 : IntSourceTree :=
  (.node 996 (sourceLit (List.headD (raw_ints% [3558439348624231534889595823947927075]) 0) 32 true) (.node 994 (sourceLit (List.headD (raw_ints% [6637483700139610734905145567950292825]) 0) 32 true) (.node 959 (sourceLit (List.headD (raw_ints% [107446883243215915270355050858066587]) 0) 35 true) (.node 958 (sourceLit (List.headD (raw_ints% [1060425800498038623051276835780213395]) 0) 32 true) .empty .empty) .empty) (.node 995 (sourceLit (List.headD (raw_ints% [1427799888435619014666915566364239979219195]) 0) 31 true) .empty .empty)) (.node 998 (sourceLit (List.headD (raw_ints% [2095899115211134838510749364442415221]) 0) 32 true) (.node 997 (sourceLit (List.headD (raw_ints% [993223799627230208888789813907762676078665]) 0) 29 false) .empty .empty) (.node 999 (sourceLit (List.headD (raw_ints% [3309302247522079917616522606541755575]) 0) 31 true) .empty .empty)))

#time def treeT_J012_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [18583547909369561482715727666755835825]) 0) 32 true) (.node 1038 (sourceLit (List.headD (raw_ints% [993228041330432201043282019015105796932245]) 0) 30 false) (.node 1037 (sourceLit (List.headD (raw_ints% [2894080450336513544034985871529780975]) 0) 33 true) (.node 1036 (sourceLit (List.headD (raw_ints% [1489876033163518153906643207411935364260035]) 0) 32 true) .empty .empty) .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [1666111582238271177429329161010148873]) 0) 33 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [9480422686134919337629194121676708679]) 0) 32 true) (.node 1077 (sourceLit (List.headD (raw_ints% [24831240330243520671395081132498728504239225]) 0) 29 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [248307837658169930780799908884428084671955]) 0) 33 false) .empty .empty)))

#time def treeT_J012_part121 : IntSourceTree :=
  (.node 1035 (sourceLit (List.headD (raw_ints% [5535496814498448254401330872675940725]) 0) 33 true) treeT_J012_part119 treeT_J012_part120)

#time def treeT_J012_part122 : IntSourceTree :=
  (.node 957 (sourceLit (List.headD (raw_ints% [166089724571929497713652488104536525]) 0) 35 true) treeT_J012_part118 treeT_J012_part121)

#time def treeT_J012_part123 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [1242277641988898655352037293394571645]) 0) 30 true) treeT_J012_part115 treeT_J012_part122)

#time def treeT_J012_part124 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [66946684625049895032827790698582799]) 0) 32 true) treeT_J012_part108 treeT_J012_part123)

#time def treeT_J012_part125 : IntSourceTree :=
  (.node 590 (sourceLit (List.headD (raw_ints% [13796491283494554283650623748424635]) 0) 33 true) treeT_J012_part093 treeT_J012_part124)

#time def treeT_J012_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [893274316882417487204618245117875]) 0) 34 true) treeT_J012_part062 treeT_J012_part125)

#time def treeT_J012 : IntSourceTree := treeT_J012_part126

#time def treeT_J013_part000 : IntSourceTree :=
  (.node 8 (sourceLit (List.headD (raw_ints% [220170766910415555380733341629875]) 0) 33 true) (.node 6 (sourceLit (List.headD (raw_ints% [1008634938830406303158993362237125]) 0) 31 true) (.node 5 (sourceLit (List.headD (raw_ints% [137063968930155751213743399511125]) 0) 34 true) (.node 4 (sourceLit (List.headD (raw_ints% [302950339459529216625912427460775]) 0) 33 true) .empty .empty) .empty) (.node 7 (sourceLit (List.headD (raw_ints% [117312041078034774526916047776375]) 0) 34 true) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [197478605706007958696105117751375]) 0) 33 true) (.node 9 (sourceLit (List.headD (raw_ints% [51992431226812450503926425403775]) 0) 35 true) .empty .empty) (.node 11 (sourceLit (List.headD (raw_ints% [47081136773586364751643603136875]) 0) 35 true) .empty .empty)))

#time def treeT_J013_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [150406832101816407275204300879625]) 0) 33 true) (.node 15 (sourceLit (List.headD (raw_ints% [20083998351874594443276538693125]) 0) 36 true) (.node 14 (sourceLit (List.headD (raw_ints% [14134323147258414430913722413352875]) 0) 31 false) (.node 13 (sourceLit (List.headD (raw_ints% [10814460651009397007918136219375]) 0) 37 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [38829063480290882590334641473375]) 0) 35 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [141701140790075733396262470512775]) 0) 33 true) (.node 18 (sourceLit (List.headD (raw_ints% [583538603094270079334258334028875]) 0) 31 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [275631862990651741233191351444625]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [90120505425078308399317801828125]) 0) 34 true) treeT_J013_part000 treeT_J013_part001)

#time def treeT_J013_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [476742808489797153185191457422275]) 0) 31 true) (.node 24 (sourceLit (List.headD (raw_ints% [249305357442182367142880993004075]) 0) 32 true) (.node 23 (sourceLit (List.headD (raw_ints% [127636271934497669776735951023375]) 0) 33 true) (.node 22 (sourceLit (List.headD (raw_ints% [1046480637619117456279397544045375]) 0) 30 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [121841101168453934222699588992875]) 0) 33 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [228579358749743670578612686815975]) 0) 32 true) (.node 27 (sourceLit (List.headD (raw_ints% [116672623898266664278378420155525]) 0) 33 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [112026100310380271454892997498955]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [200963430015279548307612185432025]) 0) 32 true) (.node 33 (sourceLit (List.headD (raw_ints% [207978219849661450596644339076975]) 0) 32 true) (.node 32 (sourceLit (List.headD (raw_ints% [211722121593358077790739259533925]) 0) 32 true) (.node 31 (sourceLit (List.headD (raw_ints% [107819855994567265893679850239725]) 0) 33 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [817582784706409931390242092536505]) 0) 30 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [194510292201259848110603467836675]) 0) 32 true) (.node 36 (sourceLit (List.headD (raw_ints% [395342692706624356263347794700775]) 0) 31 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [1531775444090919278355112574741175]) 0) 29 true) .empty .empty)))

#time def treeT_J013_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [1757957291393978367604325042954325]) 0) 29 true) treeT_J013_part003 treeT_J013_part004)

#time def treeT_J013_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [134195139963207564654560381573625]) 0) 33 true) treeT_J013_part002 treeT_J013_part005)

#time def treeT_J013_part007 : IntSourceTree :=
  (.node 49 (sourceLit (List.headD (raw_ints% [220170766910415555380733341629875]) 0) 34 true) (.node 47 (sourceLit (List.headD (raw_ints% [1008634938830406303158993362237125]) 0) 32 true) (.node 46 (sourceLit (List.headD (raw_ints% [137063968930155751213743399511125]) 0) 35 true) (.node 45 (sourceLit (List.headD (raw_ints% [302950339459529216625912427460775]) 0) 34 true) .empty .empty) .empty) (.node 48 (sourceLit (List.headD (raw_ints% [117312041078034774526916047776375]) 0) 35 true) .empty .empty)) (.node 51 (sourceLit (List.headD (raw_ints% [197478605706007958696105117751375]) 0) 34 true) (.node 50 (sourceLit (List.headD (raw_ints% [51992431226812450503926425403775]) 0) 36 true) .empty .empty) (.node 52 (sourceLit (List.headD (raw_ints% [47081136773586364751643603136875]) 0) 36 true) .empty .empty)))

#time def treeT_J013_part008 : IntSourceTree :=
  (.node 58 (sourceLit (List.headD (raw_ints% [150406832101816407275204300879625]) 0) 34 true) (.node 56 (sourceLit (List.headD (raw_ints% [20083998351874594443276538693125]) 0) 37 true) (.node 55 (sourceLit (List.headD (raw_ints% [14134323147258414430913722413352875]) 0) 32 false) (.node 54 (sourceLit (List.headD (raw_ints% [10814460651009397007918136219375]) 0) 38 true) .empty .empty) .empty) (.node 57 (sourceLit (List.headD (raw_ints% [38829063480290882590334641473375]) 0) 36 true) .empty .empty)) (.node 60 (sourceLit (List.headD (raw_ints% [141701140790075733396262470512775]) 0) 34 true) (.node 59 (sourceLit (List.headD (raw_ints% [583538603094270079334258334028875]) 0) 32 true) .empty .empty) (.node 61 (sourceLit (List.headD (raw_ints% [275631862990651741233191351444625]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part009 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [90120505425078308399317801828125]) 0) 35 true) treeT_J013_part007 treeT_J013_part008)

#time def treeT_J013_part010 : IntSourceTree :=
  (.node 67 (sourceLit (List.headD (raw_ints% [476742808489797153185191457422275]) 0) 32 true) (.node 65 (sourceLit (List.headD (raw_ints% [249305357442182367142880993004075]) 0) 33 true) (.node 64 (sourceLit (List.headD (raw_ints% [127636271934497669776735951023375]) 0) 34 true) (.node 63 (sourceLit (List.headD (raw_ints% [1046480637619117456279397544045375]) 0) 31 true) .empty .empty) .empty) (.node 66 (sourceLit (List.headD (raw_ints% [121841101168453934222699588992875]) 0) 34 true) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [228579358749743670578612686815975]) 0) 33 true) (.node 68 (sourceLit (List.headD (raw_ints% [116672623898266664278378420155525]) 0) 34 true) .empty .empty) (.node 70 (sourceLit (List.headD (raw_ints% [112026100310380271454892997498955]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [817582784706409931390242092536505]) 0) 31 true) (.node 73 (sourceLit (List.headD (raw_ints% [211722121593358077790739259533925]) 0) 33 true) (.node 72 (sourceLit (List.headD (raw_ints% [107819855994567265893679850239725]) 0) 34 true) .empty .empty) (.node 74 (sourceLit (List.headD (raw_ints% [207978219849661450596644339076975]) 0) 33 true) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [395342692706624356263347794700775]) 0) 32 true) (.node 76 (sourceLit (List.headD (raw_ints% [200963430015279548307612185432025]) 0) 33 true) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [194510292201259848110603467836675]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [1757957291393978367604325042954325]) 0) 30 true) treeT_J013_part010 treeT_J013_part011)

#time def treeT_J013_part013 : IntSourceTree :=
  (.node 62 (sourceLit (List.headD (raw_ints% [134195139963207564654560381573625]) 0) 34 true) treeT_J013_part009 treeT_J013_part012)

#time def treeT_J013_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [188548648691773375671343977039741]) 0) 32 true) treeT_J013_part006 treeT_J013_part013)

#time def treeT_J013_part015 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [683204461935654262826828248768125]) 0) 33 true) (.node 88 (sourceLit (List.headD (raw_ints% [394232085959995373889130010303625]) 0) 34 true) (.node 87 (sourceLit (List.headD (raw_ints% [430943834642588230328057550268125]) 0) 34 true) (.node 86 (sourceLit (List.headD (raw_ints% [3838570492522061162855605477135275]) 0) 31 true) .empty .empty) .empty) (.node 89 (sourceLit (List.headD (raw_ints% [182631650929257098549905670148975]) 0) 35 true) .empty .empty)) (.node 92 (sourceLit (List.headD (raw_ints% [304836705986937608992892433674625]) 0) 34 true) (.node 91 (sourceLit (List.headD (raw_ints% [160888588133663437264062098478225]) 0) 35 true) .empty .empty) (.node 93 (sourceLit (List.headD (raw_ints% [9066669030644241935931366729375]) 0) 39 true) .empty .empty)))

#time def treeT_J013_part016 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [459926187617189895704554733005725]) 0) 33 true) (.node 97 (sourceLit (List.headD (raw_ints% [492281115158170614909644937300375]) 0) 33 true) (.node 96 (sourceLit (List.headD (raw_ints% [14289639401179577961275060979246375]) 0) 33 false) (.node 95 (sourceLit (List.headD (raw_ints% [66431686856200581620068551061875]) 0) 36 true) .empty .empty) .empty) (.node 98 (sourceLit (List.headD (raw_ints% [1901521459644346406447158720267125]) 0) 31 true) .empty .empty)) (.node 101 (sourceLit (List.headD (raw_ints% [432609423197095368930489500477475]) 0) 33 true) (.node 100 (sourceLit (List.headD (raw_ints% [891445343197888417435325316613125]) 0) 32 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [3363629170231310403451664079068625]) 0) 30 true) .empty .empty)))

#time def treeT_J013_part017 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [17018179320860920299691892071852875]) 0) 31 true) treeT_J013_part015 treeT_J013_part016)

#time def treeT_J013_part018 : IntSourceTree :=
  (.node 108 (sourceLit (List.headD (raw_ints% [724906258229850635791770228028575]) 0) 32 true) (.node 106 (sourceLit (List.headD (raw_ints% [1517700051047661783957856486610325]) 0) 31 true) (.node 105 (sourceLit (List.headD (raw_ints% [388703986569536744884244215100625]) 0) 33 true) (.node 104 (sourceLit (List.headD (raw_ints% [199293820044233772284129137760325]) 0) 34 true) .empty .empty) .empty) (.node 107 (sourceLit (List.headD (raw_ints% [370691780775549072612419935815975]) 0) 33 true) .empty .empty)) (.node 110 (sourceLit (List.headD (raw_ints% [5556582188597819090911280935156875]) 0) 29 true) (.node 109 (sourceLit (List.headD (raw_ints% [354664395282686385658620683123145]) 0) 33 true) .empty .empty) (.node 111 (sourceLit (List.headD (raw_ints% [340284545246953819925892139756095]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part019 : IntSourceTree :=
  (.node 117 (sourceLit (List.headD (raw_ints% [609343427859858345119845273891425]) 0) 32 true) (.node 115 (sourceLit (List.headD (raw_ints% [630949449383366254078965170875875]) 0) 32 true) (.node 114 (sourceLit (List.headD (raw_ints% [2569971160787319313261586060006295]) 0) 30 true) (.node 113 (sourceLit (List.headD (raw_ints% [654580628106876676552794462840825]) 0) 32 true) .empty .empty) .empty) (.node 116 (sourceLit (List.headD (raw_ints% [1239822876706195506517136390372235]) 0) 31 true) .empty .empty)) (.node 119 (sourceLit (List.headD (raw_ints% [589492520113266016771069894306959]) 0) 32 true) (.node 118 (sourceLit (List.headD (raw_ints% [4793707639215070421858452140471225]) 0) 29 true) .empty .empty) (.node 127 (sourceLit (List.headD (raw_ints% [1414967776845827429848306057449075]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part020 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [1334513048207262212022846523886475]) 0) 31 true) treeT_J013_part018 treeT_J013_part019)

#time def treeT_J013_part021 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [409144287918332588841505575271125]) 0) 33 true) treeT_J013_part017 treeT_J013_part020)

#time def treeT_J013_part022 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [53679050140464825148393657961625]) 0) 37 true) (.node 131 (sourceLit (List.headD (raw_ints% [242862928114823152065361565508375]) 0) 35 true) (.node 130 (sourceLit (List.headD (raw_ints% [8164951231402790502873702796575]) 0) 40 true) (.node 129 (sourceLit (List.headD (raw_ints% [568293405009575192397526678977375]) 0) 34 true) .empty .empty) .empty) (.node 132 (sourceLit (List.headD (raw_ints% [56903725680038536256209247670675]) 0) 37 true) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [15576251234059667365302807242602875]) 0) 33 true) (.node 134 (sourceLit (List.headD (raw_ints% [25452215471567570735807330698125]) 0) 38 true) .empty .empty) (.node 136 (sourceLit (List.headD (raw_ints% [23173844252162993588396006184375]) 0) 38 true) .empty .empty)))

#time def treeT_J013_part023 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [149207141616943902137964559451925]) 0) 35 true) (.node 140 (sourceLit (List.headD (raw_ints% [159112523413557081154146131246475]) 0) 35 true) (.node 139 (sourceLit (List.headD (raw_ints% [658991428275038163556450193119125]) 0) 33 true) (.node 138 (sourceLit (List.headD (raw_ints% [170937141528177103817220318210375]) 0) 35 true) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [153953370051809169050533491292125]) 0) 35 true) .empty .empty)) (.node 144 (sourceLit (List.headD (raw_ints% [140754007991917459532384812123875]) 0) 35 true) (.node 143 (sourceLit (List.headD (raw_ints% [1158574266306096473586133267511625]) 0) 32 true) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [547869922734752721993635558037225]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part024 : IntSourceTree :=
  (.node 137 (sourceLit (List.headD (raw_ints% [14444955655100741491636399545139875]) 0) 34 false) treeT_J013_part022 treeT_J013_part023)

#time def treeT_J013_part025 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [1899312448601920361653477946101275]) 0) 31 true) (.node 149 (sourceLit (List.headD (raw_ints% [62040862435013370651644692651575]) 0) 36 true) (.node 148 (sourceLit (List.headD (raw_ints% [127009578438641204167020757830225]) 0) 35 true) (.node 147 (sourceLit (List.headD (raw_ints% [520478621278932315386332514594025]) 0) 33 true) .empty .empty) .empty) (.node 150 (sourceLit (List.headD (raw_ints% [121319147486153057101863842812095]) 0) 35 true) .empty .empty)) (.node 153 (sourceLit (List.headD (raw_ints% [911068805020546056441368004818625]) 0) 32 true) (.node 152 (sourceLit (List.headD (raw_ints% [116232344626193277016106144758185]) 0) 35 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [223301204128607612978075061881925]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part026 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [1630966097562075571751669782865025]) 0) 31 true) (.node 157 (sourceLit (List.headD (raw_ints% [211120045999892787563447148917865]) 0) 34 true) (.node 156 (sourceLit (List.headD (raw_ints% [214993009684043352885676492721925]) 0) 34 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [207416567829299248504620903027375]) 0) 34 true) .empty .empty)) (.node 169 (sourceLit (List.headD (raw_ints% [444631936199849813052377334834525]) 0) 35 true) (.node 168 (sourceLit (List.headD (raw_ints% [510367845442916027979588023572725]) 0) 35 true) .empty .empty) (.node 170 (sourceLit (List.headD (raw_ints% [1589969158102646506763278467141375]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part027 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [876194188040454690935671983734895]) 0) 32 true) treeT_J013_part025 treeT_J013_part026)

#time def treeT_J013_part028 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [133431442700541405330772313053875]) 0) 35 true) treeT_J013_part024 treeT_J013_part027)

#time def treeT_J013_part029 : IntSourceTree :=
  (.node 128 (sourceLit (List.headD (raw_ints% [156815896782276727900570751245875]) 0) 36 true) treeT_J013_part021 treeT_J013_part028)

#time def treeT_J013_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [1531775444090919278355112574741175]) 0) 30 true) treeT_J013_part014 treeT_J013_part029)

#time def treeT_J013_part031 : IntSourceTree :=
  (.node 176 (sourceLit (List.headD (raw_ints% [45442141869298912691880675464452125]) 0) 33 true) (.node 174 (sourceLit (List.headD (raw_ints% [10147260902881422680697503852764875]) 0) 31 false) (.node 173 (sourceLit (List.headD (raw_ints% [38770387618750052384346514211925]) 0) 38 true) (.node 172 (sourceLit (List.headD (raw_ints% [666615006472354999268553828358875]) 0) 34 true) .empty .empty) .empty) (.node 175 (sourceLit (List.headD (raw_ints% [137186036916339984266390094523125]) 0) 36 true) .empty .empty)) (.node 178 (sourceLit (List.headD (raw_ints% [233020811941256210272629551442505125]) 0) 31 false) (.node 177 (sourceLit (List.headD (raw_ints% [990844916980260974747699458499625]) 0) 33 true) .empty .empty) (.node 179 (sourceLit (List.headD (raw_ints% [907570944608226934833207812677275]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part032 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [737328077365802931374834281890375]) 0) 33 true) (.node 183 (sourceLit (List.headD (raw_ints% [784512845017218628262210900344275]) 0) 33 true) (.node 182 (sourceLit (List.headD (raw_ints% [6489386513084476415782479363627375]) 0) 30 true) (.node 181 (sourceLit (List.headD (raw_ints% [840290764111361280302679549494325]) 0) 33 true) .empty .empty) .empty) (.node 184 (sourceLit (List.headD (raw_ints% [759986626217628929017874991990975]) 0) 33 true) .empty .empty)) (.node 187 (sourceLit (List.headD (raw_ints% [696759760828782170033758568615025]) 0) 33 true) (.node 186 (sourceLit (List.headD (raw_ints% [2865259330830359991991227977687475]) 0) 31 true) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [1357008226885878625753559830347525]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part033 : IntSourceTree :=
  (.node 180 (sourceLit (List.headD (raw_ints% [1744520369902264236790475455863375]) 0) 32 true) treeT_J013_part031 treeT_J013_part032)

#time def treeT_J013_part034 : IntSourceTree :=
  (.node 194 (sourceLit (List.headD (raw_ints% [4718579279377049138269357978542705]) 0) 30 true) (.node 192 (sourceLit (List.headD (raw_ints% [2464111848996578511284109368316075]) 0) 31 true) (.node 191 (sourceLit (List.headD (raw_ints% [630268634642270636889018602740665]) 0) 33 true) (.node 190 (sourceLit (List.headD (raw_ints% [10325878594765603795909760383646325]) 0) 29 true) .empty .empty) .empty) (.node 193 (sourceLit (List.headD (raw_ints% [1205136885912215755704903853290135]) 0) 32 true) .empty .empty)) (.node 196 (sourceLit (List.headD (raw_ints% [2264953875455623257225551544567345]) 0) 31 true) (.node 195 (sourceLit (List.headD (raw_ints% [1155460183645494649745635324179525]) 0) 32 true) .empty .empty) (.node 197 (sourceLit (List.headD (raw_ints% [1110600649612488477965566667883975]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part035 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [247860839316038082407436385161225]) 0) 36 true) (.node 210 (sourceLit (List.headD (raw_ints% [313992716497405165006398090089325]) 0) 36 true) (.node 209 (sourceLit (List.headD (raw_ints% [1473177976762088919520825415313525]) 0) 34 true) (.node 199 (sourceLit (List.headD (raw_ints% [1069840022521127971265897329912041]) 0) 32 true) .empty .empty) .empty) (.node 211 (sourceLit (List.headD (raw_ints% [1104243301873000202632555336124625]) 0) 34 true) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [52088559765932534032885697725725]) 0) 38 true) (.node 213 (sourceLit (List.headD (raw_ints% [451898805910495698674979196512375]) 0) 35 true) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [41299763371000757411303118337970625]) 0) 32 false) .empty .empty)))

#time def treeT_J013_part036 : IntSourceTree :=
  (.node 198 (sourceLit (List.headD (raw_ints% [8717975304778067982202165390272135]) 0) 29 true) treeT_J013_part034 treeT_J013_part035)

#time def treeT_J013_part037 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [661412232226443247677545379518655]) 0) 33 true) treeT_J013_part033 treeT_J013_part036)

#time def treeT_J013_part038 : IntSourceTree :=
  (.node 221 (sourceLit (List.headD (raw_ints% [1128706889695027560588341490694875]) 0) 33 true) (.node 219 (sourceLit (List.headD (raw_ints% [234338794797806286599742451828743375]) 0) 32 false) (.node 218 (sourceLit (List.headD (raw_ints% [648970633923906767113258822078875]) 0) 34 true) (.node 217 (sourceLit (List.headD (raw_ints% [935735898818744596617454297024875]) 0) 40 true) .empty .empty) .empty) (.node 220 (sourceLit (List.headD (raw_ints% [589345897781112772524915550184325]) 0) 34 true) .empty .empty)) (.node 223 (sourceLit (List.headD (raw_ints% [4172237980472283468610212828604125]) 0) 31 true) (.node 222 (sourceLit (List.headD (raw_ints% [541876480877473476026750430590475]) 0) 34 true) .empty .empty) (.node 224 (sourceLit (List.headD (raw_ints% [503004829033383709197441276096525]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part039 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [418773937254137133473817693894465]) 0) 34 true) (.node 228 (sourceLit (List.headD (raw_ints% [442740603951499761699717052954575]) 0) 34 true) (.node 227 (sourceLit (List.headD (raw_ints% [1824302088272495361218562948499425]) 0) 32 true) (.node 226 (sourceLit (List.headD (raw_ints% [470465191964720120713289655782625]) 0) 34 true) .empty .empty) .empty) (.node 229 (sourceLit (List.headD (raw_ints% [860681327405771660540402289134925]) 0) 33 true) .empty .empty)) (.node 232 (sourceLit (List.headD (raw_ints% [397803945389884082856806313224295]) 0) 34 true) (.node 231 (sourceLit (List.headD (raw_ints% [6527253697561763072602804491443775]) 0) 30 true) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [776521521988016227421370681748725]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part040 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [972103329700505136042114425944725]) 0) 33 true) treeT_J013_part038 treeT_J013_part039)

#time def treeT_J013_part041 : IntSourceTree :=
  (.node 239 (sourceLit (List.headD (raw_ints% [5456043109653916838698825824542085]) 0) 30 true) (.node 237 (sourceLit (List.headD (raw_ints% [1420473691456052106971762948895885]) 0) 32 true) (.node 236 (sourceLit (List.headD (raw_ints% [725474164277407943974282338735675]) 0) 33 true) (.node 235 (sourceLit (List.headD (raw_ints% [2966190903296139756398014011072915]) 0) 31 true) .empty .empty) .empty) (.node 238 (sourceLit (List.headD (raw_ints% [695767513953889980956324861829225]) 0) 33 true) .empty .empty)) (.node 251 (sourceLit (List.headD (raw_ints% [894302575313505505105737479854725]) 0) 35 true) (.node 250 (sourceLit (List.headD (raw_ints% [4302742748945709171320023194112725]) 0) 33 true) .empty .empty) (.node 252 (sourceLit (List.headD (raw_ints% [1541871597273645405996556843890375]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part042 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [1915982232204186932119439170440375]) 0) 33 true) (.node 255 (sourceLit (List.headD (raw_ints% [279522441211120287996695487282675]) 0) 36 true) (.node 254 (sourceLit (List.headD (raw_ints% [24608022692017285038296838141160875]) 0) 31 true) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [43370952620149835051591896901211375]) 0) 34 false) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [1688311591087400133619827475638225]) 0) 33 true) (.node 258 (sourceLit (List.headD (raw_ints% [1191214372331650677208902751595977125]) 0) 31 true) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [470422109965514837436275379113350125]) 0) 32 false) .empty .empty)))

#time def treeT_J013_part043 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [170320064078537977638743356737375]) 0) 37 true) treeT_J013_part041 treeT_J013_part042)

#time def treeT_J013_part044 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [758534477655000529748753729526285]) 0) 33 true) treeT_J013_part040 treeT_J013_part043)

#time def treeT_J013_part045 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [90838348412013997089598082154375]) 0) 37 true) treeT_J013_part037 treeT_J013_part044)

#time def treeT_J013_part046 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [4911567306773681096345687429870325]) 0) 31 true) (.node 264 (sourceLit (List.headD (raw_ints% [2652264728037025610574462844622175]) 0) 32 true) (.node 263 (sourceLit (List.headD (raw_ints% [1382993078492675275844790822017625]) 0) 33 true) (.node 262 (sourceLit (List.headD (raw_ints% [11569923722035964553630984487490625]) 0) 30 true) .empty .empty) .empty) (.node 265 (sourceLit (List.headD (raw_ints% [1274691238767731905414930822495725]) 0) 33 true) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [2291595949659112096683566066651325]) 0) 32 true) (.node 267 (sourceLit (List.headD (raw_ints% [1185101007030098312819400054515475]) 0) 33 true) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [1109550183579555799121322832299645]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part047 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [1878677726974507469249379593925615]) 0) 32 true) (.node 273 (sourceLit (List.headD (raw_ints% [1977294677206856907149546652504225]) 0) 32 true) (.node 272 (sourceLit (List.headD (raw_ints% [1015785462141296140329673780781925]) 0) 33 true) (.node 271 (sourceLit (List.headD (raw_ints% [1044827114374277897006252172837195]) 0) 33 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [7705765072431210500472572929436895]) 0) 30 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [1791296007497143297931562687058725]) 0) 32 true) (.node 276 (sourceLit (List.headD (raw_ints% [3667427931136656255570476477578485]) 0) 31 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [14009603758518765729346041792062025]) 0) 29 true) .empty .empty)))

#time def treeT_J013_part048 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [17215923882219089341383112868671275]) 0) 29 true) treeT_J013_part046 treeT_J013_part047)

#time def treeT_J013_part049 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [16476946515754510612399989119782875]) 0) 34 true) (.node 293 (sourceLit (List.headD (raw_ints% [68123299460196856707598602961125]) 0) 39 true) (.node 292 (sourceLit (List.headD (raw_ints% [161610433999366855674575273673375]) 0) 38 true) (.node 291 (sourceLit (List.headD (raw_ints% [799624861768177242171866964497025]) 0) 36 true) .empty .empty) .empty) (.node 294 (sourceLit (List.headD (raw_ints% [59115752156302721802928829505825]) 0) 39 true) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [73314501382349662143350434406007375]) 0) 35 false) (.node 296 (sourceLit (List.headD (raw_ints% [47171023199776572726774351282075]) 0) 39 true) .empty .empty) (.node 298 (sourceLit (List.headD (raw_ints% [316752899570070041251545087090375]) 0) 36 true) .empty .empty)))

#time def treeT_J013_part050 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [219997062364822891661837386480275]) 0) 36 true) (.node 302 (sourceLit (List.headD (raw_ints% [243804086533904083442558055163125]) 0) 36 true) (.node 301 (sourceLit (List.headD (raw_ints% [58943852106901233124607965075505625]) 0) 36 false) (.node 300 (sourceLit (List.headD (raw_ints% [274741423326571840273727981363475]) 0) 36 true) .empty .empty) .empty) (.node 303 (sourceLit (List.headD (raw_ints% [1849421435390920271255192914721625]) 0) 33 true) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [201056511700752946175410291678275]) 0) 36 true) (.node 305 (sourceLit (List.headD (raw_ints% [840080699168260237266174209338725]) 0) 34 true) .empty .empty) (.node 307 (sourceLit (List.headD (raw_ints% [771816304625296433781781120342725]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part051 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [356388291782364240952161300856180125]) 0) 34 true) treeT_J013_part049 treeT_J013_part050)

#time def treeT_J013_part052 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [1713230033294431952559402117404859]) 0) 32 true) treeT_J013_part048 treeT_J013_part051)

#time def treeT_J013_part053 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [1255049402294576053237976879815125]) 0) 33 true) (.node 311 (sourceLit (List.headD (raw_ints% [2672167546164331567195077094306875]) 0) 32 true) (.node 310 (sourceLit (List.headD (raw_ints% [172694061581354666411876284601295]) 0) 36 true) (.node 309 (sourceLit (List.headD (raw_ints% [89432163890833777258947736094775]) 0) 37 true) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [161755792246098453537361464903225]) 0) 36 true) .empty .empty)) (.node 315 (sourceLit (List.headD (raw_ints% [1184893542283767686018639729590995]) 0) 33 true) (.node 314 (sourceLit (List.headD (raw_ints% [304690049887964094350198230744485]) 0) 35 true) .empty .empty) (.node 316 (sourceLit (List.headD (raw_ints% [288300890674274881318774313797485]) 0) 35 true) .empty .empty)))

#time def treeT_J013_part054 : IntSourceTree :=
  (.node 334 (sourceLit (List.headD (raw_ints% [10271106631603505595993646574935125]) 0) 31 true) (.node 332 (sourceLit (List.headD (raw_ints% [4855127296871772531378378872085825]) 0) 34 true) (.node 319 (sourceLit (List.headD (raw_ints% [2138390162216212222661803991879985]) 0) 32 true) (.node 318 (sourceLit (List.headD (raw_ints% [273882123385813329243809456307375]) 0) 35 true) .empty .empty) .empty) (.node 333 (sourceLit (List.headD (raw_ints% [476121671918929445059557737956125]) 0) 37 true) .empty .empty)) (.node 336 (sourceLit (List.headD (raw_ints% [76324845651658856276391875140777125]) 0) 34 true) (.node 335 (sourceLit (List.headD (raw_ints% [666329593289723260850165784810525]) 0) 36 true) .empty .empty) (.node 337 (sourceLit (List.headD (raw_ints% [4121908737367214376907677793665225]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part055 : IntSourceTree :=
  (.node 317 (sourceLit (List.headD (raw_ints% [280869279960075518574839191085325]) 0) 35 true) treeT_J013_part053 treeT_J013_part054)

#time def treeT_J013_part056 : IntSourceTree :=
  (.node 343 (sourceLit (List.headD (raw_ints% [2517872306049790059236138060592375]) 0) 33 true) (.node 341 (sourceLit (List.headD (raw_ints% [2878769946212059634582665050572625]) 0) 33 true) (.node 340 (sourceLit (List.headD (raw_ints% [3321528444224428765053565785962791125]) 0) 32 true) (.node 339 (sourceLit (List.headD (raw_ints% [3379734802033720526404893917807775]) 0) 33 true) .empty .empty) .empty) (.node 342 (sourceLit (List.headD (raw_ints% [7556382993405393804503450514152210625]) 0) 30 false) .empty .empty)) (.node 345 (sourceLit (List.headD (raw_ints% [2245261759069434361174467361188675]) 0) 33 true) (.node 344 (sourceLit (List.headD (raw_ints% [4745421013526655474446308814264325]) 0) 32 true) .empty .empty) (.node 346 (sourceLit (List.headD (raw_ints% [8529723879918482699913099919549275]) 0) 31 true) .empty .empty)))

#time def treeT_J013_part057 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [1718277870927396765583768380783525]) 0) 33 true) (.node 349 (sourceLit (List.headD (raw_ints% [1859891428734838405357409173943955]) 0) 33 true) (.node 348 (sourceLit (List.headD (raw_ints% [3882934487343259373570682896090475]) 0) 32 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [28573344029887804615198128011853525]) 0) 29 true) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [3198890674668293606046020224398975]) 0) 32 true) (.node 352 (sourceLit (List.headD (raw_ints% [828191042011517713432701656762475]) 0) 34 true) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [12375025364282006351335057147605105]) 0) 30 true) .empty .empty)))

#time def treeT_J013_part058 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [2031803180181948825987164612336925]) 0) 33 true) treeT_J013_part056 treeT_J013_part057)

#time def treeT_J013_part059 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [3537278416566839865796116652588213125]) 0) 31 false) treeT_J013_part055 treeT_J013_part058)

#time def treeT_J013_part060 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [185590100769649637779920750390225]) 0) 36 true) treeT_J013_part052 treeT_J013_part059)

#time def treeT_J013_part061 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [1517092827013089809796982651242975]) 0) 33 true) treeT_J013_part045 treeT_J013_part060)

#time def treeT_J013_part062 : IntSourceTree :=
  (.node 171 (sourceLit (List.headD (raw_ints% [361668290676115154919854880502575]) 0) 35 true) treeT_J013_part030 treeT_J013_part061)

#time def treeT_J013_part063 : IntSourceTree :=
  (.node 373 (sourceLit (List.headD (raw_ints% [3765154505508622824056801224707825]) 0) 35 true) (.node 358 (sourceLit (List.headD (raw_ints% [21941664076370900648233374666859575]) 0) 29 true) (.node 357 (sourceLit (List.headD (raw_ints% [2821518243291254803168826333701035]) 0) 32 true) (.node 356 (sourceLit (List.headD (raw_ints% [5811720407133485232578641359149475]) 0) 31 true) .empty .empty) .empty) (.node 359 (sourceLit (List.headD (raw_ints% [2668883940878581315341549183513141]) 0) 32 true) .empty .empty)) (.node 375 (sourceLit (List.headD (raw_ints% [55636679431414536853606309904196375]) 0) 32 false) (.node 374 (sourceLit (List.headD (raw_ints% [357890167606324001453700078944475]) 0) 38 true) .empty .empty) (.node 376 (sourceLit (List.headD (raw_ints% [477645500490616969943068379682225]) 0) 37 true) .empty .empty)))

#time def treeT_J013_part064 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [1903553600076443300812432829920125]) 0) 34 true) (.node 380 (sourceLit (List.headD (raw_ints% [2280769108727433165309981992353875]) 0) 34 true) (.node 379 (sourceLit (List.headD (raw_ints% [4962831583696296829604761856012933625]) 0) 32 false) (.node 378 (sourceLit (List.headD (raw_ints% [2854897139086934211901497445303725]) 0) 34 true) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [3793079261079638630050429506566836125]) 0) 33 true) .empty .empty)) (.node 384 (sourceLit (List.headD (raw_ints% [1637884056590498492588788514671275]) 0) 34 true) (.node 383 (sourceLit (List.headD (raw_ints% [7563780679146957485588471285811097125]) 0) 31 false) .empty .empty) (.node 385 (sourceLit (List.headD (raw_ints% [3065259615190134999913960395586875]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part065 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [37409836758502129604935577386696125]) 0) 37 true) treeT_J013_part063 treeT_J013_part064)

#time def treeT_J013_part066 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [17884673845230478346417819634626025]) 0) 30 true) (.node 389 (sourceLit (List.headD (raw_ints% [2452019865089918937427519118574075]) 0) 33 true) (.node 388 (sourceLit (List.headD (raw_ints% [1289442777103350274867481610776025]) 0) 34 true) (.node 387 (sourceLit (List.headD (raw_ints% [5442458661417296964785975438178375]) 0) 32 true) .empty .empty) .empty) (.node 390 (sourceLit (List.headD (raw_ints% [1169115182409419739709904035538775]) 0) 34 true) .empty .empty)) (.node 393 (sourceLit (List.headD (raw_ints% [2057714765751494800492829747234775]) 0) 33 true) (.node 392 (sourceLit (List.headD (raw_ints% [1071254701943002951434322521170625]) 0) 34 true) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [1980130475116437228645227301421035]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part067 : IntSourceTree :=
  (.node 414 (sourceLit (List.headD (raw_ints% [110213837544672424773823992615715275]) 0) 31 true) (.node 398 (sourceLit (List.headD (raw_ints% [1725989749748001486193588508471535]) 0) 33 true) (.node 397 (sourceLit (List.headD (raw_ints% [3564766167452881083979927830466875]) 0) 32 true) (.node 396 (sourceLit (List.headD (raw_ints% [1843159508535818515078694842796205]) 0) 33 true) .empty .empty) .empty) (.node 399 (sourceLit (List.headD (raw_ints% [13388103427506051757586158699339635]) 0) 30 true) .empty .empty)) (.node 416 (sourceLit (List.headD (raw_ints% [208286370734732249406390060185750625]) 0) 33 false) (.node 415 (sourceLit (List.headD (raw_ints% [2196791747560868750779434846745275]) 0) 36 true) .empty .empty) (.node 417 (sourceLit (List.headD (raw_ints% [11162747278332528661270510356165975]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part068 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [7635451195146935607260498229241125]) 0) 31 true) treeT_J013_part066 treeT_J013_part067)

#time def treeT_J013_part069 : IntSourceTree :=
  (.node 386 (sourceLit (List.headD (raw_ints% [1441035712266422576472826194475575]) 0) 34 true) treeT_J013_part065 treeT_J013_part068)

#time def treeT_J013_part070 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [5096342094255983144013593259088125]) 0) 33 true) (.node 421 (sourceLit (List.headD (raw_ints% [6244306488697673026657262918842875]) 0) 33 true) (.node 420 (sourceLit (List.headD (raw_ints% [13247191611617022424263089497988658375]) 0) 32 false) (.node 419 (sourceLit (List.headD (raw_ints% [8039853754314016321201095863407125]) 0) 33 true) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [68245651170679611885310322619221588625]) 0) 30 true) .empty .empty)) (.node 425 (sourceLit (List.headD (raw_ints% [4306274467292559609180686697496425]) 0) 33 true) (.node 424 (sourceLit (List.headD (raw_ints% [3784263050080242070531458797312680725]) 0) 33 false) .empty .empty) (.node 426 (sourceLit (List.headD (raw_ints% [15992353041602597299398583245145725]) 0) 31 true) .empty .empty)))

#time def treeT_J013_part071 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [11259145509138336638956206380526225]) 0) 31 true) (.node 430 (sourceLit (List.headD (raw_ints% [49891291652989601382482483782516875]) 0) 29 true) (.node 429 (sourceLit (List.headD (raw_ints% [3297879679678562694112517269160145]) 0) 33 true) (.node 428 (sourceLit (List.headD (raw_ints% [7001982835491334556001267980266275]) 0) 32 true) .empty .empty) .empty) (.node 431 (sourceLit (List.headD (raw_ints% [2958182858710282193255847761371575]) 0) 33 true) .empty .empty)) (.node 434 (sourceLit (List.headD (raw_ints% [20548410887741910456550218808151295]) 0) 30 true) (.node 433 (sourceLit (List.headD (raw_ints% [5371146940875730005428559944966025]) 0) 32 true) .empty .empty) (.node 435 (sourceLit (List.headD (raw_ints% [4924158829232830874227117107697995]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part072 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [3732339668883741479904140165565375]) 0) 33 true) treeT_J013_part070 treeT_J013_part071)

#time def treeT_J013_part073 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [859573123535125890418183233531525]) 0) 38 true) (.node 439 (sourceLit (List.headD (raw_ints% [4235075058113424629432804850372999]) 0) 32 true) (.node 438 (sourceLit (List.headD (raw_ints% [35094594602875196695445470620610425]) 0) 29 true) (.node 437 (sourceLit (List.headD (raw_ints% [4551119790852019257145953037483785]) 0) 32 true) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [82925258488043480813715151259955825]) 0) 33 true) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [4153925069622797224684506455431125]) 0) 35 true) (.node 457 (sourceLit (List.headD (raw_ints% [507565064802749286245874679279319625]) 0) 34 false) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [6644284552675704642416316207049125375]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part074 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [1729229018832742325712402372208425]) 0) 35 true) (.node 462 (sourceLit (List.headD (raw_ints% [2170376444310614862922415044461375]) 0) 35 true) (.node 461 (sourceLit (List.headD (raw_ints% [4260067718174165263578379751138873625]) 0) 35 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [37904715924913284685449396952516342875]) 0) 32 true) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [1432619377513068516353930251510425]) 0) 35 true) (.node 465 (sourceLit (List.headD (raw_ints% [7571591359775674276062831555020948325]) 0) 33 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [5274947190092650167306303903483675]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part075 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [2879542322793291577945556935526625]) 0) 35 true) treeT_J013_part073 treeT_J013_part074)

#time def treeT_J013_part076 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [9459181983160385981942355099332775]) 0) 31 true) treeT_J013_part072 treeT_J013_part075)

#time def treeT_J013_part077 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [8325737521655112455227870558085317125]) 0) 31 true) treeT_J013_part069 treeT_J013_part076)

#time def treeT_J013_part078 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [7143715977635347037970546886056675]) 0) 32 true) (.node 471 (sourceLit (List.headD (raw_ints% [16003308903879561518032332073945425]) 0) 31 true) (.node 470 (sourceLit (List.headD (raw_ints% [1064382248634571477201306616810685]) 0) 35 true) (.node 469 (sourceLit (List.headD (raw_ints% [568745371300176952321718607711525]) 0) 36 true) .empty .empty) .empty) (.node 472 (sourceLit (List.headD (raw_ints% [943464078383639620910762620100475]) 0) 35 true) .empty .empty)) (.node 475 (sourceLit (List.headD (raw_ints% [6456479846297487424644860289455085]) 0) 32 true) (.node 474 (sourceLit (List.headD (raw_ints% [1695508232879646388391666321772495]) 0) 34 true) .empty .empty) (.node 476 (sourceLit (List.headD (raw_ints% [1540499660348506179574211132450895]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part079 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [16446778558499101035161865426554431125]) 0) 31 false) (.node 496 (sourceLit (List.headD (raw_ints% [374136887710819211033820362705662275]) 0) 33 true) (.node 479 (sourceLit (List.headD (raw_ints% [10853245587684572468929655960635395]) 0) 31 true) (.node 478 (sourceLit (List.headD (raw_ints% [1412565020552008885476182264506125]) 0) 34 true) .empty .empty) .empty) (.node 497 (sourceLit (List.headD (raw_ints% [43849932627915528325493216589851625]) 0) 33 true) .empty .empty)) (.node 500 (sourceLit (List.headD (raw_ints% [39824329822319840993928354326185159875]) 0) 32 true) (.node 499 (sourceLit (List.headD (raw_ints% [25191546802668361476274955780041875]) 0) 33 true) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [16792032093648659596907192565370125]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part080 : IntSourceTree :=
  (.node 477 (sourceLit (List.headD (raw_ints% [1473603953926876224490606817216475]) 0) 34 true) treeT_J013_part078 treeT_J013_part079)

#time def treeT_J013_part081 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [7728615351220806650927301846518025]) 0) 33 true) (.node 505 (sourceLit (List.headD (raw_ints% [9527557683369378996518532280170975]) 0) 33 true) (.node 504 (sourceLit (List.headD (raw_ints% [2605561185937095422248803484364313975]) 0) 37 true) (.node 503 (sourceLit (List.headD (raw_ints% [12266669460228935759365727096602875]) 0) 33 true) .empty .empty) .empty) (.node 506 (sourceLit (List.headD (raw_ints% [60588723231246996805802051023412732325]) 0) 31 false) .empty .empty)) (.node 509 (sourceLit (List.headD (raw_ints% [6473707887443002126034116949997255]) 0) 33 true) (.node 508 (sourceLit (List.headD (raw_ints% [14097805924879266113223947633668425]) 0) 32 true) .empty .empty) (.node 510 (sourceLit (List.headD (raw_ints% [95707523399855698411877479791633525]) 0) 29 true) .empty .empty)))

#time def treeT_J013_part082 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [16366737402029563716637086058487565]) 0) 31 true) (.node 514 (sourceLit (List.headD (raw_ints% [36601316933340865847214156280302105]) 0) 30 true) (.node 513 (sourceLit (List.headD (raw_ints% [9724278313262503929143641976641575]) 0) 32 true) (.node 512 (sourceLit (List.headD (raw_ints% [20747472298620786397108457767364625]) 0) 31 true) .empty .empty) .empty) (.node 515 (sourceLit (List.headD (raw_ints% [8639907033804340232906213466481965]) 0) 32 true) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [59216058448444881671953365681243975]) 0) 29 true) (.node 517 (sourceLit (List.headD (raw_ints% [7772877491936030179447736022123375]) 0) 32 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [7065445106302646454376653265676001]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part083 : IntSourceTree :=
  (.node 511 (sourceLit (List.headD (raw_ints% [5556875130366289624354605173113905]) 0) 33 true) treeT_J013_part081 treeT_J013_part082)

#time def treeT_J013_part084 : IntSourceTree :=
  (.node 502 (sourceLit (List.headD (raw_ints% [340889985133826188754326626692109500625]) 0) 30 false) treeT_J013_part080 treeT_J013_part083)

#time def treeT_J013_part085 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [416699416983652758125225420597142186375]) 0) 31 false) (.node 541 (sourceLit (List.headD (raw_ints% [56864600695016502048241873330740654375]) 0) 33 true) (.node 540 (sourceLit (List.headD (raw_ints% [19432462157081778320383841908988625]) 0) 34 true) (.node 539 (sourceLit (List.headD (raw_ints% [29735347663850510319994497840652681875]) 0) 32 false) .empty .empty) .empty) (.node 542 (sourceLit (List.headD (raw_ints% [12451279205027429871062362476447375]) 0) 34 true) .empty .empty)) (.node 545 (sourceLit (List.headD (raw_ints% [90949549309762727788024543054678995525]) 0) 33 true) (.node 544 (sourceLit (List.headD (raw_ints% [8808211422563451107940922352186025]) 0) 34 true) .empty .empty) (.node 546 (sourceLit (List.headD (raw_ints% [6662318928343241963810671777150125]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part086 : IntSourceTree :=
  (.node 552 (sourceLit (List.headD (raw_ints% [3669946973599010382533079932912955]) 0) 34 true) (.node 550 (sourceLit (List.headD (raw_ints% [4344943390173859171631503716375885]) 0) 34 true) (.node 549 (sourceLit (List.headD (raw_ints% [9547842954477850494650198771976225]) 0) 33 true) (.node 548 (sourceLit (List.headD (raw_ints% [5285718459440415445890643291728675]) 0) 34 true) .empty .empty) .empty) (.node 551 (sourceLit (List.headD (raw_ints% [63700905592096575375812815643742675]) 0) 30 true) .empty .empty)) (.node 554 (sourceLit (List.headD (raw_ints% [6333261847503211152360309333096585]) 0) 33 true) (.node 553 (sourceLit (List.headD (raw_ints% [6801878160492719679568955440653975]) 0) 33 true) .empty .empty) (.node 555 (sourceLit (List.headD (raw_ints% [23688357240745890997924435701391935]) 0) 31 true) .empty .empty)))

#time def treeT_J013_part087 : IntSourceTree :=
  (.node 547 (sourceLit (List.headD (raw_ints% [60599273125627182106136663631219699675]) 0) 32 false) treeT_J013_part085 treeT_J013_part086)

#time def treeT_J013_part088 : IntSourceTree :=
  (.node 581 (sourceLit (List.headD (raw_ints% [60937816534678453684628175070584375]) 0) 33 true) (.node 559 (sourceLit (List.headD (raw_ints% [37509567273075736734094053759973185]) 0) 30 true) (.node 558 (sourceLit (List.headD (raw_ints% [4947747450832012408495371493111125]) 0) 33 true) (.node 557 (sourceLit (List.headD (raw_ints% [10472321586322058818674658789621665]) 0) 32 true) .empty .empty) .empty) (.node 580 (sourceLit (List.headD (raw_ints% [99295025150020861633917350007490523625]) 0) 32 false) .empty .empty)) (.node 583 (sourceLit (List.headD (raw_ints% [37538447359880783724883722809186625]) 0) 33 true) (.node 582 (sourceLit (List.headD (raw_ints% [1250723596254090221526196599983959970625]) 0) 30 true) .empty .empty) (.node 584 (sourceLit (List.headD (raw_ints% [500077374933639811637187132096800233575]) 0) 32 false) .empty .empty)))

#time def treeT_J013_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [14669165950318659657528456216917445]) 0) 33 true) (.node 587 (sourceLit (List.headD (raw_ints% [18920660362152161204315385262082475]) 0) 33 true) (.node 586 (sourceLit (List.headD (raw_ints% [788185117709348819109998395460844696525]) 0) 31 true) .empty .empty) (.node 588 (sourceLit (List.headD (raw_ints% [121212644057179243478386551210073067775]) 0) 32 false) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [11822898430329147062171409692389635]) 0) 33 true) (.node 590 (sourceLit (List.headD (raw_ints% [209823451143435517416928880911605675]) 0) 29 true) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [21476716646737894489352178938189025]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part090 : IntSourceTree :=
  (.node 585 (sourceLit (List.headD (raw_ints% [25705288006884425435245157128573125]) 0) 33 true) treeT_J013_part088 treeT_J013_part089)

#time def treeT_J013_part091 : IntSourceTree :=
  (.node 556 (sourceLit (List.headD (raw_ints% [5558907713107327873757791201580175]) 0) 33 true) treeT_J013_part087 treeT_J013_part090)

#time def treeT_J013_part092 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [35542082488669933876124203678989375]) 0) 34 true) treeT_J013_part084 treeT_J013_part091)

#time def treeT_J013_part093 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [1221448445890195602518329277394675]) 0) 35 true) treeT_J013_part077 treeT_J013_part092)

#time def treeT_J013_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [108341086932708059426841174952702665]) 0) 29 true) (.node 596 (sourceLit (List.headD (raw_ints% [31009977079462218279211785344296305]) 0) 31 true) (.node 595 (sourceLit (List.headD (raw_ints% [16693140356208504376535023865904375]) 0) 32 true) (.node 594 (sourceLit (List.headD (raw_ints% [72228733634542649025889130770161495]) 0) 30 true) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [14462753360493281315583428784197325]) 0) 32 true) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [6060817166206377976695726574267125]) 0) 37 true) (.node 599 (sourceLit (List.headD (raw_ints% [12725544697025403179604832706768499]) 0) 32 true) .empty .empty) (.node 623 (sourceLit (List.headD (raw_ints% [208427876654717872456427752572637769625]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [3788193496879178791527537544026407625]) 0) 38 false) (.node 627 (sourceLit (List.headD (raw_ints% [106098048854372000152016882386508049525]) 0) 35 true) (.node 626 (sourceLit (List.headD (raw_ints% [2380371134817647933929310668927875]) 0) 37 true) (.node 625 (sourceLit (List.headD (raw_ints% [147756731060850634856302918787869807275]) 0) 35 false) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [1704367737838968219803092746294225]) 0) 37 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [18265318193917367755139508158482875]) 0) 33 true) (.node 630 (sourceLit (List.headD (raw_ints% [1290527820018100060737119062567695]) 0) 37 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [1019118932091267084954791219934585]) 0) 37 true) .empty .empty)))

#time def treeT_J013_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [3591279492164666577117850057125075]) 0) 37 true) treeT_J013_part094 treeT_J013_part095)

#time def treeT_J013_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [1189375738707658613386007161385775]) 0) 36 true) (.node 636 (sourceLit (List.headD (raw_ints% [1391779080387647062847154083040525]) 0) 36 true) (.node 635 (sourceLit (List.headD (raw_ints% [6067547049224594753495586883596195]) 0) 34 true) (.node 634 (sourceLit (List.headD (raw_ints% [1662754453503295997345086019195685]) 0) 36 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [1283603468321259966283570409667165]) 0) 36 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [156407701958723311529379527567361375]) 0) 33 true) (.node 639 (sourceLit (List.headD (raw_ints% [8853939957454040336593390149091185]) 0) 33 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [2167500388171382791288609152677902390575]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part098 : IntSourceTree :=
  (.node 670 (sourceLit (List.headD (raw_ints% [3879319964255422518041615373963953013675]) 0) 29 false) (.node 668 (sourceLit (List.headD (raw_ints% [1818781425727131245910656669394201860175]) 0) 32 true) (.node 667 (sourceLit (List.headD (raw_ints% [57251215952012572681422556143609525]) 0) 33 true) (.node 666 (sourceLit (List.headD (raw_ints% [5516400511656569134511691796672678529325]) 0) 31 false) .empty .empty) .empty) (.node 669 (sourceLit (List.headD (raw_ints% [39870601660528323376170511664497755]) 0) 33 true) .empty .empty)) (.node 672 (sourceLit (List.headD (raw_ints% [51584556128931576531205853695742475]) 0) 32 true) (.node 671 (sourceLit (List.headD (raw_ints% [29473991810250054881416400309776605]) 0) 33 true) .empty .empty) (.node 673 (sourceLit (List.headD (raw_ints% [45588314178311514305985640589151375]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part099 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [89215655742384905032526044699429275]) 0) 33 true) treeT_J013_part097 treeT_J013_part098)

#time def treeT_J013_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [7337419243122587404891611748767525]) 0) 34 true) treeT_J013_part096 treeT_J013_part099)

#time def treeT_J013_part101 : IntSourceTree :=
  (.node 679 (sourceLit (List.headD (raw_ints% [25334478941619672448747396457576301]) 0) 32 true) (.node 677 (sourceLit (List.headD (raw_ints% [30074177211911424695525501873099475]) 0) 32 true) (.node 676 (sourceLit (List.headD (raw_ints% [66070775708131297776717604793242815]) 0) 31 true) (.node 675 (sourceLit (List.headD (raw_ints% [36515002155896967538507728748357545]) 0) 32 true) .empty .empty) .empty) (.node 678 (sourceLit (List.headD (raw_ints% [220261400957534491941752849922091575]) 0) 29 true) .empty .empty)) (.node 706 (sourceLit (List.headD (raw_ints% [70172686663843721561091559348006275]) 0) 34 true) (.node 705 (sourceLit (List.headD (raw_ints% [2758527312414785330713820827829381619675]) 0) 33 true) .empty .empty) (.node 707 (sourceLit (List.headD (raw_ints% [6365184902491545135727826855764742925525]) 0) 32 false) .empty .empty)))

#time def treeT_J013_part102 : IntSourceTree :=
  (.node 713 (sourceLit (List.headD (raw_ints% [36909717642686401721422630198207425]) 0) 33 true) (.node 711 (sourceLit (List.headD (raw_ints% [3879466086800973856983656490029220876675]) 0) 30 false) (.node 710 (sourceLit (List.headD (raw_ints% [29546379100383522890273559163956195]) 0) 34 true) (.node 709 (sourceLit (List.headD (raw_ints% [1940003617627264967239537870803046904175]) 0) 33 true) .empty .empty) .empty) (.node 712 (sourceLit (List.headD (raw_ints% [21321040353519918201778070550299925]) 0) 34 true) .empty .empty)) (.node 715 (sourceLit (List.headD (raw_ints% [114028305751583389902677750121629745]) 0) 31 true) (.node 714 (sourceLit (List.headD (raw_ints% [32286278550285146327224952435585895]) 0) 33 true) .empty .empty) (.node 716 (sourceLit (List.headD (raw_ints% [25380769512795791035730496084033345]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part103 : IntSourceTree :=
  (.node 708 (sourceLit (List.headD (raw_ints% [43616274049300826922997814173255725]) 0) 34 true) treeT_J013_part101 treeT_J013_part102)

#time def treeT_J013_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [14549151230710221517366310380923687711225]) 0) 32 false) (.node 746 (sourceLit (List.headD (raw_ints% [27584619010974851780222258419307731486725]) 0) 31 true) (.node 719 (sourceLit (List.headD (raw_ints% [149429881297902169249005728729362095]) 0) 30 true) (.node 718 (sourceLit (List.headD (raw_ints% [20559171302250155788437444582013275]) 0) 33 true) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [223439530703362313562943681248415575]) 0) 33 true) .empty .empty)) (.node 750 (sourceLit (List.headD (raw_ints% [65959435728327901469706827239661453947275]) 0) 29 true) (.node 749 (sourceLit (List.headD (raw_ints% [134594494536674984315820745028525145]) 0) 33 true) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [88711524591284036679677836346048175]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part105 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [161985835795035482028637895450016675]) 0) 31 true) (.node 754 (sourceLit (List.headD (raw_ints% [427986800137602279612119637980919495]) 0) 30 true) (.node 753 (sourceLit (List.headD (raw_ints% [124980008649847831308238923813248025]) 0) 32 true) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [92630112045243617770392080993986035]) 0) 32 true) .empty .empty)) (.node 758 (sourceLit (List.headD (raw_ints% [508268522482323721117134801894999225]) 0) 29 true) (.node 757 (sourceLit (List.headD (raw_ints% [71448900839271739447396482463033905]) 0) 32 true) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [56902206267380950705002381870476799]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part106 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [3879569255913231720136718901736612361625]) 0) 31 false) treeT_J013_part104 treeT_J013_part105)

#time def treeT_J013_part107 : IntSourceTree :=
  (.node 717 (sourceLit (List.headD (raw_ints% [45533120214991138316180478238568175]) 0) 32 true) treeT_J013_part103 treeT_J013_part106)

#time def treeT_J013_part108 : IntSourceTree :=
  (.node 674 (sourceLit (List.headD (raw_ints% [162568682145380147930642445190399305]) 0) 30 true) treeT_J013_part100 treeT_J013_part107)

#time def treeT_J013_part109 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [33695242118882059238949882897874125]) 0) 35 true) (.node 790 (sourceLit (List.headD (raw_ints% [52524057718145730712773592932284475]) 0) 35 true) (.node 789 (sourceLit (List.headD (raw_ints% [2061144356042185810575731031465841826925]) 0) 36 false) (.node 788 (sourceLit (List.headD (raw_ints% [89911628327030743319972933537579925]) 0) 35 true) .empty .empty) .empty) (.node 791 (sourceLit (List.headD (raw_ints% [34919450907564437663345241864845337411975]) 0) 31 true) .empty .empty)) (.node 794 (sourceLit (List.headD (raw_ints% [46346865049781342490506985688831065]) 0) 34 true) (.node 793 (sourceLit (List.headD (raw_ints% [3879643075348517092940161746997008776475]) 0) 32 false) .empty .empty) (.node 795 (sourceLit (List.headD (raw_ints% [156979247193009444854720943929644875]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part110 : IntSourceTree :=
  (.node 829 (sourceLit (List.headD (raw_ints% [584698532079570962243962723272114255]) 0) 33 true) (.node 799 (sourceLit (List.headD (raw_ints% [179419320592210775934064536582818565]) 0) 31 true) (.node 798 (sourceLit (List.headD (raw_ints% [25444864768510791829479518940510315]) 0) 34 true) (.node 797 (sourceLit (List.headD (raw_ints% [29113178895011085928114354302862125]) 0) 34 true) .empty .empty) .empty) (.node 828 (sourceLit (List.headD (raw_ints% [82448759057643015349266480931068636535725]) 0) 32 true) .empty .empty)) (.node 831 (sourceLit (List.headD (raw_ints% [331480937153881809022510907112227625]) 0) 33 true) (.node 830 (sourceLit (List.headD (raw_ints% [593612390875127468977093971294916961640075]) 0) 29 false) .empty .empty) (.node 832 (sourceLit (List.headD (raw_ints% [73718471071042107046827202631427287185575]) 0) 31 true) .empty .empty)))

#time def treeT_J013_part111 : IntSourceTree :=
  (.node 796 (sourceLit (List.headD (raw_ints% [33624671266223913367330792454976345]) 0) 34 true) treeT_J013_part109 treeT_J013_part110)

#time def treeT_J013_part112 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [1354974926798385778282183873488176775]) 0) 29 true) (.node 836 (sourceLit (List.headD (raw_ints% [465931152977002297390245880268562825]) 0) 31 true) (.node 835 (sourceLit (List.headD (raw_ints% [278144808353007122153663804516662485]) 0) 32 true) (.node 834 (sourceLit (List.headD (raw_ints% [31037572589588274345800906095614051131295]) 0) 30 false) .empty .empty) .empty) (.node 837 (sourceLit (List.headD (raw_ints% [197548469290519567491249857176776855]) 0) 32 true) .empty .empty)) (.node 869 (sourceLit (List.headD (raw_ints% [98937913905980501833872329182795371151125]) 0) 33 true) (.node 839 (sourceLit (List.headD (raw_ints% [146656711880705383930833769653605721]) 0) 32 true) .empty .empty) (.node 870 (sourceLit (List.headD (raw_ints% [479650416643279500818415537407545305]) 0) 34 true) .empty .empty)))

#time def treeT_J013_part113 : IntSourceTree :=
  (.node 875 (sourceLit (List.headD (raw_ints% [31037886548082660364690615537501910421045]) 0) 31 false) (.node 873 (sourceLit (List.headD (raw_ints% [38799057073195312069883682189212147981025]) 0) 33 true) (.node 872 (sourceLit (List.headD (raw_ints% [264090452916117690544611141316479375]) 0) 34 true) .empty .empty) (.node 874 (sourceLit (List.headD (raw_ints% [321450135152702431533945231175075845]) 0) 33 true) .empty .empty)) (.node 877 (sourceLit (List.headD (raw_ints% [349478437396957953677788463057114325]) 0) 32 true) (.node 876 (sourceLit (List.headD (raw_ints% [210895465820559295419002219606709795]) 0) 33 true) .empty .empty) (.node 878 (sourceLit (List.headD (raw_ints% [146658739753497983832290819295756225]) 0) 33 true) .empty .empty)))

#time def treeT_J013_part114 : IntSourceTree :=
  (.node 871 (sourceLit (List.headD (raw_ints% [663451292690256344303784455024607636464025]) 0) 30 false) treeT_J013_part112 treeT_J013_part113)

#time def treeT_J013_part115 : IntSourceTree :=
  (.node 833 (sourceLit (List.headD (raw_ints% [414143865252265116514959202552737975]) 0) 32 true) treeT_J013_part111 treeT_J013_part114)

#time def treeT_J013_part116 : IntSourceTree :=
  (.node 914 (sourceLit (List.headD (raw_ints% [651822485760713267463939821123008418827695]) 0) 30 true) (.node 912 (sourceLit (List.headD (raw_ints% [11518277558770288302353307150875545682025]) 0) 37 false) (.node 911 (sourceLit (List.headD (raw_ints% [1587120729419236194251151242517953595]) 0) 33 true) (.node 910 (sourceLit (List.headD (raw_ints% [3759625635866503527661008505144368838476075]) 0) 29 true) .empty .empty) .empty) (.node 913 (sourceLit (List.headD (raw_ints% [1698579758076676407841929927979097025]) 0) 32 true) .empty .empty)) (.node 916 (sourceLit (List.headD (raw_ints% [62076239027318297731678621320884089404915]) 0) 31 false) (.node 915 (sourceLit (List.headD (raw_ints% [1007655732257802603982117120183640895]) 0) 32 true) .empty .empty) (.node 917 (sourceLit (List.headD (raw_ints% [646033393991717614184759021250062325]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part117 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [344282405730993494076996174201005295]) 0) 35 true) (.node 952 (sourceLit (List.headD (raw_ints% [330757569125779625926635025300368555]) 0) 36 true) (.node 951 (sourceLit (List.headD (raw_ints% [1105769232139189967991198240042244118735025]) 0) 32 true) (.node 919 (sourceLit (List.headD (raw_ints% [439978247133286551398329507529419179]) 0) 32 true) .empty .empty) .empty) (.node 953 (sourceLit (List.headD (raw_ints% [407383938953844537745189511017229609805825]) 0) 33 false) .empty .empty)) (.node 956 (sourceLit (List.headD (raw_ints% [199190066609310827140778725144232775]) 0) 35 true) (.node 955 (sourceLit (List.headD (raw_ints% [170715093077198981957157609165127582312185]) 0) 33 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [7759573563219461836204037388668393314905]) 0) 35 false) .empty .empty)))

#time def treeT_J013_part118 : IntSourceTree :=
  (.node 918 (sourceLit (List.headD (raw_ints% [4236680071552941480562431535425652425]) 0) 29 true) treeT_J013_part116 treeT_J013_part117)

#time def treeT_J013_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [2541007671757255620067700581057662075]) 0) 32 true) (.node 995 (sourceLit (List.headD (raw_ints% [4500862759438093301249821667032443825]) 0) 32 true) (.node 994 (sourceLit (List.headD (raw_ints% [7169965509022225871386971997398682175720895]) 0) 30 false) (.node 959 (sourceLit (List.headD (raw_ints% [810135946484744313537094183775778195]) 0) 32 true) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [1427796983644910153388939494641904747902395]) 0) 31 true) .empty .empty)) (.node 999 (sourceLit (List.headD (raw_ints% [1557520369819591970011543300287805221]) 0) 32 true) (.node 998 (sourceLit (List.headD (raw_ints% [993229652772162667975597348181089769960265]) 0) 29 false) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [7852825881331021799215602434059192504969635]) 0) 31 false) .empty .empty)))

#time def treeT_J013_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [17133448746306953751820144362760289757841665]) 0) 31 false) (.node 1038 (sourceLit (List.headD (raw_ints% [2041633017519035989715232379103355975]) 0) 33 true) (.node 1037 (sourceLit (List.headD (raw_ints% [1489873572150665848078571793751251894421635]) 0) 32 true) .empty .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [993232893315948606952851496557824873073045]) 0) 30 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [24831206807182816237232746048201120080706425]) 0) 29 true) (.node 1077 (sourceLit (List.headD (raw_ints% [12275402300246144350679126484764388825]) 0) 32 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [6609011700256551988849386216125618679]) 0) 32 true) .empty .empty)))

#time def treeT_J013_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [3704102493000849992686706766455512725]) 0) 33 true) treeT_J013_part119 treeT_J013_part120)

#time def treeT_J013_part122 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [124843663559554907588117050488576525]) 0) 35 true) treeT_J013_part118 treeT_J013_part121)

#time def treeT_J013_part123 : IntSourceTree :=
  (.node 879 (sourceLit (List.headD (raw_ints% [996136285613964226414054800322539645]) 0) 30 true) treeT_J013_part115 treeT_J013_part122)

#time def treeT_J013_part124 : IntSourceTree :=
  (.node 787 (sourceLit (List.headD (raw_ints% [16974901956733198457975042637536237206125]) 0) 33 true) treeT_J013_part108 treeT_J013_part123)

#time def treeT_J013_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [19635297475529579131120997486662065]) 0) 32 true) treeT_J013_part093 treeT_J013_part124)

#time def treeT_J013_part126 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [2996363071232918040353792097986145]) 0) 32 true) treeT_J013_part062 treeT_J013_part125)

#time def treeT_J013 : IntSourceTree := treeT_J013_part126

#time def treeT_J014_part000 : IntSourceTree :=
  (.node 8 (sourceLit (List.headD (raw_ints% [105835470591249291987900882808875]) 0) 34 true) (.node 6 (sourceLit (List.headD (raw_ints% [120996770248656075659122168556625]) 0) 34 true) (.node 5 (sourceLit (List.headD (raw_ints% [262782342755780027739359350074525]) 0) 33 true) (.node 4 (sourceLit (List.headD (raw_ints% [145007971882285860082060753825125]) 0) 34 true) .empty .empty) .empty) (.node 7 (sourceLit (List.headD (raw_ints% [901520280953741799461518489207125]) 0) 31 true) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [47529320481951429516531639027525]) 0) 35 true) (.node 9 (sourceLit (List.headD (raw_ints% [100043384279270480468728401468375]) 0) 34 true) .empty .empty) (.node 11 (sourceLit (List.headD (raw_ints% [181411407024508283141483886796875]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [290548509490452466279400593093875]) 0) 32 true) (.node 15 (sourceLit (List.headD (raw_ints% [14180229429205556361069783073222875]) 0) 31 false) (.node 14 (sourceLit (List.headD (raw_ints% [20083998351874594443276538693125]) 0) 36 true) (.node 13 (sourceLit (List.headD (raw_ints% [41712919653893388459112811131875]) 0) 35 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 37 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [547833717135381911435100043018875]) 0) 31 true) (.node 18 (sourceLit (List.headD (raw_ints% [140955538759757774596015341494625]) 0) 33 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [133244720431391693630672348957775]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [43429500709609165761956959738125]) 0) 35 true) treeT_J014_part000 treeT_J014_part001)

#time def treeT_J014_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [115414221695854064000851096611075]) 0) 33 true) (.node 24 (sourceLit (List.headD (raw_ints% [120650533377323897796465850608375]) 0) 33 true) (.node 23 (sourceLit (List.headD (raw_ints% [988054460595482272444411249665375]) 0) 30 true) (.node 22 (sourceLit (List.headD (raw_ints% [126544092972017242961883604928625]) 0) 33 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [235916025207599304180696633875325]) 0) 32 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [110721809571785302961852038320525]) 0) 33 true) (.node 27 (sourceLit (List.headD (raw_ints% [452024041287489960024235717492275]) 0) 31 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [217102788262958188039597521848475]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [779777611338175400673486254996505]) 0) 30 true) (.node 33 (sourceLit (List.headD (raw_ints% [403360244834841561138201980374725]) 0) 31 true) (.node 32 (sourceLit (List.headD (raw_ints% [102636888677954467327673001544725]) 0) 33 true) (.node 31 (sourceLit (List.headD (raw_ints% [1672265565092646764646345144530325]) 0) 29 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [198240523679055586624146623346975]) 0) 32 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [377490249727180272313768649195775]) 0) 31 true) (.node 36 (sourceLit (List.headD (raw_ints% [191782173625851162276400053458025]) 0) 32 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [185825319940989753216213613266675]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [106485686971932107470540848893955]) 0) 33 true) treeT_J014_part003 treeT_J014_part004)

#time def treeT_J014_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [259564664309152065678570120490125]) 0) 32 true) treeT_J014_part002 treeT_J014_part005)

#time def treeT_J014_part007 : IntSourceTree :=
  (.node 49 (sourceLit (List.headD (raw_ints% [105835470591249291987900882808875]) 0) 35 true) (.node 47 (sourceLit (List.headD (raw_ints% [120996770248656075659122168556625]) 0) 35 true) (.node 46 (sourceLit (List.headD (raw_ints% [262782342755780027739359350074525]) 0) 34 true) (.node 45 (sourceLit (List.headD (raw_ints% [145007971882285860082060753825125]) 0) 35 true) .empty .empty) .empty) (.node 48 (sourceLit (List.headD (raw_ints% [901520280953741799461518489207125]) 0) 32 true) .empty .empty)) (.node 51 (sourceLit (List.headD (raw_ints% [47529320481951429516531639027525]) 0) 36 true) (.node 50 (sourceLit (List.headD (raw_ints% [100043384279270480468728401468375]) 0) 35 true) .empty .empty) (.node 52 (sourceLit (List.headD (raw_ints% [181411407024508283141483886796875]) 0) 34 true) .empty .empty)))

#time def treeT_J014_part008 : IntSourceTree :=
  (.node 58 (sourceLit (List.headD (raw_ints% [290548509490452466279400593093875]) 0) 33 true) (.node 56 (sourceLit (List.headD (raw_ints% [14180229429205556361069783073222875]) 0) 32 false) (.node 55 (sourceLit (List.headD (raw_ints% [20083998351874594443276538693125]) 0) 37 true) (.node 54 (sourceLit (List.headD (raw_ints% [41712919653893388459112811131875]) 0) 36 true) .empty .empty) .empty) (.node 57 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 38 true) .empty .empty)) (.node 60 (sourceLit (List.headD (raw_ints% [547833717135381911435100043018875]) 0) 32 true) (.node 59 (sourceLit (List.headD (raw_ints% [140955538759757774596015341494625]) 0) 34 true) .empty .empty) (.node 61 (sourceLit (List.headD (raw_ints% [133244720431391693630672348957775]) 0) 34 true) .empty .empty)))

#time def treeT_J014_part009 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [43429500709609165761956959738125]) 0) 36 true) treeT_J014_part007 treeT_J014_part008)

#time def treeT_J014_part010 : IntSourceTree :=
  (.node 67 (sourceLit (List.headD (raw_ints% [115414221695854064000851096611075]) 0) 34 true) (.node 65 (sourceLit (List.headD (raw_ints% [120650533377323897796465850608375]) 0) 34 true) (.node 64 (sourceLit (List.headD (raw_ints% [988054460595482272444411249665375]) 0) 31 true) (.node 63 (sourceLit (List.headD (raw_ints% [126544092972017242961883604928625]) 0) 34 true) .empty .empty) .empty) (.node 66 (sourceLit (List.headD (raw_ints% [235916025207599304180696633875325]) 0) 33 true) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [110721809571785302961852038320525]) 0) 34 true) (.node 68 (sourceLit (List.headD (raw_ints% [452024041287489960024235717492275]) 0) 32 true) .empty .empty) (.node 70 (sourceLit (List.headD (raw_ints% [217102788262958188039597521848475]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [198240523679055586624146623346975]) 0) 33 true) (.node 73 (sourceLit (List.headD (raw_ints% [102636888677954467327673001544725]) 0) 34 true) (.node 72 (sourceLit (List.headD (raw_ints% [1672265565092646764646345144530325]) 0) 30 true) .empty .empty) (.node 74 (sourceLit (List.headD (raw_ints% [403360244834841561138201980374725]) 0) 32 true) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [191782173625851162276400053458025]) 0) 33 true) (.node 76 (sourceLit (List.headD (raw_ints% [779777611338175400673486254996505]) 0) 31 true) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [377490249727180272313768649195775]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [106485686971932107470540848893955]) 0) 34 true) treeT_J014_part010 treeT_J014_part011)

#time def treeT_J014_part013 : IntSourceTree :=
  (.node 62 (sourceLit (List.headD (raw_ints% [259564664309152065678570120490125]) 0) 33 true) treeT_J014_part009 treeT_J014_part012)

#time def treeT_J014_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [1464124081221446960230391602301175]) 0) 29 true) treeT_J014_part006 treeT_J014_part013)

#time def treeT_J014_part015 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [164141620700547154459270126590225]) 0) 35 true) (.node 88 (sourceLit (List.headD (raw_ints% [378151610403375010648587791417625]) 0) 34 true) (.node 87 (sourceLit (List.headD (raw_ints% [3302997203138738644368231111985275]) 0) 31 true) (.node 86 (sourceLit (List.headD (raw_ints% [459035117280487364669120846743875]) 0) 34 true) .empty .empty) .empty) (.node 89 (sourceLit (List.headD (raw_ints% [701433512395200838524061686270375]) 0) 33 true) .empty .empty)) (.node 92 (sourceLit (List.headD (raw_ints% [146687781218196552304169596371975]) 0) 35 true) (.node 91 (sourceLit (List.headD (raw_ints% [618935667209655560608343324950125]) 0) 33 true) .empty .empty) (.node 93 (sourceLit (List.headD (raw_ints% [17462310921326861835296384458125]) 0) 38 true) .empty .empty)))

#time def treeT_J014_part016 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [1776554358788237818800104701732125]) 0) 31 true) (.node 97 (sourceLit (List.headD (raw_ints% [28651007367901565188418966739539625]) 0) 32 false) (.node 96 (sourceLit (List.headD (raw_ints% [30795464139541044813024025996125]) 0) 37 true) (.node 95 (sourceLit (List.headD (raw_ints% [16849856287054733222453002985662875]) 0) 31 true) .empty .empty) .empty) (.node 98 (sourceLit (List.headD (raw_ints% [458886545349563446109843947473375]) 0) 33 true) .empty .empty)) (.node 101 (sourceLit (List.headD (raw_ints% [836102769961611757191629965547625]) 0) 32 true) (.node 100 (sourceLit (List.headD (raw_ints% [430577434607639404753389017020725]) 0) 33 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [406434788753549531560805790902475]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part017 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [66775003067343737080637380783125]) 0) 36 true) treeT_J014_part015 treeT_J014_part016)

#time def treeT_J014_part018 : IntSourceTree :=
  (.node 108 (sourceLit (List.headD (raw_ints% [350935077211630953041552348123775]) 0) 33 true) (.node 106 (sourceLit (List.headD (raw_ints% [367187911813441527185012305822425]) 0) 33 true) (.node 105 (sourceLit (List.headD (raw_ints% [376069217693941484131857307895025]) 0) 33 true) (.node 104 (sourceLit (List.headD (raw_ints% [385525838510745074051068569106125]) 0) 33 true) .empty .empty) .empty) (.node 107 (sourceLit (List.headD (raw_ints% [1435304160373304473421337353510325]) 0) 31 true) .empty .empty)) (.node 110 (sourceLit (List.headD (raw_ints% [336401551315209104376867304388145]) 0) 33 true) (.node 109 (sourceLit (List.headD (raw_ints% [686945294312021732008873913136075]) 0) 32 true) .empty .empty) (.node 111 (sourceLit (List.headD (raw_ints% [5275023659322015252620775554620875]) 0) 29 true) .empty .empty)))

#time def treeT_J014_part019 : IntSourceTree :=
  (.node 117 (sourceLit (List.headD (raw_ints% [1182064972949170529033203860797235]) 0) 31 true) (.node 115 (sourceLit (List.headD (raw_ints% [2447104347340557088432129588001295]) 0) 30 true) (.node 114 (sourceLit (List.headD (raw_ints% [622854585744580151997237389010825]) 0) 32 true) (.node 113 (sourceLit (List.headD (raw_ints% [79306582516112825219258947759725]) 0) 35 true) .empty .empty) .empty) (.node 116 (sourceLit (List.headD (raw_ints% [601179921090371184220186439929875]) 0) 32 true) .empty .empty)) (.node 119 (sourceLit (List.headD (raw_ints% [4575719914413437396789906784831225]) 0) 29 true) (.node 118 (sourceLit (List.headD (raw_ints% [581303374562414895889386600565425]) 0) 32 true) .empty .empty) (.node 127 (sourceLit (List.headD (raw_ints% [169019173515915644504999339093625]) 0) 36 true) .empty .empty)))

#time def treeT_J014_part020 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [323305859209773962554490394031095]) 0) 33 true) treeT_J014_part018 treeT_J014_part019)

#time def treeT_J014_part021 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [3164980168350950778412710678176625]) 0) 30 true) treeT_J014_part017 treeT_J014_part020)

#time def treeT_J014_part022 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [51629140254293693271106318316925]) 0) 37 true) (.node 131 (sourceLit (List.headD (raw_ints% [29153075054648931235684621890675]) 0) 38 true) (.node 130 (sourceLit (List.headD (raw_ints% [501346743836659877586604883333625]) 0) 34 true) (.node 129 (sourceLit (List.headD (raw_ints% [136158069906062859330343454304375]) 0) 36 true) .empty .empty) .empty) (.node 132 (sourceLit (List.headD (raw_ints% [218762130092573638733429719076625]) 0) 35 true) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [2918187794716821414835052630625]) 0) 41 true) (.node 134 (sourceLit (List.headD (raw_ints% [97985567716721506223258264533125]) 0) 36 true) .empty .empty) (.node 136 (sourceLit (List.headD (raw_ints% [15515042858130144791761393029442875]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part023 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [144134526413114922878264961264375]) 0) 35 true) (.node 140 (sourceLit (List.headD (raw_ints% [614360320826427953682502329356625]) 0) 33 true) (.node 139 (sourceLit (List.headD (raw_ints% [158965503294902835756914302989375]) 0) 35 true) (.node 138 (sourceLit (List.headD (raw_ints% [7235388969348004413674591833158375]) 0) 35 false) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [148666357088123855561358334031475]) 0) 35 true) .empty .empty)) (.node 144 (sourceLit (List.headD (raw_ints% [1088462853877734252984149714255625]) 0) 32 true) (.node 143 (sourceLit (List.headD (raw_ints% [139945347890766144299461092986925]) 0) 35 true) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [132437652566710588127301359248875]) 0) 35 true) .empty .empty)))

#time def treeT_J014_part024 : IntSourceTree :=
  (.node 137 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 42 true) treeT_J014_part022 treeT_J014_part023)

#time def treeT_J014_part025 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [114957932171638498453163227747095]) 0) 35 true) (.node 149 (sourceLit (List.headD (raw_ints% [120106633819922825039850154901625]) 0) 35 true) (.node 148 (sourceLit (List.headD (raw_ints% [491640059542907256698550818009025]) 0) 33 true) (.node 147 (sourceLit (List.headD (raw_ints% [125886845058793731592080604605675]) 0) 35 true) .empty .empty) .empty) (.node 150 (sourceLit (List.headD (raw_ints% [29365156628066471498079774455475]) 0) 37 true) .empty .empty)) (.node 153 (sourceLit (List.headD (raw_ints% [110334485265909747613408696243185]) 0) 35 true) (.node 152 (sourceLit (List.headD (raw_ints% [1801379047114684243987215205045275]) 0) 31 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [865545075422963642369941183780875]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part026 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [197739027310712571336586493649375]) 0) 34 true) (.node 157 (sourceLit (List.headD (raw_ints% [204698873732260010971893193235925]) 0) 34 true) (.node 156 (sourceLit (List.headD (raw_ints% [833663368001190843879321666502395]) 0) 32 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [201143680805497564179858802900365]) 0) 34 true) .empty .empty)) (.node 169 (sourceLit (List.headD (raw_ints% [1700043409789796006382650936507775]) 0) 33 true) (.node 168 (sourceLit (List.headD (raw_ints% [974001777723950145391406921331375]) 0) 34 true) .empty .empty) (.node 170 (sourceLit (List.headD (raw_ints% [380490658923704282862103690627275]) 0) 35 true) .empty .empty)))

#time def treeT_J014_part027 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [212307031032762282686545382831925]) 0) 34 true) treeT_J014_part025 treeT_J014_part026)

#time def treeT_J014_part028 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [516222410180283664083017981914725]) 0) 33 true) treeT_J014_part024 treeT_J014_part027)

#time def treeT_J014_part029 : IntSourceTree :=
  (.node 128 (sourceLit (List.headD (raw_ints% [1200738461092498422453356311389075]) 0) 33 true) treeT_J014_part021 treeT_J014_part028)

#time def treeT_J014_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [185825319940989753216213613266675]) 0) 33 true) treeT_J014_part014 treeT_J014_part029)

#time def treeT_J014_part031 : IntSourceTree :=
  (.node 176 (sourceLit (List.headD (raw_ints% [62586545291397240461697658183875]) 0) 37 true) (.node 174 (sourceLit (List.headD (raw_ints% [139741557949831036003787892484575]) 0) 36 true) (.node 173 (sourceLit (List.headD (raw_ints% [148912886407266191392244181244125]) 0) 36 true) (.node 172 (sourceLit (List.headD (raw_ints% [319761419656186347466784353878825]) 0) 35 true) .empty .empty) .empty) (.node 175 (sourceLit (List.headD (raw_ints% [10578779953184556824164474055542875]) 0) 31 false) .empty .empty)) (.node 178 (sourceLit (List.headD (raw_ints% [912181075471742201217834427310625]) 0) 33 true) (.node 177 (sourceLit (List.headD (raw_ints% [90711178800422144355464538857311125]) 0) 32 true) .empty .empty) (.node 179 (sourceLit (List.headD (raw_ints% [233309001377924379056387043362800125]) 0) 31 false) .empty .empty)))

#time def treeT_J014_part032 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [89049204522974096106536550795075]) 0) 36 true) (.node 183 (sourceLit (List.headD (raw_ints% [6059629522088404285796246842743375]) 0) 30 true) (.node 182 (sourceLit (List.headD (raw_ints% [782896067951441312930060881349325]) 0) 33 true) (.node 181 (sourceLit (List.headD (raw_ints% [1621338513344100057538379351878875]) 0) 32 true) .empty .empty) .empty) (.node 184 (sourceLit (List.headD (raw_ints% [734036944615384080344620174789275]) 0) 33 true) .empty .empty)) (.node 187 (sourceLit (List.headD (raw_ints% [2694475121068964839242806501807475]) 0) 31 true) (.node 186 (sourceLit (List.headD (raw_ints% [692313308720243177833398568168575]) 0) 33 true) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [656159683258718899695092488721625]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part033 : IntSourceTree :=
  (.node 180 (sourceLit (List.headD (raw_ints% [841146591751583281301925406894275]) 0) 33 true) treeT_J014_part031 treeT_J014_part032)

#time def treeT_J014_part034 : IntSourceTree :=
  (.node 194 (sourceLit (List.headD (raw_ints% [1142497178509975809817301750880135]) 0) 32 true) (.node 192 (sourceLit (List.headD (raw_ints% [596357598163334025070815427945665]) 0) 33 true) (.node 191 (sourceLit (List.headD (raw_ints% [9759936534248018154396068966582325]) 0) 29 true) (.node 190 (sourceLit (List.headD (raw_ints% [624451519244173495941933934824855]) 0) 33 true) .empty .empty) .empty) (.node 193 (sourceLit (List.headD (raw_ints% [1166926386985781642233143622967475]) 0) 32 true) .empty .empty)) (.node 196 (sourceLit (List.headD (raw_ints% [1097276327171727077272176622725525]) 0) 32 true) (.node 195 (sourceLit (List.headD (raw_ints% [4477256256043152050527399882245705]) 0) 30 true) .empty .empty) (.node 197 (sourceLit (List.headD (raw_ints% [2152588499055592846484082805212345]) 0) 31 true) .empty .empty)))

#time def treeT_J014_part035 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [948927047951836672271216770231125]) 0) 34 true) (.node 210 (sourceLit (List.headD (raw_ints% [599348332976568064398023026587075]) 0) 35 true) (.node 209 (sourceLit (List.headD (raw_ints% [701685637911824426730720012722625]) 0) 35 true) (.node 199 (sourceLit (List.headD (raw_ints% [8297475657138406710721056600792135]) 0) 29 true) .empty .empty) .empty) (.node 211 (sourceLit (List.headD (raw_ints% [263878358705108557919365203064575]) 0) 36 true) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [199840205097810876561230097955125]) 0) 36 true) (.node 213 (sourceLit (List.headD (raw_ints% [216503139147598960924571717244975]) 0) 36 true) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [93050553234361893366427050394575]) 0) 37 true) .empty .empty)))

#time def treeT_J014_part036 : IntSourceTree :=
  (.node 198 (sourceLit (List.headD (raw_ints% [1056287615295665191885758945321975]) 0) 32 true) treeT_J014_part034 treeT_J014_part035)

#time def treeT_J014_part037 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [1279614943859607294785329358900025]) 0) 32 true) treeT_J014_part033 treeT_J014_part036)

#time def treeT_J014_part038 : IntSourceTree :=
  (.node 221 (sourceLit (List.headD (raw_ints% [543813877575335570179208738831325]) 0) 34 true) (.node 219 (sourceLit (List.headD (raw_ints% [594250068881936529704005821331875]) 0) 34 true) (.node 218 (sourceLit (List.headD (raw_ints% [119652734677814162010162906189944625]) 0) 33 true) (.node 217 (sourceLit (List.headD (raw_ints% [41163613716064339722202683577875]) 0) 38 true) .empty .empty) .empty) (.node 220 (sourceLit (List.headD (raw_ints% [234537722019577234963752048021513375]) 0) 32 false) .empty .empty)) (.node 223 (sourceLit (List.headD (raw_ints% [503005372169909024331138695375475]) 0) 34 true) (.node 222 (sourceLit (List.headD (raw_ints% [1044800407691640366025319506821375]) 0) 33 true) .empty .empty) (.node 224 (sourceLit (List.headD (raw_ints% [3882703814332935779827947414232125]) 0) 31 true) .empty .empty)))

#time def treeT_J014_part039 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [809772437810543750816052967612425]) 0) 33 true) (.node 228 (sourceLit (List.headD (raw_ints% [1711195001983150325845704865789425]) 0) 32 true) (.node 227 (sourceLit (List.headD (raw_ints% [440539618602655714649237358957225]) 0) 34 true) (.node 226 (sourceLit (List.headD (raw_ints% [908564862187301873621566830806475]) 0) 33 true) .empty .empty) .empty) (.node 229 (sourceLit (List.headD (raw_ints% [415946415618873249615392178918375]) 0) 34 true) .empty .empty)) (.node 232 (sourceLit (List.headD (raw_ints% [6157178440018649666421638556491775]) 0) 30 true) (.node 231 (sourceLit (List.headD (raw_ints% [394535654900896499035607479330665]) 0) 34 true) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [375688627631514529843998035459295]) 0) 34 true) .empty .empty)))

#time def treeT_J014_part040 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [469161639481962904090017456291525]) 0) 34 true) treeT_J014_part038 treeT_J014_part039)

#time def treeT_J014_part041 : IntSourceTree :=
  (.node 239 (sourceLit (List.headD (raw_ints% [660809560674240049212585958023225]) 0) 33 true) (.node 237 (sourceLit (List.headD (raw_ints% [687878579707207055328390236253675]) 0) 33 true) (.node 236 (sourceLit (List.headD (raw_ints% [2809929520040770362768756549240915]) 0) 31 true) (.node 235 (sourceLit (List.headD (raw_ints% [717883116444451244444210985216285]) 0) 33 true) .empty .empty) .empty) (.node 238 (sourceLit (List.headD (raw_ints% [1348013775833602589764647593610885]) 0) 32 true) .empty .empty)) (.node 251 (sourceLit (List.headD (raw_ints% [3408335355675560565446108004312225]) 0) 33 true) (.node 250 (sourceLit (List.headD (raw_ints% [1022880616899944570599336334817975]) 0) 35 true) .empty .empty) (.node 252 (sourceLit (List.headD (raw_ints% [735752015164247884210676458379475]) 0) 35 true) .empty .empty)))

#time def treeT_J014_part042 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [173928910139311837170839059086168375]) 0) 32 false) (.node 255 (sourceLit (List.headD (raw_ints% [23368553079444452924083200324670875]) 0) 31 true) (.node 254 (sourceLit (List.headD (raw_ints% [293264720345366885845355542005375]) 0) 36 true) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [123514561177326546271156442605275]) 0) 37 true) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [1190530878800437675137690292882357125]) 0) 31 true) (.node 258 (sourceLit (List.headD (raw_ints% [1722290202356375541003137321673375]) 0) 33 true) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [1535853683776162837514097878433225]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part043 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [651101275137304289486728407742875]) 0) 35 true) treeT_J014_part041 treeT_J014_part042)

#time def treeT_J014_part044 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [1468307698548599642096346062154075]) 0) 32 true) treeT_J014_part040 treeT_J014_part043)

#time def treeT_J014_part045 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [41608865669444846407687260114428625]) 0) 32 false) treeT_J014_part037 treeT_J014_part044)

#time def treeT_J014_part046 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [1184333249207608438526671256997525]) 0) 33 true) (.node 264 (sourceLit (List.headD (raw_ints% [1277984544064252016979934606712625]) 0) 33 true) (.node 263 (sourceLit (List.headD (raw_ints% [10657177000977841570608865266398625]) 0) 30 true) (.node 262 (sourceLit (List.headD (raw_ints% [1392359442349900967786774073975975]) 0) 33 true) .empty .empty) .empty) (.node 265 (sourceLit (List.headD (raw_ints% [2457916541965350242123362601510925]) 0) 32 true) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [1105998791151903958901856947107275]) 0) 33 true) (.node 267 (sourceLit (List.headD (raw_ints% [4574043776429450149729728144644325]) 0) 31 true) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [2142775060106693356906080372678825]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part047 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [7269205332345645086243368614986895]) 0) 30 true) (.node 273 (sourceLit (List.headD (raw_ints% [3823325666047086381955351310556825]) 0) 31 true) (.node 272 (sourceLit (List.headD (raw_ints% [981785021440251971071614489376995]) 0) 33 true) (.node 271 (sourceLit (List.headD (raw_ints% [16152781475689381871717625997015275]) 0) 29 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [1863011842542140428934682532794225]) 0) 32 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [3467270541025947879053430293269485]) 0) 31 true) (.node 276 (sourceLit (List.headD (raw_ints% [1774256138606077900504667318139615]) 0) 32 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [1695226703533163029427801999692725]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part048 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [1039334143231319502519634780848645]) 0) 33 true) treeT_J014_part046 treeT_J014_part047)

#time def treeT_J014_part049 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [12513385444437812029933030725675]) 0) 41 true) (.node 293 (sourceLit (List.headD (raw_ints% [129812219004162230821526185283625]) 0) 38 true) (.node 292 (sourceLit (List.headD (raw_ints% [614852076930930973293722808520275]) 0) 36 true) (.node 291 (sourceLit (List.headD (raw_ints% [94875282274354501584996391469175]) 0) 39 true) .empty .empty) .empty) (.node 294 (sourceLit (List.headD (raw_ints% [225630535019746706462749154893875]) 0) 37 true) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [10293868432657775818619219878425]) 0) 41 true) (.node 296 (sourceLit (List.headD (raw_ints% [16244354687222324832942615109774875]) 0) 34 true) .empty .empty) (.node 298 (sourceLit (List.headD (raw_ints% [36697705602140749897625245659514125]) 0) 36 false) .empty .empty)))

#time def treeT_J014_part050 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [1693618296661226447695229463041625]) 0) 33 true) (.node 302 (sourceLit (List.headD (raw_ints% [58967697870023776293883474362715875]) 0) 36 false) (.node 301 (sourceLit (List.headD (raw_ints% [248009951550206816833722284900475]) 0) 36 true) (.node 300 (sourceLit (List.headD (raw_ints% [356267150205003727525360585225967625]) 0) 34 true) .empty .empty) .empty) (.node 303 (sourceLit (List.headD (raw_ints% [222338517544997985863908844650125]) 0) 36 true) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [774675839889024184250897885352225]) 0) 34 true) (.node 305 (sourceLit (List.headD (raw_ints% [202205726145572278222479287605275]) 0) 36 true) .empty .empty) (.node 307 (sourceLit (List.headD (raw_ints% [185948407651238180969358474510075]) 0) 36 true) .empty .empty)))

#time def treeT_J014_part051 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [282010033368609752824782875085375]) 0) 36 true) treeT_J014_part049 treeT_J014_part050)

#time def treeT_J014_part052 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [13270744756199234725513304896982025]) 0) 29 true) treeT_J014_part048 treeT_J014_part051)

#time def treeT_J014_part053 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [151524098452184360306904113479425]) 0) 36 true) (.node 311 (sourceLit (List.headD (raw_ints% [161199622082605750871006825379495]) 0) 36 true) (.node 310 (sourceLit (List.headD (raw_ints% [41656331946754675190313356408325]) 0) 38 true) (.node 309 (sourceLit (List.headD (raw_ints% [172513093883257677321616192047225]) 0) 36 true) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [2498900758917683051323996860130875]) 0) 32 true) .empty .empty)) (.node 315 (sourceLit (List.headD (raw_ints% [286282181524422296122617886894485]) 0) 35 true) (.node 314 (sourceLit (List.headD (raw_ints% [1177508983749243369929502624201375]) 0) 33 true) .empty .empty) (.node 316 (sourceLit (List.headD (raw_ints% [1114818953076218680868653016436495]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part054 : IntSourceTree :=
  (.node 334 (sourceLit (List.headD (raw_ints% [745233031687930960726853940263625]) 0) 36 true) (.node 332 (sourceLit (List.headD (raw_ints% [2300257017615096166509208068634125]) 0) 35 true) (.node 319 (sourceLit (List.headD (raw_ints% [258604285714730745053804010417375]) 0) 35 true) (.node 318 (sourceLit (List.headD (raw_ints% [264907095649043161161097837457325]) 0) 35 true) .empty .empty) .empty) (.node 333 (sourceLit (List.headD (raw_ints% [1808307032586419603688162826338225]) 0) 35 true) .empty .empty)) (.node 336 (sourceLit (List.headD (raw_ints% [276913773044683438686700540616325]) 0) 37 true) (.node 335 (sourceLit (List.headD (raw_ints% [5512155403083125503148691501745125]) 0) 31 true) .empty .empty) (.node 337 (sourceLit (List.headD (raw_ints% [303883747637090435834379979964367375]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part055 : IntSourceTree :=
  (.node 317 (sourceLit (List.headD (raw_ints% [271594389724717711294069270471485]) 0) 35 true) treeT_J014_part053 treeT_J014_part054)

#time def treeT_J014_part056 : IntSourceTree :=
  (.node 343 (sourceLit (List.headD (raw_ints% [7558522504364021207187693583694030625]) 0) 30 false) (.node 341 (sourceLit (List.headD (raw_ints% [3320833984192528390187927157202646625]) 0) 32 true) (.node 340 (sourceLit (List.headD (raw_ints% [2976306850121593207682428122932775]) 0) 33 true) (.node 339 (sourceLit (List.headD (raw_ints% [3539184037337445668585706015091261125]) 0) 31 false) .empty .empty) .empty) (.node 342 (sourceLit (List.headD (raw_ints% [2575799782453408101552782484431625]) 0) 33 true) .empty .empty)) (.node 345 (sourceLit (List.headD (raw_ints% [4316556644679555548657555250655575]) 0) 32 true) (.node 344 (sourceLit (List.headD (raw_ints% [2279431736655715756842606907689375]) 0) 33 true) .empty .empty) (.node 346 (sourceLit (List.headD (raw_ints% [2050958369121548013032997344686875]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part057 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [26503302437787405523163250965109525]) 0) 29 true) (.node 349 (sourceLit (List.headD (raw_ints% [3582922488785906290861966185030975]) 0) 32 true) (.node 348 (sourceLit (List.headD (raw_ints% [1869175731267906936607878645053925]) 0) 33 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [1720875358900803334626224291906955]) 0) 33 true) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [6172277369623645823340636129966675]) 0) 31 true) (.node 352 (sourceLit (List.headD (raw_ints% [1597408931881440042864494716694925]) 0) 33 true) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [2985759307927759100886249098547375]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part058 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [7820769661794936798284638020991275]) 0) 31 true) treeT_J014_part056 treeT_J014_part057)

#time def treeT_J014_part059 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [3548170435164405678129903256080225]) 0) 33 true) treeT_J014_part055 treeT_J014_part058)

#time def treeT_J014_part060 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [715712193611574955971005819713725]) 0) 34 true) treeT_J014_part052 treeT_J014_part059)

#time def treeT_J014_part061 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [470696782552498569985042475394905625]) 0) 32 false) treeT_J014_part045 treeT_J014_part060)

#time def treeT_J014_part062 : IntSourceTree :=
  (.node 171 (sourceLit (List.headD (raw_ints% [1386451308136983949738076208384375]) 0) 33 true) treeT_J014_part030 treeT_J014_part061)

#time def treeT_J014_part063 : IntSourceTree :=
  (.node 373 (sourceLit (List.headD (raw_ints% [1781008141598447243223103327499625]) 0) 36 true) (.node 358 (sourceLit (List.headD (raw_ints% [2650283532062320351277306327851035]) 0) 32 true) (.node 357 (sourceLit (List.headD (raw_ints% [5451281083583801567895793838222475]) 0) 31 true) (.node 356 (sourceLit (List.headD (raw_ints% [2806258765784678837457218872172145]) 0) 32 true) .empty .empty) .empty) (.node 359 (sourceLit (List.headD (raw_ints% [20637363486878289903107218297555575]) 0) 29 true) .empty .empty)) (.node 375 (sourceLit (List.headD (raw_ints% [545018864576925968247925448652825]) 0) 37 true) (.node 374 (sourceLit (List.headD (raw_ints% [1357045962546926190762664516550475]) 0) 36 true) .empty .empty) (.node 376 (sourceLit (List.headD (raw_ints% [59465263345806173828621768937354375]) 0) 32 false) .empty .empty)))

#time def treeT_J014_part064 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [3792575567152718600538994952104373625]) 0) 33 true) (.node 380 (sourceLit (List.headD (raw_ints% [4964252638157460578687148355995131625]) 0) 32 false) (.node 379 (sourceLit (List.headD (raw_ints% [2420130301689966666830771755738725]) 0) 34 true) (.node 378 (sourceLit (List.headD (raw_ints% [597465392454216435015381945240480375]) 0) 33 true) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [1984267043920765940347538983330875]) 0) 34 true) .empty .empty)) (.node 384 (sourceLit (List.headD (raw_ints% [7565296977550666112978474501546197125]) 0) 31 false) (.node 383 (sourceLit (List.headD (raw_ints% [1686445712273416158097147105831125]) 0) 34 true) .empty .empty) (.node 385 (sourceLit (List.headD (raw_ints% [1470608832073426643952689757268275]) 0) 34 true) .empty .empty)))

#time def treeT_J014_part065 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [194562825583421232137746781588925]) 0) 38 true) treeT_J014_part063 treeT_J014_part064)

#time def treeT_J014_part066 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [1076076870570380331142196990388975]) 0) 34 true) (.node 389 (sourceLit (List.headD (raw_ints% [1179123355734876227321413876865025]) 0) 34 true) (.node 388 (sourceLit (List.headD (raw_ints% [4957920887348636974400614742136375]) 0) 32 true) (.node 387 (sourceLit (List.headD (raw_ints% [1307164738516595289155563446646575]) 0) 34 true) .empty .empty) .empty) (.node 390 (sourceLit (List.headD (raw_ints% [2249919866489756684771938779964575]) 0) 33 true) .empty .empty)) (.node 393 (sourceLit (List.headD (raw_ints% [991312538072702601636878262777225]) 0) 34 true) (.node 392 (sourceLit (List.headD (raw_ints% [16507699402116673317867263524586025]) 0) 30 true) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [3817259402125159083481630881563925]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part067 : IntSourceTree :=
  (.node 414 (sourceLit (List.headD (raw_ints% [2816783251508963525719352714735625]) 0) 36 true) (.node 398 (sourceLit (List.headD (raw_ints% [3332024318391456278607011138563875]) 0) 32 true) (.node 397 (sourceLit (List.headD (raw_ints% [1719881206885807992280941790286205]) 0) 33 true) (.node 396 (sourceLit (List.headD (raw_ints% [7111662595337374109154061306489125]) 0) 31 true) .empty .empty) .empty) (.node 399 (sourceLit (List.headD (raw_ints% [1615866389203397371062090286181535]) 0) 33 true) .empty .empty)) (.node 416 (sourceLit (List.headD (raw_ints% [813123956109168497809150356689325]) 0) 37 true) (.node 415 (sourceLit (List.headD (raw_ints% [81338786199920150705661837557485275]) 0) 31 true) .empty .empty) (.node 417 (sourceLit (List.headD (raw_ints% [422814274328702783491623517839076125]) 0) 32 false) .empty .empty)))

#time def treeT_J014_part068 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [1840630581830069916395777550969435]) 0) 33 true) treeT_J014_part066 treeT_J014_part067)

#time def treeT_J014_part069 : IntSourceTree :=
  (.node 386 (sourceLit (List.headD (raw_ints% [2767204964901507180155759479951125]) 0) 33 true) treeT_J014_part065 treeT_J014_part068)

#time def treeT_J014_part070 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [68239731578807518815811612817364008625]) 0) 30 true) (.node 421 (sourceLit (List.headD (raw_ints% [13249339260507449547562223869192909875]) 0) 32 false) (.node 420 (sourceLit (List.headD (raw_ints% [6704214356638273459640658900022125]) 0) 33 true) (.node 419 (sourceLit (List.headD (raw_ints% [8318907176971177148708761577015104125]) 0) 31 true) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [5361268393229655659837373448891875]) 0) 33 true) .empty .empty)) (.node 425 (sourceLit (List.headD (raw_ints% [1892403383548836417131783014199213175]) 0) 34 false) (.node 424 (sourceLit (List.headD (raw_ints% [4466351112437948875545981515635125]) 0) 33 true) .empty .empty) (.node 426 (sourceLit (List.headD (raw_ints% [3831476959172158562777761684386225]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part071 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [2706898550400081281704293244860975]) 0) 33 true) (.node 430 (sourceLit (List.headD (raw_ints% [2995618064038701574659431215553145]) 0) 33 true) (.node 429 (sourceLit (List.headD (raw_ints% [6332919285911367657939263299241775]) 0) 32 true) (.node 428 (sourceLit (List.headD (raw_ints% [3359483222798474220014375141532375]) 0) 33 true) .empty .empty) .empty) (.node 431 (sourceLit (List.headD (raw_ints% [45494133289884808389538789993756875]) 0) 29 true) .empty .empty)) (.node 434 (sourceLit (List.headD (raw_ints% [4944740996653861712208777003670425]) 0) 32 true) (.node 433 (sourceLit (List.headD (raw_ints% [5167711016246513747263313697309675]) 0) 32 true) .empty .empty) (.node 435 (sourceLit (List.headD (raw_ints% [18967136809359023835224373680276295]) 0) 30 true) .empty .empty)))

#time def treeT_J014_part072 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [14316870057417120642961437818617725]) 0) 31 true) treeT_J014_part070 treeT_J014_part071)

#time def treeT_J014_part073 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [70402024772863162267141803247419825]) 0) 33 true) (.node 439 (sourceLit (List.headD (raw_ints% [32675025607385010554604959919466425]) 0) 29 true) (.node 438 (sourceLit (List.headD (raw_ints% [4229241295480911617846460833293785]) 0) 32 true) (.node 437 (sourceLit (List.headD (raw_ints% [8772044107090946650412328774755775]) 0) 31 true) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [141985274183252347341964204130175]) 0) 41 true) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [255069916695729804626751365769889125]) 0) 35 false) (.node 457 (sourceLit (List.headD (raw_ints% [38660070657859204104462723443775]) 0) 42 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [3241860050242293255927559504936125]) 0) 35 true) .empty .empty)))

#time def treeT_J014_part074 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [37902514278179092464395043659455102875]) 0) 32 true) (.node 462 (sourceLit (List.headD (raw_ints% [4260478706915042037025304705324320875]) 0) 35 false) (.node 461 (sourceLit (List.headD (raw_ints% [2359973656358753759646559958345625]) 0) 35 true) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [1837411340478119750870113171530375]) 0) 35 true) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [7572380739160247175707287816276803825]) 0) 33 false) (.node 465 (sourceLit (List.headD (raw_ints% [1497871140182261115796645879183425]) 0) 35 true) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [1262156110327781636811099118869825]) 0) 35 true) .empty .empty)))

#time def treeT_J014_part075 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [6641579907564318863697954966505117875]) 0) 33 true) treeT_J014_part073 treeT_J014_part074)

#time def treeT_J014_part076 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [4556263561535600828125891331705595]) 0) 32 true) treeT_J014_part072 treeT_J014_part075)

#time def treeT_J014_part077 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [8903850402174553178685890765610975]) 0) 33 true) treeT_J014_part069 treeT_J014_part076)

#time def treeT_J014_part078 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [857793006163689340033707491041875]) 0) 35 true) (.node 471 (sourceLit (List.headD (raw_ints% [959770596734160621758617112582085]) 0) 35 true) (.node 470 (sourceLit (List.headD (raw_ints% [255187463713850685822957782454825]) 0) 37 true) (.node 469 (sourceLit (List.headD (raw_ints% [1090179933531798996346480632333675]) 0) 35 true) .empty .empty) .empty) (.node 472 (sourceLit (List.headD (raw_ints% [14493216943884067535835763234585425]) 0) 31 true) .empty .empty)) (.node 475 (sourceLit (List.headD (raw_ints% [1552055207411895897906499726350495]) 0) 34 true) (.node 474 (sourceLit (List.headD (raw_ints% [6518162630367868411044996513055425]) 0) 32 true) .empty .empty) (.node 476 (sourceLit (List.headD (raw_ints% [5927737107010824863035156186893585]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part079 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [30684061951473271824283938040814625]) 0) 33 true) (.node 496 (sourceLit (List.headD (raw_ints% [3730404817754906617133704175476275]) 0) 37 true) (.node 479 (sourceLit (List.headD (raw_ints% [1306687453138757123392185273556125]) 0) 34 true) (.node 478 (sourceLit (List.headD (raw_ints% [1360004947174872592951329409047975]) 0) 34 true) .empty .empty) .empty) (.node 497 (sourceLit (List.headD (raw_ints% [704422373420155432560190730828755425]) 0) 32 true) .empty .empty)) (.node 500 (sourceLit (List.headD (raw_ints% [19230666045300072587779817139466875]) 0) 33 true) (.node 499 (sourceLit (List.headD (raw_ints% [16481144511234530896764805281651556125]) 0) 31 false) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [39815658890764725002354043735213381375]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part080 : IntSourceTree :=
  (.node 477 (sourceLit (List.headD (raw_ints% [1418191177324896417922474770709695]) 0) 34 true) treeT_J014_part078 treeT_J014_part079)

#time def treeT_J014_part081 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [60593362783339394526301263968033048325]) 0) 31 false) (.node 505 (sourceLit (List.headD (raw_ints% [41687321045276765298658609687853529225]) 0) 33 true) (.node 504 (sourceLit (List.headD (raw_ints% [10232939611387009131414923856607875]) 0) 33 true) (.node 503 (sourceLit (List.headD (raw_ints% [340910368821370209185431113958120544625]) 0) 30 false) .empty .empty) .empty) (.node 506 (sourceLit (List.headD (raw_ints% [8151492162285930363595405349081175]) 0) 33 true) .empty .empty)) (.node 509 (sourceLit (List.headD (raw_ints% [12384979054225599679182382853720925]) 0) 32 true) (.node 508 (sourceLit (List.headD (raw_ints% [6737765659823778874474417809426225]) 0) 33 true) .empty .empty) (.node 510 (sourceLit (List.headD (raw_ints% [5725821404215690396112413843116255]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part082 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [7860178097759566355126106479098365]) 0) 32 true) (.node 514 (sourceLit (List.headD (raw_ints% [8779947101965167728330542852999575]) 0) 32 true) (.node 513 (sourceLit (List.headD (raw_ints% [4662752963818776894286224768637875]) 0) 33 true) (.node 512 (sourceLit (List.headD (raw_ints% [4971266223473203692364643655795705]) 0) 33 true) .empty .empty) .empty) (.node 515 (sourceLit (List.headD (raw_ints% [33178164233583923453135598424167105]) 0) 30 true) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [7116288123118259725533337332383775]) 0) 32 true) (.node 517 (sourceLit (List.headD (raw_ints% [14938904320952352801728295972818565]) 0) 31 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [54365291011806835394280122259603975]) 0) 29 true) .empty .empty)))

#time def treeT_J014_part083 : IntSourceTree :=
  (.node 511 (sourceLit (List.headD (raw_ints% [85161848131606742751815594623113525]) 0) 29 true) treeT_J014_part081 treeT_J014_part082)

#time def treeT_J014_part084 : IntSourceTree :=
  (.node 502 (sourceLit (List.headD (raw_ints% [13518520857640374417335106217873125]) 0) 33 true) treeT_J014_part080 treeT_J014_part083)

#time def treeT_J014_part085 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [9843698176684134915594879874812375]) 0) 34 true) (.node 541 (sourceLit (List.headD (raw_ints% [14510718732582565068486697222775625]) 0) 34 true) (.node 540 (sourceLit (List.headD (raw_ints% [29764304326363168624160715214661791875]) 0) 32 false) (.node 539 (sourceLit (List.headD (raw_ints% [24200341850988685312428819030942375]) 0) 34 true) .empty .empty) .empty) (.node 542 (sourceLit (List.headD (raw_ints% [56857573718424893150455262556510664875]) 0) 33 true) .empty .empty)) (.node 545 (sourceLit (List.headD (raw_ints% [7237197331022486899821632098241025]) 0) 34 true) (.node 544 (sourceLit (List.headD (raw_ints% [416715397377728394114221201277030750375]) 0) 31 false) .empty .empty) (.node 546 (sourceLit (List.headD (raw_ints% [90947022829713777773024507191983862275]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part086 : IntSourceTree :=
  (.node 552 (sourceLit (List.headD (raw_ints% [56175414243838607680144068153942675]) 0) 30 true) (.node 550 (sourceLit (List.headD (raw_ints% [8301979634803988706015058334443725]) 0) 33 true) (.node 549 (sourceLit (List.headD (raw_ints% [4557405792760180881781456544758875]) 0) 34 true) (.node 548 (sourceLit (List.headD (raw_ints% [60602721732509463009969824791109529675]) 0) 32 false) .empty .empty) .empty) (.node 551 (sourceLit (List.headD (raw_ints% [3806280210747369152595179617952085]) 0) 34 true) .empty .empty)) (.node 554 (sourceLit (List.headD (raw_ints% [12132849224907239166099902561496075]) 0) 32 true) (.node 553 (sourceLit (List.headD (raw_ints% [3255680211145825012297228673711955]) 0) 34 true) .empty .empty) (.node 555 (sourceLit (List.headD (raw_ints% [5675836687141375932517543400298585]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part087 : IntSourceTree :=
  (.node 547 (sourceLit (List.headD (raw_ints% [5627179941630367089973207111341525]) 0) 34 true) treeT_J014_part085 treeT_J014_part086)

#time def treeT_J014_part088 : IntSourceTree :=
  (.node 581 (sourceLit (List.headD (raw_ints% [99344267543491062250675474164536965125]) 0) 32 false) (.node 559 (sourceLit (List.headD (raw_ints% [4502913216840745478748966785271525]) 0) 33 true) (.node 558 (sourceLit (List.headD (raw_ints% [9498884532252862429922978336626665]) 0) 32 true) (.node 557 (sourceLit (List.headD (raw_ints% [5023795743109773519281156937678975]) 0) 33 true) .empty .empty) .empty) (.node 580 (sourceLit (List.headD (raw_ints% [77570701358654668661935458984302625]) 0) 33 true) .empty .empty)) (.node 583 (sourceLit (List.headD (raw_ints% [1250631548316168499592715314862291182625]) 0) 30 true) (.node 582 (sourceLit (List.headD (raw_ints% [44524354072689885856611682673229375]) 0) 33 true) .empty .empty) (.node 584 (sourceLit (List.headD (raw_ints% [29141853095349530530964595642641625]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [121217828444073151619618831965072780275]) 0) 32 false) (.node 587 (sourceLit (List.headD (raw_ints% [788169545421049616710497321503903946525]) 0) 31 true) (.node 586 (sourceLit (List.headD (raw_ints% [20797297161804017235691123043882925]) 0) 33 true) .empty .empty) (.node 588 (sourceLit (List.headD (raw_ints% [15770954106697689485418410635939875]) 0) 33 true) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [180501500182120895840666272079085675]) 0) 29 true) (.node 590 (sourceLit (List.headD (raw_ints% [12503801766825033131013412335919245]) 0) 33 true) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [10253854619516272918016074816012635]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part090 : IntSourceTree :=
  (.node 585 (sourceLit (List.headD (raw_ints% [500090039468281924711538420652737808825]) 0) 32 false) treeT_J014_part088 treeT_J014_part089)

#time def treeT_J014_part091 : IntSourceTree :=
  (.node 556 (sourceLit (List.headD (raw_ints% [21322690019562273727065286050379935]) 0) 31 true) treeT_J014_part087 treeT_J014_part090)

#time def treeT_J014_part092 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [1724702040203074651067196193908311925]) 0) 33 true) treeT_J014_part084 treeT_J014_part091)

#time def treeT_J014_part093 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [4679474585034241834280411538240675]) 0) 33 true) treeT_J014_part077 treeT_J014_part092)

#time def treeT_J014_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [12978894849320834351591290418332125]) 0) 32 true) (.node 596 (sourceLit (List.headD (raw_ints% [14843168650805937374944067122095975]) 0) 32 true) (.node 595 (sourceLit (List.headD (raw_ints% [63884629565673989875663622067801495]) 0) 30 true) (.node 594 (sourceLit (List.headD (raw_ints% [17265494587201432370047286536696065]) 0) 32 true) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [27706475718172194652402276127941305]) 0) 31 true) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [9762615078869747212570671045065476875]) 0) 37 false) (.node 599 (sourceLit (List.headD (raw_ints% [97616861504238963484487531126422665]) 0) 29 true) .empty .empty) (.node 623 (sourceLit (List.headD (raw_ints% [4335081987000718867627100349802125]) 0) 37 true) .empty .empty)))

#time def treeT_J014_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [1401693539242188575454619261397625]) 0) 37 true) (.node 627 (sourceLit (List.headD (raw_ints% [1896264652521706268214739491567675]) 0) 37 true) (.node 626 (sourceLit (List.headD (raw_ints% [147759265574498925621140731961180417775]) 0) 35 false) (.node 625 (sourceLit (List.headD (raw_ints% [2738081970540880453892870443050075]) 0) 37 true) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [106096533394194884965058393286876684525]) 0) 35 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [1087190194509707997302279089745895]) 0) 37 true) (.node 630 (sourceLit (List.headD (raw_ints% [1894158287870436806380075734740737875]) 0) 39 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [15540760742285286020065275490642875]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [208418368211737111713367064517415241625]) 0) 34 true) treeT_J014_part094 treeT_J014_part095)

#time def treeT_J014_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [1137974449119958263904956111957165]) 0) 36 true) (.node 636 (sourceLit (List.headD (raw_ints% [5320242443263964518574792002177695]) 0) 34 true) (.node 635 (sourceLit (List.headD (raw_ints% [1448707237507507054691217892049685]) 0) 36 true) (.node 634 (sourceLit (List.headD (raw_ints% [6347888290914065234224816629473775]) 0) 34 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [1227421613462020481957863773052125]) 0) 36 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [3749861008506823786010807102399053262625]) 0) 30 false) (.node 639 (sourceLit (List.headD (raw_ints% [1059497704060011109105290454132575]) 0) 36 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [109580770488673473233102615551026375]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part098 : IntSourceTree :=
  (.node 670 (sourceLit (List.headD (raw_ints% [32350391488925001283534404028804755]) 0) 33 true) (.node 668 (sourceLit (List.headD (raw_ints% [44909514773996911097453253094225725]) 0) 33 true) (.node 667 (sourceLit (List.headD (raw_ints% [5516466043805015236587000744261677315325]) 0) 31 false) (.node 666 (sourceLit (List.headD (raw_ints% [66821325895504157288880731133719475]) 0) 33 true) .empty .empty) .empty) (.node 669 (sourceLit (List.headD (raw_ints% [1818762362751191311060553124555099732675]) 0) 32 true) .empty .empty)) (.node 672 (sourceLit (List.headD (raw_ints% [24536231604794382995656856055856005]) 0) 33 true) (.node 671 (sourceLit (List.headD (raw_ints% [3879416675058836700362235771021110253675]) 0) 29 false) .empty .empty) (.node 673 (sourceLit (List.headD (raw_ints% [86801683549718788057523034845751825]) 0) 31 true) .empty .empty)))

#time def treeT_J014_part099 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [2167436985162178818418474936792059741825]) 0) 32 true) treeT_J014_part097 treeT_J014_part098)

#time def treeT_J014_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [874771801046305988214855767787585]) 0) 37 true) treeT_J014_part096 treeT_J014_part099)

#time def treeT_J014_part101 : IntSourceTree :=
  (.node 679 (sourceLit (List.headD (raw_ints% [193704597470470352075181233534611575]) 0) 29 true) (.node 677 (sourceLit (List.headD (raw_ints% [57417403374051237644794395906901815]) 0) 31 true) (.node 676 (sourceLit (List.headD (raw_ints% [31515462949434288375174905423493945]) 0) 32 true) (.node 675 (sourceLit (List.headD (raw_ints% [139247795743576097619530510075359305]) 0) 30 true) .empty .empty) .empty) (.node 678 (sourceLit (List.headD (raw_ints% [26298596781463821071060350319335875]) 0) 32 true) .empty .empty)) (.node 706 (sourceLit (List.headD (raw_ints% [2758474047460174520903037864636781412925]) 0) 33 true) (.node 705 (sourceLit (List.headD (raw_ints% [87676114724346429601959652006625775]) 0) 34 true) .empty .empty) (.node 707 (sourceLit (List.headD (raw_ints% [51651208675330507143162815201178075]) 0) 34 true) .empty .empty)))

#time def treeT_J014_part102 : IntSourceTree :=
  (.node 713 (sourceLit (List.headD (raw_ints% [17538057196423935089938009913555325]) 0) 34 true) (.node 711 (sourceLit (List.headD (raw_ints% [23652869932847337305116171310837595]) 0) 34 true) (.node 710 (sourceLit (List.headD (raw_ints% [1939988493174899266668877971578506956675]) 0) 33 true) (.node 709 (sourceLit (List.headD (raw_ints% [33695966460059402493816299003044725]) 0) 34 true) .empty .empty) .empty) (.node 712 (sourceLit (List.headD (raw_ints% [3879541001144774982650396293225035396675]) 0) 30 false) .empty .empty)) (.node 715 (sourceLit (List.headD (raw_ints% [27130242779702094438173739465311895]) 0) 33 true) (.node 714 (sourceLit (List.headD (raw_ints% [61410130386062527120623768327856725]) 0) 32 true) .empty .empty) (.node 716 (sourceLit (List.headD (raw_ints% [96685856197464381470932174057937745]) 0) 31 true) .empty .empty)))

#time def treeT_J014_part103 : IntSourceTree :=
  (.node 708 (sourceLit (List.headD (raw_ints% [6365238310958574316307467890556690791525]) 0) 32 false) treeT_J014_part101 treeT_J014_part102)

#time def treeT_J014_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [161695319927325117475198007710486575]) 0) 33 true) (.node 746 (sourceLit (List.headD (raw_ints% [283883133001881561118957876892783625]) 0) 33 true) (.node 719 (sourceLit (List.headD (raw_ints% [17822615148983732198218026686275275]) 0) 33 true) (.node 718 (sourceLit (List.headD (raw_ints% [39209812188131905422315098115587175]) 0) 32 true) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [27584258423486411403811303661355928618725]) 0) 31 true) .empty .empty)) (.node 750 (sourceLit (List.headD (raw_ints% [102433474351312608691730791983374145]) 0) 33 true) (.node 749 (sourceLit (List.headD (raw_ints% [14549238984668339943675488905668481315725]) 0) 32 false) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [65959048456655613233766330861533332867275]) 0) 29 true) .empty .empty)))

#time def treeT_J014_part105 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [77005508169374089377520052437753635]) 0) 32 true) (.node 754 (sourceLit (List.headD (raw_ints% [101584556891629329843800596706733225]) 0) 32 true) (.node 753 (sourceLit (List.headD (raw_ints% [969906950707081175359613454064970287125]) 0) 33 false) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [352033247344924119345459636547494495]) 0) 30 true) .empty .empty)) (.node 758 (sourceLit (List.headD (raw_ints% [60485763385488677006987630636971905]) 0) 32 true) (.node 757 (sourceLit (List.headD (raw_ints% [135954309020877525297069952208973675]) 0) 31 true) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [433652397539640134681860336314783225]) 0) 29 true) .empty .empty)))

#time def treeT_J014_part106 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [70075248126594966224807829187494375]) 0) 33 true) treeT_J014_part104 treeT_J014_part105)

#time def treeT_J014_part107 : IntSourceTree :=
  (.node 717 (sourceLit (List.headD (raw_ints% [21696090041738124519511995239076945]) 0) 33 true) treeT_J014_part103 treeT_J014_part106)

#time def treeT_J014_part108 : IntSourceTree :=
  (.node 674 (sourceLit (List.headD (raw_ints% [38719900679762150875703482601709375]) 0) 32 true) treeT_J014_part100 treeT_J014_part107)

#time def treeT_J014_part109 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [34919294728900194108208363577379184131975]) 0) 31 true) (.node 790 (sourceLit (List.headD (raw_ints% [1030576717365202450646522929827936767025]) 0) 37 false) (.node 789 (sourceLit (List.headD (raw_ints% [63999676733632857490690854353720925]) 0) 35 true) (.node 788 (sourceLit (List.headD (raw_ints% [16974748367222492860059385775956309705125]) 0) 33 true) .empty .empty) .empty) (.node 791 (sourceLit (List.headD (raw_ints% [39390302209232635693307310336268275]) 0) 35 true) .empty .empty)) (.node 794 (sourceLit (List.headD (raw_ints% [3879689212958710763965574440028209005225]) 0) 32 false) (.node 793 (sourceLit (List.headD (raw_ints% [26268595465085515567434909636969525]) 0) 35 true) .empty .empty) (.node 795 (sourceLit (List.headD (raw_ints% [37227157055963617702813428620710665]) 0) 34 true) .empty .empty)))

#time def treeT_J014_part110 : IntSourceTree :=
  (.node 829 (sourceLit (List.headD (raw_ints% [82448232453558311383913032009493720136225]) 0) 32 true) (.node 799 (sourceLit (List.headD (raw_ints% [21331574118252472404384801975348315]) 0) 34 true) (.node 798 (sourceLit (List.headD (raw_ints% [24186124208186404968688713523346625]) 0) 34 true) (.node 797 (sourceLit (List.headD (raw_ints% [27654709063817982429004028599338345]) 0) 34 true) .empty .empty) .empty) (.node 828 (sourceLit (List.headD (raw_ints% [767232377378879098427982239055935625]) 0) 33 true) .empty .empty)) (.node 831 (sourceLit (List.headD (raw_ints% [593614327747639267964786070933436957584075]) 0) 29 false) (.node 830 (sourceLit (List.headD (raw_ints% [409563939517750251233796042846393255]) 0) 33 true) .empty .empty) (.node 832 (sourceLit (List.headD (raw_ints% [245047169547266119321650653502651825]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part111 : IntSourceTree :=
  (.node 796 (sourceLit (List.headD (raw_ints% [127673695573729868937263731244778375]) 0) 32 true) treeT_J014_part109 treeT_J014_part110)

#time def treeT_J014_part112 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [160751909125055182425044598157734855]) 0) 32 true) (.node 836 (sourceLit (List.headD (raw_ints% [220811748278334852244987376527931685]) 0) 32 true) (.node 835 (sourceLit (List.headD (raw_ints% [31037865736917031035843940979862219536295]) 0) 30 false) (.node 834 (sourceLit (List.headD (raw_ints% [318712970549738919235157957484779175]) 0) 32 true) .empty .empty) .empty) (.node 837 (sourceLit (List.headD (raw_ints% [374740473274041950451984972770139825]) 0) 31 true) .empty .empty)) (.node 869 (sourceLit (List.headD (raw_ints% [639233023911613383446600530348493775]) 0) 34 true) (.node 839 (sourceLit (List.headD (raw_ints% [1114259551784289783314217329179400775]) 0) 29 true) .empty .empty) (.node 870 (sourceLit (List.headD (raw_ints% [98937459931401550594257398886740708408625]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part113 : IntSourceTree :=
  (.node 875 (sourceLit (List.headD (raw_ints% [244258656437811683829531100243357845]) 0) 33 true) (.node 873 (sourceLit (List.headD (raw_ints% [192509978617095088186780834228712775]) 0) 34 true) (.node 872 (sourceLit (List.headD (raw_ints% [663452917205439656181202798088195325848025]) 0) 30 false) .empty .empty) (.node 874 (sourceLit (List.headD (raw_ints% [77597906473587423681820755411046458417675]) 0) 32 true) .empty .empty)) (.node 877 (sourceLit (List.headD (raw_ints% [165502330150698887386979319329254995]) 0) 33 true) (.node 876 (sourceLit (List.headD (raw_ints% [31038121084308178495581815507324709093045]) 0) 31 false) .empty .empty) (.node 878 (sourceLit (List.headD (raw_ints% [277995976441296330577230118676753325]) 0) 32 true) .empty .empty)))

#time def treeT_J014_part114 : IntSourceTree :=
  (.node 871 (sourceLit (List.headD (raw_ints% [330783335099284979847181422173856705]) 0) 34 true) treeT_J014_part112 treeT_J014_part113)

#time def treeT_J014_part115 : IntSourceTree :=
  (.node 833 (sourceLit (List.headD (raw_ints% [36859108630314356458927590485509124706225]) 0) 32 true) treeT_J014_part111 treeT_J014_part114)

#time def treeT_J014_part116 : IntSourceTree :=
  (.node 914 (sourceLit (List.headD (raw_ints% [1221366858387021786259088716344923025]) 0) 32 true) (.node 912 (sourceLit (List.headD (raw_ints% [1078086170849873800067075035192774995]) 0) 33 true) (.node 911 (sourceLit (List.headD (raw_ints% [3759613045552488886981022835309139626660075]) 0) 29 true) (.node 910 (sourceLit (List.headD (raw_ints% [2147368156128703282552606078547581845]) 0) 33 true) .empty .empty) .empty) (.node 913 (sourceLit (List.headD (raw_ints% [737171134466068369099057979059213575260475]) 0) 31 false) .empty .empty)) (.node 916 (sourceLit (List.headD (raw_ints% [756222877472911883073137024445499695]) 0) 32 true) (.node 915 (sourceLit (List.headD (raw_ints% [651821117525616420490409984268233886877695]) 0) 30 true) .empty .empty) (.node 917 (sourceLit (List.headD (raw_ints% [62076616909089631033114082999622188325915]) 0) 31 false) .empty .empty)))

#time def treeT_J014_part117 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [407384520469827896390439367235130016839075]) 0) 33 false) (.node 952 (sourceLit (List.headD (raw_ints% [1105766490689482135790556408349333738127025]) 0) 32 true) (.node 951 (sourceLit (List.headD (raw_ints% [454146205257354575676356164093431285]) 0) 36 true) (.node 919 (sourceLit (List.headD (raw_ints% [3333676071276451505921464569648652425]) 0) 29 true) .empty .empty) .empty) (.node 953 (sourceLit (List.headD (raw_ints% [221394048058194677970073550241015555]) 0) 36 true) .empty .empty)) (.node 956 (sourceLit (List.headD (raw_ints% [170714809652481149746497949943889648992685]) 0) 33 true) (.node 955 (sourceLit (List.headD (raw_ints% [244277050487302525607389404025391295]) 0) 35 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [147680136830553248921539426279061175]) 0) 35 true) .empty .empty)))

#time def treeT_J014_part118 : IntSourceTree :=
  (.node 918 (sourceLit (List.headD (raw_ints% [501257411477740367122872679159285125]) 0) 32 true) treeT_J014_part116 treeT_J014_part117)

#time def treeT_J014_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [1427795094128938829005097682550739380267395]) 0) 31 true) (.node 995 (sourceLit (List.headD (raw_ints% [7169973445042862762737439860030314156302895]) 0) 30 false) (.node 994 (sourceLit (List.headD (raw_ints% [5863242679475207908783264891367574735]) 0) 32 true) (.node 959 (sourceLit (List.headD (raw_ints% [95792162647297532376649421238061725]) 0) 35 true) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [3152209930323928526645093439960761025]) 0) 32 true) .empty .empty)) (.node 999 (sourceLit (List.headD (raw_ints% [993233652157128433722620485140423489920265]) 0) 29 false) (.node 998 (sourceLit (List.headD (raw_ints% [1861624777811111615621758141305693675]) 0) 32 true) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [4886134477525997806353707275266009555]) 0) 33 true) .empty .empty)))

#time def treeT_J014_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [16392327979780062698769735661103277195]) 0) 32 true) (.node 1038 (sourceLit (List.headD (raw_ints% [1489871989034004901334542342780480245346635]) 0) 32 true) (.node 1037 (sourceLit (List.headD (raw_ints% [2561489383001715530958935734844516325]) 0) 33 true) .empty .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [1478456127221921486115160456353446775]) 0) 33 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [8384332754195750508213984798072371625]) 0) 32 true) (.node 1077 (sourceLit (List.headD (raw_ints% [17133460461434513552451961002162484884814665]) 0) 31 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [24831185476701206855075297969628107415466425]) 0) 29 true) .empty .empty)))

#time def treeT_J014_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [7852832683652787361723431659805872752273635]) 0) 31 false) treeT_J014_part119 treeT_J014_part120)

#time def treeT_J014_part122 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [7759611863133259041180582528717608134905]) 0) 35 false) treeT_J014_part118 treeT_J014_part121)

#time def treeT_J014_part123 : IntSourceTree :=
  (.node 879 (sourceLit (List.headD (raw_ints% [118088760888550237616274994207038225]) 0) 33 true) treeT_J014_part115 treeT_J014_part122)

#time def treeT_J014_part124 : IntSourceTree :=
  (.node 787 (sourceLit (List.headD (raw_ints% [116115962163275526987897530845802775]) 0) 35 true) treeT_J014_part108 treeT_J014_part123)

#time def treeT_J014_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [37524402388563500102999169079391175]) 0) 31 true) treeT_J014_part093 treeT_J014_part124)

#time def treeT_J014_part126 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [11570938407642248832628673372235105]) 0) 30 true) treeT_J014_part062 treeT_J014_part125)

#time def treeT_J014 : IntSourceTree := treeT_J014_part126

#time def treeT_J015_part000 : IntSourceTree :=
  (.node 8 (sourceLit (List.headD (raw_ints% [815828554652410196503538590783125]) 0) 31 true) (.node 6 (sourceLit (List.headD (raw_ints% [232790238550313966704066385626125]) 0) 33 true) (.node 5 (sourceLit (List.headD (raw_ints% [126262906753869571935002651044875]) 0) 34 true) (.node 4 (sourceLit (List.headD (raw_ints% [556689317072936537830300234399125]) 0) 32 true) .empty .empty) .empty) (.node 7 (sourceLit (List.headD (raw_ints% [108500060163045216894416766703125]) 0) 34 true) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [91712244222196574625591466899375]) 0) 34 true) (.node 9 (sourceLit (List.headD (raw_ints% [48231469013520573957185915709375]) 0) 35 true) .empty .empty) (.node 11 (sourceLit (List.headD (raw_ints% [43780307456268171887120018471475]) 0) 35 true) .empty .empty)))

#time def treeT_J015_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 33 true) (.node 15 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 37 true) (.node 14 (sourceLit (List.headD (raw_ints% [38829063480290882590334641473375]) 0) 35 true) (.node 13 (sourceLit (List.headD (raw_ints% [20152661594103225535390304637375]) 0) 36 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [14220218901479511109116840359154075]) 0) 31 false) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [132624398702683868752878406925625]) 0) 33 true) (.node 18 (sourceLit (List.headD (raw_ints% [272906095251943018611581202241875]) 0) 32 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [516263081129628162976896922546875]) 0) 31 true) .empty .empty)))

#time def treeT_J015_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [167778632385660073579987084774875]) 0) 33 true) treeT_J015_part000 treeT_J015_part001)

#time def treeT_J015_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [223919183525412879766579448095965]) 0) 32 true) (.node 24 (sourceLit (List.headD (raw_ints% [935894279368584774991727833233375]) 0) 30 true) (.node 23 (sourceLit (List.headD (raw_ints% [119727705652593138181135203917625]) 0) 33 true) (.node 22 (sourceLit (List.headD (raw_ints% [245282709925596798518906804086125]) 0) 32 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [114402178334518468414113149681625]) 0) 33 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [429807667801959544442537225308275]) 0) 31 true) (.node 27 (sourceLit (List.headD (raw_ints% [109646509348649052263294757294075]) 0) 33 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [105366076677952077776978294669025]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [189419316559800862790236927920975]) 0) 32 true) (.node 33 (sourceLit (List.headD (raw_ints% [195901244791700790581816951699325]) 0) 32 true) (.node 32 (sourceLit (List.headD (raw_ints% [1594866586497895639393976204018325]) 0) 29 true) (.node 31 (sourceLit (List.headD (raw_ints% [101487002937687763964658688152555]) 0) 33 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [385183211983043948389539577678725]) 0) 31 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [183451033568777256433263118889025]) 0) 32 true) (.node 36 (sourceLit (List.headD (raw_ints% [745500920817642759490294295626905]) 0) 30 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [361278301508009428510907587331775]) 0) 31 true) .empty .empty)))

#time def treeT_J015_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [206760683364521615268806844452475]) 0) 32 true) treeT_J015_part003 treeT_J015_part004)

#time def treeT_J015_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [125746694380025178371849107845675]) 0) 33 true) treeT_J015_part002 treeT_J015_part005)

#time def treeT_J015_part007 : IntSourceTree :=
  (.node 49 (sourceLit (List.headD (raw_ints% [815828554652410196503538590783125]) 0) 32 true) (.node 47 (sourceLit (List.headD (raw_ints% [232790238550313966704066385626125]) 0) 34 true) (.node 46 (sourceLit (List.headD (raw_ints% [126262906753869571935002651044875]) 0) 35 true) (.node 45 (sourceLit (List.headD (raw_ints% [556689317072936537830300234399125]) 0) 33 true) .empty .empty) .empty) (.node 48 (sourceLit (List.headD (raw_ints% [108500060163045216894416766703125]) 0) 35 true) .empty .empty)) (.node 51 (sourceLit (List.headD (raw_ints% [91712244222196574625591466899375]) 0) 35 true) (.node 50 (sourceLit (List.headD (raw_ints% [48231469013520573957185915709375]) 0) 36 true) .empty .empty) (.node 52 (sourceLit (List.headD (raw_ints% [43780307456268171887120018471475]) 0) 36 true) .empty .empty)))

#time def treeT_J015_part008 : IntSourceTree :=
  (.node 58 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 34 true) (.node 56 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 38 true) (.node 55 (sourceLit (List.headD (raw_ints% [38829063480290882590334641473375]) 0) 36 true) (.node 54 (sourceLit (List.headD (raw_ints% [20152661594103225535390304637375]) 0) 37 true) .empty .empty) .empty) (.node 57 (sourceLit (List.headD (raw_ints% [14220218901479511109116840359154075]) 0) 32 false) .empty .empty)) (.node 60 (sourceLit (List.headD (raw_ints% [132624398702683868752878406925625]) 0) 34 true) (.node 59 (sourceLit (List.headD (raw_ints% [272906095251943018611581202241875]) 0) 33 true) .empty .empty) (.node 61 (sourceLit (List.headD (raw_ints% [516263081129628162976896922546875]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part009 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [167778632385660073579987084774875]) 0) 34 true) treeT_J015_part007 treeT_J015_part008)

#time def treeT_J015_part010 : IntSourceTree :=
  (.node 67 (sourceLit (List.headD (raw_ints% [223919183525412879766579448095965]) 0) 33 true) (.node 65 (sourceLit (List.headD (raw_ints% [935894279368584774991727833233375]) 0) 31 true) (.node 64 (sourceLit (List.headD (raw_ints% [119727705652593138181135203917625]) 0) 34 true) (.node 63 (sourceLit (List.headD (raw_ints% [245282709925596798518906804086125]) 0) 33 true) .empty .empty) .empty) (.node 66 (sourceLit (List.headD (raw_ints% [114402178334518468414113149681625]) 0) 34 true) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [429807667801959544442537225308275]) 0) 32 true) (.node 68 (sourceLit (List.headD (raw_ints% [109646509348649052263294757294075]) 0) 34 true) .empty .empty) (.node 70 (sourceLit (List.headD (raw_ints% [105366076677952077776978294669025]) 0) 34 true) .empty .empty)))

#time def treeT_J015_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [385183211983043948389539577678725]) 0) 32 true) (.node 73 (sourceLit (List.headD (raw_ints% [1594866586497895639393976204018325]) 0) 30 true) (.node 72 (sourceLit (List.headD (raw_ints% [101487002937687763964658688152555]) 0) 34 true) .empty .empty) (.node 74 (sourceLit (List.headD (raw_ints% [195901244791700790581816951699325]) 0) 33 true) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [745500920817642759490294295626905]) 0) 31 true) (.node 76 (sourceLit (List.headD (raw_ints% [189419316559800862790236927920975]) 0) 33 true) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [183451033568777256433263118889025]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [206760683364521615268806844452475]) 0) 33 true) treeT_J015_part010 treeT_J015_part011)

#time def treeT_J015_part013 : IntSourceTree :=
  (.node 62 (sourceLit (List.headD (raw_ints% [125746694380025178371849107845675]) 0) 34 true) treeT_J015_part009 treeT_J015_part012)

#time def treeT_J015_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [177932660939551316101662833148675]) 0) 32 true) treeT_J015_part006 treeT_J015_part013)

#time def treeT_J015_part015 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [632404066208017047252355656984375]) 0) 33 true) (.node 88 (sourceLit (List.headD (raw_ints% [2908815262152613270761523579234875]) 0) 31 true) (.node 87 (sourceLit (List.headD (raw_ints% [396551566852433070845593837476375]) 0) 34 true) (.node 86 (sourceLit (List.headD (raw_ints% [880588395595559108956534083172125]) 0) 33 true) .empty .empty) .empty) (.node 89 (sourceLit (List.headD (raw_ints% [168768651312569859831647617696875]) 0) 35 true) .empty .empty)) (.node 92 (sourceLit (List.headD (raw_ints% [565919321391912523424744650420125]) 0) 33 true) (.node 91 (sourceLit (List.headD (raw_ints% [149145568597814123941623644366025]) 0) 35 true) .empty .empty) (.node 93 (sourceLit (List.headD (raw_ints% [67407953318433118238849732305575]) 0) 36 true) .empty .empty)))

#time def treeT_J015_part016 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [429727555149804775658864676481875]) 0) 33 true) (.node 97 (sourceLit (List.headD (raw_ints% [459254095646199059602923518116125]) 0) 33 true) (.node 96 (sourceLit (List.headD (raw_ints% [16705278964218127594898257413450075]) 0) 31 true) (.node 95 (sourceLit (List.headD (raw_ints% [30932790623998306997251557884625]) 0) 37 true) .empty .empty) .empty) (.node 98 (sourceLit (List.headD (raw_ints% [28713343898210965236845261920550025]) 0) 32 false) .empty .empty)) (.node 101 (sourceLit (List.headD (raw_ints% [404750900430710296639664519856825]) 0) 33 true) (.node 100 (sourceLit (List.headD (raw_ints% [1666985680885915985915752695388125]) 0) 31 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [787243452333659527434887041007625]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part017 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [32237392226342297747413110825375]) 0) 37 true) treeT_J015_part015 treeT_J015_part016)

#time def treeT_J015_part018 : IntSourceTree :=
  (.node 108 (sourceLit (List.headD (raw_ints% [1361545800401343493690098359459445]) 0) 31 true) (.node 106 (sourceLit (List.headD (raw_ints% [355987547921585947612574192568705]) 0) 33 true) (.node 105 (sourceLit (List.headD (raw_ints% [364508644275854084310427665988875]) 0) 33 true) (.node 104 (sourceLit (List.headD (raw_ints% [2988629079440964001310781032144625]) 0) 30 true) .empty .empty) .empty) (.node 107 (sourceLit (List.headD (raw_ints% [347962203989424821393157841432425]) 0) 33 true) .empty .empty)) (.node 110 (sourceLit (List.headD (raw_ints% [652854652239397473616267606164075]) 0) 32 true) (.node 109 (sourceLit (List.headD (raw_ints% [333219960716644131276200734507275]) 0) 33 true) .empty .empty) (.node 111 (sourceLit (List.headD (raw_ints% [319977303774120547143254490523545]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part019 : IntSourceTree :=
  (.node 117 (sourceLit (List.headD (raw_ints% [574226232670426194727684592794875]) 0) 32 true) (.node 115 (sourceLit (List.headD (raw_ints% [594185662607002299537030878876325]) 0) 32 true) (.node 114 (sourceLit (List.headD (raw_ints% [75605210907178230687777289146225]) 0) 35 true) (.node 113 (sourceLit (List.headD (raw_ints% [615994778709801321135452553521115]) 0) 32 true) .empty .empty) .empty) (.node 116 (sourceLit (List.headD (raw_ints% [2335964775046708827626022325802895]) 0) 30 true) .empty .empty)) (.node 119 (sourceLit (List.headD (raw_ints% [555871473335557709631389642407425]) 0) 32 true) (.node 118 (sourceLit (List.headD (raw_ints% [1129723540127276090469681003922035]) 0) 31 true) .empty .empty) (.node 127 (sourceLit (List.headD (raw_ints% [40487384815327821390779231096625]) 0) 38 true) .empty .empty)))

#time def treeT_J015_part020 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [5021475281166796049207842818460875]) 0) 29 true) treeT_J015_part018 treeT_J015_part019)

#time def treeT_J015_part021 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [383259071867507575306261227465075]) 0) 33 true) treeT_J015_part017 treeT_J015_part020)

#time def treeT_J015_part022 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [199070344503126224922378782822625]) 0) 35 true) (.node 131 (sourceLit (List.headD (raw_ints% [448979577763623898001172723185625]) 0) 34 true) (.node 130 (sourceLit (List.headD (raw_ints% [30134295574762321468615425496875]) 0) 38 true) (.node 129 (sourceLit (List.headD (raw_ints% [1046493353750101537128992494225875]) 0) 33 true) .empty .empty) .empty) (.node 132 (sourceLit (List.headD (raw_ints% [52682630570772976027251812947275]) 0) 37 true) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [90120505425078308399317801828125]) 0) 36 true) (.node 134 (sourceLit (List.headD (raw_ints% [5906911465541236587932428458525]) 0) 40 true) .empty .empty) (.node 136 (sourceLit (List.headD (raw_ints% [5390064514947540730930626623625]) 0) 40 true) .empty .empty)))

#time def treeT_J015_part023 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [139502103025342559133907706005575]) 0) 35 true) (.node 140 (sourceLit (List.headD (raw_ints% [148551578223560453452993134778125]) 0) 35 true) (.node 139 (sourceLit (List.headD (raw_ints% [7246562498365727063864210780697975]) 0) 35 false) (.node 138 (sourceLit (List.headD (raw_ints% [159333053591538449249993873632125]) 0) 35 true) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [575361299878143911469427886420625]) 0) 33 true) .empty .empty)) (.node 144 (sourceLit (List.headD (raw_ints% [131765683107457218562563011773725]) 0) 35 true) (.node 143 (sourceLit (List.headD (raw_ints% [135490185602015682228995059230375]) 0) 35 true) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [1026367400036189613159526599455625]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part024 : IntSourceTree :=
  (.node 137 (sourceLit (List.headD (raw_ints% [15462748932848819352007548886302075]) 0) 33 true) treeT_J015_part022 treeT_J015_part023)

#time def treeT_J015_part025 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [27880873054679741146716297606975]) 0) 37 true) (.node 149 (sourceLit (List.headD (raw_ints% [465869066299691974623780567075585]) 0) 33 true) (.node 148 (sourceLit (List.headD (raw_ints% [119157847320387884564931542069175]) 0) 35 true) (.node 147 (sourceLit (List.headD (raw_ints% [488055912317759015458568937041445]) 0) 33 true) .empty .empty) .empty) (.node 150 (sourceLit (List.headD (raw_ints% [113926942019346026749611219919125]) 0) 35 true) .empty .empty)) (.node 153 (sourceLit (List.headD (raw_ints% [1713304347334450204906933307221275]) 0) 31 true) (.node 152 (sourceLit (List.headD (raw_ints% [109245150418216391589297901185495]) 0) 35 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [210046766959050265276817800910895]) 0) 34 true) .empty .empty)))

#time def treeT_J015_part026 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [192111309654816665489693354147565]) 0) 34 true) (.node 157 (sourceLit (List.headD (raw_ints% [795231927114533034067864015087995]) 0) 32 true) (.node 156 (sourceLit (List.headD (raw_ints% [202383173023600718373396975477675]) 0) 34 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [195387599550824469147210736952925]) 0) 34 true) .empty .empty)) (.node 169 (sourceLit (List.headD (raw_ints% [407334362066205848070706523849625]) 0) 35 true) (.node 168 (sourceLit (List.headD (raw_ints% [7455955250571309005277959581501125]) 0) 31 true) .empty .empty) (.node 170 (sourceLit (List.headD (raw_ints% [1460582641292186027005629331467375]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part027 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [824500162531807742614897048660875]) 0) 32 true) treeT_J015_part025 treeT_J015_part026)

#time def treeT_J015_part028 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [125053232970667807948157258153625]) 0) 35 true) treeT_J015_part024 treeT_J015_part027)

#time def treeT_J015_part029 : IntSourceTree :=
  (.node 128 (sourceLit (List.headD (raw_ints% [144025753344693926975588535386625]) 0) 36 true) treeT_J015_part021 treeT_J015_part028)

#time def treeT_J015_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [361278301508009428510907587331775]) 0) 32 true) treeT_J015_part014 treeT_J015_part029)

#time def treeT_J015_part031 : IntSourceTree :=
  (.node 176 (sourceLit (List.headD (raw_ints% [10937566617013115857341918096450075]) 0) 31 false) (.node 174 (sourceLit (List.headD (raw_ints% [134595560050441629427552561171875]) 0) 36 true) (.node 173 (sourceLit (List.headD (raw_ints% [143322568964658785870157519483525]) 0) 36 true) (.node 172 (sourceLit (List.headD (raw_ints% [1229998989662583068579946242322375]) 0) 33 true) .empty .empty) .empty) (.node 175 (sourceLit (List.headD (raw_ints% [63577792824661478409667297451775]) 0) 37 true) .empty .empty)) (.node 178 (sourceLit (List.headD (raw_ints% [90564339629606242644875457465758325]) 0) 32 true) (.node 177 (sourceLit (List.headD (raw_ints% [920602420180371367515316897531875]) 0) 33 true) .empty .empty) (.node 179 (sourceLit (List.headD (raw_ints% [844936873582502818341086312575125]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part032 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [689616820583803664190076428200925]) 0) 33 true) (.node 183 (sourceLit (List.headD (raw_ints% [732757752335232897765000420579525]) 0) 33 true) (.node 182 (sourceLit (List.headD (raw_ints% [1514201747178916118442824504674875]) 0) 32 true) (.node 181 (sourceLit (List.headD (raw_ints% [783661725357773330984280558368175]) 0) 33 true) .empty .empty) .empty) (.node 184 (sourceLit (List.headD (raw_ints% [5682742799088039661344902758599375]) 0) 30 true) .empty .empty)) (.node 187 (sourceLit (List.headD (raw_ints% [652463659775917642192100223796575]) 0) 33 true) (.node 186 (sourceLit (List.headD (raw_ints% [83797481514325458193369050860865]) 0) 36 true) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [2542901498140728629978453136872115]) 0) 31 true) .empty .empty)))

#time def treeT_J015_part033 : IntSourceTree :=
  (.node 180 (sourceLit (List.headD (raw_ints% [233556985628589182029570497677723325]) 0) 31 false) treeT_J015_part031 treeT_J015_part032)

#time def treeT_J015_part034 : IntSourceTree :=
  (.node 194 (sourceLit (List.headD (raw_ints% [1108462660077024359404714994051475]) 0) 32 true) (.node 192 (sourceLit (List.headD (raw_ints% [9253531722829231417910901556310325]) 0) 29 true) (.node 191 (sourceLit (List.headD (raw_ints% [591438232380647666853635268829455]) 0) 33 true) (.node 190 (sourceLit (List.headD (raw_ints% [1210621612959370424878854662138265]) 0) 32 true) .empty .empty) .empty) (.node 193 (sourceLit (List.headD (raw_ints% [1131927627981660944293313865446805]) 0) 32 true) .empty .empty)) (.node 196 (sourceLit (List.headD (raw_ints% [4260036525207753113293154063484105]) 0) 30 true) (.node 195 (sourceLit (List.headD (raw_ints% [1086188473065399822677511528410835]) 0) 32 true) .empty .empty) (.node 197 (sourceLit (List.headD (raw_ints% [1044839151518379552259491211026525]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part035 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [227637899456837067501719537689425]) 0) 36 true) (.node 210 (sourceLit (List.headD (raw_ints% [286797179767156562196244821862125]) 0) 36 true) (.node 209 (sourceLit (List.headD (raw_ints% [5362968543071105931019974593049375]) 0) 32 true) (.node 199 (sourceLit (List.headD (raw_ints% [1007229323071038043546296253215975]) 0) 32 true) .empty .empty) .empty) (.node 211 (sourceLit (List.headD (raw_ints% [505801531764281064502228304140875]) 0) 35 true) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [96067277240328893166698091815325]) 0) 37 true) (.node 213 (sourceLit (List.headD (raw_ints% [831858300656330618735188676677125]) 0) 34 true) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [179070614675804950455787320515625]) 0) 36 true) .empty .empty)))

#time def treeT_J015_part036 : IntSourceTree :=
  (.node 198 (sourceLit (List.headD (raw_ints% [2051204168330856045801775056429945]) 0) 31 true) treeT_J015_part034 treeT_J015_part035)

#time def treeT_J015_part037 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [620042817846458945243251602046125]) 0) 33 true) treeT_J015_part033 treeT_J015_part036)

#time def treeT_J015_part038 : IntSourceTree :=
  (.node 221 (sourceLit (List.headD (raw_ints% [234707708228345469852509353450564575]) 0) 32 false) (.node 219 (sourceLit (List.headD (raw_ints% [119550589623069150900332300588550225]) 0) 33 true) (.node 218 (sourceLit (List.headD (raw_ints% [601936312997294469015329150267625]) 0) 34 true) (.node 217 (sourceLit (List.headD (raw_ints% [41863064482710754561357015869054225]) 0) 32 false) .empty .empty) .empty) (.node 220 (sourceLit (List.headD (raw_ints% [547833717135381911435100043018875]) 0) 34 true) .empty .empty)) (.node 223 (sourceLit (List.headD (raw_ints% [972241004770853389526844267753375]) 0) 33 true) (.node 222 (sourceLit (List.headD (raw_ints% [504657519307088212716465146357025]) 0) 34 true) .empty .empty) (.node 224 (sourceLit (List.headD (raw_ints% [469226386120318460639874397032075]) 0) 34 true) .empty .empty)))

#time def treeT_J015_part039 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [392188933807766891744029162207875]) 0) 34 true) (.node 228 (sourceLit (List.headD (raw_ints% [414147965135141873062237139658225]) 0) 34 true) (.node 227 (sourceLit (List.headD (raw_ints% [852703791911448315635335876732395]) 0) 33 true) (.node 226 (sourceLit (List.headD (raw_ints% [439510354642468048293761911893675]) 0) 34 true) .empty .empty) .empty) (.node 229 (sourceLit (List.headD (raw_ints% [1611163365541344680730892002720945]) 0) 32 true) .empty .empty)) (.node 232 (sourceLit (List.headD (raw_ints% [372947931544214883675039466458465]) 0) 34 true) (.node 231 (sourceLit (List.headD (raw_ints% [764527644084494566531393900426665]) 0) 33 true) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [5826923028160331008097034941867775]) 0) 30 true) .empty .empty)))

#time def treeT_J015_part040 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [3630007999015660435025849559688125]) 0) 31 true) treeT_J015_part038 treeT_J015_part039)

#time def treeT_J015_part041 : IntSourceTree :=
  (.node 239 (sourceLit (List.headD (raw_ints% [1282758929711589383843001639839685]) 0) 32 true) (.node 237 (sourceLit (List.headD (raw_ints% [2669572670978687045157426033308115]) 0) 31 true) (.node 236 (sourceLit (List.headD (raw_ints% [681422127018198385930717577455485]) 0) 33 true) (.node 235 (sourceLit (List.headD (raw_ints% [1392425157622240976194532939442075]) 0) 32 true) .empty .empty) .empty) (.node 238 (sourceLit (List.headD (raw_ints% [654063952416730613965069737120675]) 0) 33 true) .empty .empty)) (.node 251 (sourceLit (List.headD (raw_ints% [814185558470243229228756123864525]) 0) 35 true) (.node 250 (sourceLit (List.headD (raw_ints% [243899118861182494000896578848875]) 0) 37 true) .empty .empty) (.node 252 (sourceLit (List.headD (raw_ints% [2816413264451665447437880190804625]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part042 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [1768519804771392823585149723733725]) 0) 33 true) (.node 255 (sourceLit (List.headD (raw_ints% [128556761655996307923728886178875]) 0) 37 true) (.node 254 (sourceLit (List.headD (raw_ints% [562667180555447359880083554333375]) 0) 35 true) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [22398085956264632686512306609450075]) 0) 31 true) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [1562808378406675057720230288495375]) 0) 33 true) (.node 258 (sourceLit (List.headD (raw_ints% [174290468595027751767589489203866775]) 0) 32 false) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [1189961702613142389232228902386125125]) 0) 31 true) .empty .empty)))

#time def treeT_J015_part043 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [311953229949015349133281555895325]) 0) 36 true) treeT_J015_part041 treeT_J015_part042)

#time def treeT_J015_part044 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [711834094063560413739678263625015]) 0) 33 true) treeT_J015_part040 treeT_J015_part043)

#time def treeT_J015_part045 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [42017534764871315485944790957275]) 0) 38 true) treeT_J015_part037 treeT_J015_part044)

#time def treeT_J015_part046 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [2289248294786453103931944745914285]) 0) 32 true) (.node 264 (sourceLit (List.headD (raw_ints% [9873113277245614571084605525454625]) 0) 30 true) (.node 263 (sourceLit (List.headD (raw_ints% [1285872324893119953100860164848575]) 0) 33 true) (.node 262 (sourceLit (List.headD (raw_ints% [470929618203869855823461531405804025]) 0) 32 false) .empty .empty) .empty) (.node 265 (sourceLit (List.headD (raw_ints% [1187288723897470178369421159927375]) 0) 33 true) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [4278728837150857895104233876987045]) 0) 31 true) (.node 267 (sourceLit (List.headD (raw_ints% [1105577758793954550982947423778125]) 0) 33 true) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [1036549042694108547005696956586775]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part047 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [1761147903188841832281201526089225]) 0) 32 true) (.node 273 (sourceLit (List.headD (raw_ints% [1851655824372058125107001866220915]) 0) 32 true) (.node 272 (sourceLit (List.headD (raw_ints% [15211352887874594711093703257342955]) 0) 29 true) (.node 271 (sourceLit (List.headD (raw_ints% [977317502850419900122481380002045]) 0) 33 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [3609997708006282289287604953764825]) 0) 31 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [1680849356554413991463379098795415]) 0) 32 true) (.node 276 (sourceLit (List.headD (raw_ints% [6879364735770174696263109452052495]) 0) 30 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [3287941173626518044513077010186285]) 0) 31 true) .empty .empty)))

#time def treeT_J015_part048 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [2011705118123318936582929343303625]) 0) 32 true) treeT_J015_part046 treeT_J015_part047)

#time def treeT_J015_part049 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [191798282939821204712148116908875]) 0) 37 true) (.node 293 (sourceLit (List.headD (raw_ints% [496138740948833707175672878531875]) 0) 36 true) (.node 292 (sourceLit (List.headD (raw_ints% [146636914753351540431759146543775]) 0) 38 true) (.node 291 (sourceLit (List.headD (raw_ints% [1445391419125178887504944326650125]) 0) 35 true) .empty .empty) .empty) (.node 294 (sourceLit (List.headD (raw_ints% [1686609005536612937238933313125]) 0) 44 true) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [16065287609743846811967330619626075]) 0) 34 true) (.node 296 (sourceLit (List.headD (raw_ints% [2704350840347656013680752975675]) 0) 43 true) .empty .empty) (.node 298 (sourceLit (List.headD (raw_ints% [291645872943524588642455143366525]) 0) 36 true) .empty .empty)))

#time def treeT_J015_part050 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [204161484693200373115246441954125]) 0) 36 true) (.node 302 (sourceLit (List.headD (raw_ints% [225753905969166525509913616837575]) 0) 36 true) (.node 301 (sourceLit (List.headD (raw_ints% [356167352710371964771184563959172425]) 0) 34 true) (.node 300 (sourceLit (List.headD (raw_ints% [253743665317823286571282561369125]) 0) 36 true) .empty .empty) .empty) (.node 303 (sourceLit (List.headD (raw_ints% [58987732401080088651623546959194675]) 0) 36 false) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [186944592313750532518914812008425]) 0) 36 true) (.node 305 (sourceLit (List.headD (raw_ints% [1560776319557488534014688991441625]) 0) 33 true) .empty .empty) (.node 307 (sourceLit (List.headD (raw_ints% [718272251437502394148304434590945]) 0) 34 true) .empty .empty)))

#time def treeT_J015_part051 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [36730132277262112833490223724052125]) 0) 36 false) treeT_J015_part049 treeT_J015_part050)

#time def treeT_J015_part052 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [1609026486595884412313982695266725]) 0) 32 true) treeT_J015_part048 treeT_J015_part051)

#time def treeT_J015_part053 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [2346107464928565925749167078868795]) 0) 32 true) (.node 311 (sourceLit (List.headD (raw_ints% [38974296063713261564110482589905]) 0) 38 true) (.node 310 (sourceLit (List.headD (raw_ints% [161090027221585413815416948594725]) 0) 36 true) (.node 309 (sourceLit (List.headD (raw_ints% [666891367902378303593335468566525]) 0) 34 true) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [151092392826551254111860478385895]) 0) 36 true) .empty .empty)) (.node 315 (sourceLit (List.headD (raw_ints% [1108786275192020656546536007161375]) 0) 33 true) (.node 314 (sourceLit (List.headD (raw_ints% [284955432577124427841830900648975]) 0) 35 true) .empty .empty) (.node 316 (sourceLit (List.headD (raw_ints% [269931444042660861587620987158435]) 0) 35 true) .empty .empty)))

#time def treeT_J015_part054 : IntSourceTree :=
  (.node 334 (sourceLit (List.headD (raw_ints% [1421887783239887468822607959794125]) 0) 35 true) (.node 332 (sourceLit (List.headD (raw_ints% [8746718088549765652601674422396375]) 0) 33 true) (.node 319 (sourceLit (List.headD (raw_ints% [250647780489366082583759421293325]) 0) 35 true) (.node 318 (sourceLit (List.headD (raw_ints% [256696351034420844374577340418685]) 0) 35 true) .empty .empty) .empty) (.node 333 (sourceLit (List.headD (raw_ints% [861142088077796974320791616454875]) 0) 36 true) .empty .empty)) (.node 336 (sourceLit (List.headD (raw_ints% [2152094260032481516642652354885925]) 0) 31 true) (.node 335 (sourceLit (List.headD (raw_ints% [303215143761376604009438041981125]) 0) 37 true) .empty .empty) (.node 337 (sourceLit (List.headD (raw_ints% [3769990716260606692433032370448675]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part055 : IntSourceTree :=
  (.node 317 (sourceLit (List.headD (raw_ints% [1052448016197871912776420854686095]) 0) 33 true) treeT_J015_part053 treeT_J015_part054)

#time def treeT_J015_part056 : IntSourceTree :=
  (.node 343 (sourceLit (List.headD (raw_ints% [2326190170613544455057757704552625]) 0) 33 true) (.node 341 (sourceLit (List.headD (raw_ints% [2652225501901418270384401368198675]) 0) 33 true) (.node 340 (sourceLit (List.headD (raw_ints% [3540690168357917610575603220725461125]) 0) 31 false) (.node 339 (sourceLit (List.headD (raw_ints% [3103525588689718360559052005369025]) 0) 33 true) .empty .empty) .empty) (.node 342 (sourceLit (List.headD (raw_ints% [3320268439886845573992938043079183425]) 0) 32 true) .empty .empty)) (.node 345 (sourceLit (List.headD (raw_ints% [2079295031193735791474521911338625]) 0) 33 true) (.node 344 (sourceLit (List.headD (raw_ints% [7560302860615496961978898616302373025]) 0) 30 false) .empty .empty) (.node 346 (sourceLit (List.headD (raw_ints% [3953856983443501032126811219852215]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part057 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [1600122932694946720924189797513555]) 0) 33 true) (.node 349 (sourceLit (List.headD (raw_ints% [1729170131941142164677144179892825]) 0) 33 true) (.node 348 (sourceLit (List.headD (raw_ints% [7213627185849180411268637076468075]) 0) 31 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [3323425825095707492163754405228575]) 0) 32 true) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [2983300746077582006472533442127725]) 0) 32 true) (.node 352 (sourceLit (List.headD (raw_ints% [24698326281367785130555430914719765]) 0) 29 true) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [5774432151707981413709063361710355]) 0) 31 true) .empty .empty)))

#time def treeT_J015_part058 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [1885535718226053969319689568356675]) 0) 33 true) treeT_J015_part056 treeT_J015_part057)

#time def treeT_J015_part059 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [302812769472978526263328134160875375]) 0) 32 true) treeT_J015_part055 treeT_J015_part058)

#time def treeT_J015_part060 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [172857448414703169480177571029975]) 0) 36 true) treeT_J015_part052 treeT_J015_part059)

#time def treeT_J015_part061 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [1407673143183754314756119613707325]) 0) 33 true) treeT_J015_part045 treeT_J015_part060)

#time def treeT_J015_part062 : IntSourceTree :=
  (.node 171 (sourceLit (List.headD (raw_ints% [333003160598383019556223163583975]) 0) 35 true) treeT_J015_part030 treeT_J015_part061)

#time def treeT_J015_part063 : IntSourceTree :=
  (.node 373 (sourceLit (List.headD (raw_ints% [6762163124754430823898982908268875]) 0) 34 true) (.node 358 (sourceLit (List.headD (raw_ints% [5131642955956457257698289827302475]) 0) 31 true) (.node 357 (sourceLit (List.headD (raw_ints% [2638053748128159793938556695739545]) 0) 32 true) (.node 356 (sourceLit (List.headD (raw_ints% [10861215667302155808481466662529505]) 0) 30 true) .empty .empty) .empty) (.node 359 (sourceLit (List.headD (raw_ints% [2498115129954849097679254751432235]) 0) 32 true) .empty .empty)) (.node 375 (sourceLit (List.headD (raw_ints% [1038291217360245059398311725976375]) 0) 36 true) (.node 374 (sourceLit (List.headD (raw_ints% [645256135369110518354208152374875]) 0) 37 true) .empty .empty) (.node 376 (sourceLit (List.headD (raw_ints% [216675916870251611571653946759525]) 0) 38 true) .empty .empty)))

#time def treeT_J015_part064 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [1749209878024752168344746900848375]) 0) 34 true) (.node 380 (sourceLit (List.headD (raw_ints% [2088550927418425214273921759892525]) 0) 34 true) (.node 379 (sourceLit (List.headD (raw_ints% [596653827691075428931249923953292375]) 0) 33 true) (.node 378 (sourceLit (List.headD (raw_ints% [2603407224486508337863211796982575]) 0) 34 true) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [4965359579199405469660341476562150825]) 0) 32 false) .empty .empty)) (.node 384 (sourceLit (List.headD (raw_ints% [1509544231840742962596771936736125]) 0) 34 true) (.node 383 (sourceLit (List.headD (raw_ints% [3792170299095486283205926418752740825]) 0) 33 true) .empty .empty) (.node 385 (sourceLit (List.headD (raw_ints% [7566545965893726916114957372268139525]) 0) 31 false) .empty .empty)))

#time def treeT_J015_part065 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [62109056178942905731226670123618375]) 0) 32 false) treeT_J015_part063 treeT_J015_part064)

#time def treeT_J015_part066 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [2076248351056883122112218962351615]) 0) 33 true) (.node 389 (sourceLit (List.headD (raw_ints% [4546061714239667196895295202201975]) 0) 32 true) (.node 388 (sourceLit (List.headD (raw_ints% [1194105924567241291398979284236775]) 0) 34 true) (.node 387 (sourceLit (List.headD (raw_ints% [2517312480568496243830202350670325]) 0) 33 true) .empty .empty) .empty) (.node 390 (sourceLit (List.headD (raw_ints% [1084810023054800509415476385513925]) 0) 34 true) .empty .empty)) (.node 393 (sourceLit (List.headD (raw_ints% [15313896421653521427558762599244585]) 0) 30 true) (.node 392 (sourceLit (List.headD (raw_ints% [995753361388741704476747883969975]) 0) 34 true) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [1843479015769084295105209839531825]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part067 : IntSourceTree :=
  (.node 414 (sourceLit (List.headD (raw_ints% [2670137670757271677538187474237375]) 0) 36 true) (.node 398 (sourceLit (List.headD (raw_ints% [1611268343990476416440247334064805]) 0) 33 true) (.node 397 (sourceLit (List.headD (raw_ints% [6651423602510668157375783243785125]) 0) 31 true) (.node 396 (sourceLit (List.headD (raw_ints% [1718413241874505566837608935660635]) 0) 33 true) .empty .empty) .empty) (.node 399 (sourceLit (List.headD (raw_ints% [3126460712041528597028214456955875]) 0) 32 true) .empty .empty)) (.node 416 (sourceLit (List.headD (raw_ints% [64298543651023202284849298107602075]) 0) 31 true) (.node 415 (sourceLit (List.headD (raw_ints% [987297126976844432698978262768625]) 0) 37 true) .empty .empty) (.node 417 (sourceLit (List.headD (raw_ints% [10097267963435496448152820222160925]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part068 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [3556859601323940100615991347387605]) 0) 32 true) treeT_J015_part066 treeT_J015_part067)

#time def treeT_J015_part069 : IntSourceTree :=
  (.node 386 (sourceLit (List.headD (raw_ints% [1331516661938733661398862663304925]) 0) 34 true) treeT_J015_part065 treeT_J015_part068)

#time def treeT_J015_part070 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [4670649341485464218321229898840875]) 0) 33 true) (.node 421 (sourceLit (List.headD (raw_ints% [5701978207772282586711285671371425]) 0) 33 true) (.node 420 (sourceLit (List.headD (raw_ints% [8313920789886521042025602612351800125]) 0) 31 true) (.node 419 (sourceLit (List.headD (raw_ints% [7310103309256314990893795182561275]) 0) 33 true) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [13250987598285656513313620996203485075]) 0) 32 false) .empty .empty)) (.node 425 (sourceLit (List.headD (raw_ints% [3958881896169236058912565835605875]) 0) 33 true) (.node 424 (sourceLit (List.headD (raw_ints% [68235027646143277493273721316346226225]) 0) 30 true) .empty .empty) (.node 426 (sourceLit (List.headD (raw_ints% [1892624955719292604286771045871997935]) 0) 34 false) .empty .empty)))

#time def treeT_J015_part071 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [41741620952452474777035575880531915]) 0) 29 true) (.node 430 (sourceLit (List.headD (raw_ints% [5768697603383626901626835999175375]) 0) 32 true) (.node 429 (sourceLit (List.headD (raw_ints% [3047253566327823000918772957054275]) 0) 33 true) (.node 428 (sourceLit (List.headD (raw_ints% [12924872658698789539372981728894525]) 0) 31 true) .empty .empty) .empty) (.node 431 (sourceLit (List.headD (raw_ints% [2739117159524255316737715744542145]) 0) 33 true) .empty .empty)) (.node 434 (sourceLit (List.headD (raw_ints% [4769732134972770006924849618767115]) 0) 32 true) (.node 433 (sourceLit (List.headD (raw_ints% [4982726145032351629341449629632075]) 0) 32 true) .empty .empty) (.node 435 (sourceLit (List.headD (raw_ints% [4575777045031188167232746473832925]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part072 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [3440530929528880676275761084863025]) 0) 33 true) treeT_J015_part070 treeT_J015_part071)

#time def treeT_J015_part073 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [192655302526648205281831079002275]) 0) 40 true) (.node 439 (sourceLit (List.headD (raw_ints% [3946958246007056568081734584826985]) 0) 32 true) (.node 438 (sourceLit (List.headD (raw_ints% [8171204249064879057053276660267775]) 0) 31 true) (.node 437 (sourceLit (List.headD (raw_ints% [4235599219369862473411879046902995]) 0) 32 true) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [4301984124154298295678063222498375]) 0) 36 true) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [3746930369474494055144804212589175]) 0) 35 true) (.node 457 (sourceLit (List.headD (raw_ints% [63203799914983054008037984115610225]) 0) 33 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [255921177380484941664257849590351125]) 0) 35 false) .empty .empty)))

#time def treeT_J015_part074 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [1580552554822360627862228981052375]) 0) 35 true) (.node 462 (sourceLit (List.headD (raw_ints% [1976384164873765209183269385261525]) 0) 35 true) (.node 461 (sourceLit (List.headD (raw_ints% [6639640184542963255842972044456975475]) 0) 33 true) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [4260789474345285699129886853739056475]) 0) 35 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [1313682617115251198756851586150475]) 0) 35 true) (.node 465 (sourceLit (List.headD (raw_ints% [37900786806018502204694339344307182875]) 0) 32 true) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [7573017135357738913390914385838662065]) 0) 33 false) .empty .empty)))

#time def treeT_J015_part075 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [2610776190918944888309936711334375]) 0) 35 true) treeT_J015_part073 treeT_J015_part074)

#time def treeT_J015_part076 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [17593661143289364996446464116571335]) 0) 30 true) treeT_J015_part072 treeT_J015_part075)

#time def treeT_J015_part077 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [427030881830864337725781474408112125]) 0) 32 false) treeT_J015_part069 treeT_J015_part076)

#time def treeT_J015_part078 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [13213862265399476674738406640643665]) 0) 31 true) (.node 471 (sourceLit (List.headD (raw_ints% [230778078270421486219663564801485]) 0) 37 true) (.node 470 (sourceLit (List.headD (raw_ints% [981221771636511245751648285770175]) 0) 35 true) (.node 469 (sourceLit (List.headD (raw_ints% [4189405472229561171238843263346275]) 0) 33 true) .empty .empty) .empty) (.node 472 (sourceLit (List.headD (raw_ints% [871681899067756806130483930286085]) 0) 35 true) .empty .empty)) (.node 475 (sourceLit (List.headD (raw_ints% [5982604668621599913233707890146625]) 0) 32 true) (.node 474 (sourceLit (List.headD (raw_ints% [1569623564631633667118119895050125]) 0) 34 true) .empty .empty) (.node 476 (sourceLit (List.headD (raw_ints% [1428681901578341300197568769086145]) 0) 34 true) .empty .empty)))

#time def treeT_J015_part079 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [679846081490796553757933410870553025]) 0) 32 true) (.node 496 (sourceLit (List.headD (raw_ints% [211028440294851888638546748132293925]) 0) 31 true) (.node 479 (sourceLit (List.headD (raw_ints% [1261185884255837615006265550827975]) 0) 34 true) (.node 478 (sourceLit (List.headD (raw_ints% [1312165437689693028485815856419095]) 0) 34 true) .empty .empty) .empty) (.node 497 (sourceLit (List.headD (raw_ints% [39222489483386444103995936002421475]) 0) 33 true) .empty .empty)) (.node 500 (sourceLit (List.headD (raw_ints% [16503398466062039175281853799243036125]) 0) 31 false) (.node 499 (sourceLit (List.headD (raw_ints% [22665339646539637450264638518152125]) 0) 33 true) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [15184231319579276519768208019303575]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part080 : IntSourceTree :=
  (.node 477 (sourceLit (List.headD (raw_ints% [5471118770389348419535340436393105]) 0) 32 true) treeT_J015_part078 treeT_J015_part079)

#time def treeT_J015_part081 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [7068930007393128913779051604340775]) 0) 33 true) (.node 505 (sourceLit (List.headD (raw_ints% [8685538542409648963985266012813125]) 0) 33 true) (.node 504 (sourceLit (List.headD (raw_ints% [340925554004241562237586479955645840625]) 0) 30 false) (.node 503 (sourceLit (List.headD (raw_ints% [11140423977504657455144925183251325]) 0) 33 true) .empty .empty) .empty) (.node 506 (sourceLit (List.headD (raw_ints% [41686036717457087413267881436051178745]) 0) 33 true) .empty .empty)) (.node 509 (sourceLit (List.headD (raw_ints% [5938446453518734538588354245450725]) 0) 33 true) (.node 508 (sourceLit (List.headD (raw_ints% [60597061955520610096666688068438191045]) 0) 31 false) .empty .empty) (.node 510 (sourceLit (List.headD (raw_ints% [10988924285534617783328537054209725]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part082 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [30267176205683434309423199004601665]) 0) 30 true) (.node 514 (sourceLit (List.headD (raw_ints% [4222065065213353333906778510938275]) 0) 33 true) (.node 513 (sourceLit (List.headD (raw_ints% [8964184240051757268746293254945285]) 0) 32 true) (.node 512 (sourceLit (List.headD (raw_ints% [76416755122003326167432169297828405]) 0) 29 true) .empty .empty) .empty) (.node 515 (sourceLit (List.headD (raw_ints% [7981211472021881169712212686568075]) 0) 32 true) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [13713270832492514621088085085304645]) 0) 31 true) (.node 517 (sourceLit (List.headD (raw_ints% [7193855993256867928168671105786165]) 0) 32 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [6550365255510487659804792266525775]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part083 : IntSourceTree :=
  (.node 511 (sourceLit (List.headD (raw_ints% [5110657013567834649275470541619255]) 0) 33 true) treeT_J015_part081 treeT_J015_part082)

#time def treeT_J015_part084 : IntSourceTree :=
  (.node 502 (sourceLit (List.headD (raw_ints% [39809548336457509536685509174031386975]) 0) 32 true) treeT_J015_part080 treeT_J015_part083)

#time def treeT_J015_part085 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [56852706233838652333205056588987612875]) 0) 33 true) (.node 541 (sourceLit (List.headD (raw_ints% [29782678835147965686967797888156987075]) 0) 32 false) (.node 540 (sourceLit (List.headD (raw_ints% [17443787264701747673644765095483375]) 0) 34 true) (.node 539 (sourceLit (List.headD (raw_ints% [1703530791012736320414964809231957525]) 0) 33 true) .empty .empty) .empty) (.node 542 (sourceLit (List.headD (raw_ints% [11231462989831746101401669248780525]) 0) 34 true) .empty .empty)) (.node 545 (sourceLit (List.headD (raw_ints% [416727127616278566646975158644260206375]) 0) 31 false) (.node 544 (sourceLit (List.headD (raw_ints% [7979318867859936199420467221146575]) 0) 34 true) .empty .empty) (.node 546 (sourceLit (List.headD (raw_ints% [6058173308179146566471562840512175]) 0) 34 true) .empty .empty)))

#time def treeT_J015_part086 : IntSourceTree :=
  (.node 552 (sourceLit (List.headD (raw_ints% [3367293215432321037014502681047085]) 0) 34 true) (.node 550 (sourceLit (List.headD (raw_ints% [3976002910245712047085057673910375]) 0) 34 true) (.node 549 (sourceLit (List.headD (raw_ints% [60605440766465069219009165754964883595]) 0) 32 false) (.node 548 (sourceLit (List.headD (raw_ints% [4822505002431489528902269803714525]) 0) 34 true) .empty .empty) .empty) (.node 551 (sourceLit (List.headD (raw_ints% [7296475033207874003813920017385965]) 0) 33 true) .empty .empty)) (.node 554 (sourceLit (List.headD (raw_ints% [5824937110788489934510053464845035]) 0) 33 true) (.node 553 (sourceLit (List.headD (raw_ints% [49989030591204372817955356016541075]) 0) 30 true) .empty .empty) (.node 555 (sourceLit (List.headD (raw_ints% [10905655592231813422393406153606475]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part087 : IntSourceTree :=
  (.node 547 (sourceLit (List.headD (raw_ints% [90945090570271913739926677257941019555]) 0) 33 true) treeT_J015_part085 treeT_J015_part086)

#time def treeT_J015_part088 : IntSourceTree :=
  (.node 581 (sourceLit (List.headD (raw_ints% [54590917739227714174810852362629925]) 0) 33 true) (.node 559 (sourceLit (List.headD (raw_ints% [8668527295469164161063022881992745]) 0) 32 true) (.node 558 (sourceLit (List.headD (raw_ints% [4569525117877481871197039392947975]) 0) 33 true) (.node 557 (sourceLit (List.headD (raw_ints% [19324938664904737470352518131815455]) 0) 31 true) .empty .empty) .empty) (.node 580 (sourceLit (List.headD (raw_ints% [30131644794163929738601572273098696325]) 0) 31 true) .empty .empty)) (.node 583 (sourceLit (List.headD (raw_ints% [33785427981822326950461751811870775]) 0) 33 true) (.node 582 (sourceLit (List.headD (raw_ints% [99374906006753440910621104950345361125]) 0) 32 false) .empty .empty) (.node 584 (sourceLit (List.headD (raw_ints% [1250568853745659999568867385379447646625]) 0) 30 true) .empty .empty)))

#time def treeT_J015_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [13351573556207223577020724969407375]) 0) 33 true) (.node 587 (sourceLit (List.headD (raw_ints% [17163763225323457352107199757707925]) 0) 33 true) (.node 586 (sourceLit (List.headD (raw_ints% [500099201051192741473510921516362563865]) 0) 32 false) .empty .empty) (.node 588 (sourceLit (List.headD (raw_ints% [788157786517695920016080106131966347485]) 0) 31 true) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [10793354627415013539064760154022245]) 0) 33 true) (.node 590 (sourceLit (List.headD (raw_ints% [121221870457215673055801660046983976915]) 0) 32 false) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [157070445940648641954613271258522475]) 0) 29 true) .empty .empty)))

#time def treeT_J015_part090 : IntSourceTree :=
  (.node 585 (sourceLit (List.headD (raw_ints% [23231736929030095833696602871773175]) 0) 33 true) treeT_J015_part088 treeT_J015_part089)

#time def treeT_J015_part091 : IntSourceTree :=
  (.node 556 (sourceLit (List.headD (raw_ints% [5123847668865198569317075148395785]) 0) 33 true) treeT_J015_part087 treeT_J015_part090)

#time def treeT_J015_part092 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [31728628744437455993706327577243125]) 0) 34 true) treeT_J015_part084 treeT_J015_part091)

#time def treeT_J015_part093 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [1123212502480819692438390900313125]) 0) 35 true) treeT_J015_part077 treeT_J015_part092)

#time def treeT_J015_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [24936606497316960319616951178326265]) 0) 31 true) (.node 596 (sourceLit (List.headD (raw_ints% [56978068532171073069724050224250135]) 0) 30 true) (.node 595 (sourceLit (List.headD (raw_ints% [15318536971132078568328001172812065]) 0) 32 true) (.node 594 (sourceLit (List.headD (raw_ints% [33100770330350959482328241972787975]) 0) 31 true) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [13301534682203926349099629487796975]) 0) 32 true) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [5419931843674496009176147889231175]) 0) 37 true) (.node 599 (sourceLit (List.headD (raw_ints% [11727735215999439824983365305266125]) 0) 32 true) .empty .empty) (.node 623 (sourceLit (List.headD (raw_ints% [9764225765037005827739135096208310875]) 0) 37 false) .empty .empty)))

#time def treeT_J015_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [106095403410520123654386158985866403885]) 0) 35 true) (.node 627 (sourceLit (List.headD (raw_ints% [147761072905366163803359399693575895855]) 0) 35 false) (.node 626 (sourceLit (List.headD (raw_ints% [2146695452606368658403130003907625]) 0) 37 true) (.node 625 (sourceLit (List.headD (raw_ints% [208411997670242320776980318002963481625]) 0) 34 true) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [1542657277861495977900616244249175]) 0) 37 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [1894205733316388764528210530734396295]) 0) 39 false) (.node 630 (sourceLit (List.headD (raw_ints% [1171946330745188941241958411937125]) 0) 37 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [928257676497836562756282184121895]) 0) 37 true) .empty .empty)))

#time def treeT_J015_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [3225763639245298843880160573840525]) 0) 37 true) treeT_J015_part094 treeT_J015_part095)

#time def treeT_J015_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [1091501195540805559737823761856125]) 0) 36 true) (.node 636 (sourceLit (List.headD (raw_ints% [1274336162783359999876365753052035]) 0) 36 true) (.node 635 (sourceLit (List.headD (raw_ints% [5548778684529786514983708954795375]) 0) 34 true) (.node 634 (sourceLit (List.headD (raw_ints% [1518653046577290136607459341073295]) 0) 36 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [4706641233408291949921441511554335]) 0) 34 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [139652391015761545343174980643526825]) 0) 33 true) (.node 639 (sourceLit (List.headD (raw_ints% [1016754950115487259909620518520845]) 0) 36 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [3750210649595133491470085970008775230625]) 0) 30 false) .empty .empty)))

#time def treeT_J015_part098 : IntSourceTree :=
  (.node 670 (sourceLit (List.headD (raw_ints% [1818748325025537651525980203820846439075]) 0) 32 true) (.node 668 (sourceLit (List.headD (raw_ints% [5516512119489413161723580896326395014845]) 0) 31 false) (.node 667 (sourceLit (List.headD (raw_ints% [51530491258080339716792960367336075]) 0) 33 true) (.node 666 (sourceLit (List.headD (raw_ints% [2167395182413131307689353465540070416865]) 0) 32 true) .empty .empty) .empty) (.node 669 (sourceLit (List.headD (raw_ints% [36013459335360647715798994846566225]) 0) 33 true) .empty .empty)) (.node 672 (sourceLit (List.headD (raw_ints% [3879490412277904838395729780215302134635]) 0) 29 false) (.node 671 (sourceLit (List.headD (raw_ints% [26708927956431032580677909027965755]) 0) 33 true) .empty .empty) (.node 673 (sourceLit (List.headD (raw_ints% [41434329812454728989032331590369885]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part099 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [79992699526819467170468535491123625]) 0) 33 true) treeT_J015_part097 treeT_J015_part098)

#time def treeT_J015_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [13385176918680533642082239405247675]) 0) 33 true) treeT_J015_part096 treeT_J015_part099)

#time def treeT_J015_part101 : IntSourceTree :=
  (.node 679 (sourceLit (List.headD (raw_ints% [23200303041306338086626995074129875]) 0) 32 true) (.node 677 (sourceLit (List.headD (raw_ints% [27477222526863593646944074609868145]) 0) 32 true) (.node 676 (sourceLit (List.headD (raw_ints% [120582849372782095409754636329201865]) 0) 30 true) (.node 675 (sourceLit (List.headD (raw_ints% [33278360519341205803110697741533375]) 0) 32 true) .empty .empty) .empty) (.node 678 (sourceLit (List.headD (raw_ints% [50369653237215710879126113006543095]) 0) 31 true) .empty .empty)) (.node 706 (sourceLit (List.headD (raw_ints% [62819135905968517903243495459862625]) 0) 34 true) (.node 705 (sourceLit (List.headD (raw_ints% [5417506630957072057685928514032483083625]) 0) 31 false) .empty .empty) (.node 707 (sourceLit (List.headD (raw_ints% [2758439474034595962902791064314374000285]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part102 : IntSourceTree :=
  (.node 713 (sourceLit (List.headD (raw_ints% [3879597493693254282664866438130544116035]) 0) 30 false) (.node 711 (sourceLit (List.headD (raw_ints% [1939977491957786532455785677787847801955]) 0) 33 true) (.node 710 (sourceLit (List.headD (raw_ints% [26637888689399136185863327551069225]) 0) 34 true) (.node 709 (sourceLit (List.headD (raw_ints% [6365275346773574150958670168213326245925]) 0) 32 false) .empty .empty) .empty) (.node 712 (sourceLit (List.headD (raw_ints% [19282866544448340078627651554990595]) 0) 34 true) .empty .empty)) (.node 715 (sourceLit (List.headD (raw_ints% [51785530280974163594394837450011925]) 0) 32 true) (.node 714 (sourceLit (List.headD (raw_ints% [29285105439836407896172656861783525]) 0) 33 true) .empty .empty) (.node 716 (sourceLit (List.headD (raw_ints% [23083671217074325804099771717117095]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part103 : IntSourceTree :=
  (.node 708 (sourceLit (List.headD (raw_ints% [39189233035188371893588030413342675]) 0) 34 true) treeT_J015_part101 treeT_J015_part102)

#time def treeT_J015_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [27584027911766180864945909410841387017125]) 0) 31 true) (.node 746 (sourceLit (List.headD (raw_ints% [3792450906685101682687640989786276750245]) 0) 33 false) (.node 719 (sourceLit (List.headD (raw_ints% [34101574035367914720572184710209575]) 0) 32 true) (.node 718 (sourceLit (List.headD (raw_ints% [18745212962537149169041484515019145]) 0) 33 true) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [199746052365793731896181021472114425]) 0) 33 true) .empty .empty)) (.node 750 (sourceLit (List.headD (raw_ints% [14549299018572685953443320540247498930925]) 0) 32 false) (.node 749 (sourceLit (List.headD (raw_ints% [120743472805392839858553126806804475]) 0) 33 true) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [79842626801165512162775401176311145]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part105 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [293701392875011213345404063270893535]) 0) 30 true) (.node 754 (sourceLit (List.headD (raw_ints% [969917868584568343993630191950953327365]) 0) 33 false) (.node 753 (sourceLit (List.headD (raw_ints% [112828602543131991639988880849554875]) 0) 32 true) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [83862061240004425781579929705600725]) 0) 32 true) .empty .empty)) (.node 758 (sourceLit (List.headD (raw_ints% [115489785773815808741640095466991275]) 0) 31 true) (.node 757 (sourceLit (List.headD (raw_ints% [64857462341433709569455012258600235]) 0) 32 true) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [51780548808842258589538942985946705]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part106 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [65958770154927073876980871469426431797195]) 0) 29 true) treeT_J015_part104 treeT_J015_part105)

#time def treeT_J015_part107 : IntSourceTree :=
  (.node 717 (sourceLit (List.headD (raw_ints% [82929719505515759810383104236767185]) 0) 31 true) treeT_J015_part103 treeT_J015_part106)

#time def treeT_J015_part108 : IntSourceTree :=
  (.node 674 (sourceLit (List.headD (raw_ints% [73980645019093309654329673269193425]) 0) 31 true) treeT_J015_part100 treeT_J015_part107)

#time def treeT_J015_part109 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [30279880128358586042073874810660275]) 0) 35 true) (.node 790 (sourceLit (List.headD (raw_ints% [47052792057996851836344899627867625]) 0) 35 true) (.node 789 (sourceLit (List.headD (raw_ints% [16974651629269877507952289789527356631525]) 0) 33 true) (.node 788 (sourceLit (List.headD (raw_ints% [80278409665302680001296495529385875]) 0) 35 true) .empty .empty) .empty) (.node 791 (sourceLit (List.headD (raw_ints% [1030579781908154530368694138627209170805]) 0) 37 false) .empty .empty)) (.node 794 (sourceLit (List.headD (raw_ints% [41771748551647791871908111993885675]) 0) 34 true) (.node 793 (sourceLit (List.headD (raw_ints% [34919183824310164079822868953778487956615]) 0) 31 true) .empty .empty) (.node 795 (sourceLit (List.headD (raw_ints% [3879723259868554350138115162641263321385]) 0) 32 false) .empty .empty)))

#time def treeT_J015_part110 : IntSourceTree :=
  (.node 829 (sourceLit (List.headD (raw_ints% [521483804517028600151818837428282525]) 0) 33 true) (.node 799 (sourceLit (List.headD (raw_ints% [20347052934611973505266977689195425]) 0) 34 true) (.node 798 (sourceLit (List.headD (raw_ints% [23056124689448280200206763871790545]) 0) 34 true) (.node 797 (sourceLit (List.headD (raw_ints% [105385836684747726767510479517063175]) 0) 32 true) .empty .empty) .empty) (.node 828 (sourceLit (List.headD (raw_ints% [110330758211004575491170493761936807023325]) 0) 31 false) .empty .empty)) (.node 831 (sourceLit (List.headD (raw_ints% [296579709662809302527983795846629855]) 0) 33 true) (.node 830 (sourceLit (List.headD (raw_ints% [82447905535652195985252479698356925457025]) 0) 32 true) .empty .empty) (.node 832 (sourceLit (List.headD (raw_ints% [593615618491902193425752270446557527249355]) 0) 29 false) .empty .empty)))

#time def treeT_J015_part111 : IntSourceTree :=
  (.node 796 (sourceLit (List.headD (raw_ints% [30389195011465049988740078994241815]) 0) 34 true) treeT_J015_part109 treeT_J015_part110)

#time def treeT_J015_part112 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [306053560965175098328401822601261425]) 0) 31 true) (.node 836 (sourceLit (List.headD (raw_ints% [31038079780341309812318266705193377464615]) 0) 30 false) (.node 835 (sourceLit (List.headD (raw_ints% [250311927173177909193684966245484675]) 0) 32 true) (.node 834 (sourceLit (List.headD (raw_ints% [36859019561479300767810129337680394611345]) 0) 32 true) .empty .empty) .empty) (.node 837 (sourceLit (List.headD (raw_ints% [178256097750286690340465619695334285]) 0) 32 true) .empty .empty)) (.node 869 (sourceLit (List.headD (raw_ints% [144280061469544330507075073340991520286375]) 0) 32 false) (.node 839 (sourceLit (List.headD (raw_ints% [132668448706743983012115167988377655]) 0) 32 true) .empty .empty) (.node 870 (sourceLit (List.headD (raw_ints% [427378220401034896479129038172547275]) 0) 34 true) .empty .empty)))

#time def treeT_J015_part113 : IntSourceTree :=
  (.node 875 (sourceLit (List.headD (raw_ints% [77597762382827155885758373838002052544075]) 0) 32 true) (.node 873 (sourceLit (List.headD (raw_ints% [663453986140522521585398008354114503162585]) 0) 30 false) (.node 872 (sourceLit (List.headD (raw_ints% [236019949406092130443836046225309305]) 0) 34 true) .empty .empty) (.node 874 (sourceLit (List.headD (raw_ints% [288105982407309801289376892133238175]) 0) 33 true) .empty .empty)) (.node 877 (sourceLit (List.headD (raw_ints% [31038290552014679307771801726152411590965]) 0) 31 false) (.node 876 (sourceLit (List.headD (raw_ints% [189533537150247809216204808257001045]) 0) 33 true) .empty .empty) (.node 878 (sourceLit (List.headD (raw_ints% [132143848371390129940052091951753195]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part114 : IntSourceTree :=
  (.node 871 (sourceLit (List.headD (raw_ints% [98937182046182668471151585916392272189905]) 0) 33 true) treeT_J015_part112 treeT_J015_part113)

#time def treeT_J015_part115 : IntSourceTree :=
  (.node 833 (sourceLit (List.headD (raw_ints% [371649479510605385033193116121009525]) 0) 32 true) treeT_J015_part111 treeT_J015_part114)

#time def treeT_J015_part116 : IntSourceTree :=
  (.node 914 (sourceLit (List.headD (raw_ints% [737172025263481123121018267029475292385275]) 0) 31 false) (.node 912 (sourceLit (List.headD (raw_ints% [3759605443969747584502603019771110237326315]) 0) 29 true) (.node 911 (sourceLit (List.headD (raw_ints% [1412933171941330283388532356843559245]) 0) 33 true) (.node 910 (sourceLit (List.headD (raw_ints% [371008028474740856999402626380339966029775]) 0) 32 false) .empty .empty) .empty) (.node 913 (sourceLit (List.headD (raw_ints% [1516510115738131658517495253681464915]) 0) 32 true) .empty .empty)) (.node 916 (sourceLit (List.headD (raw_ints% [651820178842958556898385257409209797817215]) 0) 30 true) (.node 915 (sourceLit (List.headD (raw_ints% [902112002456061295963822602287468025]) 0) 32 true) .empty .empty) (.node 917 (sourceLit (List.headD (raw_ints% [579878050850704546524353613332669895]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part117 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [307101033332705464307029590387056685]) 0) 35 true) (.node 952 (sourceLit (List.headD (raw_ints% [294228305633809538236174077654562485]) 0) 36 true) (.node 951 (sourceLit (List.headD (raw_ints% [14685787828778860170954819134272882444365]) 0) 38 false) (.node 919 (sourceLit (List.headD (raw_ints% [395906944778816536748093199818635125]) 0) 32 true) .empty .empty) .empty) (.node 953 (sourceLit (List.headD (raw_ints% [1105764857527567526522000257031306185122225]) 0) 32 true) .empty .empty)) (.node 956 (sourceLit (List.headD (raw_ints% [178144616326453371686904448507616745]) 0) 35 true) (.node 955 (sourceLit (List.headD (raw_ints% [407384893823154139503388320433738672464675]) 0) 33 false) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [170714617348743309051539264783840552352045]) 0) 33 true) .empty .empty)))

#time def treeT_J015_part118 : IntSourceTree :=
  (.node 918 (sourceLit (List.headD (raw_ints% [62076887157590323790641931854127424443355]) 0) 31 false) treeT_J015_part116 treeT_J015_part117)

#time def treeT_J015_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [2270435810372549400466117562789198025]) 0) 32 true) (.node 995 (sourceLit (List.headD (raw_ints% [4011504530867226132948650843905438935]) 0) 32 true) (.node 994 (sourceLit (List.headD (raw_ints% [5160231455373751229209019295154700032874175]) 0) 31 true) (.node 959 (sourceLit (List.headD (raw_ints% [7759638977867443814730779898504908615385]) 0) 35 false) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [7169978480013424788952598384349028557252015]) 0) 30 false) .empty .empty)) (.node 999 (sourceLit (List.headD (raw_ints% [1395029865138441129589112885705031675]) 0) 32 true) (.node 998 (sourceLit (List.headD (raw_ints% [1427793825947536796202956050124851843259715]) 0) 31 true) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [5975001243020059508215795936022177377803525]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [54969988424173900854678965872526447579680215]) 0) 30 true) (.node 1038 (sourceLit (List.headD (raw_ints% [1822701607893234983881816041408281325]) 0) 33 true) (.node 1037 (sourceLit (List.headD (raw_ints% [7852836949408398025158755443484390766660195]) 0) 31 false) .empty .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [1489870937770476346720802289312891112182795]) 0) 32 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [17133467724764332846520466937093633376580105]) 0) 31 false) (.node 1077 (sourceLit (List.headD (raw_ints% [10925268451873101184338014636710689795]) 0) 32 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [5895776566434498805938151279928093625]) 0) 32 true) .empty .empty)))

#time def treeT_J015_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [3298926065561412646201033049874971955]) 0) 33 true) treeT_J015_part119 treeT_J015_part120)

#time def treeT_J015_part122 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [111933550619828604146075380345229175]) 0) 35 true) treeT_J015_part118 treeT_J015_part121)

#time def treeT_J015_part123 : IntSourceTree :=
  (.node 879 (sourceLit (List.headD (raw_ints% [224665349226727204307333911844479725]) 0) 32 true) treeT_J015_part115 treeT_J015_part122)

#time def treeT_J015_part124 : IntSourceTree :=
  (.node 787 (sourceLit (List.headD (raw_ints% [10343341287404799328278073043886927500775]) 0) 33 false) treeT_J015_part108 treeT_J015_part123)

#time def treeT_J015_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [17974161483406811027369728193431395]) 0) 32 true) treeT_J015_part093 treeT_J015_part124)

#time def treeT_J015_part126 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [2798139018045149013188092884294375]) 0) 32 true) treeT_J015_part062 treeT_J015_part125)

#time def treeT_J015 : IntSourceTree := treeT_J015_part126

#time def treeT_J016_part000 : IntSourceTree :=
  (.node 9 (sourceLit (List.headD (raw_ints% [1491069120841698231904141410714375]) 0) 30 true) (.node 7 (sourceLit (List.headD (raw_ints% [418717814279587213040487514301625]) 0) 32 true) (.node 6 (sourceLit (List.headD (raw_ints% [224408215815114711649418147919375]) 0) 33 true) (.node 5 (sourceLit (List.headD (raw_ints% [972790645682750914557664697946375]) 0) 31 true) .empty .empty) .empty) (.node 8 (sourceLit (List.headD (raw_ints% [196916121974215839345556994713125]) 0) 33 true) .empty .empty)) (.node 11 (sourceLit (List.headD (raw_ints% [338731379196161866281778713427125]) 0) 32 true) (.node 10 (sourceLit (List.headD (raw_ints% [177304988447068722372861910520625]) 0) 33 true) .empty .empty) (.node 12 (sourceLit (List.headD (raw_ints% [162340503601152491084576821990275]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part001 : IntSourceTree :=
  (.node 18 (sourceLit (List.headD (raw_ints% [8269881674301303594290339461875]) 0) 37 true) (.node 16 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 33 true) (.node 15 (sourceLit (List.headD (raw_ints% [290548509490452466279400593093875]) 0) 32 true) (.node 14 (sourceLit (List.headD (raw_ints% [150406832101816407275204300879625]) 0) 33 true) .empty .empty) .empty) (.node 17 (sourceLit (List.headD (raw_ints% [57021463594381166597570297207468175]) 0) 29 false) .empty .empty)) (.node 20 (sourceLit (List.headD (raw_ints% [15653128861104416744748381320625]) 0) 36 true) (.node 19 (sourceLit (List.headD (raw_ints% [32160650955616180644462431240625]) 0) 35 true) .empty .empty) (.node 21 (sourceLit (List.headD (raw_ints% [122036370859250932689077442094125]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part002 : IntSourceTree :=
  (.node 13 (sourceLit (List.headD (raw_ints% [624251866721599573952303082148875]) 0) 31 true) treeT_J016_part000 treeT_J016_part001)

#time def treeT_J016_part003 : IntSourceTree :=
  (.node 27 (sourceLit (List.headD (raw_ints% [106552361437201741379330655938295]) 0) 33 true) (.node 25 (sourceLit (List.headD (raw_ints% [444515808273772027312041288141375]) 0) 31 true) (.node 24 (sourceLit (List.headD (raw_ints% [28403796103766521924599716513625]) 0) 35 true) (.node 23 (sourceLit (List.headD (raw_ints% [58125495925419150513750888047625]) 0) 34 true) .empty .empty) .empty) (.node 26 (sourceLit (List.headD (raw_ints% [54389329397996790984997859423775]) 0) 34 true) .empty .empty)) (.node 29 (sourceLit (List.headD (raw_ints% [204861834725042474999630343307575]) 0) 32 true) (.node 28 (sourceLit (List.headD (raw_ints% [52219773406488930555667086594225]) 0) 34 true) .empty .empty) (.node 30 (sourceLit (List.headD (raw_ints% [50259107503404967145335082319825]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [368643448634441341200958898754975]) 0) 31 true) (.node 33 (sourceLit (List.headD (raw_ints% [3049145184532669117685016637184775]) 0) 28 true) (.node 32 (sourceLit (List.headD (raw_ints% [48475953267825782609701347772215]) 0) 34 true) .empty .empty) (.node 34 (sourceLit (List.headD (raw_ints% [187380760642420659605881450435575]) 0) 32 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [714259145603615612578530790993155]) 0) 30 true) (.node 36 (sourceLit (List.headD (raw_ints% [181385717219051025012926312443725]) 0) 32 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [175851682841040923400671996140275]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part005 : IntSourceTree :=
  (.node 31 (sourceLit (List.headD (raw_ints% [98694075400156735597638896531175]) 0) 33 true) treeT_J016_part003 treeT_J016_part004)

#time def treeT_J016_part006 : IntSourceTree :=
  (.node 22 (sourceLit (List.headD (raw_ints% [29763007065683411722689232070325]) 0) 35 true) treeT_J016_part002 treeT_J016_part005)

#time def treeT_J016_part007 : IntSourceTree :=
  (.node 50 (sourceLit (List.headD (raw_ints% [1491069120841698231904141410714375]) 0) 31 true) (.node 48 (sourceLit (List.headD (raw_ints% [418717814279587213040487514301625]) 0) 33 true) (.node 47 (sourceLit (List.headD (raw_ints% [224408215815114711649418147919375]) 0) 34 true) (.node 46 (sourceLit (List.headD (raw_ints% [972790645682750914557664697946375]) 0) 32 true) .empty .empty) .empty) (.node 49 (sourceLit (List.headD (raw_ints% [196916121974215839345556994713125]) 0) 34 true) .empty .empty)) (.node 52 (sourceLit (List.headD (raw_ints% [338731379196161866281778713427125]) 0) 33 true) (.node 51 (sourceLit (List.headD (raw_ints% [177304988447068722372861910520625]) 0) 34 true) .empty .empty) (.node 53 (sourceLit (List.headD (raw_ints% [162340503601152491084576821990275]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part008 : IntSourceTree :=
  (.node 59 (sourceLit (List.headD (raw_ints% [8269881674301303594290339461875]) 0) 38 true) (.node 57 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 34 true) (.node 56 (sourceLit (List.headD (raw_ints% [290548509490452466279400593093875]) 0) 33 true) (.node 55 (sourceLit (List.headD (raw_ints% [150406832101816407275204300879625]) 0) 34 true) .empty .empty) .empty) (.node 58 (sourceLit (List.headD (raw_ints% [57021463594381166597570297207468175]) 0) 30 false) .empty .empty)) (.node 61 (sourceLit (List.headD (raw_ints% [15653128861104416744748381320625]) 0) 37 true) (.node 60 (sourceLit (List.headD (raw_ints% [32160650955616180644462431240625]) 0) 36 true) .empty .empty) (.node 62 (sourceLit (List.headD (raw_ints% [122036370859250932689077442094125]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part009 : IntSourceTree :=
  (.node 54 (sourceLit (List.headD (raw_ints% [624251866721599573952303082148875]) 0) 32 true) treeT_J016_part007 treeT_J016_part008)

#time def treeT_J016_part010 : IntSourceTree :=
  (.node 68 (sourceLit (List.headD (raw_ints% [106552361437201741379330655938295]) 0) 34 true) (.node 66 (sourceLit (List.headD (raw_ints% [444515808273772027312041288141375]) 0) 32 true) (.node 65 (sourceLit (List.headD (raw_ints% [28403796103766521924599716513625]) 0) 36 true) (.node 64 (sourceLit (List.headD (raw_ints% [58125495925419150513750888047625]) 0) 35 true) .empty .empty) .empty) (.node 67 (sourceLit (List.headD (raw_ints% [54389329397996790984997859423775]) 0) 35 true) .empty .empty)) (.node 70 (sourceLit (List.headD (raw_ints% [204861834725042474999630343307575]) 0) 33 true) (.node 69 (sourceLit (List.headD (raw_ints% [52219773406488930555667086594225]) 0) 35 true) .empty .empty) (.node 71 (sourceLit (List.headD (raw_ints% [50259107503404967145335082319825]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [368643448634441341200958898754975]) 0) 32 true) (.node 74 (sourceLit (List.headD (raw_ints% [3049145184532669117685016637184775]) 0) 29 true) (.node 73 (sourceLit (List.headD (raw_ints% [48475953267825782609701347772215]) 0) 35 true) .empty .empty) (.node 75 (sourceLit (List.headD (raw_ints% [187380760642420659605881450435575]) 0) 33 true) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [714259145603615612578530790993155]) 0) 31 true) (.node 77 (sourceLit (List.headD (raw_ints% [181385717219051025012926312443725]) 0) 33 true) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [175851682841040923400671996140275]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part012 : IntSourceTree :=
  (.node 72 (sourceLit (List.headD (raw_ints% [98694075400156735597638896531175]) 0) 34 true) treeT_J016_part010 treeT_J016_part011)

#time def treeT_J016_part013 : IntSourceTree :=
  (.node 63 (sourceLit (List.headD (raw_ints% [29763007065683411722689232070325]) 0) 36 true) treeT_J016_part009 treeT_J016_part012)

#time def treeT_J016_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [346479565880312358921124874610525]) 0) 31 true) treeT_J016_part006 treeT_J016_part013)

#time def treeT_J016_part015 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [546879450187122398406870820092225]) 0) 33 true) (.node 90 (sourceLit (List.headD (raw_ints% [610359499449794635009366068331875]) 0) 33 true) (.node 89 (sourceLit (List.headD (raw_ints% [5208415907631697176743658818111625]) 0) 30 true) (.node 88 (sourceLit (List.headD (raw_ints% [700716741286243007252115596964375]) 0) 33 true) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [576168870822768182811181348643625]) 0) 33 true) .empty .empty)) (.node 94 (sourceLit (List.headD (raw_ints% [498955182302793557063102987081475]) 0) 33 true) (.node 93 (sourceLit (List.headD (raw_ints% [2085599166847695356301926625268125]) 0) 31 true) .empty .empty) (.node 95 (sourceLit (List.headD (raw_ints% [957955223952746681625205571203875]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part016 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [392534044430607957622321457755875]) 0) 33 true) (.node 99 (sourceLit (List.headD (raw_ints% [57536034009671025487881696107318175]) 0) 31 false) (.node 98 (sourceLit (List.headD (raw_ints% [107508461765916946725774413004375]) 0) 35 true) (.node 97 (sourceLit (List.headD (raw_ints% [66319015898075645518511116186472175]) 0) 29 true) .empty .empty) .empty) (.node 100 (sourceLit (List.headD (raw_ints% [50505924533306012009574334374375]) 0) 36 true) .empty .empty)) (.node 103 (sourceLit (List.headD (raw_ints% [185947245793082714864403996140625]) 0) 34 true) (.node 102 (sourceLit (List.headD (raw_ints% [95462023823151922235297818494675]) 0) 35 true) .empty .empty) (.node 104 (sourceLit (List.headD (raw_ints% [90648232158967124966157211767675]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part017 : IntSourceTree :=
  (.node 96 (sourceLit (List.headD (raw_ints% [461039339944143467997881432666625]) 0) 33 true) treeT_J016_part015 treeT_J016_part016)

#time def treeT_J016_part018 : IntSourceTree :=
  (.node 110 (sourceLit (List.headD (raw_ints% [158619986122550755077333264057075]) 0) 34 true) (.node 108 (sourceLit (List.headD (raw_ints% [165337544185498233384324351100875]) 0) 34 true) (.node 107 (sourceLit (List.headD (raw_ints% [42245430854571285741588829025385]) 0) 36 true) (.node 106 (sourceLit (List.headD (raw_ints% [172841039432135384411799872685225]) 0) 34 true) .empty .empty) .empty) (.node 109 (sourceLit (List.headD (raw_ints% [647557056772571456035014904198785]) 0) 32 true) .empty .empty)) (.node 112 (sourceLit (List.headD (raw_ints% [152560476745794085971638981507085]) 0) 34 true) (.node 111 (sourceLit (List.headD (raw_ints% [311029594049928214401621790083975]) 0) 33 true) .empty .empty) (.node 113 (sourceLit (List.headD (raw_ints% [9583696466687393038812762118805625]) 0) 28 true) .empty .empty)))

#time def treeT_J016_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [549691186035163176651033253634625]) 0) 32 true) (.node 116 (sourceLit (List.headD (raw_ints% [568137325350631613410599489298575]) 0) 32 true) (.node 115 (sourceLit (List.headD (raw_ints% [2311858287263786435283098839674825]) 0) 30 true) .empty .empty) (.node 117 (sourceLit (List.headD (raw_ints% [2234888443471915117029140399046645]) 0) 30 true) .empty .empty)) (.node 128 (sourceLit (List.headD (raw_ints% [277036415701581850758588591822375]) 0) 35 true) (.node 119 (sourceLit (List.headD (raw_ints% [1082038725326918866235936707375785]) 0) 31 true) .empty .empty) (.node 129 (sourceLit (List.headD (raw_ints% [251900309656013583953279301125625]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part020 : IntSourceTree :=
  (.node 114 (sourceLit (List.headD (raw_ints% [588234491642791862149340113919865]) 0) 32 true) treeT_J016_part018 treeT_J016_part019)

#time def treeT_J016_part021 : IntSourceTree :=
  (.node 105 (sourceLit (List.headD (raw_ints% [1415500061339640789127987129382625]) 0) 31 true) treeT_J016_part017 treeT_J016_part020)

#time def treeT_J016_part022 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [174274175100488574893949343100925]) 0) 35 true) (.node 133 (sourceLit (List.headD (raw_ints% [192269473292984953661146999050975]) 0) 35 true) (.node 132 (sourceLit (List.headD (raw_ints% [813606362449374499340583983860125]) 0) 33 true) (.node 131 (sourceLit (List.headD (raw_ints% [216527255501362956318252078905625]) 0) 35 true) .empty .empty) .empty) (.node 134 (sourceLit (List.headD (raw_ints% [730673650063047891174811771559625]) 0) 33 true) .empty .empty)) (.node 137 (sourceLit (List.headD (raw_ints% [160225675740510653447472830907375]) 0) 35 true) (.node 136 (sourceLit (List.headD (raw_ints% [41712919653893388459112811131875]) 0) 37 true) .empty .empty) (.node 138 (sourceLit (List.headD (raw_ints% [61670239746228406058040706696970175]) 0) 31 true) .empty .empty)))

#time def treeT_J016_part023 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [32849508378734255256304293212175]) 0) 37 true) (.node 141 (sourceLit (List.headD (raw_ints% [17426397836100797632412976526875]) 0) 38 true) (.node 140 (sourceLit (List.headD (raw_ints% [58050604424960884378193095007168175]) 0) 32 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [135248836785678512466622007830875]) 0) 35 true) .empty .empty)) (.node 145 (sourceLit (List.headD (raw_ints% [31122218027600301520778747627025]) 0) 37 true) (.node 144 (sourceLit (List.headD (raw_ints% [15977718733457945543831638511625]) 0) 38 true) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [485492126532934380907972920620625]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part024 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [74428935068711732348613055156875]) 0) 36 true) treeT_J016_part022 treeT_J016_part023)

#time def treeT_J016_part025 : IntSourceTree :=
  (.node 152 (sourceLit (List.headD (raw_ints% [6635484957805358712624465423525]) 0) 39 true) (.node 150 (sourceLit (List.headD (raw_ints% [221347611023764490517692280445605]) 0) 34 true) (.node 149 (sourceLit (List.headD (raw_ints% [56558885389504651414328632253325]) 0) 36 true) (.node 148 (sourceLit (List.headD (raw_ints% [231411085399368544553379976264785]) 0) 34 true) .empty .empty) .empty) (.node 151 (sourceLit (List.headD (raw_ints% [54180439309572893965999090868625]) 0) 36 true) .empty .empty)) (.node 154 (sourceLit (List.headD (raw_ints% [3267275641077361960563872740810425]) 0) 30 true) (.node 153 (sourceLit (List.headD (raw_ints% [52042261738984151680968816867435]) 0) 36 true) .empty .empty) (.node 155 (sourceLit (List.headD (raw_ints% [200426865500185601271729331742145]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part026 : IntSourceTree :=
  (.node 169 (sourceLit (List.headD (raw_ints% [12521914697269541271806011058520375]) 0) 30 true) (.node 158 (sourceLit (List.headD (raw_ints% [760314648934149752225304804026745]) 0) 32 true) (.node 157 (sourceLit (List.headD (raw_ints% [193375804065790294198836588427425]) 0) 34 true) .empty .empty) (.node 159 (sourceLit (List.headD (raw_ints% [186919751597061126625180628747175]) 0) 34 true) .empty .empty)) (.node 171 (sourceLit (List.headD (raw_ints% [160313065321528911201072169381875]) 0) 36 true) (.node 170 (sourceLit (List.headD (raw_ints% [1404842977798314036616868340673125]) 0) 33 true) .empty .empty) (.node 172 (sourceLit (List.headD (raw_ints% [1185338593823781252139145811152775]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part027 : IntSourceTree :=
  (.node 156 (sourceLit (List.headD (raw_ints% [1574571389994903752881181042164875]) 0) 31 true) treeT_J016_part025 treeT_J016_part026)

#time def treeT_J016_part028 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [59225855017069296713401006630725]) 0) 36 true) treeT_J016_part024 treeT_J016_part027)

#time def treeT_J016_part029 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [1858673393394999472419758703698625]) 0) 32 true) treeT_J016_part021 treeT_J016_part028)

#time def treeT_J016_part030 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [1526863477085914616074841881591125]) 0) 32 true) treeT_J016_part014 treeT_J016_part029)

#time def treeT_J016_part031 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [212942889715104360169171248810375]) 0) 35 true) (.node 176 (sourceLit (List.headD (raw_ints% [933154060859765131153713312140775]) 0) 33 true) (.node 175 (sourceLit (List.headD (raw_ints% [1964739376299444883074041515034625]) 0) 32 true) (.node 174 (sourceLit (List.headD (raw_ints% [1039200604041086072226073005326325]) 0) 33 true) .empty .empty) .empty) (.node 177 (sourceLit (List.headD (raw_ints% [44962001035282230627445356886952175]) 0) 29 false) .empty .empty)) (.node 180 (sourceLit (List.headD (raw_ints% [98351945604117452687651775939375]) 0) 36 true) (.node 179 (sourceLit (List.headD (raw_ints% [180876513502127837603963109501258525]) 0) 31 true) .empty .empty) (.node 181 (sourceLit (List.headD (raw_ints% [29221569234695746167907708232462025]) 0) 34 false) .empty .empty)))

#time def treeT_J016_part032 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [316510403114649237941617604519085]) 0) 34 true) (.node 185 (sourceLit (List.headD (raw_ints% [2674795934425593270092912329593375]) 0) 31 true) (.node 184 (sourceLit (List.headD (raw_ints% [172147834870906917084277133929725]) 0) 35 true) (.node 183 (sourceLit (List.headD (raw_ints% [355048101349631335002084035182875]) 0) 34 true) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [325114449009469439920660089347175]) 0) 34 true) .empty .empty)) (.node 189 (sourceLit (List.headD (raw_ints% [1203731626422376900392024905919495]) 0) 32 true) (.node 188 (sourceLit (List.headD (raw_ints% [308469295951056140322883701944925]) 0) 34 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [293851096993486456237295793969525]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part033 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [183360341554460839883309805935325]) 0) 35 true) treeT_J016_part031 treeT_J016_part032)

#time def treeT_J016_part034 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [1035277598650853196763235164638585]) 0) 32 true) (.node 194 (sourceLit (List.headD (raw_ints% [1077117884004700991641662025838055]) 0) 32 true) (.node 193 (sourceLit (List.headD (raw_ints% [17595249920483356248097048255952775]) 0) 28 true) (.node 192 (sourceLit (List.headD (raw_ints% [280883037730789065756353745441915]) 0) 34 true) .empty .empty) .empty) (.node 195 (sourceLit (List.headD (raw_ints% [4222692994890937485844646641946025]) 0) 30 true) .empty .empty)) (.node 198 (sourceLit (List.headD (raw_ints% [997315246491159176939659453784775]) 0) 32 true) (.node 197 (sourceLit (List.headD (raw_ints% [4063397116507699894495583769612855]) 0) 30 true) .empty .empty) (.node 199 (sourceLit (List.headD (raw_ints% [1959219870409680142665282508731195]) 0) 31 true) .empty .empty)))

#time def treeT_J016_part035 : IntSourceTree :=
  (.node 214 (sourceLit (List.headD (raw_ints% [2961904432621204856073121702493625]) 0) 32 true) (.node 212 (sourceLit (List.headD (raw_ints% [1751402682695088079876570726249875]) 0) 33 true) (.node 211 (sourceLit (List.headD (raw_ints% [971788466795588123980364182861875]) 0) 34 true) .empty .empty) (.node 213 (sourceLit (List.headD (raw_ints% [800799647237811344816851813050825]) 0) 34 true) .empty .empty)) (.node 216 (sourceLit (List.headD (raw_ints% [1297332661837150667728236536924625]) 0) 33 true) (.node 215 (sourceLit (List.headD (raw_ints% [690652253840108922438174319124475]) 0) 34 true) .empty .empty) (.node 217 (sourceLit (List.headD (raw_ints% [612702709378743824258767650326025]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part036 : IntSourceTree :=
  (.node 210 (sourceLit (List.headD (raw_ints% [8804567910479542326966493651123125]) 0) 31 true) treeT_J016_part034 treeT_J016_part035)

#time def treeT_J016_part037 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [574360850045129747669147331698445]) 0) 33 true) treeT_J016_part033 treeT_J016_part036)

#time def treeT_J016_part038 : IntSourceTree :=
  (.node 223 (sourceLit (List.headD (raw_ints% [117661324796992329370701219510975]) 0) 36 true) (.node 221 (sourceLit (List.headD (raw_ints% [63499149931915857422825822885625]) 0) 37 true) (.node 220 (sourceLit (List.headD (raw_ints% [59731779481772180495539051127106675]) 0) 34 true) (.node 219 (sourceLit (List.headD (raw_ints% [34628488661598156955139548413375]) 0) 38 true) .empty .empty) .empty) (.node 222 (sourceLit (List.headD (raw_ints% [7339204517870356170093582560073225]) 0) 37 false) .empty .empty)) (.node 225 (sourceLit (List.headD (raw_ints% [109903398815706314042719638675675]) 0) 36 true) (.node 224 (sourceLit (List.headD (raw_ints% [227226351481967770651430927089875]) 0) 35 true) .empty .empty) (.node 226 (sourceLit (List.headD (raw_ints% [1703811681359724508276966488352125]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part039 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [185490218374340668305297612232275]) 0) 35 true) (.node 229 (sourceLit (List.headD (raw_ints% [195351525172046837494226437438275]) 0) 35 true) (.node 228 (sourceLit (List.headD (raw_ints% [401609720829929931329855232773385]) 0) 34 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [761036404374847919356640345028285]) 0) 33 true) .empty .empty)) (.node 233 (sourceLit (List.headD (raw_ints% [176798514252820762394416111707045]) 0) 35 true) (.node 232 (sourceLit (List.headD (raw_ints% [362025331395358268865164438145645]) 0) 34 true) .empty .empty) (.node 234 (sourceLit (List.headD (raw_ints% [11060698638328632326969302774331925]) 0) 29 true) .empty .empty)))

#time def treeT_J016_part040 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [206662738975330846493858076085725]) 0) 35 true) treeT_J016_part038 treeT_J016_part039)

#time def treeT_J016_part041 : IntSourceTree :=
  (.node 251 (sourceLit (List.headD (raw_ints% [6239558865335079747749338941013125]) 0) 32 true) (.node 238 (sourceLit (List.headD (raw_ints% [2542767818639400390044974161559365]) 0) 31 true) (.node 237 (sourceLit (List.headD (raw_ints% [648525990519272608365561987783735]) 0) 33 true) (.node 236 (sourceLit (List.headD (raw_ints% [1324060802448016866481732799890575]) 0) 32 true) .empty .empty) .empty) (.node 239 (sourceLit (List.headD (raw_ints% [623475743297036923689298196290425]) 0) 33 true) .empty .empty)) (.node 253 (sourceLit (List.headD (raw_ints% [9587969728813404000589820564386125]) 0) 31 true) (.node 252 (sourceLit (List.headD (raw_ints% [2701815273358571243782310920294725]) 0) 33 true) .empty .empty) (.node 254 (sourceLit (List.headD (raw_ints% [2163997984910159307041334246876975]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part042 : IntSourceTree :=
  (.node 259 (sourceLit (List.headD (raw_ints% [174589497014933440173744939891075525]) 0) 32 false) (.node 257 (sourceLit (List.headD (raw_ints% [86476646214071051994748926068540175]) 0) 29 true) (.node 256 (sourceLit (List.headD (raw_ints% [1829454954500670558598983964357125]) 0) 33 true) .empty .empty) (.node 258 (sourceLit (List.headD (raw_ints% [199879909831819732044798200757825]) 0) 36 true) .empty .empty)) (.node 261 (sourceLit (List.headD (raw_ints% [148685128198240107158985810486675375]) 0) 34 true) (.node 260 (sourceLit (List.headD (raw_ints% [178675963688667802953464611367625]) 0) 36 true) .empty .empty) (.node 262 (sourceLit (List.headD (raw_ints% [324632857900866019499296777149675]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part043 : IntSourceTree :=
  (.node 255 (sourceLit (List.headD (raw_ints% [3959069488942964829072201889952625]) 0) 32 true) treeT_J016_part041 treeT_J016_part042)

#time def treeT_J016_part044 : IntSourceTree :=
  (.node 235 (sourceLit (List.headD (raw_ints% [676264153004329789098203362353765]) 0) 33 true) treeT_J016_part040 treeT_J016_part043)

#time def treeT_J016_part045 : IntSourceTree :=
  (.node 218 (sourceLit (List.headD (raw_ints% [168302480527739042743526770280892525]) 0) 30 false) treeT_J016_part037 treeT_J016_part044)

#time def treeT_J016_part046 : IntSourceTree :=
  (.node 268 (sourceLit (List.headD (raw_ints% [518181659950267245652548602397975]) 0) 34 true) (.node 266 (sourceLit (List.headD (raw_ints% [554112741516181072421097020058225]) 0) 34 true) (.node 265 (sourceLit (List.headD (raw_ints% [4596447312997375390752877337282625]) 0) 31 true) (.node 264 (sourceLit (List.headD (raw_ints% [298497464317062400398527744114175]) 0) 35 true) .empty .empty) .empty) (.node 267 (sourceLit (List.headD (raw_ints% [1070790875130426032393731279313955]) 0) 33 true) .empty .empty)) (.node 270 (sourceLit (List.headD (raw_ints% [487555003694700893739609955783575]) 0) 34 true) (.node 269 (sourceLit (List.headD (raw_ints% [2009146140217062550246816956267585]) 0) 32 true) .empty .empty) (.node 271 (sourceLit (List.headD (raw_ints% [947711958704566091044133358358125]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part047 : IntSourceTree :=
  (.node 277 (sourceLit (List.headD (raw_ints% [6529089303076435037358278629511745]) 0) 30 true) (.node 275 (sourceLit (List.headD (raw_ints% [1709501410859423710281164033096475]) 0) 32 true) (.node 274 (sourceLit (List.headD (raw_ints% [1751658344040431206668995761474665]) 0) 32 true) (.node 273 (sourceLit (List.headD (raw_ints% [28743992498122502166643999826689785]) 0) 28 true) .empty .empty) .empty) (.node 276 (sourceLit (List.headD (raw_ints% [1669779013366465959629578284776475]) 0) 32 true) .empty .empty)) (.node 279 (sourceLit (List.headD (raw_ints% [3126315766869120637424665814387535]) 0) 31 true) (.node 278 (sourceLit (List.headD (raw_ints% [1596788715585931256522588497350165]) 0) 32 true) .empty .empty) (.node 292 (sourceLit (List.headD (raw_ints% [2244078091319995833936384107381625]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part048 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [461077835766573607464836703487185]) 0) 34 true) treeT_J016_part046 treeT_J016_part047)

#time def treeT_J016_part049 : IntSourceTree :=
  (.node 298 (sourceLit (List.headD (raw_ints% [63694781685452523684568924087358175]) 0) 32 true) (.node 296 (sourceLit (List.headD (raw_ints% [83179275847056692541998917282125]) 0) 38 true) (.node 295 (sourceLit (List.headD (raw_ints% [368336432767512596150789981938125]) 0) 36 true) (.node 294 (sourceLit (List.headD (raw_ints% [1656516324048049786129174715473125]) 0) 34 true) .empty .empty) .empty) (.node 297 (sourceLit (List.headD (raw_ints% [304188061280481683585054078507775]) 0) 36 true) .empty .empty)) (.node 300 (sourceLit (List.headD (raw_ints% [294053055978477801164823042145288875]) 0) 33 false) (.node 299 (sourceLit (List.headD (raw_ints% [130622932508623418134519103931075]) 0) 37 true) .empty .empty) (.node 301 (sourceLit (List.headD (raw_ints% [7198550859796996595664924280125]) 0) 41 true) .empty .empty)))

#time def treeT_J016_part050 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [723158907909412720618977712232625]) 0) 34 true) (.node 304 (sourceLit (List.headD (raw_ints% [59004773369378648913575417961722175]) 0) 36 false) (.node 303 (sourceLit (List.headD (raw_ints% [51742883275968422532148889409675]) 0) 38 true) .empty .empty) (.node 305 (sourceLit (List.headD (raw_ints% [47148516375339021588952026359625]) 0) 38 true) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [334590577150248050531938023270285]) 0) 35 true) (.node 307 (sourceLit (List.headD (raw_ints% [86862500635212556481809735993125]) 0) 37 true) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [80707533694555102039580541239925]) 0) 37 true) .empty .empty)))

#time def treeT_J016_part051 : IntSourceTree :=
  (.node 302 (sourceLit (List.headD (raw_ints% [178041946269721531839360140726968275]) 0) 35 true) treeT_J016_part049 treeT_J016_part050)

#time def treeT_J016_part052 : IntSourceTree :=
  (.node 293 (sourceLit (List.headD (raw_ints% [475253906530189974741364776810975]) 0) 36 true) treeT_J016_part048 treeT_J016_part051)

#time def treeT_J016_part053 : IntSourceTree :=
  (.node 315 (sourceLit (List.headD (raw_ints% [268848547759025354392698099780225]) 0) 35 true) (.node 313 (sourceLit (List.headD (raw_ints% [71069830378438211267605147945035]) 0) 37 true) (.node 312 (sourceLit (List.headD (raw_ints% [571959596981648263846649336145]) 0) 44 true) (.node 311 (sourceLit (List.headD (raw_ints% [75516196330090056358578085887825]) 0) 37 true) .empty .empty) .empty) (.node 314 (sourceLit (List.headD (raw_ints% [4420823464948467459918674263089465]) 0) 31 true) .empty .empty)) (.node 317 (sourceLit (List.headD (raw_ints% [255313255711798337816004074248185]) 0) 35 true) (.node 316 (sourceLit (List.headD (raw_ints% [2094942019270830554080595266302375]) 0) 32 true) .empty .empty) (.node 318 (sourceLit (List.headD (raw_ints% [996580371109258661828326116988095]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part054 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [4063927969779530979813655746652875]) 0) 33 true) (.node 334 (sourceLit (List.headD (raw_ints% [5440064519572880288820502182098625]) 0) 33 true) (.node 333 (sourceLit (List.headD (raw_ints% [26317279732306529342392325153719875]) 0) 31 true) .empty .empty) (.node 335 (sourceLit (List.headD (raw_ints% [9293061103441433459961195833832375]) 0) 32 true) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [408496212729143635125309956257725]) 0) 36 true) (.node 337 (sourceLit (List.headD (raw_ints% [1301067746684998831742034771644175]) 0) 29 false) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [301979060385838487542882788065791875]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part055 : IntSourceTree :=
  (.node 319 (sourceLit (List.headD (raw_ints% [243328243072223583208322575264935]) 0) 35 true) treeT_J016_part053 treeT_J016_part054)

#time def treeT_J016_part056 : IntSourceTree :=
  (.node 345 (sourceLit (List.headD (raw_ints% [3780901942953230905859579626887501825]) 0) 31 false) (.node 343 (sourceLit (List.headD (raw_ints% [829950105466161457413939967904227575]) 0) 34 true) (.node 342 (sourceLit (List.headD (raw_ints% [596781652153149544745813530706325]) 0) 35 true) (.node 341 (sourceLit (List.headD (raw_ints% [221369092088358954161904426315982125]) 0) 35 false) .empty .empty) .empty) (.node 344 (sourceLit (List.headD (raw_ints% [529388668098432360115854486440625]) 0) 35 true) .empty .empty)) (.node 347 (sourceLit (List.headD (raw_ints% [1821844756507224850082179569616545]) 0) 33 true) (.node 346 (sourceLit (List.headD (raw_ints% [954639782494667618425367823449775]) 0) 34 true) .empty .empty) (.node 348 (sourceLit (List.headD (raw_ints% [871618350213133658056407173492025]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part057 : IntSourceTree :=
  (.node 353 (sourceLit (List.headD (raw_ints% [46223895797456099072264021960507655]) 0) 28 true) (.node 351 (sourceLit (List.headD (raw_ints% [1548507512979863170736219864120475]) 0) 33 true) (.node 350 (sourceLit (List.headD (raw_ints% [803765535418180738893678704055225]) 0) 34 true) .empty .empty) (.node 352 (sourceLit (List.headD (raw_ints% [747181305514867294272412670718015]) 0) 34 true) .empty .empty)) (.node 355 (sourceLit (List.headD (raw_ints% [1355661027044521874818755114996495]) 0) 33 true) (.node 354 (sourceLit (List.headD (raw_ints% [2796810800179614314457733707007575]) 0) 32 true) .empty .empty) (.node 356 (sourceLit (List.headD (raw_ints% [2631797750777939710653591311707125]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part058 : IntSourceTree :=
  (.node 349 (sourceLit (List.headD (raw_ints% [3344303094186906258264191416056975]) 0) 32 true) treeT_J016_part056 treeT_J016_part057)

#time def treeT_J016_part059 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [343815766345825869584611804356675]) 0) 36 true) treeT_J016_part055 treeT_J016_part058)

#time def treeT_J016_part060 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [312027433960553657722544152809825]) 0) 35 true) treeT_J016_part052 treeT_J016_part059)

#time def treeT_J016_part061 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [117782320387275330056499404996354475]) 0) 34 false) treeT_J016_part045 treeT_J016_part060)

#time def treeT_J016_part062 : IntSourceTree :=
  (.node 173 (sourceLit (List.headD (raw_ints% [4423251732747300638422745245612875]) 0) 31 true) treeT_J016_part030 treeT_J016_part061)

#time def treeT_J016_part063 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [6631324276335619298617230480804375]) 0) 33 true) (.node 374 (sourceLit (List.headD (raw_ints% [19691214436114330197875626291827375]) 0) 32 true) (.node 359 (sourceLit (List.headD (raw_ints% [4846327202004948657201943121517225]) 0) 31 true) (.node 358 (sourceLit (List.headD (raw_ints% [2488223375802842148533476690620795]) 0) 32 true) .empty .empty) .empty) (.node 375 (sourceLit (List.headD (raw_ints% [3966718788502829904217342254346125]) 0) 34 true) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [256080194488495093570017731121076875]) 0) 30 false) (.node 377 (sourceLit (List.headD (raw_ints% [2847175724657604245473439432621775]) 0) 34 true) .empty .empty) (.node 379 (sourceLit (List.headD (raw_ints% [138936640110260108495395426163325]) 0) 38 true) .empty .empty)))

#time def treeT_J016_part064 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [340794602597076273760046381002125]) 0) 36 true) (.node 383 (sourceLit (List.headD (raw_ints% [389810119049275854617217973067625]) 0) 36 true) (.node 382 (sourceLit (List.headD (raw_ints% [620780130446439440163168993358932525]) 0) 35 false) (.node 381 (sourceLit (List.headD (raw_ints% [228638952589073924053973015874675]) 0) 37 true) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [947959652204918755241090803827671925]) 0) 35 true) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [607189779953817392498128879477275]) 0) 35 true) (.node 386 (sourceLit (List.headD (raw_ints% [3783794578584868556742055537736432325]) 0) 32 false) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [1152663602206728749018303523075975]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part065 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [298016058182158144353852915105540375]) 0) 34 true) treeT_J016_part063 treeT_J016_part064)

#time def treeT_J016_part066 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [28540601937662229232589324908149795]) 0) 29 true) (.node 392 (sourceLit (List.headD (raw_ints% [962820885670655348557250943907995]) 0) 34 true) (.node 391 (sourceLit (List.headD (raw_ints% [501700750097820513459366360503925]) 0) 35 true) (.node 390 (sourceLit (List.headD (raw_ints% [2096193358344691627374014804817675]) 0) 33 true) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [462901984001114449201992078937875]) 0) 35 true) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [3327702088907256945194425193683605]) 0) 32 true) (.node 395 (sourceLit (List.headD (raw_ints% [1721416609143512896886941307886675]) 0) 33 true) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [1610544727930746359389575014714385]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part067 : IntSourceTree :=
  (.node 417 (sourceLit (List.headD (raw_ints% [213503444589424816387493410157384175]) 0) 29 true) (.node 415 (sourceLit (List.headD (raw_ints% [30089367768787226935790056749822375]) 0) 32 true) (.node 399 (sourceLit (List.headD (raw_ints% [1514910403513947815700186389561055]) 0) 33 true) .empty .empty) (.node 416 (sourceLit (List.headD (raw_ints% [11802947184231788637055713270731625]) 0) 33 true) .empty .empty)) (.node 419 (sourceLit (List.headD (raw_ints% [860038315260172068655783307252660625]) 0) 31 false) (.node 418 (sourceLit (List.headD (raw_ints% [2030183299199316975222819520106325]) 0) 35 true) .empty .empty) (.node 420 (sourceLit (List.headD (raw_ints% [767677354536254998378551604949925]) 0) 36 true) .empty .empty)))

#time def treeT_J016_part068 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [6244125366653174747973179032954875]) 0) 31 true) treeT_J016_part066 treeT_J016_part067)

#time def treeT_J016_part069 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [548788215434913249898085008532325]) 0) 35 true) treeT_J016_part065 treeT_J016_part068)

#time def treeT_J016_part070 : IntSourceTree :=
  (.node 426 (sourceLit (List.headD (raw_ints% [1771717038281942571655003224567225]) 0) 34 true) (.node 424 (sourceLit (List.headD (raw_ints% [1029851808098671058353017405829875]) 0) 35 true) (.node 423 (sourceLit (List.headD (raw_ints% [3313070627251919218066615941339957675]) 0) 34 false) (.node 422 (sourceLit (List.headD (raw_ints% [1232329968559441847685970596291075]) 0) 35 true) .empty .empty) .empty) (.node 425 (sourceLit (List.headD (raw_ints% [34115610813510631073574485349373003425]) 0) 31 true) .empty .empty)) (.node 428 (sourceLit (List.headD (raw_ints% [1557140769602135911936108344417075]) 0) 34 true) (.node 427 (sourceLit (List.headD (raw_ints% [1892808211670687890796068858653024435]) 0) 34 false) .empty .empty) (.node 429 (sourceLit (List.headD (raw_ints% [5877005723466923733882236768550825]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part071 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [17695313721306054234039283988177835]) 0) 30 true) (.node 433 (sourceLit (List.headD (raw_ints% [77017177568387785543064098859715705]) 0) 28 true) (.node 432 (sourceLit (List.headD (raw_ints% [1259621694876414759565052771297685]) 0) 34 true) (.node 431 (sourceLit (List.headD (raw_ints% [2643879203709520084011809745514875]) 0) 33 true) .empty .empty) .empty) (.node 434 (sourceLit (List.headD (raw_ints% [4609620943838216872774139555998425]) 0) 32 true) .empty .empty)) (.node 437 (sourceLit (List.headD (raw_ints% [16391169860167846166268918048561585]) 0) 30 true) (.node 436 (sourceLit (List.headD (raw_ints% [4253868685796111876894173919839575]) 0) 32 true) .empty .empty) (.node 438 (sourceLit (List.headD (raw_ints% [3953955535920143289024823368236745]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part072 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [1391387326321472260698661330074075]) 0) 34 true) treeT_J016_part070 treeT_J016_part071)

#time def treeT_J016_part073 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [2052102547988804646071194967674822125]) 0) 32 false) (.node 458 (sourceLit (List.headD (raw_ints% [234791819538959954978755570639230525]) 0) 31 true) (.node 457 (sourceLit (List.headD (raw_ints% [4477885729787092195791136919054925]) 0) 35 true) (.node 456 (sourceLit (List.headD (raw_ints% [1466127718278225477323301641813625]) 0) 37 true) .empty .empty) .empty) (.node 459 (sourceLit (List.headD (raw_ints% [1474436738758276541241237815453025]) 0) 36 true) .empty .empty)) (.node 462 (sourceLit (List.headD (raw_ints% [1659550430987473637194683676201977525]) 0) 35 true) (.node 461 (sourceLit (List.headD (raw_ints% [269519200973590537162289294537625]) 0) 38 true) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [421259924755082996534376311611725]) 0) 37 true) .empty .empty)))

#time def treeT_J016_part074 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [3786769086943582510341156020829124845]) 0) 34 false) (.node 466 (sourceLit (List.headD (raw_ints% [18949702696047749815158270443554717875]) 0) 33 true) (.node 465 (sourceLit (List.headD (raw_ints% [344528602750797392296485512413875]) 0) 37 true) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [582263629164062589578437172544975]) 0) 36 true) .empty .empty)) (.node 470 (sourceLit (List.headD (raw_ints% [1890406182561116053254110981866575]) 0) 34 true) (.node 469 (sourceLit (List.headD (raw_ints% [504176277083611331019011667942375]) 0) 36 true) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [444843288111825873619647484785075]) 0) 36 true) .empty .empty)))

#time def treeT_J016_part075 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [133157196233026186665865835786488425]) 0) 40 false) treeT_J016_part073 treeT_J016_part074)

#time def treeT_J016_part076 : IntSourceTree :=
  (.node 439 (sourceLit (List.headD (raw_ints% [7641923531301400838744414944392525]) 0) 31 true) treeT_J016_part072 treeT_J016_part075)

#time def treeT_J016_part077 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [129846287567629274628939335355380625]) 0) 37 true) treeT_J016_part069 treeT_J016_part076)

#time def treeT_J016_part078 : IntSourceTree :=
  (.node 477 (sourceLit (List.headD (raw_ints% [1321661978932682758752299452562595]) 0) 34 true) (.node 475 (sourceLit (List.headD (raw_ints% [1444102167347351987943599124055875]) 0) 34 true) (.node 474 (sourceLit (List.headD (raw_ints% [24238287815362778155237386975782955]) 0) 30 true) (.node 473 (sourceLit (List.headD (raw_ints% [398359855437650155181530346179905]) 0) 36 true) .empty .empty) .empty) (.node 476 (sourceLit (List.headD (raw_ints% [11039909543491540343650433600810625]) 0) 31 true) .empty .empty)) (.node 479 (sourceLit (List.headD (raw_ints% [1219522566203097736662318489337845]) 0) 34 true) (.node 478 (sourceLit (List.headD (raw_ints% [5073522246757335709147869507803355]) 0) 32 true) .empty .empty) (.node 497 (sourceLit (List.headD (raw_ints% [537153947169026628002037030451191825]) 0) 29 true) .empty .empty)))

#time def treeT_J016_part079 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [9951272351201813766845350646147867775]) 0) 34 true) (.node 501 (sourceLit (List.headD (raw_ints% [4129643149070873040134224333360912125]) 0) 33 false) (.node 500 (sourceLit (List.headD (raw_ints% [2181196122980298084103924025956125]) 0) 36 true) (.node 499 (sourceLit (List.headD (raw_ints% [1329621954338091978613294448531121675]) 0) 31 true) .empty .empty) .empty) (.node 502 (sourceLit (List.headD (raw_ints% [3079977247018006746910658116310925]) 0) 35 true) .empty .empty)) (.node 505 (sourceLit (List.headD (raw_ints% [170468579756129446219421101194737150625]) 0) 31 false) (.node 504 (sourceLit (List.headD (raw_ints% [2340227589941992913921993087063925]) 0) 35 true) .empty .empty) (.node 506 (sourceLit (List.headD (raw_ints% [3740740605730815705088764974054775]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part080 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [6925588160374867416359454318003525]) 0) 35 true) treeT_J016_part078 treeT_J016_part079)

#time def treeT_J016_part081 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [2299124610018192229392127106982915]) 0) 34 true) (.node 510 (sourceLit (List.headD (raw_ints% [2642022890347418387453432013464925]) 0) 34 true) (.node 509 (sourceLit (List.headD (raw_ints% [30300029701272127006463130403401549585]) 0) 32 false) (.node 508 (sourceLit (List.headD (raw_ints% [3100968263710364804691389035942725]) 0) 34 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [4917745526534944129004634181951425]) 0) 33 true) .empty .empty)) (.node 514 (sourceLit (List.headD (raw_ints% [8137894430166588093034831521758535]) 0) 32 true) (.node 513 (sourceLit (List.headD (raw_ints% [138158287140586900595119427745964935]) 0) 28 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [30781261909419502076435489963388075]) 0) 30 true) .empty .empty)))

#time def treeT_J016_part082 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [67570308091106718044525889172730775]) 0) 30 true) (.node 518 (sourceLit (List.headD (raw_ints% [6619340295541318780993572252264015]) 0) 32 true) (.node 517 (sourceLit (List.headD (raw_ints% [27768468313798315208332816354680915]) 0) 30 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [12652165455727941997847063086820895]) 0) 31 true) .empty .empty)) (.node 540 (sourceLit (List.headD (raw_ints% [422715562790862078085561177025742975]) 0) 35 true) (.node 539 (sourceLit (List.headD (raw_ints% [1362787855404147718779554125637625]) 0) 38 true) .empty .empty) (.node 541 (sourceLit (List.headD (raw_ints% [1642157721033117009779345436880875]) 0) 37 true) .empty .empty)))

#time def treeT_J016_part083 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [7298948652982704026654619072607425]) 0) 32 true) treeT_J016_part081 treeT_J016_part082)

#time def treeT_J016_part084 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [10421255453859218852977169651103871155]) 0) 35 true) treeT_J016_part080 treeT_J016_part083)

#time def treeT_J016_part085 : IntSourceTree :=
  (.node 547 (sourceLit (List.headD (raw_ints% [2576213347402690525931890628964825]) 0) 35 true) (.node 545 (sourceLit (List.headD (raw_ints% [1651170384440398129329022062236175]) 0) 36 true) (.node 544 (sourceLit (List.headD (raw_ints% [14212302630658651740153057391315497375]) 0) 35 true) (.node 543 (sourceLit (List.headD (raw_ints% [2237457397507840753841905493087475]) 0) 36 true) .empty .empty) .empty) (.node 546 (sourceLit (List.headD (raw_ints% [208367985148224945849737642081846586375]) 0) 32 false) .empty .empty)) (.node 549 (sourceLit (List.headD (raw_ints% [2092615709543142142653365700057975]) 0) 35 true) (.node 548 (sourceLit (List.headD (raw_ints% [45471790902380457922249834625244609465]) 0) 34 true) .empty .empty) (.node 550 (sourceLit (List.headD (raw_ints% [30303810513637249238569638625365282735]) 0) 33 false) .empty .empty)))

#time def treeT_J016_part086 : IntSourceTree :=
  (.node 555 (sourceLit (List.headD (raw_ints% [5249690095471884117147633273646785]) 0) 33 true) (.node 553 (sourceLit (List.headD (raw_ints% [1502404899142891919029066414623105]) 0) 35 true) (.node 552 (sourceLit (List.headD (raw_ints% [3236687208496079393550075380344545]) 0) 34 true) .empty .empty) (.node 554 (sourceLit (List.headD (raw_ints% [89681711509861344284644653794399025]) 0) 29 true) .empty .empty)) (.node 557 (sourceLit (List.headD (raw_ints% [4655624695117338509150020167482235]) 0) 33 true) (.node 556 (sourceLit (List.headD (raw_ints% [9870676182963980866392528181288725]) 0) 32 true) .empty .empty) (.node 558 (sourceLit (List.headD (raw_ints% [17621423820283643790037077339074205]) 0) 31 true) .empty .empty)))

#time def treeT_J016_part087 : IntSourceTree :=
  (.node 551 (sourceLit (List.headD (raw_ints% [1752336314123766640214137043894775]) 0) 35 true) treeT_J016_part085 treeT_J016_part086)

#time def treeT_J016_part088 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [6609602000089370101445628885285975]) 0) 35 true) (.node 582 (sourceLit (List.headD (raw_ints% [10057284521246929331324105378736075]) 0) 35 true) (.node 581 (sourceLit (List.headD (raw_ints% [7511367651397769664818713749566855925]) 0) 33 true) (.node 580 (sourceLit (List.headD (raw_ints% [8721106720252883666132508979144875]) 0) 36 true) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [24848760373293454395892534017677602125]) 0) 34 false) .empty .empty)) (.node 586 (sourceLit (List.headD (raw_ints% [9468622469792369329543411523834625]) 0) 34 true) (.node 585 (sourceLit (List.headD (raw_ints% [625262263937206301904318937716833066625]) 0) 31 true) .empty .empty) (.node 587 (sourceLit (List.headD (raw_ints% [250053006963661821261646320686262070995]) 0) 33 false) .empty .empty)))

#time def treeT_J016_part089 : IntSourceTree :=
  (.node 592 (sourceLit (List.headD (raw_ints% [4710220646476874331464421068596185]) 0) 34 true) (.node 590 (sourceLit (List.headD (raw_ints% [5728439947825150183160030786766975]) 0) 34 true) (.node 589 (sourceLit (List.headD (raw_ints% [394074356920315790384461807405358425305]) 0) 32 true) .empty .empty) (.node 591 (sourceLit (List.headD (raw_ints% [60612538772801033421268281884912516895]) 0) 33 false) .empty .empty)) (.node 594 (sourceLit (List.headD (raw_ints% [15900583956119682611430231112211145]) 0) 32 true) (.node 593 (sourceLit (List.headD (raw_ints% [276137675546911261779290220938136825]) 0) 28 true) .empty .empty) (.node 595 (sourceLit (List.headD (raw_ints% [29450224800220921104104581915505475]) 0) 31 true) .empty .empty)))

#time def treeT_J016_part090 : IntSourceTree :=
  (.node 588 (sourceLit (List.headD (raw_ints% [7203885125900397299036173479916575]) 0) 34 true) treeT_J016_part088 treeT_J016_part089)

#time def treeT_J016_part091 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [4180295163135123307668935273588325]) 0) 33 true) treeT_J016_part087 treeT_J016_part090)

#time def treeT_J016_part092 : IntSourceTree :=
  (.node 542 (sourceLit (List.headD (raw_ints% [7448744011045820314523591685764867175]) 0) 34 false) treeT_J016_part084 treeT_J016_part091)

#time def treeT_J016_part093 : IntSourceTree :=
  (.node 472 (sourceLit (List.headD (raw_ints% [52533072438714522982954962550215]) 0) 39 true) treeT_J016_part077 treeT_J016_part092)

#time def treeT_J016_part094 : IntSourceTree :=
  (.node 623 (sourceLit (List.headD (raw_ints% [977478390467386072185274985706075]) 0) 39 true) (.node 599 (sourceLit (List.headD (raw_ints% [22590682184839345582227091591327515]) 0) 31 true) (.node 598 (sourceLit (List.headD (raw_ints% [12003158484928035255606508417664925]) 0) 32 true) (.node 597 (sourceLit (List.headD (raw_ints% [51196941149913531722807409095628885]) 0) 30 true) .empty .empty) .empty) (.node 622 (sourceLit (List.headD (raw_ints% [3740027915610897494835576358832930775]) 0) 36 true) .empty .empty)) (.node 625 (sourceLit (List.headD (raw_ints% [619803951956121496514575852881225]) 0) 39 true) (.node 624 (sourceLit (List.headD (raw_ints% [9765265750988026534011397852248274875]) 0) 37 false) .empty .empty) (.node 626 (sourceLit (List.headD (raw_ints% [104203781135678905969257072474834956625]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part095 : IntSourceTree :=
  (.node 632 (sourceLit (List.headD (raw_ints% [118390186445331112305980140547446995]) 0) 43 false) (.node 630 (sourceLit (List.headD (raw_ints% [53047270929244129952878930753840463505]) 0) 36 true) (.node 629 (sourceLit (List.headD (raw_ints% [638908677044656894547850972482325]) 0) 38 true) (.node 628 (sourceLit (List.headD (raw_ints% [73881199466510569795974038827876670115]) 0) 36 false) .empty .empty) .empty) (.node 631 (sourceLit (List.headD (raw_ints% [497012954212672942868236717859025]) 0) 38 true) .empty .empty)) (.node 634 (sourceLit (List.headD (raw_ints% [23306995504631239686830695892967225]) 0) 32 true) (.node 633 (sourceLit (List.headD (raw_ints% [400976968416747801554419331746635]) 0) 38 true) .empty .empty) (.node 635 (sourceLit (List.headD (raw_ints% [1331361732580974811785324729820545]) 0) 36 true) .empty .empty)))

#time def treeT_J016_part096 : IntSourceTree :=
  (.node 627 (sourceLit (List.headD (raw_ints% [861551140298709850451440111858725]) 0) 38 true) treeT_J016_part094 treeT_J016_part095)

#time def treeT_J016_part097 : IntSourceTree :=
  (.node 664 (sourceLit (List.headD (raw_ints% [24669706494866984208483170657308425]) 0) 35 true) (.node 639 (sourceLit (List.headD (raw_ints% [977857915224113993492196643009575]) 0) 36 true) (.node 638 (sourceLit (List.headD (raw_ints% [4196939666203735991596291469569335]) 0) 34 true) (.node 637 (sourceLit (List.headD (raw_ints% [1130523379223436741598236731812185]) 0) 36 true) .empty .empty) .empty) (.node 663 (sourceLit (List.headD (raw_ints% [54768983698180634354577144888341048325]) 0) 34 true) .empty .empty)) (.node 666 (sourceLit (List.headD (raw_ints% [30198830455399406447389443060563775]) 0) 34 true) (.node 665 (sourceLit (List.headD (raw_ints% [1875216280063673698257777862804612250625]) 0) 31 false) .empty .empty) (.node 667 (sourceLit (List.headD (raw_ints% [1083683256049093069015702900484941723995]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part098 : IntSourceTree :=
  (.node 672 (sourceLit (List.headD (raw_ints% [11194193888328659840319153902892615]) 0) 34 true) (.node 670 (sourceLit (List.headD (raw_ints% [14716637717603870442371200332667425]) 0) 34 true) (.node 669 (sourceLit (List.headD (raw_ints% [2758272739848654023855631049897411868985]) 0) 32 false) .empty .empty) (.node 671 (sourceLit (List.headD (raw_ints% [909368873640707112667331173946359932975]) 0) 33 true) .empty .empty)) (.node 674 (sourceLit (List.headD (raw_ints% [35424468001224035987535443351358135]) 0) 32 true) (.node 673 (sourceLit (List.headD (raw_ints% [7759095396556766687346493781138424401145]) 0) 28 false) .empty .empty) (.node 675 (sourceLit (List.headD (raw_ints% [63777757218304037643218201656363425]) 0) 31 true) .empty .empty)))

#time def treeT_J016_part099 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [20365751363658317915409910099562625]) 0) 34 true) treeT_J016_part097 treeT_J016_part098)

#time def treeT_J016_part100 : IntSourceTree :=
  (.node 636 (sourceLit (List.headD (raw_ints% [9789774308628470118856026867108375]) 0) 33 true) treeT_J016_part096 treeT_J016_part099)

#time def treeT_J016_part101 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [2708846529149104946011834442603291903625]) 0) 32 false) (.node 679 (sourceLit (List.headD (raw_ints% [44560352474420430283313571921781845]) 0) 31 true) (.node 678 (sourceLit (List.headD (raw_ints% [24173589650221940475537067000324995]) 0) 32 true) (.node 677 (sourceLit (List.headD (raw_ints% [105439447788141990178889020778105115]) 0) 30 true) .empty .empty) .empty) (.node 705 (sourceLit (List.headD (raw_ints% [19711274879218012236366563834258625]) 0) 36 true) .empty .empty)) (.node 708 (sourceLit (List.headD (raw_ints% [1379208053915135348199599055796448404455]) 0) 34 true) (.node 707 (sourceLit (List.headD (raw_ints% [23306421333009727643777922165693975]) 0) 35 true) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [15254481947301062759027102319704025]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part102 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [7759281852520803737263988426705568138945]) 0) 29 false) (.node 712 (sourceLit (List.headD (raw_ints% [969984649100716642167993005906652794415]) 0) 34 true) (.node 711 (sourceLit (List.headD (raw_ints% [10740534083902486899425306589795225]) 0) 35 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [7986378140994677427883799248919535]) 0) 35 true) .empty .empty)) (.node 716 (sourceLit (List.headD (raw_ints% [44198208601047097405506147922146675]) 0) 32 true) (.node 715 (sourceLit (List.headD (raw_ints% [24773574140576237493252845512793775]) 0) 33 true) .empty .empty) (.node 717 (sourceLit (List.headD (raw_ints% [19859576679898867602408583477780245]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part103 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [3182650907282607063478662495928135577025]) 0) 33 false) treeT_J016_part101 treeT_J016_part102)

#time def treeT_J016_part104 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [13791937171169736809452423496268999104625]) 0) 32 true) (.node 747 (sourceLit (List.headD (raw_ints% [948132446299549503756884335772058406905]) 0) 35 false) (.node 746 (sourceLit (List.headD (raw_ints% [127491368578344691443543067613505225]) 0) 34 true) (.node 719 (sourceLit (List.headD (raw_ints% [16350726328429028527599493856248395]) 0) 33 true) .empty .empty) .empty) (.node 748 (sourceLit (List.headD (raw_ints% [72859933968380592659701778563213275]) 0) 34 true) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [7274670688205921239624656165802631087025]) 0) 33 false) (.node 750 (sourceLit (List.headD (raw_ints% [46301290071600380593737208946148675]) 0) 34 true) .empty .empty) (.node 752 (sourceLit (List.headD (raw_ints% [31767942447281287757382072456288285]) 0) 34 true) .empty .empty)))

#time def treeT_J016_part105 : IntSourceTree :=
  (.node 757 (sourceLit (List.headD (raw_ints% [248146221020234789065160162599068285]) 0) 30 true) (.node 755 (sourceLit (List.headD (raw_ints% [7759409408035240345339274863108880865795]) 0) 30 false) (.node 754 (sourceLit (List.headD (raw_ints% [92357582254690802858605344631354425]) 0) 32 true) .empty .empty) (.node 756 (sourceLit (List.headD (raw_ints% [70190532848618588437816904718897375]) 0) 32 true) .empty .empty)) (.node 759 (sourceLit (List.headD (raw_ints% [99167508442603774208923806121319025]) 0) 31 true) (.node 758 (sourceLit (List.headD (raw_ints% [55264717069373529934097266910795985]) 0) 32 true) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [52092473622667481899882572723905625]) 0) 36 true) .empty .empty)))

#time def treeT_J016_part106 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [131917130481448496884849598537189982086265]) 0) 28 true) treeT_J016_part104 treeT_J016_part105)

#time def treeT_J016_part107 : IntSourceTree :=
  (.node 718 (sourceLit (List.headD (raw_ints% [71863930458512102246118689021550435]) 0) 31 true) treeT_J016_part103 treeT_J016_part106)

#time def treeT_J016_part108 : IntSourceTree :=
  (.node 676 (sourceLit (List.headD (raw_ints% [28903763713686361535194477332277725]) 0) 32 true) treeT_J016_part100 treeT_J016_part107)

#time def treeT_J016_part109 : IntSourceTree :=
  (.node 793 (sourceLit (List.headD (raw_ints% [11890782153143305164749136603684375]) 0) 36 true) (.node 791 (sourceLit (List.headD (raw_ints% [17780377993848946847155951178176725]) 0) 36 true) (.node 790 (sourceLit (List.headD (raw_ints% [8487294039226171936465542996098567340825]) 0) 34 true) (.node 789 (sourceLit (List.headD (raw_ints% [28802726010539764950337338121754625]) 0) 36 true) .empty .empty) .empty) (.node 792 (sourceLit (List.headD (raw_ints% [257645479290832433806020286615915121295]) 0) 39 false) .empty .empty)) (.node 795 (sourceLit (List.headD (raw_ints% [33792004057057282682676249559280325]) 0) 34 true) (.node 794 (sourceLit (List.headD (raw_ints% [69838206166984650311056793481947775112605]) 0) 30 true) .empty .empty) (.node 796 (sourceLit (List.headD (raw_ints% [7759497804452442439534085875404725159145]) 0) 31 false) .empty .empty)))

#time def treeT_J016_part110 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [184120518012717739008961496027888325]) 0) 34 true) (.node 828 (sourceLit (List.headD (raw_ints% [343879855012959262539358803228031725]) 0) 34 true) (.node 799 (sourceLit (List.headD (raw_ints% [19456995370472250703248886527273795]) 0) 34 true) (.node 798 (sourceLit (List.headD (raw_ints% [88141145280861343409520736788758925]) 0) 32 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [55165839884076403715269514687346455361225]) 0) 32 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [110475081503510287019865536969125515]) 0) 34 true) (.node 831 (sourceLit (List.headD (raw_ints% [41223846845110608985486828150196900450325]) 0) 33 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [1187233013656698145754308692515978318910585]) 0) 28 false) .empty .empty)))

#time def treeT_J016_part111 : IntSourceTree :=
  (.node 797 (sourceLit (List.headD (raw_ints% [25165478084359860417704160620558565]) 0) 34 true) treeT_J016_part109 treeT_J016_part110)

#time def treeT_J016_part112 : IntSourceTree :=
  (.node 839 (sourceLit (List.headD (raw_ints% [253397072680841599429159141033716675]) 0) 31 true) (.node 837 (sourceLit (List.headD (raw_ints% [31038239364030789992925408661781499704865]) 0) 30 false) (.node 836 (sourceLit (List.headD (raw_ints% [200145499607839673023593091755345225]) 0) 32 true) (.node 835 (sourceLit (List.headD (raw_ints% [147435821742004540967452861827004431091005]) 0) 30 true) .empty .empty) .empty) (.node 838 (sourceLit (List.headD (raw_ints% [146059107605505353407536018053672535]) 0) 32 true) .empty .empty)) (.node 870 (sourceLit (List.headD (raw_ints% [72140427962528747588200600679543590042875]) 0) 33 false) (.node 869 (sourceLit (List.headD (raw_ints% [286274402991879732638684126984522475]) 0) 35 true) .empty .empty) (.node 871 (sourceLit (List.headD (raw_ints% [148559762025019845314649593671534875]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part113 : IntSourceTree :=
  (.node 876 (sourceLit (List.headD (raw_ints% [77597659773228491703493473851204578125075]) 0) 32 true) (.node 874 (sourceLit (List.headD (raw_ints% [1326909425990667446376422279479873869135795]) 0) 29 false) (.node 873 (sourceLit (List.headD (raw_ints% [86693517197223676690367263761756765]) 0) 35 true) .empty .empty) (.node 875 (sourceLit (List.headD (raw_ints% [220563438531780397048014527567984925]) 0) 33 true) .empty .empty)) (.node 878 (sourceLit (List.headD (raw_ints% [31038415646321351715612227703255077222715]) 0) 31 false) (.node 877 (sourceLit (List.headD (raw_ints% [149814543439119952188184770514228095]) 0) 33 true) .empty .empty) (.node 879 (sourceLit (List.headD (raw_ints% [107145116864560852001038244999124945]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part114 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [49468502182417246867279477321906184331765]) 0) 34 true) treeT_J016_part112 treeT_J016_part113)

#time def treeT_J016_part115 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [288147446645894962413367026686545575]) 0) 32 true) treeT_J016_part111 treeT_J016_part114)

#time def treeT_J016_part116 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [92146577983291999208992196331679893764175]) 0) 34 false) (.node 913 (sourceLit (List.headD (raw_ints% [7519201293006105744766081789719969913376505]) 0) 28 true) (.node 912 (sourceLit (List.headD (raw_ints% [483763966596569094238732837717013985]) 0) 34 true) (.node 911 (sourceLit (List.headD (raw_ints% [185504702770168104161888029509284080536075]) 0) 33 false) .empty .empty) .empty) (.node 914 (sourceLit (List.headD (raw_ints% [1098948828509683864632509193501562665]) 0) 32 true) .empty .empty)) (.node 917 (sourceLit (List.headD (raw_ints% [651819517549858723620873199471418124705465]) 0) 30 true) (.node 916 (sourceLit (List.headD (raw_ints% [682108254519281915168465018516594475]) 0) 32 true) .empty .empty) (.node 918 (sourceLit (List.headD (raw_ints% [453199066150974455345203064003239845]) 0) 32 true) .empty .empty)))

#time def treeT_J016_part117 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [2211527679749193297785626017299960945628075]) 0) 31 true) (.node 952 (sourceLit (List.headD (raw_ints% [229466020461509131864421393389834243035]) 0) 44 false) (.node 951 (sourceLit (List.headD (raw_ints% [203104332982445336557781354559666675]) 0) 37 true) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [99267612349836354387091393488814305]) 0) 37 true) .empty .empty)) (.node 956 (sourceLit (List.headD (raw_ints% [814770283639564485375431044504643728238475]) 0) 32 false) (.node 955 (sourceLit (List.headD (raw_ints% [219596347494475866896123666483394435]) 0) 35 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [133073427770040490745070062000591595]) 0) 35 true) .empty .empty)))

#time def treeT_J016_part118 : IntSourceTree :=
  (.node 919 (sourceLit (List.headD (raw_ints% [62077084689715384272823884565651188162105]) 0) 31 false) treeT_J016_part116 treeT_J016_part117)

#time def treeT_J016_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [7169981786666374606624321555508567950613265]) 0) 30 false) (.node 995 (sourceLit (List.headD (raw_ints% [2580113991682361294621594802626680520684775]) 0) 32 true) (.node 994 (sourceLit (List.headD (raw_ints% [5254178361879842816141339989782552855]) 0) 32 true) (.node 959 (sourceLit (List.headD (raw_ints% [86513487321603400836041204751028725]) 0) 35 true) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [2831433305392331955169513645217716485]) 0) 32 true) .empty .empty)) (.node 999 (sourceLit (List.headD (raw_ints% [1427792951082075534945794738914997592018465]) 0) 31 true) (.node 998 (sourceLit (List.headD (raw_ints% [1675975778169673396575917928006225675]) 0) 32 true) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [4375792971901939348556845323848975115]) 0) 33 true) .empty .empty)))

#time def treeT_J016_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [14671738582215425439057867650178183975]) 0) 32 true) (.node 1038 (sourceLit (List.headD (raw_ints% [7852839719862554681960806982683241152541445]) 0) 31 false) (.node 1037 (sourceLit (List.headD (raw_ints% [2299139594312169992189233397215350105]) 0) 33 true) .empty .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [1329921828883259793231753109002110775]) 0) 33 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [7520582599079006572181015660855174745]) 0) 32 true) (.node 1077 (sourceLit (List.headD (raw_ints% [54969967922700671203573286753572606107477465]) 0) 30 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [17133472390807184898867408704281479897101355]) 0) 31 false) .empty .empty)))

#time def treeT_J016_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [5974998267004287074618620649758004769608025]) 0) 32 true) treeT_J016_part119 treeT_J016_part120)

#time def treeT_J016_part122 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [170714483299045018834121356793668300482045]) 0) 33 true) treeT_J016_part118 treeT_J016_part121)

#time def treeT_J016_part123 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [960977093954801191545775011910201575]) 0) 34 true) treeT_J016_part115 treeT_J016_part122)

#time def treeT_J016_part124 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [5171737839113333363227136398884682032075]) 0) 34 false) treeT_J016_part108 treeT_J016_part123)

#time def treeT_J016_part125 : IntSourceTree :=
  (.node 596 (sourceLit (List.headD (raw_ints% [13699811728904832441935914021979715]) 0) 32 true) treeT_J016_part093 treeT_J016_part124)

#time def treeT_J016_part126 : IntSourceTree :=
  (.node 357 (sourceLit (List.headD (raw_ints% [10230446851090209395286483500907255]) 0) 30 true) treeT_J016_part062 treeT_J016_part125)

#time def treeT_J016 : IntSourceTree := treeT_J016_part126

#time def treeT_J017_part000 : IntSourceTree :=
  (.node 9 (sourceLit (List.headD (raw_ints% [180376358625613232156976315789375]) 0) 33 true) (.node 7 (sourceLit (List.headD (raw_ints% [202355198016977902064643909354375]) 0) 33 true) (.node 6 (sourceLit (List.headD (raw_ints% [866936160251694228550748352834375]) 0) 31 true) (.node 5 (sourceLit (List.headD (raw_ints% [234668464910544123167818425017625]) 0) 33 true) .empty .empty) .empty) (.node 8 (sourceLit (List.headD (raw_ints% [380912640911352682323731676761625]) 0) 32 true) .empty .empty)) (.node 11 (sourceLit (List.headD (raw_ints% [164073177768186636621997367381625]) 0) 33 true) (.node 10 (sourceLit (List.headD (raw_ints% [1373453025918301914118678805034375]) 0) 30 true) .empty .empty) (.node 12 (sourceLit (List.headD (raw_ints% [314673541598194437643843180447125]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part001 : IntSourceTree :=
  (.node 18 (sourceLit (List.headD (raw_ints% [57145998283123586228166669378188175]) 0) 29 false) (.node 16 (sourceLit (List.headD (raw_ints% [272906095251943018611581202241875]) 0) 32 true) (.node 15 (sourceLit (List.headD (raw_ints% [140955538759757774596015341494625]) 0) 33 true) (.node 14 (sourceLit (List.headD (raw_ints% [583538603094270079334258334028875]) 0) 31 true) .empty .empty) .empty) (.node 17 (sourceLit (List.headD (raw_ints% [8269881674301303594290339461875]) 0) 37 true) .empty .empty)) (.node 20 (sourceLit (List.headD (raw_ints% [30419623234710643045664465038125]) 0) 35 true) (.node 19 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 36 true) .empty .empty) (.node 21 (sourceLit (List.headD (raw_ints% [29652281387348572770638694748875]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part002 : IntSourceTree :=
  (.node 13 (sourceLit (List.headD (raw_ints% [151313994702084086292189702707775]) 0) 33 true) treeT_J017_part000 treeT_J017_part001)

#time def treeT_J017_part003 : IntSourceTree :=
  (.node 27 (sourceLit (List.headD (raw_ints% [51844750421288697571370062666275]) 0) 34 true) (.node 25 (sourceLit (List.headD (raw_ints% [54050964982765942651102653206625]) 0) 34 true) (.node 24 (sourceLit (List.headD (raw_ints% [55249015343053479698345552582625]) 0) 34 true) (.node 23 (sourceLit (List.headD (raw_ints% [28259392215810447432818261259075]) 0) 35 true) .empty .empty) .empty) (.node 26 (sourceLit (List.headD (raw_ints% [423344911187560690110658019118975]) 0) 31 true) .empty .empty)) (.node 29 (sourceLit (List.headD (raw_ints% [49856950070974272385869846747975]) 0) 34 true) (.node 28 (sourceLit (List.headD (raw_ints% [101651690815393561471603047368295]) 0) 33 true) .empty .empty) (.node 30 (sourceLit (List.headD (raw_ints% [195736448049951381378344451487575]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [179597342596019432693608189765575]) 0) 32 true) (.node 33 (sourceLit (List.headD (raw_ints% [185633931397001826844515051626985]) 0) 32 true) (.node 32 (sourceLit (List.headD (raw_ints% [94425749374710901484456785841175]) 0) 33 true) .empty .empty) (.node 34 (sourceLit (List.headD (raw_ints% [2920836717343509498282693794624775]) 0) 28 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [174034711286338755151334899588725]) 0) 32 true) (.node 36 (sourceLit (List.headD (raw_ints% [353521379287147528914256563738975]) 0) 31 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [685649825216843535279364211233155]) 0) 30 true) .empty .empty)))

#time def treeT_J017_part005 : IntSourceTree :=
  (.node 31 (sourceLit (List.headD (raw_ints% [48053805723591286186857658463325]) 0) 34 true) treeT_J017_part003 treeT_J017_part004)

#time def treeT_J017_part006 : IntSourceTree :=
  (.node 22 (sourceLit (List.headD (raw_ints% [115735508631211844236284802504125]) 0) 33 true) treeT_J017_part002 treeT_J017_part005)

#time def treeT_J017_part007 : IntSourceTree :=
  (.node 50 (sourceLit (List.headD (raw_ints% [180376358625613232156976315789375]) 0) 34 true) (.node 48 (sourceLit (List.headD (raw_ints% [202355198016977902064643909354375]) 0) 34 true) (.node 47 (sourceLit (List.headD (raw_ints% [866936160251694228550748352834375]) 0) 32 true) (.node 46 (sourceLit (List.headD (raw_ints% [234668464910544123167818425017625]) 0) 34 true) .empty .empty) .empty) (.node 49 (sourceLit (List.headD (raw_ints% [380912640911352682323731676761625]) 0) 33 true) .empty .empty)) (.node 52 (sourceLit (List.headD (raw_ints% [164073177768186636621997367381625]) 0) 34 true) (.node 51 (sourceLit (List.headD (raw_ints% [1373453025918301914118678805034375]) 0) 31 true) .empty .empty) (.node 53 (sourceLit (List.headD (raw_ints% [314673541598194437643843180447125]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part008 : IntSourceTree :=
  (.node 59 (sourceLit (List.headD (raw_ints% [57145998283123586228166669378188175]) 0) 30 false) (.node 57 (sourceLit (List.headD (raw_ints% [272906095251943018611581202241875]) 0) 33 true) (.node 56 (sourceLit (List.headD (raw_ints% [140955538759757774596015341494625]) 0) 34 true) (.node 55 (sourceLit (List.headD (raw_ints% [583538603094270079334258334028875]) 0) 32 true) .empty .empty) .empty) (.node 58 (sourceLit (List.headD (raw_ints% [8269881674301303594290339461875]) 0) 38 true) .empty .empty)) (.node 61 (sourceLit (List.headD (raw_ints% [30419623234710643045664465038125]) 0) 36 true) (.node 60 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 37 true) .empty .empty) (.node 62 (sourceLit (List.headD (raw_ints% [29652281387348572770638694748875]) 0) 36 true) .empty .empty)))

#time def treeT_J017_part009 : IntSourceTree :=
  (.node 54 (sourceLit (List.headD (raw_ints% [151313994702084086292189702707775]) 0) 34 true) treeT_J017_part007 treeT_J017_part008)

#time def treeT_J017_part010 : IntSourceTree :=
  (.node 68 (sourceLit (List.headD (raw_ints% [51844750421288697571370062666275]) 0) 35 true) (.node 66 (sourceLit (List.headD (raw_ints% [54050964982765942651102653206625]) 0) 35 true) (.node 65 (sourceLit (List.headD (raw_ints% [55249015343053479698345552582625]) 0) 35 true) (.node 64 (sourceLit (List.headD (raw_ints% [28259392215810447432818261259075]) 0) 36 true) .empty .empty) .empty) (.node 67 (sourceLit (List.headD (raw_ints% [423344911187560690110658019118975]) 0) 32 true) .empty .empty)) (.node 70 (sourceLit (List.headD (raw_ints% [49856950070974272385869846747975]) 0) 35 true) (.node 69 (sourceLit (List.headD (raw_ints% [101651690815393561471603047368295]) 0) 34 true) .empty .empty) (.node 71 (sourceLit (List.headD (raw_ints% [195736448049951381378344451487575]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [179597342596019432693608189765575]) 0) 33 true) (.node 74 (sourceLit (List.headD (raw_ints% [185633931397001826844515051626985]) 0) 33 true) (.node 73 (sourceLit (List.headD (raw_ints% [94425749374710901484456785841175]) 0) 34 true) .empty .empty) (.node 75 (sourceLit (List.headD (raw_ints% [2920836717343509498282693794624775]) 0) 29 true) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [174034711286338755151334899588725]) 0) 33 true) (.node 77 (sourceLit (List.headD (raw_ints% [353521379287147528914256563738975]) 0) 32 true) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [685649825216843535279364211233155]) 0) 31 true) .empty .empty)))

#time def treeT_J017_part012 : IntSourceTree :=
  (.node 72 (sourceLit (List.headD (raw_ints% [48053805723591286186857658463325]) 0) 35 true) treeT_J017_part010 treeT_J017_part011)

#time def treeT_J017_part013 : IntSourceTree :=
  (.node 63 (sourceLit (List.headD (raw_ints% [115735508631211844236284802504125]) 0) 34 true) treeT_J017_part009 treeT_J017_part012)

#time def treeT_J017_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [168887571957418773005480131330275]) 0) 32 true) treeT_J017_part006 treeT_J017_part013)

#time def treeT_J017_part015 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [529389742160053738237417812293625]) 0) 33 true) (.node 90 (sourceLit (List.headD (raw_ints% [4721149228663341003061028023151625]) 0) 30 true) (.node 89 (sourceLit (List.headD (raw_ints% [629044433442298376101599321628125]) 0) 33 true) (.node 88 (sourceLit (List.headD (raw_ints% [1352959679592035774777765028907125]) 0) 32 true) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [557432256734266292005907895775875]) 0) 33 true) .empty .empty)) (.node 94 (sourceLit (List.headD (raw_ints% [1933849729691285421816487109548125]) 0) 31 true) (.node 93 (sourceLit (List.headD (raw_ints% [504978716370662460195799766818725]) 0) 33 true) .empty .empty) (.node 95 (sourceLit (List.headD (raw_ints% [464300440048578570572743469336475]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part016 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [95314819468760014876415323786125]) 0) 35 true) (.node 99 (sourceLit (List.headD (raw_ints% [50538165787396855298440963378125]) 0) 36 true) (.node 98 (sourceLit (List.headD (raw_ints% [65878993331185762823737267849928175]) 0) 29 true) (.node 97 (sourceLit (List.headD (raw_ints% [107876012062552560218853983647125]) 0) 35 true) .empty .empty) .empty) (.node 100 (sourceLit (List.headD (raw_ints% [57632712254878956516897300818798175]) 0) 31 false) .empty .empty)) (.node 103 (sourceLit (List.headD (raw_ints% [90349733333583843649736517736425]) 0) 35 true) (.node 102 (sourceLit (List.headD (raw_ints% [370978463124158444494346638105875]) 0) 33 true) .empty .empty) (.node 104 (sourceLit (List.headD (raw_ints% [176222001919370208774224052425625]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part017 : IntSourceTree :=
  (.node 96 (sourceLit (List.headD (raw_ints% [894171110936597140056935465815875]) 0) 32 true) treeT_J017_part015 treeT_J017_part016)

#time def treeT_J017_part018 : IntSourceTree :=
  (.node 110 (sourceLit (List.headD (raw_ints% [617477078473197110394479927458785]) 0) 32 true) (.node 108 (sourceLit (List.headD (raw_ints% [40211652546520891079881871468835]) 0) 36 true) (.node 107 (sourceLit (List.headD (raw_ints% [164359109509775073033040550160225]) 0) 34 true) (.node 106 (sourceLit (List.headD (raw_ints% [1344623579790150660236399663525025]) 0) 31 true) .empty .empty) .empty) (.node 109 (sourceLit (List.headD (raw_ints% [157522051614180517899610403917125]) 0) 34 true) .empty .empty)) (.node 112 (sourceLit (List.headD (raw_ints% [297047146725191861272232117133975]) 0) 33 true) (.node 111 (sourceLit (List.headD (raw_ints% [151373994560305803356621728528575]) 0) 34 true) .empty .empty) (.node 113 (sourceLit (List.headD (raw_ints% [583226960180458752145207483786215]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [2142521209080336696034688298678645]) 0) 30 true) (.node 116 (sourceLit (List.headD (raw_ints% [2213793958769214440454180667146825]) 0) 30 true) (.node 115 (sourceLit (List.headD (raw_ints% [562938382991987874684452016742365]) 0) 32 true) .empty .empty) (.node 117 (sourceLit (List.headD (raw_ints% [544354659097738975623097859473575]) 0) 32 true) .empty .empty)) (.node 128 (sourceLit (List.headD (raw_ints% [266981731804110344270992940680875]) 0) 35 true) (.node 119 (sourceLit (List.headD (raw_ints% [527251273187936247599859467024625]) 0) 32 true) .empty .empty) (.node 129 (sourceLit (List.headD (raw_ints% [243011759670170773113508338036375]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part020 : IntSourceTree :=
  (.node 114 (sourceLit (List.headD (raw_ints% [9165659202619485891727774793045625]) 0) 28 true) treeT_J017_part018 treeT_J017_part019)

#time def treeT_J017_part021 : IntSourceTree :=
  (.node 105 (sourceLit (List.headD (raw_ints% [172024172743717636811443436865975]) 0) 34 true) treeT_J017_part017 treeT_J017_part020)

#time def treeT_J017_part022 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [675155563298507671241114387759625]) 0) 33 true) (.node 133 (sourceLit (List.headD (raw_ints% [744105942721913038830992444140125]) 0) 33 true) (.node 132 (sourceLit (List.headD (raw_ints% [196679539483039827691955264197125]) 0) 35 true) (.node 131 (sourceLit (List.headD (raw_ints% [1673848101372519544471174609058625]) 0) 32 true) .empty .empty) .empty) (.node 134 (sourceLit (List.headD (raw_ints% [176832360834289186951805032055475]) 0) 35 true) .empty .empty)) (.node 137 (sourceLit (List.headD (raw_ints% [38829063480290882590334641473375]) 0) 37 true) (.node 136 (sourceLit (List.headD (raw_ints% [161672450644410397988364063920925]) 0) 35 true) .empty .empty) (.node 138 (sourceLit (List.headD (raw_ints% [74796485365347345841692625799625]) 0) 36 true) .empty .empty)))

#time def treeT_J017_part023 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [127621477246473300129030917800875]) 0) 35 true) (.node 141 (sourceLit (List.headD (raw_ints% [58119426226634326805627932259408175]) 0) 32 false) (.node 140 (sourceLit (List.headD (raw_ints% [17458639090191640921279605530625]) 0) 38 true) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [32831269040705721052888314518625]) 0) 37 true) .empty .empty)) (.node 145 (sourceLit (List.headD (raw_ints% [15121623322039591134484812480375]) 0) 38 true) (.node 144 (sourceLit (List.headD (raw_ints% [31045170558886698108459128238675]) 0) 37 true) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [58986603880475847080170391829675]) 0) 36 true) .empty .empty)))

#time def treeT_J017_part024 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [61512495807154674525951968614058175]) 0) 31 true) treeT_J017_part022 treeT_J017_part023)

#time def treeT_J017_part025 : IntSourceTree :=
  (.node 152 (sourceLit (List.headD (raw_ints% [51660094418357258584882035032625]) 0) 36 true) (.node 150 (sourceLit (List.headD (raw_ints% [53832550771603122756870278584575]) 0) 36 true) (.node 149 (sourceLit (List.headD (raw_ints% [220041529556773567167451924382385]) 0) 34 true) (.node 148 (sourceLit (List.headD (raw_ints% [56257179544243187730835243746975]) 0) 36 true) .empty .empty) .empty) (.node 151 (sourceLit (List.headD (raw_ints% [210870315211622864508067737985605]) 0) 34 true) .empty .empty)) (.node 154 (sourceLit (List.headD (raw_ints% [198796514391728462650346216079615]) 0) 34 true) (.node 153 (sourceLit (List.headD (raw_ints% [1582979666800632498341994775725]) 0) 41 true) .empty .empty) (.node 155 (sourceLit (List.headD (raw_ints% [3122411242637988196722540499210425]) 0) 30 true) .empty .empty)))

#time def treeT_J017_part026 : IntSourceTree :=
  (.node 169 (sourceLit (List.headD (raw_ints% [1506809420990584378066344203818875]) 0) 33 true) (.node 158 (sourceLit (List.headD (raw_ints% [185159973905700110235881479942425]) 0) 34 true) (.node 157 (sourceLit (List.headD (raw_ints% [1506751200194919382625667539668875]) 0) 31 true) .empty .empty) (.node 159 (sourceLit (List.headD (raw_ints% [728435691931746580377662043722745]) 0) 32 true) .empty .empty)) (.node 171 (sourceLit (List.headD (raw_ints% [1237240042532474283772584127579125]) 0) 33 true) (.node 170 (sourceLit (List.headD (raw_ints% [10831603390227588476203505611176375]) 0) 30 true) .empty .empty) (.node 172 (sourceLit (List.headD (raw_ints% [143057294901558225779219599595625]) 0) 36 true) .empty .empty)))

#time def treeT_J017_part027 : IntSourceTree :=
  (.node 156 (sourceLit (List.headD (raw_ints% [191670520197984220995421913488395]) 0) 34 true) treeT_J017_part025 treeT_J017_part026)

#time def treeT_J017_part028 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [460639334301294985062870822203025]) 0) 33 true) treeT_J017_part024 treeT_J017_part027)

#time def treeT_J017_part029 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [224334037408342571972311502919375]) 0) 35 true) treeT_J017_part021 treeT_J017_part028)

#time def treeT_J017_part030 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [736318661625198590606629790716125]) 0) 33 true) treeT_J017_part014 treeT_J017_part029)

#time def treeT_J017_part031 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [45998512829276830937485931415560175]) 0) 29 false) (.node 176 (sourceLit (List.headD (raw_ints% [1806451142257433544907522085222625]) 0) 32 true) (.node 175 (sourceLit (List.headD (raw_ints% [950358446625734925041696787107325]) 0) 33 true) (.node 174 (sourceLit (List.headD (raw_ints% [4018997812084018888831452443572875]) 0) 31 true) .empty .empty) .empty) (.node 177 (sourceLit (List.headD (raw_ints% [215468889226268235757874144194725]) 0) 35 true) .empty .empty)) (.node 180 (sourceLit (List.headD (raw_ints% [180657703869188305568801238046914525]) 0) 31 true) (.node 179 (sourceLit (List.headD (raw_ints% [99054804943297836384944288221125]) 0) 36 true) .empty .empty) (.node 181 (sourceLit (List.headD (raw_ints% [184023405974306239864058364703875]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part032 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [307533721534031703608322584477175]) 0) 34 true) (.node 185 (sourceLit (List.headD (raw_ints% [324698556198469532923902614952825]) 0) 34 true) (.node 184 (sourceLit (List.headD (raw_ints% [334263907066522991741899618777875]) 0) 34 true) (.node 183 (sourceLit (List.headD (raw_ints% [172300418992061924773369998412575]) 0) 35 true) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [2526511990651984670191712331450975]) 0) 31 true) .empty .empty)) (.node 189 (sourceLit (List.headD (raw_ints% [292535384739764983947071546058675]) 0) 34 true) (.node 188 (sourceLit (List.headD (raw_ints% [299792724115211420743343336327685]) 0) 34 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [1142855157980991426945135467600295]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part033 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [29245202344879242625061139448757025]) 0) 34 false) treeT_J017_part031 treeT_J017_part032)

#time def treeT_J017_part034 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [4031028526506761952990900331274025]) 0) 30 true) (.node 194 (sourceLit (List.headD (raw_ints% [16769879658242076961107467612432775]) 0) 28 true) (.node 193 (sourceLit (List.headD (raw_ints% [1069896061206973522571017637257785]) 0) 32 true) (.node 192 (sourceLit (List.headD (raw_ints% [546434114121299596760038834808445]) 0) 33 true) .empty .empty) .empty) (.node 195 (sourceLit (List.headD (raw_ints% [1027433732141839826518317711894555]) 0) 32 true) .empty .empty)) (.node 198 (sourceLit (List.headD (raw_ints% [3884483591699340834467981859996855]) 0) 30 true) (.node 197 (sourceLit (List.headD (raw_ints% [989009502486134792340277448433585]) 0) 32 true) .empty .empty) (.node 199 (sourceLit (List.headD (raw_ints% [954028518057664634287192372514775]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part035 : IntSourceTree :=
  (.node 214 (sourceLit (List.headD (raw_ints% [714792877825077787436232282647325]) 0) 34 true) (.node 212 (sourceLit (List.headD (raw_ints% [843880963566394628388673599184875]) 0) 34 true) (.node 211 (sourceLit (List.headD (raw_ints% [7483907187482549387261156393059125]) 0) 31 true) .empty .empty) (.node 213 (sourceLit (List.headD (raw_ints% [1544810775703018573636521149389875]) 0) 33 true) .empty .empty)) (.node 216 (sourceLit (List.headD (raw_ints% [627013545336914129064968659265475]) 0) 34 true) (.node 215 (sourceLit (List.headD (raw_ints% [2668686685487003546349223668053625]) 0) 32 true) .empty .empty) (.node 217 (sourceLit (List.headD (raw_ints% [1185186126572779423462167821648625]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part036 : IntSourceTree :=
  (.node 210 (sourceLit (List.headD (raw_ints% [1058141346173899234121721197980125]) 0) 34 true) treeT_J017_part034 treeT_J017_part035)

#time def treeT_J017_part037 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [279286411612519178698340500148025]) 0) 34 true) treeT_J017_part033 treeT_J017_part036)

#time def treeT_J017_part038 : IntSourceTree :=
  (.node 223 (sourceLit (List.headD (raw_ints% [7343205955531428981297542591639475]) 0) 37 false) (.node 221 (sourceLit (List.headD (raw_ints% [59694282523955658093607292576580675]) 0) 34 true) (.node 220 (sourceLit (List.headD (raw_ints% [64137526762914554542385077159875]) 0) 37 true) (.node 219 (sourceLit (List.headD (raw_ints% [169023504443586179989389868643676525]) 0) 30 false) .empty .empty) .empty) (.node 222 (sourceLit (List.headD (raw_ints% [118360867892894797758281735666625]) 0) 36 true) .empty .empty)) (.node 225 (sourceLit (List.headD (raw_ints% [213290920490206262666021118934875]) 0) 35 true) (.node 224 (sourceLit (List.headD (raw_ints% [110210077874288528556451741935225]) 0) 36 true) .empty .empty) (.node 226 (sourceLit (List.headD (raw_ints% [206725348437517838763561831293475]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part039 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [721114527557745697928999991629085]) 0) 33 true) (.node 229 (sourceLit (List.headD (raw_ints% [379543918673649274319234748272985]) 0) 34 true) (.node 228 (sourceLit (List.headD (raw_ints% [195019362445545328146652096983225]) 0) 35 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [184870283196558738433330988889525]) 0) 35 true) .empty .empty)) (.node 233 (sourceLit (List.headD (raw_ints% [343812716770818636972263503515645]) 0) 34 true) (.node 232 (sourceLit (List.headD (raw_ints% [175966222775804661528576430082775]) 0) 35 true) .empty .empty) (.node 234 (sourceLit (List.headD (raw_ints% [672303032423516597270325205098555]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part040 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [1605233322049394700065970687044925]) 0) 32 true) treeT_J017_part038 treeT_J017_part039)

#time def treeT_J017_part041 : IntSourceTree :=
  (.node 251 (sourceLit (List.headD (raw_ints% [2995325342163122652714300664341375]) 0) 33 true) (.node 238 (sourceLit (List.headD (raw_ints% [618689554674734571868514488548735]) 0) 33 true) (.node 237 (sourceLit (List.headD (raw_ints% [1262138663155921285182616395802575]) 0) 32 true) (.node 236 (sourceLit (List.headD (raw_ints% [644092691745871384527473884917765]) 0) 33 true) .empty .empty) .empty) (.node 239 (sourceLit (List.headD (raw_ints% [2427612207835847673712657772551365]) 0) 31 true) .empty .empty)) (.node 253 (sourceLit (List.headD (raw_ints% [2307066254771922352214852049981225]) 0) 33 true) (.node 252 (sourceLit (List.headD (raw_ints% [5194990469057617774793642799529125]) 0) 32 true) .empty .empty) (.node 254 (sourceLit (List.headD (raw_ints% [8339488393540129700260716751546125]) 0) 31 true) .empty .empty)))

#time def treeT_J017_part042 : IntSourceTree :=
  (.node 259 (sourceLit (List.headD (raw_ints% [182290002778543943447418748569075]) 0) 36 true) (.node 257 (sourceLit (List.headD (raw_ints% [205772328055322946653547257535375]) 0) 36 true) (.node 256 (sourceLit (List.headD (raw_ints% [3530922228716573547790925250884625]) 0) 32 true) .empty .empty) (.node 258 (sourceLit (List.headD (raw_ints% [83924468879605772488275301708316175]) 0) 29 true) .empty .empty)) (.node 261 (sourceLit (List.headD (raw_ints% [329076808129010196475022252575125]) 0) 35 true) (.node 260 (sourceLit (List.headD (raw_ints% [174840604156387242779095553345295525]) 0) 32 false) .empty .empty) (.node 262 (sourceLit (List.headD (raw_ints% [148633767392790558812275724601918375]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part043 : IntSourceTree :=
  (.node 255 (sourceLit (List.headD (raw_ints% [1908813064674576224703232343481975]) 0) 33 true) treeT_J017_part041 treeT_J017_part042)

#time def treeT_J017_part044 : IntSourceTree :=
  (.node 235 (sourceLit (List.headD (raw_ints% [10525057172966100567662386614011925]) 0) 29 true) treeT_J017_part040 treeT_J017_part043)

#time def treeT_J017_part045 : IntSourceTree :=
  (.node 218 (sourceLit (List.headD (raw_ints% [35168100965230222479045379598775]) 0) 38 true) treeT_J017_part037 treeT_J017_part044)

#time def treeT_J017_part046 : IntSourceTree :=
  (.node 268 (sourceLit (List.headD (raw_ints% [1005647873818971858579284014389555]) 0) 33 true) (.node 266 (sourceLit (List.headD (raw_ints% [4298797465034615735120963474465025]) 0) 31 true) (.node 265 (sourceLit (List.headD (raw_ints% [556982066795838695527711320528975]) 0) 34 true) (.node 264 (sourceLit (List.headD (raw_ints% [117825559195569386692502581085009475]) 0) 34 false) .empty .empty) .empty) (.node 267 (sourceLit (List.headD (raw_ints% [519367672216039651445924740696725]) 0) 34 true) .empty .empty)) (.node 270 (sourceLit (List.headD (raw_ints% [1893496191408202767608742518583585]) 0) 32 true) (.node 269 (sourceLit (List.headD (raw_ints% [487542065042416328639536841874225]) 0) 34 true) .empty .empty) (.node 271 (sourceLit (List.headD (raw_ints% [460194721173715775034983455410075]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part047 : IntSourceTree :=
  (.node 277 (sourceLit (List.headD (raw_ints% [1587361264497350745769618091237475]) 0) 32 true) (.node 275 (sourceLit (List.headD (raw_ints% [1661778397552226562562983108499665]) 0) 32 true) (.node 274 (sourceLit (List.headD (raw_ints% [27238148088422708571342260837569785]) 0) 28 true) (.node 273 (sourceLit (List.headD (raw_ints% [1745563503205901061886205244066615]) 0) 32 true) .empty .empty) .empty) (.node 276 (sourceLit (List.headD (raw_ints% [1623507161614834653667871570684475]) 0) 32 true) .empty .empty)) (.node 279 (sourceLit (List.headD (raw_ints% [1520729700641273653186865581680165]) 0) 32 true) (.node 278 (sourceLit (List.headD (raw_ints% [6212625713548029446992949306423745]) 0) 30 true) .empty .empty) (.node 292 (sourceLit (List.headD (raw_ints% [537861094649182006081406766289125]) 0) 36 true) .empty .empty)))

#time def treeT_J017_part048 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [895794940994191799097961148449725]) 0) 33 true) treeT_J017_part046 treeT_J017_part047)

#time def treeT_J017_part049 : IntSourceTree :=
  (.node 298 (sourceLit (List.headD (raw_ints% [135436126124862501695456498337825]) 0) 37 true) (.node 296 (sourceLit (List.headD (raw_ints% [320449879834415523909565921054125]) 0) 36 true) (.node 295 (sourceLit (List.headD (raw_ints% [1417700427013281538477873270873125]) 0) 34 true) (.node 294 (sourceLit (List.headD (raw_ints% [398068344236711141194654941833475]) 0) 36 true) .empty .empty) .empty) (.node 297 (sourceLit (List.headD (raw_ints% [73304253191993566385273669663625]) 0) 38 true) .empty .empty)) (.node 300 (sourceLit (List.headD (raw_ints% [7384529750976836806564604463075]) 0) 41 true) (.node 299 (sourceLit (List.headD (raw_ints% [63236993330797988119416292587998175]) 0) 32 true) .empty .empty) (.node 301 (sourceLit (List.headD (raw_ints% [294229169204298558966310138498456875]) 0) 33 false) .empty .empty)))

#time def treeT_J017_part050 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [87564179589580214191037372308875]) 0) 37 true) (.node 304 (sourceLit (List.headD (raw_ints% [47733243676307184425826300579675]) 0) 38 true) (.node 303 (sourceLit (List.headD (raw_ints% [178006591214916274737465894968476275]) 0) 35 true) .empty .empty) (.node 305 (sourceLit (List.headD (raw_ints% [59019425058029796477584301101972175]) 0) 36 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [81087077442623580824818160928375]) 0) 37 true) (.node 307 (sourceLit (List.headD (raw_ints% [673391035746305258763748196855025]) 0) 34 true) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [313051977572661292130024633058285]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part051 : IntSourceTree :=
  (.node 302 (sourceLit (List.headD (raw_ints% [52678985059028849679185129227125]) 0) 38 true) treeT_J017_part049 treeT_J017_part050)

#time def treeT_J017_part052 : IntSourceTree :=
  (.node 293 (sourceLit (List.headD (raw_ints% [1825089846677299600578560825069625]) 0) 34 true) treeT_J017_part048 treeT_J017_part051)

#time def treeT_J017_part053 : IntSourceTree :=
  (.node 315 (sourceLit (List.headD (raw_ints% [4178272728864152000919968555889465]) 0) 31 true) (.node 313 (sourceLit (List.headD (raw_ints% [8624722253490205658214025702095]) 0) 40 true) (.node 312 (sourceLit (List.headD (raw_ints% [71057124599477778376601756331825]) 0) 37 true) (.node 311 (sourceLit (List.headD (raw_ints% [293095415962614267419935631738625]) 0) 35 true) .empty .empty) .empty) (.node 314 (sourceLit (List.headD (raw_ints% [268315117695596116153970009742015]) 0) 35 true) .empty .empty)) (.node 317 (sourceLit (List.headD (raw_ints% [1984875660073748022153126745566375]) 0) 32 true) (.node 316 (sourceLit (List.headD (raw_ints% [254421426451588794508877305895475]) 0) 35 true) .empty .empty) (.node 318 (sourceLit (List.headD (raw_ints% [242167927455654043475275900672185]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part054 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [7810681187389678760032060916100375]) 0) 32 true) (.node 334 (sourceLit (List.headD (raw_ints% [20861949153296663908996256449567875]) 0) 31 true) (.node 333 (sourceLit (List.headD (raw_ints% [6298711259614989745087656210644775]) 0) 33 true) .empty .empty) (.node 335 (sourceLit (List.headD (raw_ints% [4460280443112802034411246725853625]) 0) 33 true) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [8860913611004360509755063972764175]) 0) 29 false) (.node 337 (sourceLit (List.headD (raw_ints% [435127431613508101165584584572875]) 0) 36 true) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [359454501720906063334407244782225]) 0) 36 true) .empty .empty)))

#time def treeT_J017_part055 : IntSourceTree :=
  (.node 319 (sourceLit (List.headD (raw_ints% [946253376428045443320072883468095]) 0) 33 true) treeT_J017_part053 treeT_J017_part054)

#time def treeT_J017_part056 : IntSourceTree :=
  (.node 345 (sourceLit (List.headD (raw_ints% [970481730845991206098730298020625]) 0) 34 true) (.node 343 (sourceLit (List.headD (raw_ints% [541720708364944328607205123380075]) 0) 35 true) (.node 342 (sourceLit (List.headD (raw_ints% [221431468298544558889292931550187625]) 0) 35 false) (.node 341 (sourceLit (List.headD (raw_ints% [616142999996024914765247118698475]) 0) 35 true) .empty .empty) .empty) (.node 344 (sourceLit (List.headD (raw_ints% [829851924055234485642366160958914575]) 0) 34 true) .empty .empty)) (.node 347 (sourceLit (List.headD (raw_ints% [881659201217243775610673216245275]) 0) 34 true) (.node 346 (sourceLit (List.headD (raw_ints% [3781542001178941590300516234000684225]) 0) 31 false) .empty .empty) (.node 348 (sourceLit (List.headD (raw_ints% [1687916269166249176475708773030545]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part057 : IntSourceTree :=
  (.node 353 (sourceLit (List.headD (raw_ints% [2802092471160676754216307161170185]) 0) 32 true) (.node 351 (sourceLit (List.headD (raw_ints% [750492406209714585789839956528725]) 0) 34 true) (.node 350 (sourceLit (List.headD (raw_ints% [3115335449754377906471651610348975]) 0) 32 true) .empty .empty) (.node 352 (sourceLit (List.headD (raw_ints% [1448968386706722340261523905459275]) 0) 33 true) .empty .empty)) (.node 355 (sourceLit (List.headD (raw_ints% [2631263485577311295900537047372575]) 0) 32 true) (.node 354 (sourceLit (List.headD (raw_ints% [43415576612169056180747037713992455]) 0) 28 true) .empty .empty) (.node 356 (sourceLit (List.headD (raw_ints% [1277382783624658673626048492602495]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part058 : IntSourceTree :=
  (.node 349 (sourceLit (List.headD (raw_ints% [809851174039560964557553732979775]) 0) 34 true) treeT_J017_part056 treeT_J017_part057)

#time def treeT_J017_part059 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [301314590817983219017928138521291875]) 0) 32 true) treeT_J017_part055 treeT_J017_part058)

#time def treeT_J017_part060 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [75667945461464397551551463246175]) 0) 37 true) treeT_J017_part052 treeT_J017_part059)

#time def treeT_J017_part061 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [301143052579517266259756944253925]) 0) 35 true) treeT_J017_part045 treeT_J017_part060)

#time def treeT_J017_part062 : IntSourceTree :=
  (.node 173 (sourceLit (List.headD (raw_ints% [1068457599493656161339842346758275]) 0) 33 true) treeT_J017_part030 treeT_J017_part061)

#time def treeT_J017_part063 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [3178480923775139938772983041637125]) 0) 34 true) (.node 374 (sourceLit (List.headD (raw_ints% [4706437882668145180309036443310875]) 0) 34 true) (.node 359 (sourceLit (List.headD (raw_ints% [2353957138649191042417548829074795]) 0) 32 true) (.node 358 (sourceLit (List.headD (raw_ints% [9666379567041954730232064658107255]) 0) 30 true) .empty .empty) .empty) (.node 375 (sourceLit (List.headD (raw_ints% [15191147445243537755084763366075375]) 0) 32 true) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [149845652744322799735064043117525]) 0) 38 true) (.node 377 (sourceLit (List.headD (raw_ints% [5464945085245884635703303486864375]) 0) 33 true) .empty .empty) (.node 379 (sourceLit (List.headD (raw_ints% [261808886934196312987420234324756875]) 0) 30 false) .empty .empty)))

#time def treeT_J017_part064 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [947890774171294078597534763162858925]) 0) 35 true) (.node 383 (sourceLit (List.headD (raw_ints% [620869527812005392516051758068851525]) 0) 35 false) (.node 382 (sourceLit (List.headD (raw_ints% [405427059759909516048506601789975]) 0) 36 true) (.node 381 (sourceLit (List.headD (raw_ints% [297771880011140888992119138509874375]) 0) 34 true) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [350787733659715590903899921061375]) 0) 36 true) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [3784235565321926811335571226788104325]) 0) 32 false) (.node 386 (sourceLit (List.headD (raw_ints% [620225012487670349334580808785125]) 0) 35 true) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [557310891446749452311400572531775]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part065 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [241302025705276674429373573373025]) 0) 37 true) treeT_J017_part063 treeT_J017_part064)

#time def treeT_J017_part066 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [1728832000378292289600427122202125]) 0) 33 true) (.node 392 (sourceLit (List.headD (raw_ints% [466263907811803472283432931201425]) 0) 35 true) (.node 391 (sourceLit (List.headD (raw_ints% [1942953785903920836791909083394475]) 0) 33 true) (.node 390 (sourceLit (List.headD (raw_ints% [507179392193703374351347879995075]) 0) 35 true) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [896986162483349178135826260525195]) 0) 34 true) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [1613577779770956117865027823790675]) 0) 33 true) (.node 395 (sourceLit (List.headD (raw_ints% [26702485696712448177067163490434595]) 0) 29 true) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [3124655474424886672351067224843605]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part067 : IntSourceTree :=
  (.node 417 (sourceLit (List.headD (raw_ints% [2308226060548123736441813872491375]) 0) 35 true) (.node 415 (sourceLit (List.headD (raw_ints% [14365471087559778686824899047389875]) 0) 33 true) (.node 399 (sourceLit (List.headD (raw_ints% [5881366061329772956951773124234875]) 0) 31 true) .empty .empty) (.node 416 (sourceLit (List.headD (raw_ints% [22571613703097396750137465816050375]) 0) 32 true) .empty .empty)) (.node 419 (sourceLit (List.headD (raw_ints% [839310720233676334546105100157975]) 0) 36 true) (.node 418 (sourceLit (List.headD (raw_ints% [183739156338872668852260775552424175]) 0) 29 true) .empty .empty) (.node 420 (sourceLit (List.headD (raw_ints% [864438068570162751023276511367340625]) 0) 31 false) .empty .empty)))

#time def treeT_J017_part068 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [1514709848905453792471315200401385]) 0) 33 true) treeT_J017_part066 treeT_J017_part067)

#time def treeT_J017_part069 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [1061812314020926592215659506913975]) 0) 34 true) treeT_J017_part065 treeT_J017_part068)

#time def treeT_J017_part070 : IntSourceTree :=
  (.node 426 (sourceLit (List.headD (raw_ints% [34114046774660352105421628655212169825]) 0) 31 true) (.node 424 (sourceLit (List.headD (raw_ints% [3313330035303256055706573193234320675]) 0) 34 false) (.node 423 (sourceLit (List.headD (raw_ints% [1079987530674693735586821283779825]) 0) 35 true) (.node 422 (sourceLit (List.headD (raw_ints% [32450209269355340492588254378753875]) 0) 39 true) .empty .empty) .empty) (.node 425 (sourceLit (List.headD (raw_ints% [1835820138431733521132469070470375]) 0) 34 true) .empty .empty)) (.node 428 (sourceLit (List.headD (raw_ints% [1892961740795546530256023467780567435]) 0) 34 false) (.node 427 (sourceLit (List.headD (raw_ints% [1599240848733437621727650018895225]) 0) 34 true) .empty .empty) (.node 429 (sourceLit (List.headD (raw_ints% [1419392391747436844688048557147325]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part071 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [4284064515935857862501171441435925]) 0) 32 true) (.node 433 (sourceLit (List.headD (raw_ints% [4658130053828178802318619738052615]) 0) 32 true) (.node 432 (sourceLit (List.headD (raw_ints% [2436939185101119333322294261329675]) 0) 33 true) (.node 431 (sourceLit (List.headD (raw_ints% [1278225162565098911615551563451575]) 0) 34 true) .empty .empty) .empty) (.node 434 (sourceLit (List.headD (raw_ints% [71398652185699638620638723633232505]) 0) 28 true) .empty .empty)) (.node 437 (sourceLit (List.headD (raw_ints% [3970929560355754505087692492072575]) 0) 32 true) (.node 436 (sourceLit (List.headD (raw_ints% [16483423427715178788058775549614635]) 0) 30 true) .empty .empty) (.node 438 (sourceLit (List.headD (raw_ints% [15330864228357138648576473140641585]) 0) 30 true) .empty .empty)))

#time def treeT_J017_part072 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [5379163062413034831253624444962825]) 0) 32 true) treeT_J017_part070 treeT_J017_part071)

#time def treeT_J017_part073 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [299004347264199830058365763392475]) 0) 38 true) (.node 458 (sourceLit (List.headD (raw_ints% [1708843449570832537501557700021275]) 0) 36 true) (.node 457 (sourceLit (List.headD (raw_ints% [1069166788615719507152135145574125]) 0) 37 true) (.node 456 (sourceLit (List.headD (raw_ints% [5593495081892319374025958002876375]) 0) 35 true) .empty .empty) .empty) (.node 459 (sourceLit (List.headD (raw_ints% [222774021636534490919840504938590525]) 0) 31 true) .empty .empty)) (.node 462 (sourceLit (List.headD (raw_ints% [454423072943139482310617433247875]) 0) 37 true) (.node 461 (sourceLit (List.headD (raw_ints% [2055525588614726306991753065406838125]) 0) 32 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [1659276224431376288278875898188975525]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part074 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [520964978643344084708124723181725]) 0) 36 true) (.node 466 (sourceLit (List.headD (raw_ints% [607797562972031585898944130842625]) 0) 36 true) (.node 465 (sourceLit (List.headD (raw_ints% [266326300592159383394006747274823725]) 0) 39 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [18949141169991139458378599941000137075]) 0) 33 true) .empty .empty)) (.node 470 (sourceLit (List.headD (raw_ints% [456106499776866735168350338576125]) 0) 36 true) (.node 469 (sourceLit (List.headD (raw_ints% [3786985293905113987104262595068048845]) 0) 34 false) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [1718104638254556997230857680784175]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part075 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [364599898507489072341460681359225]) 0) 37 true) treeT_J017_part073 treeT_J017_part074)

#time def treeT_J017_part076 : IntSourceTree :=
  (.node 439 (sourceLit (List.headD (raw_ints% [3704882256972624127467711972530745]) 0) 32 true) treeT_J017_part072 treeT_J017_part075)

#time def treeT_J017_part077 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [1314273205646188480669741468285725]) 0) 35 true) treeT_J017_part069 treeT_J017_part076)

#time def treeT_J017_part078 : IntSourceTree :=
  (.node 477 (sourceLit (List.headD (raw_ints% [10234112478865405443356641099927425]) 0) 31 true) (.node 475 (sourceLit (List.headD (raw_ints% [22348083244493595221785780071398955]) 0) 30 true) (.node 474 (sourceLit (List.headD (raw_ints% [1464649026724943256359096307925245]) 0) 34 true) (.node 473 (sourceLit (List.headD (raw_ints% [12030882989201329337394281256285]) 0) 41 true) .empty .empty) .empty) (.node 476 (sourceLit (List.headD (raw_ints% [1335243368082450872318071808822625]) 0) 34 true) .empty .empty)) (.node 479 (sourceLit (List.headD (raw_ints% [4724749083513682845812350008203355]) 0) 32 true) (.node 478 (sourceLit (List.headD (raw_ints% [1228109855725150356308188645835595]) 0) 34 true) .empty .empty) (.node 497 (sourceLit (List.headD (raw_ints% [8878764103236515011610102133261375]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part079 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [2555397052870422122898118182203175]) 0) 35 true) (.node 501 (sourceLit (List.headD (raw_ints% [3469796350581008800264110745993875]) 0) 35 true) (.node 500 (sourceLit (List.headD (raw_ints% [1309986111843231732862957521244521675]) 0) 31 true) (.node 499 (sourceLit (List.headD (raw_ints% [2578376178907988740457010299884575]) 0) 36 true) .empty .empty) .empty) (.node 502 (sourceLit (List.headD (raw_ints% [4132338981853468098517401345647086125]) 0) 33 false) .empty .empty)) (.node 505 (sourceLit (List.headD (raw_ints% [3997778237688091636330901831277225]) 0) 34 true) (.node 504 (sourceLit (List.headD (raw_ints% [9950434933028761208822076785990222775]) 0) 34 true) .empty .empty) (.node 506 (sourceLit (List.headD (raw_ints% [170473112677845956403153083259921917025]) 0) 31 false) .empty .empty)))

#time def treeT_J017_part080 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [363674239432375718809632418981527825]) 0) 29 true) treeT_J017_part078 treeT_J017_part079)

#time def treeT_J017_part081 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [4435479367917108655601136461807025]) 0) 33 true) (.node 510 (sourceLit (List.headD (raw_ints% [30301261514303324931665354384989353585]) 0) 32 false) (.node 509 (sourceLit (List.headD (raw_ints% [2748327437399315832976949228306475]) 0) 34 true) (.node 508 (sourceLit (List.headD (raw_ints% [10421051455393342994317311704390352255]) 0) 35 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [2370626835649834969731251145157425]) 0) 34 true) .empty .empty)) (.node 514 (sourceLit (List.headD (raw_ints% [125715334709374941243229180469740935]) 0) 28 true) (.node 513 (sourceLit (List.headD (raw_ints% [8333250022224548226995278377949785]) 0) 32 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [7433127697863688188371599021966035]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part082 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [1792480163416420618527136108310025]) 0) 38 true) (.node 518 (sourceLit (List.headD (raw_ints% [25605585687104483124850091259068115]) 0) 30 true) (.node 517 (sourceLit (List.headD (raw_ints% [6711017384303852473456881978508425]) 0) 32 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [6119996588828578722997797194154015]) 0) 32 true) .empty .empty)) (.node 540 (sourceLit (List.headD (raw_ints% [1980367484379589080340278773099625]) 0) 37 true) (.node 539 (sourceLit (List.headD (raw_ints% [81873803840693263030048590895653225]) 0) 30 false) .empty .empty) (.node 541 (sourceLit (List.headD (raw_ints% [420688962557244754981838823331419975]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part083 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [28212743061272011655512784593183275]) 0) 30 true) treeT_J017_part081 treeT_J017_part082)

#time def treeT_J017_part084 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [3263139655042815065463903027845775]) 0) 34 true) treeT_J017_part080 treeT_J017_part083)

#time def treeT_J017_part085 : IntSourceTree :=
  (.node 547 (sourceLit (List.headD (raw_ints% [208371395017828235319910283141922191175]) 0) 32 false) (.node 545 (sourceLit (List.headD (raw_ints% [14211655742503311343126184742387402375]) 0) 35 true) (.node 544 (sourceLit (List.headD (raw_ints% [1826197255855443978215196819484725]) 0) 36 true) (.node 543 (sourceLit (List.headD (raw_ints% [7450891430716220675075153142025037175]) 0) 34 false) .empty .empty) .empty) (.node 546 (sourceLit (List.headD (raw_ints% [2782183111744028464533013569591975]) 0) 35 true) .empty .empty)) (.node 549 (sourceLit (List.headD (raw_ints% [45471191115478485964373509412629457865]) 0) 34 true) (.node 548 (sourceLit (List.headD (raw_ints% [2221209697756126896047653581482325]) 0) 35 true) .empty .empty) (.node 550 (sourceLit (List.headD (raw_ints% [1836114437845582362640248551154225]) 0) 35 true) .empty .empty)))

#time def treeT_J017_part086 : IntSourceTree :=
  (.node 555 (sourceLit (List.headD (raw_ints% [81019168220387750799657620326943025]) 0) 29 true) (.node 553 (sourceLit (List.headD (raw_ints% [2895526345299338500414668461002545]) 0) 34 true) (.node 552 (sourceLit (List.headD (raw_ints% [1558665580896539530399132512907275]) 0) 35 true) .empty .empty) (.node 554 (sourceLit (List.headD (raw_ints% [5403951968774661714277085762099295]) 0) 33 true) .empty .empty)) (.node 557 (sourceLit (List.headD (raw_ints% [8989315291203303106078071746627925]) 0) 32 true) (.node 556 (sourceLit (List.headD (raw_ints% [4762640961698786443735455404320785]) 0) 33 true) .empty .empty) (.node 558 (sourceLit (List.headD (raw_ints% [4254797672853551760840504686837235]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part087 : IntSourceTree :=
  (.node 551 (sourceLit (List.headD (raw_ints% [30304697723579834045659816100350921935]) 0) 33 false) treeT_J017_part085 treeT_J017_part086)

#time def treeT_J017_part088 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [24852217794461202558972383070040297125]) 0) 34 false) (.node 582 (sourceLit (List.headD (raw_ints% [7497850682311426138372111932298445925]) 0) 33 true) (.node 581 (sourceLit (List.headD (raw_ints% [12373143524455703842458119438803125]) 0) 35 true) (.node 580 (sourceLit (List.headD (raw_ints% [347964978920981248973251528035043725]) 0) 33 false) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [7688403765908497219673385335789325]) 0) 35 true) .empty .empty)) (.node 586 (sourceLit (List.headD (raw_ints% [625246096437951919383190995016318793025]) 0) 31 true) (.node 585 (sourceLit (List.headD (raw_ints% [10611799809155460189390672724600575]) 0) 34 true) .empty .empty) (.node 587 (sourceLit (List.headD (raw_ints% [7865592791933298792668151250522125]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part089 : IntSourceTree :=
  (.node 592 (sourceLit (List.headD (raw_ints% [60613830926527585199975233337163650895]) 0) 33 false) (.node 590 (sourceLit (List.headD (raw_ints% [394070790438131212646653429686025016505]) 0) 32 true) (.node 589 (sourceLit (List.headD (raw_ints% [6136511353625191751213665097622825]) 0) 34 true) .empty .empty) (.node 591 (sourceLit (List.headD (raw_ints% [4973830915732494480829743059459475]) 0) 34 true) .empty .empty)) (.node 594 (sourceLit (List.headD (raw_ints% [244912037488940386809848382538584825]) 0) 28 true) (.node 593 (sourceLit (List.headD (raw_ints% [16605399272120084259390841828566615]) 0) 32 true) .empty .empty) (.node 595 (sourceLit (List.headD (raw_ints% [14182680177234958668736744026431145]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part090 : IntSourceTree :=
  (.node 588 (sourceLit (List.headD (raw_ints% [250055600839401607297179529959483600195]) 0) 33 false) treeT_J017_part088 treeT_J017_part089)

#time def treeT_J017_part091 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [16156087520077117433225391242661405]) 0) 31 true) treeT_J017_part087 treeT_J017_part090)

#time def treeT_J017_part092 : IntSourceTree :=
  (.node 542 (sourceLit (List.headD (raw_ints% [2560950204694729835642875879498125]) 0) 36 true) treeT_J017_part084 treeT_J017_part091)

#time def treeT_J017_part093 : IntSourceTree :=
  (.node 472 (sourceLit (List.headD (raw_ints% [405980627376647719666059316125075]) 0) 36 true) treeT_J017_part077 treeT_J017_part092)

#time def treeT_J017_part094 : IntSourceTree :=
  (.node 623 (sourceLit (List.headD (raw_ints% [3737185528256911703361816268580870775]) 0) 36 true) (.node 599 (sourceLit (List.headD (raw_ints% [10899194102585628320364221553194925]) 0) 32 true) (.node 598 (sourceLit (List.headD (raw_ints% [46308936642521941723774482713955285]) 0) 30 true) (.node 597 (sourceLit (List.headD (raw_ints% [12339546462491293301484939638774715]) 0) 32 true) .empty .empty) .empty) (.node 622 (sourceLit (List.headD (raw_ints% [1226524164970121750851905444913125]) 0) 39 true) .empty .empty)) (.node 625 (sourceLit (List.headD (raw_ints% [9765968384241128475524641953106924875]) 0) 37 false) (.node 624 (sourceLit (List.headD (raw_ints% [732775813756631655182273564538075]) 0) 39 true) .empty .empty) (.node 626 (sourceLit (List.headD (raw_ints% [978702087176428965607207394376075]) 0) 38 true) .empty .empty)))

#time def treeT_J017_part095 : IntSourceTree :=
  (.node 632 (sourceLit (List.headD (raw_ints% [426895666854494368803826318319025]) 0) 38 true) (.node 630 (sourceLit (List.headD (raw_ints% [537549614472451173571677068308575]) 0) 38 true) (.node 629 (sourceLit (List.headD (raw_ints% [73881697988720023315388259843028264515]) 0) 36 false) (.node 628 (sourceLit (List.headD (raw_ints% [705547886772146487077562208629975]) 0) 38 true) .empty .empty) .empty) (.node 631 (sourceLit (List.headD (raw_ints% [53046936020213880836539155723296992305]) 0) 36 true) .empty .empty)) (.node 634 (sourceLit (List.headD (raw_ints% [1400180912918177818139219508308415]) 0) 36 true) (.node 633 (sourceLit (List.headD (raw_ints% [473568175413069410456841000043942605]) 0) 41 false) .empty .empty) (.node 635 (sourceLit (List.headD (raw_ints% [20486608658569079501273845276455225]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part096 : IntSourceTree :=
  (.node 627 (sourceLit (List.headD (raw_ints% [104202186431972519337887659769780123025]) 0) 35 true) treeT_J017_part094 treeT_J017_part095)

#time def treeT_J017_part097 : IntSourceTree :=
  (.node 664 (sourceLit (List.headD (raw_ints% [54749702020516496185866913218687263325]) 0) 34 true) (.node 639 (sourceLit (List.headD (raw_ints% [3769106140305603036318636433911735]) 0) 34 true) (.node 638 (sourceLit (List.headD (raw_ints% [1010593598704717692580554368992185]) 0) 36 true) (.node 637 (sourceLit (List.headD (raw_ints% [8706948644177283232997173060125975]) 0) 33 true) .empty .empty) .empty) (.node 663 (sourceLit (List.headD (raw_ints% [31560369513135398807587588901430675]) 0) 35 true) .empty .empty)) (.node 666 (sourceLit (List.headD (raw_ints% [1875290049620816364250345165014005177025]) 0) 31 false) (.node 665 (sourceLit (List.headD (raw_ints% [36285852271268965742274835405836225]) 0) 34 true) .empty .empty) (.node 667 (sourceLit (List.headD (raw_ints% [23452873997712428106762485369512275]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part098 : IntSourceTree :=
  (.node 672 (sourceLit (List.headD (raw_ints% [909364807249949678584601724909915527775]) 0) 33 true) (.node 670 (sourceLit (List.headD (raw_ints% [2758285126077171958739077744662929480985]) 0) 32 false) (.node 669 (sourceLit (List.headD (raw_ints% [16441021023083495835268325578536375]) 0) 34 true) .empty .empty) (.node 671 (sourceLit (List.headD (raw_ints% [12227756747385943073463923126414925]) 0) 34 true) .empty .empty)) (.node 674 (sourceLit (List.headD (raw_ints% [7759185898005218161311692793102494225145]) 0) 28 false) (.node 673 (sourceLit (List.headD (raw_ints% [38037246085255194947498926916268585]) 0) 32 true) .empty .empty) (.node 675 (sourceLit (List.headD (raw_ints% [30623109036146731511718280239438135]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part099 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [1083673092295181762000280808117724584395]) 0) 33 true) treeT_J017_part097 treeT_J017_part098)

#time def treeT_J017_part100 : IntSourceTree :=
  (.node 636 (sourceLit (List.headD (raw_ints% [1177504901942021528125161077763795]) 0) 36 true) treeT_J017_part096 treeT_J017_part099)

#time def treeT_J017_part101 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [28456235573857534017417176250827625]) 0) 35 true) (.node 679 (sourceLit (List.headD (raw_ints% [21439801055965337842213518254554995]) 0) 32 true) (.node 678 (sourceLit (List.headD (raw_ints% [93002241664314590004180286248060315]) 0) 30 true) (.node 677 (sourceLit (List.headD (raw_ints% [25340610399653395598520214849666725]) 0) 32 true) .empty .empty) .empty) (.node 705 (sourceLit (List.headD (raw_ints% [93813575557481010087965481031114962825]) 0) 35 true) .empty .empty)) (.node 708 (sourceLit (List.headD (raw_ints% [17808490903535256210141987700472475]) 0) 35 true) (.node 707 (sourceLit (List.headD (raw_ints% [2708907541076596518953446443172246161225]) 0) 32 false) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [1379199884250061855261833847489837642455]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part102 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [26835798781909772402385170849801265]) 0) 33 true) (.node 712 (sourceLit (List.headD (raw_ints% [8812591412549988123033312579862725]) 0) 35 true) (.node 711 (sourceLit (List.headD (raw_ints% [3182660614238883005431390990449305419425]) 0) 33 false) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [969981533702822563123077372915540181215]) 0) 34 true) .empty .empty)) (.node 716 (sourceLit (List.headD (raw_ints% [21203069820610559286716991617327775]) 0) 33 true) (.node 715 (sourceLit (List.headD (raw_ints% [7759349790874486713947702983864705866945]) 0) 29 false) .empty .empty) (.node 717 (sourceLit (List.headD (raw_ints% [38129324766363881967028617118689075]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part103 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [12140624107303886446694909032067775]) 0) 35 true) treeT_J017_part101 treeT_J017_part102)

#time def treeT_J017_part104 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [54792942591057529005299625223353525]) 0) 34 true) (.node 747 (sourceLit (List.headD (raw_ints% [90372068297717707962906219633798225]) 0) 34 true) (.node 746 (sourceLit (List.headD (raw_ints% [4877324467460208687065240558009683987425]) 0) 31 true) (.node 719 (sourceLit (List.headD (raw_ints% [62849392541869765713631194776766435]) 0) 31 true) .empty .empty) .empty) (.node 748 (sourceLit (List.headD (raw_ints% [948145158342944570238431812822492686405]) 0) 35 false) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [36334739681829602713315713001856175]) 0) 34 true) (.node 750 (sourceLit (List.headD (raw_ints% [13791884200077666800833748524581630620625]) 0) 32 true) .empty .empty) (.node 752 (sourceLit (List.headD (raw_ints% [7274686035727715689447383705808526366625]) 0) 33 false) .empty .empty)))

#time def treeT_J017_part105 : IntSourceTree :=
  (.node 757 (sourceLit (List.headD (raw_ints% [59471668882788841548347751619644375]) 0) 32 true) (.node 755 (sourceLit (List.headD (raw_ints% [76720086091492358097822403159766925]) 0) 32 true) (.node 754 (sourceLit (List.headD (raw_ints% [131916822211966506241065596526291637420665]) 0) 28 true) .empty .empty) (.node 756 (sourceLit (List.headD (raw_ints% [7759460877318596150844569029791183748995]) 0) 30 false) .empty .empty)) (.node 759 (sourceLit (List.headD (raw_ints% [47583645384097278389289601336361985]) 0) 32 true) (.node 758 (sourceLit (List.headD (raw_ints% [212032356466596465732048650701452285]) 0) 30 true) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [3793116004268402603009343500590965074325]) 0) 33 true) .empty .empty)))

#time def treeT_J017_part106 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [102964216515544615021034074361535015]) 0) 32 true) treeT_J017_part104 treeT_J017_part105)

#time def treeT_J017_part107 : IntSourceTree :=
  (.node 718 (sourceLit (List.headD (raw_ints% [17255861610015654057875779897729245]) 0) 33 true) treeT_J017_part103 treeT_J017_part106)

#time def treeT_J017_part108 : IntSourceTree :=
  (.node 676 (sourceLit (List.headD (raw_ints% [55543222054718448433022963238941025]) 0) 31 true) treeT_J017_part100 treeT_J017_part107)

#time def treeT_J017_part109 : IntSourceTree :=
  (.node 793 (sourceLit (List.headD (raw_ints% [64411465386176080098206727177531769905]) 0) 41 false) (.node 791 (sourceLit (List.headD (raw_ints% [8487272407158274903132569757515468020025]) 0) 34 true) (.node 790 (sourceLit (List.headD (raw_ints% [21326159241876821279302358095642875]) 0) 36 true) (.node 789 (sourceLit (List.headD (raw_ints% [5171780517621840136215561098779808388075]) 0) 34 false) .empty .empty) .empty) (.node 792 (sourceLit (List.headD (raw_ints% [13761074134639807295141200210996725]) 0) 36 true) .empty .empty)) (.node 795 (sourceLit (List.headD (raw_ints% [69838086001420496477506649755078171643805]) 0) 30 true) (.node 794 (sourceLit (List.headD (raw_ints% [38064208866817421309324451755866875]) 0) 34 true) .empty .empty) (.node 796 (sourceLit (List.headD (raw_ints% [27758508135440899405552705771219575]) 0) 34 true) .empty .empty)))

#time def treeT_J017_part110 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [55166128341052387890558237314820097725225]) 0) 32 false) (.node 828 (sourceLit (List.headD (raw_ints% [5689406320954291743486207126235950447135]) 0) 34 true) (.node 799 (sourceLit (List.headD (raw_ints% [74591481962363350009208727962342925]) 0) 32 true) (.node 798 (sourceLit (List.headD (raw_ints% [21107903636386593745235985860957565]) 0) 34 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [235461366985672278005757302509949475]) 0) 34 true) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [41223775664360815301977662735870398446725]) 0) 33 true) (.node 831 (sourceLit (List.headD (raw_ints% [134274534253184967521103151763286825]) 0) 34 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [337390155792929218423484332390360185]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part111 : IntSourceTree :=
  (.node 797 (sourceLit (List.headD (raw_ints% [7759537135968128878608503087025421127145]) 0) 31 false) treeT_J017_part109 treeT_J017_part110)

#time def treeT_J017_part112 : IntSourceTree :=
  (.node 839 (sourceLit (List.headD (raw_ints% [121279583706995471572598285551298535]) 0) 32 true) (.node 837 (sourceLit (List.headD (raw_ints% [162596396200738353696073894550112225]) 0) 32 true) (.node 836 (sourceLit (List.headD (raw_ints% [147435632880159589105857868539947527036605]) 0) 30 true) (.node 835 (sourceLit (List.headD (raw_ints% [227793584843047012376773210887168075]) 0) 32 true) .empty .empty) .empty) (.node 838 (sourceLit (List.headD (raw_ints% [31038360576228982110899744396752385960865]) 0) 30 false) .empty .empty)) (.node 870 (sourceLit (List.headD (raw_ints% [192809048501918635447152586318663725]) 0) 35 true) (.node 869 (sourceLit (List.headD (raw_ints% [16550593159530423623187975351251709282345]) 0) 34 true) .empty .empty) (.node 871 (sourceLit (List.headD (raw_ints% [72140673155368937696823376829851033765275]) 0) 33 false) .empty .empty)))

#time def treeT_J017_part113 : IntSourceTree :=
  (.node 876 (sourceLit (List.headD (raw_ints% [172276568572165213565667799344728925]) 0) 33 true) (.node 874 (sourceLit (List.headD (raw_ints% [261261738059294375804835428878626435]) 0) 33 true) (.node 873 (sourceLit (List.headD (raw_ints% [49468443233791353554548123814594464994565]) 0) 34 true) .empty .empty) (.node 875 (sourceLit (List.headD (raw_ints% [1326910443101916395525097914113128498831795]) 0) 29 false) .empty .empty)) (.node 878 (sourceLit (List.headD (raw_ints% [120380588927965166205601922828197095]) 0) 33 true) (.node 877 (sourceLit (List.headD (raw_ints% [77597585008063858992233185813486474081875]) 0) 32 true) .empty .empty) (.node 879 (sourceLit (List.headD (raw_ints% [31038509759192906837599762814208310646715]) 0) 31 false) .empty .empty)))

#time def treeT_J017_part114 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [106752385983905352930820751341293375]) 0) 35 true) treeT_J017_part112 treeT_J017_part113)

#time def treeT_J017_part115 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [1187234271099075402570084614602972155544185]) 0) 28 false) treeT_J017_part111 treeT_J017_part114)

#time def treeT_J017_part116 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [817253367394130490842568504627337665]) 0) 32 true) (.node 913 (sourceLit (List.headD (raw_ints% [1370648019949556428469647689070333815]) 0) 32 true) (.node 912 (sourceLit (List.headD (raw_ints% [185505121975098690695624416395572465977275]) 0) 33 false) (.node 911 (sourceLit (List.headD (raw_ints% [636961659754489574267507193511368075]) 0) 34 true) .empty .empty) .empty) (.node 914 (sourceLit (List.headD (raw_ints% [7519195005024368657552244462871063674848505]) 0) 28 true) .empty .empty)) (.node 917 (sourceLit (List.headD (raw_ints% [526509878087922500566597302828803475]) 0) 32 true) (.node 916 (sourceLit (List.headD (raw_ints% [92146629748879749039434736415817251616775]) 0) 34 false) .empty .empty) (.node 918 (sourceLit (List.headD (raw_ints% [651819040640739854048765230904644178615865]) 0) 30 true) .empty .empty)))

#time def treeT_J017_part117 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [277346570472565513166203065047926845]) 0) 35 true) (.node 952 (sourceLit (List.headD (raw_ints% [132552318442646055334171610542518675]) 0) 37 true) (.node 951 (sourceLit (List.headD (raw_ints% [64927886693166178643221354238671201437315]) 0) 35 true) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [3671461956388906941408945940783858296435]) 0) 40 false) .empty .empty)) (.node 956 (sourceLit (List.headD (raw_ints% [161244199705491319319225176320652185]) 0) 35 true) (.node 955 (sourceLit (List.headD (raw_ints% [2211526362031571263269335594246048043420075]) 0) 31 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [814770622999101851307711077140024487016075]) 0) 32 false) .empty .empty)))

#time def treeT_J017_part118 : IntSourceTree :=
  (.node 919 (sourceLit (List.headD (raw_ints% [360242772004865193249809405761489845]) 0) 32 true) treeT_J017_part116 treeT_J017_part117)

#time def treeT_J017_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [2053397317199938608541005518301631485]) 0) 32 true) (.node 995 (sourceLit (List.headD (raw_ints% [3620291760166917719816680536139491855]) 0) 32 true) (.node 994 (sourceLit (List.headD (raw_ints% [37595811351762294321574329609772430839244025]) 0) 28 false) (.node 959 (sourceLit (List.headD (raw_ints% [170714387599983190221591248429713122315645]) 0) 33 true) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [2580112881027090259427074539909317049887175]) 0) 32 true) .empty .empty)) (.node 999 (sourceLit (List.headD (raw_ints% [1264274384634964144194172114240935675]) 0) 32 true) (.node 998 (sourceLit (List.headD (raw_ints% [7169984024633554664510453848024840074744465]) 0) 30 false) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [46441916799888579374651671986756623012924325]) 0) 29 false) .empty .empty)))

#time def treeT_J017_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [56762368323996940412359970146393891212473025]) 0) 30 false) (.node 1038 (sourceLit (List.headD (raw_ints% [1647268028039981274180010138301025105]) 0) 33 true) (.node 1037 (sourceLit (List.headD (raw_ints% [5974996385053282370161860156958658586790425]) 0) 32 true) .empty .empty) (.node 1039 (sourceLit (List.headD (raw_ints% [7852841575033487425396818841743692564007045]) 0) 31 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [54969955105059813625805335103694108769067865]) 0) 30 true) (.node 1077 (sourceLit (List.headD (raw_ints% [9847862528179871161618113805125900975]) 0) 32 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [5324797727524960952525868438963164745]) 0) 32 true) .empty .empty)))

#time def treeT_J017_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [2975314961344952442539779830856883115]) 0) 33 true) treeT_J017_part119 treeT_J017_part120)

#time def treeT_J017_part122 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [101532322289989333590248845000151595]) 0) 35 true) treeT_J017_part118 treeT_J017_part121)

#time def treeT_J017_part123 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [187570873617295776876062040124833771983985]) 0) 32 true) treeT_J017_part115 treeT_J017_part122)

#time def treeT_J017_part124 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [36281788697091225876382115966662875]) 0) 36 true) treeT_J017_part108 treeT_J017_part123)

#time def treeT_J017_part125 : IntSourceTree :=
  (.node 596 (sourceLit (List.headD (raw_ints% [26403212579557869572072417866879875]) 0) 31 true) treeT_J017_part093 treeT_J017_part124)

#time def treeT_J017_part126 : IntSourceTree :=
  (.node 357 (sourceLit (List.headD (raw_ints% [2483381558728069966372418803090125]) 0) 32 true) treeT_J017_part062 treeT_J017_part125)

#time def treeT_J017 : IntSourceTree := treeT_J017_part126

-- kcost: 1.731s estimated (577 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J009_check : treeT_J009.check 40 (sourceBaseT momentData 9) = true := by
  decide +kernel

-- kcost: 1.731s estimated (577 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J010_check : treeT_J010.check 40 (sourceBaseT momentData 10) = true := by
  decide +kernel

-- kcost: 1.731s estimated (577 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J011_check : treeT_J011.check 40 (sourceBaseT momentData 11) = true := by
  decide +kernel

-- kcost: 1.731s estimated (577 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J012_check : treeT_J012.check 40 (sourceBaseT momentData 12) = true := by
  decide +kernel

-- kcost: 1.698s estimated (566 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J013_check : treeT_J013.check 40 (sourceBaseT momentData 13) = true := by
  decide +kernel

-- kcost: 1.698s estimated (566 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J014_check : treeT_J014.check 40 (sourceBaseT momentData 14) = true := by
  decide +kernel

-- kcost: 1.698s estimated (566 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J015_check : treeT_J015.check 40 (sourceBaseT momentData 15) = true := by
  decide +kernel

-- kcost: 1.659s estimated (553 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J016_check : treeT_J016.check 40 (sourceBaseT momentData 16) = true := by
  decide +kernel

-- kcost: 1.659s estimated (553 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeT_J017_check : treeT_J017.check 40 (sourceBaseT momentData 17) = true := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
