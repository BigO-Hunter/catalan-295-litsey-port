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

#time def treeG_J021_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 9 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 44 false) (.node 8 (sourceLit (List.headD (raw_ints% [112326275241430930687590030375]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [375468046789895416399878853875]) 0) 42 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [54644634165690336084396285375]) 0) 47 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 47 true) (.node 12 (sourceLit (List.headD (raw_ints% [13336702143723546594650347275]) 0) 49 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [6526564810551439673783917725]) 0) 50 false) .empty .empty)))

#time def treeG_J021_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [241486037094158525018846925]) 0) 55 true) (.node 17 (sourceLit (List.headD (raw_ints% [1020535923455844514822206675]) 0) 52 true) (.node 16 (sourceLit (List.headD (raw_ints% [400036339468804842880651575]) 0) 54 false) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [196475174779364697389047875]) 0) 55 false) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [685889057976841245701792475]) 0) 55 true) (.node 20 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 57 false) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [73377550479464945339373537716475]) 0) 39 true) .empty .empty)))

#time def treeG_J021_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [4376084461420692498833086875]) 0) 49 true) treeG_J021_part000 treeG_J021_part001)

#time def treeG_J021_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [237684848330019367209074048339175]) 0) 35 true) (.node 26 (sourceLit (List.headD (raw_ints% [160529533726556928133836312656625]) 0) 36 true) (.node 25 (sourceLit (List.headD (raw_ints% [11903342734316464203898125]) 0) 59 false) (.node 24 (sourceLit (List.headD (raw_ints% [61263095659985695769397053876475]) 0) 38 true) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [733806069739038499157955]) 0) 63 false) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [1490786527137973977830769116895825]) 0) 32 true) (.node 29 (sourceLit (List.headD (raw_ints% [1448673487732721951627355]) 0) 62 false) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [357733154518475152853865]) 0) 64 false) .empty .empty)))

#time def treeG_J021_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [13398604121010078968229593821572255]) 0) 28 true) (.node 34 (sourceLit (List.headD (raw_ints% [7991072810010548210388175397010045]) 0) 29 true) (.node 33 (sourceLit (List.headD (raw_ints% [22097657690020577631525]) 0) 68 false) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [2731464120561156471825]) 0) 71 false) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [181337232810264878444102910417395025]) 0) 24 true) (.node 37 (sourceLit (List.headD (raw_ints% [2702369558422758804825]) 0) 71 false) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [668690152373505606225]) 0) 73 false) .empty .empty)))

#time def treeG_J021_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [2415533305743070694083385615865285]) 0) 31 true) treeG_J021_part003 treeG_J021_part004)

#time def treeG_J021_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 57 false) treeG_J021_part002 treeG_J021_part005)

#time def treeG_J021_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [13336702143723546594650347275]) 0) 50 false) (.node 51 (sourceLit (List.headD (raw_ints% [54644634165690336084396285375]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 45 false) (.node 49 (sourceLit (List.headD (raw_ints% [112326275241430930687590030375]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [6526564810551439673783917725]) 0) 51 false) (.node 54 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 48 true) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [4376084461420692498833086875]) 0) 50 true) .empty .empty)))

#time def treeG_J021_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 58 false) (.node 59 (sourceLit (List.headD (raw_ints% [196475174779364697389047875]) 0) 56 false) (.node 58 (sourceLit (List.headD (raw_ints% [1020535923455844514822206675]) 0) 53 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [241486037094158525018846925]) 0) 56 true) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [73377550479464945339373537716475]) 0) 40 true) (.node 62 (sourceLit (List.headD (raw_ints% [685889057976841245701792475]) 0) 56 true) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 58 false) .empty .empty)))

#time def treeG_J021_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [400036339468804842880651575]) 0) 55 false) treeG_J021_part007 treeG_J021_part008)

#time def treeG_J021_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [2415533305743070694083385615865285]) 0) 32 true) (.node 69 (sourceLit (List.headD (raw_ints% [237684848330019367209074048339175]) 0) 36 true) (.node 67 (sourceLit (List.headD (raw_ints% [160529533726556928133836312656625]) 0) 37 true) (.node 66 (sourceLit (List.headD (raw_ints% [11903342734316464203898125]) 0) 60 false) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [733806069739038499157955]) 0) 64 false) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [1490786527137973977830769116895825]) 0) 33 true) (.node 70 (sourceLit (List.headD (raw_ints% [1448673487732721951627355]) 0) 63 false) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [357733154518475152853865]) 0) 65 false) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [13398604121010078968229593821572255]) 0) 29 true) (.node 75 (sourceLit (List.headD (raw_ints% [7991072810010548210388175397010045]) 0) 30 true) (.node 74 (sourceLit (List.headD (raw_ints% [22097657690020577631525]) 0) 69 false) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [2731464120561156471825]) 0) 72 false) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [181337232810264878444102910417395025]) 0) 25 true) (.node 78 (sourceLit (List.headD (raw_ints% [2702369558422758804825]) 0) 72 false) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [162938963701275369381079502625]) 0) 45 false) .empty .empty))))

#time def treeG_J021_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [61263095659985695769397053876475]) 0) 39 true) treeG_J021_part009 treeG_J021_part010)

#time def treeG_J021_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [375468046789895416399878853875]) 0) 43 false) treeG_J021_part006 treeG_J021_part011)

#time def treeG_J021_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [1568784995603644480713748125]) 0) 50 true) (.node 93 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 47 false) (.node 92 (sourceLit (List.headD (raw_ints% [10326983005491697372436484525]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 46 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [20146839476895653515516776825]) 0) 50 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [2335012614509003469188673525]) 0) 51 true) (.node 96 (sourceLit (List.headD (raw_ints% [4926419452676220302261311425]) 0) 52 false) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [603597504158244988372255275]) 0) 55 false) .empty .empty)))

#time def treeG_J021_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [183550656386384370691168275]) 0) 59 true) (.node 101 (sourceLit (List.headD (raw_ints% [280055090399792854373595225]) 0) 55 true) (.node 100 (sourceLit (List.headD (raw_ints% [74080803605334230163083625]) 0) 58 false) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [124037997906378170813820651956475]) 0) 39 false) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [9102556208594943214745625]) 0) 61 false) (.node 104 (sourceLit (List.headD (raw_ints% [525757308175733866945591247855325]) 0) 38 true) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [819679996833214204176516549366975]) 0) 36 true) .empty .empty)))

#time def treeG_J021_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [537563849267527464784512825]) 0) 54 true) treeG_J021_part013 treeG_J021_part014)

#time def treeG_J021_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [9510758911360721128562767319301315]) 0) 31 true) (.node 110 (sourceLit (List.headD (raw_ints% [6115128619422645772859600429957775]) 0) 32 true) (.node 109 (sourceLit (List.headD (raw_ints% [4421775070179586041636285]) 0) 62 false) (.node 108 (sourceLit (List.headD (raw_ints% [1046551421482436057861616452913825]) 0) 35 true) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [545470166607123399386745]) 0) 65 false) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [30657460081878582894945994456834515]) 0) 29 true) (.node 113 (sourceLit (List.headD (raw_ints% [269342523758392842327765]) 0) 66 false) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [16634729448898264687875]) 0) 70 false) .empty .empty)))

#time def treeG_J021_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [276287808015206061124439156625]) 0) 45 false) (.node 118 (sourceLit (List.headD (raw_ints% [676173430934380175522591094163229295]) 0) 24 true) (.node 117 (sourceLit (List.headD (raw_ints% [8223486923821867082475]) 0) 71 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [254209925756156649825]) 0) 76 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 47 false) (.node 131 (sourceLit (List.headD (raw_ints% [7210205134467574325399218125]) 0) 52 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [27971229878243242895095590825]) 0) 50 false) .empty .empty)))

#time def treeG_J021_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [50529978359074306714875809354508105]) 0) 28 true) treeG_J021_part016 treeG_J021_part017)

#time def treeG_J021_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [8968118455360310207266305]) 0) 61 false) treeG_J021_part015 treeG_J021_part018)

#time def treeG_J021_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [50890291172360036372900925]) 0) 59 false) (.node 137 (sourceLit (List.headD (raw_ints% [3326274094801000930738705125]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [1238514470213403537405590625]) 0) 50 false) (.node 135 (sourceLit (List.headD (raw_ints% [3405068666586053460433214775]) 0) 53 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [293940767597314439544260175]) 0) 52 true) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [99848039641972223263286625]) 0) 58 false) (.node 140 (sourceLit (List.headD (raw_ints% [54591775079210414746818975]) 0) 55 true) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 57 false) .empty .empty)))

#time def treeG_J021_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [329575231553328638021340118355175]) 0) 38 true) (.node 145 (sourceLit (List.headD (raw_ints% [232247106257874085588097096989425]) 0) 40 true) (.node 144 (sourceLit (List.headD (raw_ints% [782516193114233719827553725]) 0) 58 true) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [24506882100063308655084375]) 0) 60 false) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [404433286576208345326271202287325]) 0) 37 true) (.node 148 (sourceLit (List.headD (raw_ints% [6032894176404156210634485]) 0) 62 false) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [1486550791223432045004465]) 0) 64 false) .empty .empty)))

#time def treeG_J021_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [98707774192921558076597094836475]) 0) 41 false) treeG_J021_part020 treeG_J021_part021)

#time def treeG_J021_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [247418099062057648539244091872917135]) 0) 26 true) (.node 155 (sourceLit (List.headD (raw_ints% [11333193635934017342278909529912235]) 0) 31 true) (.node 153 (sourceLit (List.headD (raw_ints% [3547612802808825217239690851718015]) 0) 33 true) (.node 152 (sourceLit (List.headD (raw_ints% [733207178695771645919625]) 0) 65 false) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [180951892998310531801665]) 0) 67 false) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [18565687119032113873323107766467925]) 0) 30 true) (.node 156 (sourceLit (List.headD (raw_ints% [11171801207775951744225]) 0) 71 false) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [2760558682699554138825]) 0) 73 false) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [35795620279590832274674404825]) 0) 50 false) (.node 172 (sourceLit (List.headD (raw_ints% [18513837532378599929160387975]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [7084302769620668233959978375]) 0) 51 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [91666584322061373815179114125]) 0) 47 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [8693855213667993539471547675]) 0) 52 false) (.node 175 (sourceLit (List.headD (raw_ints% [4541219724115812970487165625]) 0) 51 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [1786763542361203503297132075]) 0) 52 false) .empty .empty))))

#time def treeG_J021_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [2312171046142335897514415656530975]) 0) 34 true) treeG_J021_part022 treeG_J021_part023)

#time def treeG_J021_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 49 false) treeG_J021_part019 treeG_J021_part024)

#time def treeG_J021_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [170007916317171525290783775375]) 0) 47 false) treeG_J021_part012 treeG_J021_part025)

#time def treeG_J021_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [570018296561292937046435175]) 0) 58 false) (.node 181 (sourceLit (List.headD (raw_ints% [170871540241372024879957275]) 0) 55 false) (.node 180 (sourceLit (List.headD (raw_ints% [129480361084105915328520075]) 0) 58 false) (.node 179 (sourceLit (List.headD (raw_ints% [781186930937740490024765475]) 0) 53 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [19339739890757504833296615860475]) 0) 39 true) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [818926417948613492686536225]) 0) 59 true) (.node 184 (sourceLit (List.headD (raw_ints% [2105081695262478796171144765238925]) 0) 38 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [6612227403418756534642590554294625]) 0) 36 true) .empty .empty)))

#time def treeG_J021_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [117635078077038580702215]) 0) 68 false) (.node 189 (sourceLit (List.headD (raw_ints% [7644013282628726379632685]) 0) 62 false) (.node 188 (sourceLit (List.headD (raw_ints% [4226652283370822150479825440768975]) 0) 35 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [19768601721454688328021756516431025]) 0) 32 true) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [115966163734344700897965]) 0) 68 false) (.node 192 (sourceLit (List.headD (raw_ints% [27483977826916653231667883185194285]) 0) 31 true) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [82866149608003824056724112798141965]) 0) 29 true) .empty .empty)))

#time def treeG_J021_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [7769381822351499223909035]) 0) 62 false) treeG_J021_part027 treeG_J021_part028)

#time def treeG_J021_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [177107569240516705848999459375]) 0) 47 false) (.node 198 (sourceLit (List.headD (raw_ints% [1700234520301730400262766699944665105]) 0) 24 true) (.node 197 (sourceLit (List.headD (raw_ints% [14120115491730036405975]) 0) 71 false) (.node 196 (sourceLit (List.headD (raw_ints% [130801119815869970761586743124087655]) 0) 28 true) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [1743718979674927539525]) 0) 74 false) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [76639275416805410894657947875]) 0) 48 false) (.node 213 (sourceLit (List.headD (raw_ints% [46084120251271156821545961075]) 0) 50 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [22175345613246618432941545725]) 0) 51 false) .empty .empty)))

#time def treeG_J021_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [890370481096161319518403425]) 0) 54 false) (.node 218 (sourceLit (List.headD (raw_ints% [3867467852319721446138524325]) 0) 52 false) (.node 217 (sourceLit (List.headD (raw_ints% [2683790559433496304366421275]) 0) 54 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [1304834427726750372027779775]) 0) 55 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [234962427335676366448239975]) 0) 56 true) (.node 221 (sourceLit (List.headD (raw_ints% [159112682526239607393753525]) 0) 58 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [216755288276600620986490805533425]) 0) 40 true) .empty .empty)))

#time def treeG_J021_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [16926364426249848344543071875]) 0) 50 false) treeG_J021_part030 treeG_J021_part031)

#time def treeG_J021_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [114412975202717473050165]) 0) 68 false) treeG_J021_part029 treeG_J021_part032)

#time def treeG_J021_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [3417785710218405459827283036194325]) 0) 36 true) (.node 227 (sourceLit (List.headD (raw_ints% [5953076940312099258599910317584275]) 0) 37 true) (.node 226 (sourceLit (List.headD (raw_ints% [105429162506084600167702575]) 0) 63 true) (.node 225 (sourceLit (List.headD (raw_ints% [2569575907778226967347338959217775]) 0) 39 false) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [9505869468298842237183585]) 0) 62 false) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [15144259629170016532992925203369075]) 0) 33 true) (.node 230 (sourceLit (List.headD (raw_ints% [4670911700181862289623755]) 0) 63 false) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [1148954070536845645315815]) 0) 65 false) .empty .empty)))

#time def treeG_J021_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [93669745577805743014940527591151805]) 0) 29 true) (.node 235 (sourceLit (List.headD (raw_ints% [60199762336135789372166293738317495]) 0) 30 true) (.node 234 (sourceLit (List.headD (raw_ints% [282912761939068271790195]) 0) 67 false) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [69725770371613666073265]) 0) 69 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [1205398322177615103184278516198830835]) 0) 25 true) (.node 238 (sourceLit (List.headD (raw_ints% [8598998126330928128325]) 0) 72 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [262548554158972037882819804625]) 0) 47 false) .empty .empty)))

#time def treeG_J021_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [20388752221299002797188501481758255]) 0) 32 true) treeG_J021_part034 treeG_J021_part035)

#time def treeG_J021_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [186181480083391727395809112090875]) 0) 39 false) (.node 258 (sourceLit (List.headD (raw_ints% [3248502032382481654738647975]) 0) 54 false) (.node 256 (sourceLit (List.headD (raw_ints% [6740745199789312446734999025]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [58474396520342159012709285375]) 0) 49 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [13352837341527441337948807725]) 0) 51 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [786912983390326710713699475]) 0) 56 false) (.node 259 (sourceLit (List.headD (raw_ints% [1543140460690990478056879425]) 0) 54 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [359749470427394647319223075]) 0) 56 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [47725441927870388012200013901779025]) 0) 36 false) (.node 264 (sourceLit (List.headD (raw_ints% [3839124001475283764063071209506325]) 0) 38 true) (.node 263 (sourceLit (List.headD (raw_ints% [1374999020458262240541110325]) 0) 57 true) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [685369801046358271651740075]) 0) 61 false) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [43397963239125971918319457099905225]) 0) 35 true) (.node 267 (sourceLit (List.headD (raw_ints% [429486031846689899894719335]) 0) 62 true) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [11367725653968958094734485]) 0) 62 false) .empty .empty))))

#time def treeG_J021_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [56372620222951481368417517325]) 0) 50 false) treeG_J021_part036 treeG_J021_part037)

#time def treeG_J021_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [1922552786236819593920424075]) 0) 58 false) treeG_J021_part033 treeG_J021_part038)

#time def treeG_J021_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [84249893368175399370015]) 0) 69 false) (.node 273 (sourceLit (List.headD (raw_ints% [685089415599466841723955]) 0) 66 false) (.node 272 (sourceLit (List.headD (raw_ints% [93670099206443479032275518441758315]) 0) 31 true) (.node 271 (sourceLit (List.headD (raw_ints% [2788750450949244998388315]) 0) 64 false) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [243353885932780220698291910909990115]) 0) 29 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [41485539388153593261315]) 0) 70 false) (.node 276 (sourceLit (List.headD (raw_ints% [350796978873216344215743606782452305]) 0) 28 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [4294629196677837152693427065889050415]) 0) 24 true) .empty .empty)))

#time def treeG_J021_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [2028477320177908071184288875]) 0) 55 false) (.node 295 (sourceLit (List.headD (raw_ints% [2137329663106553933467248225]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [92954639371083313494080928375]) 0) 49 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [10387008023523077667041553375]) 0) 52 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [242958450581966410338858525]) 0) 58 false) (.node 298 (sourceLit (List.headD (raw_ints% [1185671186150964986476285425]) 0) 55 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [2195910440285819636595355425]) 0) 54 false) .empty .empty)))

#time def treeG_J021_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [5111560166981073049275]) 0) 73 false) treeG_J021_part040 treeG_J021_part041)

#time def treeG_J021_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [896228126058527471987145225]) 0) 62 false) (.node 304 (sourceLit (List.headD (raw_ints% [51524246979610653663461475]) 0) 64 true) (.node 303 (sourceLit (List.headD (raw_ints% [100734192089998087095574979406075]) 0) 42 false) (.node 302 (sourceLit (List.headD (raw_ints% [954461368190465661086686125]) 0) 56 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [1602174977313377682852602542181025]) 0) 41 true) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [868477933161678642026622255]) 0) 62 true) (.node 307 (sourceLit (List.headD (raw_ints% [13419629717045621817699981054840825]) 0) 39 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [9995044382226891614623043515927725]) 0) 38 true) .empty .empty)))

#time def treeG_J021_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [6284010213443727655215]) 0) 73 false) (.node 312 (sourceLit (List.headD (raw_ints% [409949095103099838268125]) 0) 67 false) (.node 311 (sourceLit (List.headD (raw_ints% [18614070344091067463364593859604575]) 0) 35 true) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [18320336746286119058771754240000015]) 0) 34 true) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [98774016364737132666765]) 0) 69 false) (.node 315 (sourceLit (List.headD (raw_ints% [45788530899161107831531404292918155]) 0) 32 true) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [64281808323852650300200769797825125]) 0) 31 true) .empty .empty)))

#time def treeG_J021_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [3348406976893547902555365]) 0) 64 false) treeG_J021_part043 treeG_J021_part044)

#time def treeG_J021_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [468687618337847495926192425]) 0) 57 false) treeG_J021_part042 treeG_J021_part045)

#time def treeG_J021_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [4865407248329150629998507525]) 0) 54 false) (.node 336 (sourceLit (List.headD (raw_ints% [10357892105063119021002986775]) 0) 53 false) (.node 335 (sourceLit (List.headD (raw_ints% [127434882221824467975452571375]) 0) 49 false) (.node 319 (sourceLit (List.headD (raw_ints% [772307718625055512377287137422554895]) 0) 27 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [28195194752564869330217405775]) 0) 51 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [1156754621265404571997168725]) 0) 56 false) (.node 339 (sourceLit (List.headD (raw_ints% [3199544283912869467848262275]) 0) 54 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [1476411499431030341956909275]) 0) 55 false) .empty .empty)))

#time def treeG_J021_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [150264640475926559714766576601364625]) 0) 36 true) (.node 344 (sourceLit (List.headD (raw_ints% [7062618148355222551121470550500725]) 0) 38 false) (.node 343 (sourceLit (List.headD (raw_ints% [1164730194324363950813898225]) 0) 58 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [1509757752720128730267123675]) 0) 61 true) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [472826114184585870084718850854811625]) 0) 35 false) (.node 347 (sourceLit (List.headD (raw_ints% [2221942283963744843869009785]) 0) 62 false) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [1748323591977326242147978995]) 0) 62 true) .empty .empty)))

#time def treeG_J021_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [59545813959721660548342462027525]) 0) 39 false) treeG_J021_part047 treeG_J021_part048)

#time def treeG_J021_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [12161513734228441324157970002354181585]) 0) 24 true) (.node 354 (sourceLit (List.headD (raw_ints% [929147665829531399063100360450010845]) 0) 29 true) (.node 352 (sourceLit (List.headD (raw_ints% [501980151804470679795391485065588085]) 0) 31 true) (.node 351 (sourceLit (List.headD (raw_ints% [3908063502837850806722415]) 0) 64 false) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [954706964812932511348545]) 0) 66 false) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [1114436009899939106393261330590928655]) 0) 28 true) (.node 355 (sourceLit (List.headD (raw_ints% [116838433462023885596865]) 0) 69 false) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [28644238488291769702725]) 0) 71 false) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [18709825263357149438407122375]) 0) 52 false) (.node 376 (sourceLit (List.headD (raw_ints% [85886850127732157307286357875]) 0) 50 false) (.node 359 (sourceLit (List.headD (raw_ints% [14064422801529590906115]) 0) 72 false) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [6300937464707302878634409025]) 0) 54 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [4203178127539919299101169125]) 0) 54 false) (.node 379 (sourceLit (List.headD (raw_ints% [2921739643673419347287639325]) 0) 55 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [172016750731889269017744075]) 0) 59 false) .empty .empty))))

#time def treeG_J021_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [1189765139919507840285298269396961425]) 0) 32 true) treeG_J021_part049 treeG_J021_part050)

#time def treeG_J021_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [24287543135491737004665]) 0) 71 false) treeG_J021_part046 treeG_J021_part051)

#time def treeG_J021_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [89600541005534286386451300641787375]) 0) 32 true) treeG_J021_part039 treeG_J021_part052)

#time def treeG_J021_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [2119079086484510953994194575]) 0) 54 false) treeG_J021_part026 treeG_J021_part053)

#time def treeG_J021_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [203943159344109046985566500820727925]) 0) 37 true) (.node 385 (sourceLit (List.headD (raw_ints% [13471318057608733282531880719224825]) 0) 39 false) (.node 384 (sourceLit (List.headD (raw_ints% [2813506097671904868044665425]) 0) 59 false) (.node 383 (sourceLit (List.headD (raw_ints% [343390954400270687833957455596775]) 0) 40 true) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [601496469694664050563567225]) 0) 64 true) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [512806291713493436543211024918522525]) 0) 36 false) (.node 388 (sourceLit (List.headD (raw_ints% [5312362501089168329764641825]) 0) 62 false) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [1755020405931113337953089725]) 0) 63 true) .empty .empty)))

#time def treeG_J021_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [745993542232886967736974743278338225]) 0) 30 true) (.node 393 (sourceLit (List.headD (raw_ints% [428698804819326203560304468105588025]) 0) 32 true) (.node 392 (sourceLit (List.headD (raw_ints% [2268267122425451453649915]) 0) 65 false) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [552530311152533941414785]) 0) 67 false) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [857308776604528505192458251399628155]) 0) 29 true) (.node 396 (sourceLit (List.headD (raw_ints% [134902850559310638526965]) 0) 69 false) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [33000933841091802400785]) 0) 71 false) .empty .empty)))

#time def treeG_J021_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [1115308858543143570431839893958543125]) 0) 33 true) treeG_J021_part055 treeG_J021_part056)

#time def treeG_J021_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [1363383314054444478572129925]) 0) 56 false) (.node 419 (sourceLit (List.headD (raw_ints% [12310736695531410502710597825]) 0) 53 false) (.node 418 (sourceLit (List.headD (raw_ints% [7736467681085455127270310525]) 0) 54 false) (.node 417 (sourceLit (List.headD (raw_ints% [14422913843791821994267238025]) 0) 53 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [220623127801001846911308825]) 0) 59 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [451877564352040805189393325]) 0) 59 true) (.node 422 (sourceLit (List.headD (raw_ints% [301199458871161383750757560346875]) 0) 39 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [9809745783557388053793130195274925]) 0) 38 true) .empty .empty)))

#time def treeG_J021_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [12373048594155662901677262645]) 0) 62 false) (.node 427 (sourceLit (List.headD (raw_ints% [7033914041521057248377547585]) 0) 62 true) (.node 426 (sourceLit (List.headD (raw_ints% [365805729397666292235276668108961825]) 0) 36 false) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [2104371388937458245969250857420635025]) 0) 35 true) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [439732117358487797189953035]) 0) 66 true) (.node 430 (sourceLit (List.headD (raw_ints% [17599566474751297809668051066789682225]) 0) 32 false) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [8420490716540677883659327666602756915]) 0) 31 true) .empty .empty)))

#time def treeG_J021_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [5833021603112162328578912775]) 0) 60 false) treeG_J021_part058 treeG_J021_part059)

#time def treeG_J021_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [9072282859728219274648821452663962005]) 0) 25 true) treeG_J021_part057 treeG_J021_part060)

#time def treeG_J021_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [42706247968461383008159358087222020335]) 0) 24 true) (.node 436 (sourceLit (List.headD (raw_ints% [4853512327963156635502536615635777145]) 0) 28 true) (.node 435 (sourceLit (List.headD (raw_ints% [318853444228486170221055]) 0) 68 false) (.node 434 (sourceLit (List.headD (raw_ints% [5930033211279687857901771129239397555]) 0) 29 true) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [77614373582727099121515]) 0) 70 false) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [38981830111810138538661829725]) 0) 52 false) (.node 439 (sourceLit (List.headD (raw_ints% [9468255519781105747335]) 0) 73 false) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [150460251169126118124458475]) 0) 60 false) .empty .empty)))

#time def treeG_J021_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [3717261226375986478423452075]) 0) 59 true) (.node 462 (sourceLit (List.headD (raw_ints% [551204124217081069068509175]) 0) 58 false) (.node 461 (sourceLit (List.headD (raw_ints% [269229504870114424804873575]) 0) 59 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [322295206635716035792357507971825]) 0) 41 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [10644993360669474733087450575]) 0) 61 false) (.node 465 (sourceLit (List.headD (raw_ints% [11640531920583060668162505457249875]) 0) 40 true) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [284874444370887669610421584464844875]) 0) 38 false) .empty .empty)))

#time def treeG_J021_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [2026889641997872800902357175]) 0) 56 false) treeG_J021_part062 treeG_J021_part063)

#time def treeG_J021_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [91975296834587765847045]) 0) 70 false) (.node 472 (sourceLit (List.headD (raw_ints% [1761196736556376640213462055]) 0) 65 true) (.node 470 (sourceLit (List.headD (raw_ints% [7064034500043388119815176185]) 0) 64 false) (.node 469 (sourceLit (List.headD (raw_ints% [1308588840325475841256230941169578775]) 0) 37 true) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [9357437666647220690049945480374112675]) 0) 34 false) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [761029846459985000886585]) 0) 67 false) (.node 473 (sourceLit (List.headD (raw_ints% [3995895955860675840049511599248584445]) 0) 33 true) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [2592019834523400445082398192980529665]) 0) 31 true) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [6667773354069682008987807975]) 0) 55 false) (.node 478 (sourceLit (List.headD (raw_ints% [22306719870817648360365]) 0) 72 false) (.node 477 (sourceLit (List.headD (raw_ints% [1998101775679314065155039182118074495]) 0) 30 true) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [16816982554366581866755268317279029165]) 0) 26 true) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [2690395969941301123232584425]) 0) 56 false) (.node 500 (sourceLit (List.headD (raw_ints% [381217876875502625586525075]) 0) 59 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [263415735726208822457632667211525]) 0) 39 false) .empty .empty))))

#time def treeG_J021_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [19380190584131282826519736995]) 0) 62 true) treeG_J021_part064 treeG_J021_part065)

#time def treeG_J021_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [656780078806259471150685]) 0) 67 false) treeG_J021_part061 treeG_J021_part066)

#time def treeG_J021_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [6662362498871660959735996208858153025]) 0) 35 false) (.node 506 (sourceLit (List.headD (raw_ints% [738302750856324233616476842740957825]) 0) 36 true) (.node 505 (sourceLit (List.headD (raw_ints% [4775141414744074403501182425]) 0) 61 true) (.node 504 (sourceLit (List.headD (raw_ints% [14966469089728844626470850322824125]) 0) 38 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [1104931712636908248841562385]) 0) 66 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [101349252255581751650066831301642723825]) 0) 32 true) (.node 509 (sourceLit (List.headD (raw_ints% [51133429762418228554716736635]) 0) 62 true) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [7943498734760363714195082255]) 0) 65 false) .empty .empty)))

#time def treeG_J021_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [36618805024411250485815834472052697495]) 0) 28 true) (.node 514 (sourceLit (List.headD (raw_ints% [121938637376261939023682600046715304685]) 0) 29 true) (.node 513 (sourceLit (List.headD (raw_ints% [1762510296713989159155763425]) 0) 66 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [221088201115749415332765]) 0) 69 false) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [213050779318490817331685657223891515025]) 0) 24 true) (.node 517 (sourceLit (List.headD (raw_ints% [106336220086448432572575]) 0) 70 false) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [6419232175518271306515]) 0) 74 false) .empty .empty)))

#time def treeG_J021_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [158139493382896208924458455352588559715]) 0) 31 false) treeG_J021_part068 treeG_J021_part069)

#time def treeG_J021_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [38247532930894965962795861237323875]) 0) 39 false) (.node 543 (sourceLit (List.headD (raw_ints% [381174677545223249127082348732125]) 0) 40 true) (.node 542 (sourceLit (List.headD (raw_ints% [1587987721507138985095566075]) 0) 57 false) (.node 541 (sourceLit (List.headD (raw_ints% [493206248880890826368176575]) 0) 59 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [5723424603514230226939257075]) 0) 59 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [1308051639598099572837320011670647575]) 0) 37 true) (.node 546 (sourceLit (List.headD (raw_ints% [20195276190157623540089815425]) 0) 61 true) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [54738005388512346789449733315]) 0) 62 false) .empty .empty)))

#time def treeG_J021_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [166131285294617560604557478551085728605]) 0) 32 false) (.node 551 (sourceLit (List.headD (raw_ints% [120064127588876193030166722262390949175]) 0) 33 true) (.node 550 (sourceLit (List.headD (raw_ints% [65261498762505004794347089005]) 0) 63 true) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [17648194206077104068603626565]) 0) 65 false) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [116754597707215138133517803660754245355]) 0) 30 true) (.node 554 (sourceLit (List.headD (raw_ints% [881635663280224572078325005]) 0) 68 true) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [16139113035145206185715]) 0) 73 false) .empty .empty)))

#time def treeG_J021_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [9279540179522612642248458091197310575]) 0) 36 false) treeG_J021_part071 treeG_J021_part072)

#time def treeG_J021_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [290055232004488075505340675]) 0) 60 false) treeG_J021_part070 treeG_J021_part073)

#time def treeG_J021_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [418175655631104763420238925]) 0) 58 true) (.node 581 (sourceLit (List.headD (raw_ints% [6591371454202317292938317175]) 0) 56 false) (.node 559 (sourceLit (List.headD (raw_ints% [179416814209757653598175120589333456695]) 0) 25 true) (.node 558 (sourceLit (List.headD (raw_ints% [61722780344813135851845]) 0) 71 false) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [770912735526849135842041573402875]) 0) 39 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [15273707433002379033941621925]) 0) 60 false) (.node 584 (sourceLit (List.headD (raw_ints% [18015866510090630619487509112681125]) 0) 38 true) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [1350263277750643689021210622538139825]) 0) 36 false) .empty .empty)))

#time def treeG_J021_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [81148496232025732222737253515]) 0) 64 true) (.node 589 (sourceLit (List.headD (raw_ints% [160609440539442922133616203265]) 0) 62 false) (.node 588 (sourceLit (List.headD (raw_ints% [17126775615656457542434556302223333625]) 0) 35 true) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [398294538000305356202017490219956662225]) 0) 32 false) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [9705352251395546613879694995]) 0) 67 false) (.node 592 (sourceLit (List.headD (raw_ints% [1118652514093905753165792233451716153115]) 0) 31 true) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [2780039202090142908696602256864086962365]) 0) 29 false) .empty .empty)))

#time def treeG_J021_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [37874183592348155521554813585]) 0) 62 true) treeG_J021_part075 treeG_J021_part076)

#time def treeG_J021_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [7032924930123199572785421293750625]) 0) 42 true) (.node 599 (sourceLit (List.headD (raw_ints% [36045851642740050625785]) 0) 72 false) (.node 597 (sourceLit (List.headD (raw_ints% [151889588475874866398865]) 0) 70 false) (.node 596 (sourceLit (List.headD (raw_ints% [897417976633309854582326594813981265345]) 0) 28 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [1874795714956877013420682733676367589295]) 0) 24 true) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [144010926634009048121140490266875]) 0) 43 false) (.node 622 (sourceLit (List.headD (raw_ints% [1250845933173794576960687775]) 0) 59 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [95962504049145859224367125]) 0) 65 true) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [3300789474397383773085376799177580525]) 0) 39 true) (.node 627 (sourceLit (List.headD (raw_ints% [332289364668592907732316329276098425]) 0) 40 false) (.node 626 (sourceLit (List.headD (raw_ints% [17734491811580001287015718675]) 0) 62 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [130486372573208657832559360485]) 0) 62 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [64794833198647693654023026560293451425]) 0) 36 false) (.node 630 (sourceLit (List.headD (raw_ints% [112935469650973963463981646135]) 0) 64 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [6174793152381427268208805005]) 0) 69 true) .empty .empty))))

#time def treeG_J021_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [440928375740670160746828885]) 0) 70 true) treeG_J021_part077 treeG_J021_part078)

#time def treeG_J021_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [32622601473052622355505756107816548505]) 0) 29 true) treeG_J021_part074 treeG_J021_part079)

#time def treeG_J021_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [250770422142280468564475625]) 0) 61 false) treeG_J021_part067 treeG_J021_part080)

#time def treeG_J021_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [22541702032765432636755]) 0) 73 false) (.node 636 (sourceLit (List.headD (raw_ints% [440992932192810741571571745]) 0) 71 true) (.node 635 (sourceLit (List.headD (raw_ints% [362099224974669755853765007565605150965]) 0) 33 false) (.node 634 (sourceLit (List.headD (raw_ints% [330843372333617849561188125]) 0) 73 false) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [108099421895032154028352604838270589605]) 0) 32 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [5421559388326283071262990025]) 0) 58 false) (.node 639 (sourceLit (List.headD (raw_ints% [211922362593389919977813451635879266575]) 0) 28 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [27232565814667209699240500489761125]) 0) 38 false) .empty .empty)))

#time def treeG_J021_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [421582185685860237798734924235]) 0) 62 true) (.node 667 (sourceLit (List.headD (raw_ints% [73343167215508158095586250935]) 0) 62 false) (.node 666 (sourceLit (List.headD (raw_ints% [2250477668806413234337744548138219825]) 0) 36 true) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [38393294954446403637302801375893632825]) 0) 35 false) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [307019435533973659150700545785]) 0) 64 false) (.node 670 (sourceLit (List.headD (raw_ints% [1243296643446035602111873950809417276625]) 0) 32 true) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [5265521838807358147023265933310497044315]) 0) 31 false) .empty .empty)))

#time def treeG_J021_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [21415307692147714024301117925]) 0) 60 true) treeG_J021_part082 treeG_J021_part083)

#time def treeG_J021_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [53472108295299585849095850943518174288465]) 0) 24 true) (.node 676 (sourceLit (List.headD (raw_ints% [24071768375012174229223287079012710927105]) 0) 28 false) (.node 675 (sourceLit (List.headD (raw_ints% [5734422333078555753725838885]) 0) 70 false) (.node 674 (sourceLit (List.headD (raw_ints% [23336579992306515929022197648908917069885]) 0) 29 true) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [1764123618359718841152685845]) 0) 70 true) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [11563159647471618061622486025]) 0) 59 false) (.node 679 (sourceLit (List.headD (raw_ints% [54120956488321679921235]) 0) 72 false) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [83495965255652806281523870839766125]) 0) 39 false) .empty .empty)))

#time def treeG_J021_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [647453124987808164726698216505]) 0) 63 true) (.node 708 (sourceLit (List.headD (raw_ints% [277172707004224974023731862355]) 0) 62 false) (.node 707 (sourceLit (List.headD (raw_ints% [4908792586155156496196275182347007225]) 0) 37 true) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [64799610749625473821985815769314277025]) 0) 36 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [405816125972076495442041425865]) 0) 65 false) (.node 711 (sourceLit (List.headD (raw_ints% [1761655309035217151344058163291764888025]) 0) 33 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [6550305638195881460793615645313298926035]) 0) 32 false) .empty .empty)))

#time def treeG_J021_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [56884291315307716598332555275]) 0) 61 true) treeG_J021_part085 treeG_J021_part086)

#time def treeG_J021_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [59103697470446964759550135035]) 0) 67 true) treeG_J021_part084 treeG_J021_part087)

#time def treeG_J021_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [51776729394552466489273343330431140155865]) 0) 25 true) (.node 717 (sourceLit (List.headD (raw_ints% [24936563750172431461450107917718875643945]) 0) 29 false) (.node 716 (sourceLit (List.headD (raw_ints% [3087707632635683247648705315]) 0) 72 false) (.node 715 (sourceLit (List.headD (raw_ints% [26233373792103873975852317709433758277605]) 0) 30 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [1764213785167849902883232865]) 0) 71 true) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [3586413112896858134842126481574477825]) 0) 36 false) (.node 745 (sourceLit (List.headD (raw_ints% [16489233669809666042961801975]) 0) 61 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [65113729265407937346959403105]) 0) 63 true) .empty .empty)))

#time def treeG_J021_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [19358764311089095357775731239644616148515]) 0) 31 true) (.node 750 (sourceLit (List.headD (raw_ints% [3316884187434050764415420055427474141425]) 0) 32 false) (.node 749 (sourceLit (List.headD (raw_ints% [975927599694310185846198648945]) 0) 62 false) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [477236280260890911938699381145]) 0) 65 true) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [128141470203440619301720047973921699886445]) 0) 29 false) (.node 753 (sourceLit (List.headD (raw_ints% [524023520912970424961141695935]) 0) 66 false) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [81159530051279847452959832805]) 0) 69 true) .empty .empty)))

#time def treeG_J021_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [77663635643687655606873002834669690625]) 0) 35 true) treeG_J021_part089 treeG_J021_part090)

#time def treeG_J021_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [811690362341059175286448432725]) 0) 64 false) (.node 786 (sourceLit (List.headD (raw_ints% [89862758654927048684256159225]) 0) 61 false) (.node 758 (sourceLit (List.headD (raw_ints% [1649412188306335199381902757677526215500945]) 0) 24 false) (.node 757 (sourceLit (List.headD (raw_ints% [26465784679445184822342328365]) 0) 70 false) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [441066976531084556140788525]) 0) 74 true) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [537627624065856723411569474775]) 0) 62 true) (.node 787 (sourceLit (List.headD (raw_ints% [4247602849526007315519200831960742525]) 0) 38 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [71231623196656564714429409301991983825]) 0) 37 true) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [663404891683215896852158006005]) 0) 67 false) (.node 792 (sourceLit (List.headD (raw_ints% [1360288686493858319319440188155]) 0) 65 true) (.node 791 (sourceLit (List.headD (raw_ints% [2539269748234633957879739109359619514725]) 0) 34 false) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [12954534974642488409284673442478957537275]) 0) 33 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [93510360581822580443554654065]) 0) 70 true) (.node 795 (sourceLit (List.headD (raw_ints% [77187421997772246638786182841677729082025]) 0) 31 false) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [129437661231007798748745968336100826395945]) 0) 30 true) .empty .empty))))

#time def treeG_J021_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [233938758711843166036041828754482777147945]) 0) 28 true) treeG_J021_part091 treeG_J021_part092)

#time def treeG_J021_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [69690685385122735945508155035]) 0) 68 true) treeG_J021_part088 treeG_J021_part093)

#time def treeG_J021_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [7875708072020070906138902250754961106225]) 0) 32 true) (.node 828 (sourceLit (List.headD (raw_ints% [145625281236103772655180216146041571025]) 0) 35 false) (.node 827 (sourceLit (List.headD (raw_ints% [220090217185742923378174965435]) 0) 62 false) (.node 799 (sourceLit (List.headD (raw_ints% [850594458850443832935588050503978677828405]) 0) 26 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [2051182847826023632669337598495]) 0) 62 true) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [59987080282843238683851556989398528384115]) 0) 31 false) (.node 831 (sourceLit (List.headD (raw_ints% [644463321300975043612573906935]) 0) 66 false) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [942156103703414372140290942045]) 0) 67 true) .empty .empty)))

#time def treeG_J021_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [18217432825875333439221386704698431994181905]) 0) 24 true) (.node 836 (sourceLit (List.headD (raw_ints% [1468937510676199112256620754221326442460345]) 0) 28 false) (.node 835 (sourceLit (List.headD (raw_ints% [825723951785775591758077671615]) 0) 68 false) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [213486505843090345709451636495]) 0) 70 true) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [977808058437342570167919405645]) 0) 62 false) (.node 839 (sourceLit (List.headD (raw_ints% [14997133185368686474894357665]) 0) 73 false) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [288088527629416902084039034750025538675]) 0) 36 false) .empty .empty)))

#time def treeG_J021_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [542686589392000248398829598133248341079245]) 0) 29 true) treeG_J021_part095 treeG_J021_part096)

#time def treeG_J021_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [241716504307703380434677197725]) 0) 71 true) (.node 874 (sourceLit (List.headD (raw_ints% [2547717099090044641132739890095]) 0) 67 true) (.node 872 (sourceLit (List.headD (raw_ints% [3938141971697758493769735815895]) 0) 65 false) (.node 871 (sourceLit (List.headD (raw_ints% [12954247568489338821898380469474200135675]) 0) 33 true) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [85896150232128215502420903874356443458665]) 0) 32 false) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [1012744672949420752645186979745]) 0) 69 false) (.node 875 (sourceLit (List.headD (raw_ints% [697061433387544741676401963816603799243295]) 0) 30 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [1727812833138214709754112690893528095252235]) 0) 29 false) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [6252416857712042157692530091685]) 0) 64 true) (.node 909 (sourceLit (List.headD (raw_ints% [4006798964700708773005176409785]) 0) 62 false) (.node 879 (sourceLit (List.headD (raw_ints% [19918621743576221105092562805706389349838715]) 0) 25 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [17094540956161411772828151362755778343825]) 0) 32 false) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [5822454179104587238050317699985]) 0) 66 false) (.node 912 (sourceLit (List.headD (raw_ints% [163621060830757949259038600745192129469515]) 0) 31 true) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [1917024993106051696437564060122951436417885]) 0) 29 false) .empty .empty))))

#time def treeG_J021_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [3674563572508141983242234463945]) 0) 63 true) treeG_J021_part097 treeG_J021_part098)

#time def treeG_J021_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [3840681268604425378123705436865]) 0) 64 false) (.node 918 (sourceLit (List.headD (raw_ints% [128797454146721074863484598921884230090324945]) 0) 24 false) (.node 917 (sourceLit (List.headD (raw_ints% [76639448674531943647164913515]) 0) 74 false) (.node 916 (sourceLit (List.headD (raw_ints% [7045428977776557045667836464754156836406705]) 0) 28 true) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [271710770678440753384465913055]) 0) 72 true) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [2547639707352450162865566476895]) 0) 67 true) (.node 951 (sourceLit (List.headD (raw_ints% [7512197131162687648681632958057494619875]) 0) 35 false) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [62379302765721541190364876154887143232045]) 0) 34 true) .empty .empty)))

#time def treeG_J021_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [1467947683100214478789315813965]) 0) 71 false) (.node 956 (sourceLit (List.headD (raw_ints% [4386185723825240985536004541455]) 0) 69 true) (.node 955 (sourceLit (List.headD (raw_ints% [653521606623399109528491505984888808915295]) 0) 32 false) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [2193310452728692938855487288911921232914735]) 0) 31 true) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [16013013008514387889512583607565]) 0) 66 true) (.node 959 (sourceLit (List.headD (raw_ints% [37179018972574323992144290431897654860040915]) 0) 27 false) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [5909300370112230332620916134035728603268765]) 0) 29 true) .empty .empty)))

#time def treeG_J021_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [130783926221791123112235274845]) 0) 73 false) treeG_J021_part100 treeG_J021_part101)

#time def treeG_J021_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [36731362200640100306001513811918283653355085]) 0) 29 false) (.node 999 (sourceLit (List.headD (raw_ints% [434914613444663808043445431755]) 0) 74 false) (.node 997 (sourceLit (List.headD (raw_ints% [5612416902617752083890643157695]) 0) 70 true) (.node 996 (sourceLit (List.headD (raw_ints% [27958120389725328550579564656270598721696145]) 0) 28 false) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [690284930045266467210489344883336065716497105]) 0) 24 true) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [8523386796605826770734882157975283838929945]) 0) 30 true) (.node 1034 (sourceLit (List.headD (raw_ints% [24383184286709019768695641197645]) 0) 67 true) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [16129798052895693097609879693245]) 0) 69 false) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [96145214762571942716458621920072869433135705]) 0) 28 true) (.node 1039 (sourceLit (List.headD (raw_ints% [839001005935563763179066506610926685156660765]) 0) 25 true) (.node 1038 (sourceLit (List.headD (raw_ints% [1770091146429491640669989742915]) 0) 73 true) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [36126796615779471880769516349435]) 0) 68 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [3041092110886232886794586228846106219531222545]) 0) 24 false) (.node 1077 (sourceLit (List.headD (raw_ints% [5435553738878361295375130712735]) 0) 72 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [1102502879937077724356717587335]) 0) 75 true) .empty .empty))))

#time def treeG_J021_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [5871806164535226056036937575895]) 0) 69 false) treeG_J021_part102 treeG_J021_part103)

#time def treeG_J021_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [1686720525437910116445408780855]) 0) 69 true) treeG_J021_part099 treeG_J021_part104)

#time def treeG_J021_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [14114999232306517362612780615]) 0) 72 false) treeG_J021_part094 treeG_J021_part105)

#time def treeG_J021_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [160597974923565414221293714000350235215]) 0) 35 true) treeG_J021_part081 treeG_J021_part106)

#time def treeG_J021_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [260975065620282340435111575]) 0) 57 false) treeG_J021_part054 treeG_J021_part107)

#time def treeG_J021 : IntSourceTree := treeG_J021_part108

#time def treeG_J022_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [54644634165690336084396285375]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [112326275241430930687590030375]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [126873422328661058371828703625]) 0) 43 false) (.node 7 (sourceLit (List.headD (raw_ints% [927965070033238035548567954325]) 0) 43 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [22540963357883944380781749375]) 0) 44 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [13336702143723546594650347275]) 0) 49 false) (.node 12 (sourceLit (List.headD (raw_ints% [6147535461241075740213204375]) 0) 46 true) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [10350978511662324109589754375]) 0) 47 true) .empty .empty)))

#time def treeG_J022_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [196475174779364697389047875]) 0) 55 false) (.node 17 (sourceLit (List.headD (raw_ints% [400036339468804842880651575]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [1259531685465509779252473375]) 0) 51 true) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [1098423250566591175784183925]) 0) 52 true) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 57 false) (.node 20 (sourceLit (List.headD (raw_ints% [501419072714546522370793725]) 0) 54 true) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [694673342989331470622316225]) 0) 55 true) .empty .empty)))

#time def treeG_J022_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [6526564810551439673783917725]) 0) 50 false) treeG_J022_part000 treeG_J022_part001)

#time def treeG_J022_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [2813856862841554753768545]) 0) 61 false) (.node 26 (sourceLit (List.headD (raw_ints% [11399201159686590425850675]) 0) 59 false) (.node 25 (sourceLit (List.headD (raw_ints% [61263095659985695769397053876475]) 0) 38 true) (.node 24 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 58 false) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [160529533726556928133836312656625]) 0) 36 true) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [1390082321332570593003705]) 0) 62 false) (.node 29 (sourceLit (List.headD (raw_ints% [237684848330019367209074048339175]) 0) 35 true) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [1490786527137973977830769116895825]) 0) 32 true) .empty .empty)))

#time def treeG_J022_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [5254287723987295537575]) 0) 70 false) (.node 34 (sourceLit (List.headD (raw_ints% [21238549678288153018275]) 0) 68 false) (.node 33 (sourceLit (List.headD (raw_ints% [2415533305743070694083385615865285]) 0) 31 true) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [7991072810010548210388175397010045]) 0) 29 true) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [2600868766303020607275]) 0) 71 false) (.node 37 (sourceLit (List.headD (raw_ints% [13398604121010078968229593821572255]) 0) 28 true) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [181337232810264878444102910417395025]) 0) 24 true) .empty .empty)))

#time def treeG_J022_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [42944734040611268341905]) 0) 67 false) treeG_J022_part003 treeG_J022_part004)

#time def treeG_J022_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [73377550479464945339373537716475]) 0) 39 true) treeG_J022_part002 treeG_J022_part005)

#time def treeG_J022_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [6147535461241075740213204375]) 0) 47 true) (.node 51 (sourceLit (List.headD (raw_ints% [22540963357883944380781749375]) 0) 45 false) (.node 50 (sourceLit (List.headD (raw_ints% [112326275241430930687590030375]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [126873422328661058371828703625]) 0) 44 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [54644634165690336084396285375]) 0) 48 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [10350978511662324109589754375]) 0) 48 true) (.node 54 (sourceLit (List.headD (raw_ints% [13336702143723546594650347275]) 0) 50 false) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [6526564810551439673783917725]) 0) 51 false) .empty .empty)))

#time def treeG_J022_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [501419072714546522370793725]) 0) 55 true) (.node 59 (sourceLit (List.headD (raw_ints% [1098423250566591175784183925]) 0) 53 true) (.node 58 (sourceLit (List.headD (raw_ints% [400036339468804842880651575]) 0) 55 false) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [196475174779364697389047875]) 0) 56 false) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [694673342989331470622316225]) 0) 56 true) (.node 62 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 58 false) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [73377550479464945339373537716475]) 0) 40 true) .empty .empty)))

#time def treeG_J022_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [1259531685465509779252473375]) 0) 52 true) treeG_J022_part007 treeG_J022_part008)

#time def treeG_J022_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [42944734040611268341905]) 0) 68 false) (.node 69 (sourceLit (List.headD (raw_ints% [2813856862841554753768545]) 0) 62 false) (.node 67 (sourceLit (List.headD (raw_ints% [11399201159686590425850675]) 0) 60 false) (.node 66 (sourceLit (List.headD (raw_ints% [61263095659985695769397053876475]) 0) 39 true) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [160529533726556928133836312656625]) 0) 37 true) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [1390082321332570593003705]) 0) 63 false) (.node 70 (sourceLit (List.headD (raw_ints% [237684848330019367209074048339175]) 0) 36 true) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [1490786527137973977830769116895825]) 0) 33 true) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [5254287723987295537575]) 0) 71 false) (.node 75 (sourceLit (List.headD (raw_ints% [21238549678288153018275]) 0) 69 false) (.node 74 (sourceLit (List.headD (raw_ints% [2415533305743070694083385615865285]) 0) 32 true) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [7991072810010548210388175397010045]) 0) 30 true) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [2600868766303020607275]) 0) 72 false) (.node 78 (sourceLit (List.headD (raw_ints% [13398604121010078968229593821572255]) 0) 29 true) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [703312519550376174173387893575]) 0) 45 false) .empty .empty))))

#time def treeG_J022_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 59 false) treeG_J022_part009 treeG_J022_part010)

#time def treeG_J022_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [927965070033238035548567954325]) 0) 44 false) treeG_J022_part006 treeG_J022_part011)

#time def treeG_J022_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [20146839476895653515516776825]) 0) 50 false) (.node 93 (sourceLit (List.headD (raw_ints% [10326983005491697372436484525]) 0) 51 false) (.node 92 (sourceLit (List.headD (raw_ints% [14344249409562510060497476875]) 0) 47 false) (.node 91 (sourceLit (List.headD (raw_ints% [170007916317171525290783775375]) 0) 47 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [1944092410819827370836654375]) 0) 47 true) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [4926419452676220302261311425]) 0) 52 false) (.node 96 (sourceLit (List.headD (raw_ints% [5312851769800284992579860875]) 0) 49 true) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [1420640120364428382720762825]) 0) 52 true) .empty .empty)))

#time def treeG_J022_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [124037997906378170813820651956475]) 0) 39 false) (.node 101 (sourceLit (List.headD (raw_ints% [74080803605334230163083625]) 0) 58 false) (.node 100 (sourceLit (List.headD (raw_ints% [74625522231505581676673775]) 0) 57 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [308164802439761574119271225]) 0) 55 true) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [525757308175733866945591247855325]) 0) 38 true) (.node 104 (sourceLit (List.headD (raw_ints% [740886320663736566943332475]) 0) 57 true) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [34813776514718505895165575]) 0) 59 false) .empty .empty)))

#time def treeG_J022_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [603597504158244988372255275]) 0) 55 false) treeG_J022_part013 treeG_J022_part014)

#time def treeG_J022_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [1046524449007680446268465]) 0) 64 false) (.node 110 (sourceLit (List.headD (raw_ints% [4237631404350538914533385]) 0) 62 false) (.node 109 (sourceLit (List.headD (raw_ints% [1046551421482436057861616452913825]) 0) 35 true) (.node 108 (sourceLit (List.headD (raw_ints% [4292672148422517836041065]) 0) 62 false) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [6115128619422645772859600429957775]) 0) 32 true) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [64650918402934383665535]) 0) 68 false) (.node 113 (sourceLit (List.headD (raw_ints% [9510758911360721128562767319301315]) 0) 31 true) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [30657460081878582894945994456834515]) 0) 29 true) .empty .empty)))

#time def treeG_J022_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [478659969067514312798207832825]) 0) 46 false) (.node 118 (sourceLit (List.headD (raw_ints% [7907706681671570467875]) 0) 71 false) (.node 117 (sourceLit (List.headD (raw_ints% [50529978359074306714875809354508105]) 0) 28 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [676173430934380175522591094163229295]) 0) 24 true) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [7210205134467574325399218125]) 0) 52 false) (.node 131 (sourceLit (List.headD (raw_ints% [52166229485388556995523477125]) 0) 47 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [34836034280366095861208158125]) 0) 47 false) .empty .empty)))

#time def treeG_J022_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [3996065488575214370175]) 0) 72 false) treeG_J022_part016 treeG_J022_part017)

#time def treeG_J022_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [819679996833214204176516549366975]) 0) 36 true) treeG_J022_part015 treeG_J022_part018)

#time def treeG_J022_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [80554217449459301734144725]) 0) 55 true) (.node 137 (sourceLit (List.headD (raw_ints% [274725027938245875569967375]) 0) 50 true) (.node 136 (sourceLit (List.headD (raw_ints% [3405068666586053460433214775]) 0) 53 false) (.node 135 (sourceLit (List.headD (raw_ints% [262715190651328023086034375]) 0) 53 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [3326274094801000930738705125]) 0) 53 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [95585105137498131042596475]) 0) 55 true) (.node 140 (sourceLit (List.headD (raw_ints% [50890291172360036372900925]) 0) 59 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [99848039641972223263286625]) 0) 58 false) .empty .empty)))

#time def treeG_J022_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [5853643838757978867328725]) 0) 62 false) (.node 145 (sourceLit (List.headD (raw_ints% [787099298338141663264348725]) 0) 58 true) (.node 144 (sourceLit (List.headD (raw_ints% [98707774192921558076597094836475]) 0) 41 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [232247106257874085588097096989425]) 0) 40 true) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [5771487434003480918313585]) 0) 62 false) (.node 148 (sourceLit (List.headD (raw_ints% [329575231553328638021340118355175]) 0) 38 true) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [404433286576208345326271202287325]) 0) 37 true) .empty .empty)))

#time def treeG_J022_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 59 false) treeG_J022_part020 treeG_J022_part021)

#time def treeG_J022_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [663354739421068732575]) 0) 75 false) (.node 155 (sourceLit (List.headD (raw_ints% [10853092181161557661815]) 0) 71 false) (.node 153 (sourceLit (List.headD (raw_ints% [702966576682790299533225]) 0) 65 false) (.node 152 (sourceLit (List.headD (raw_ints% [2312171046142335897514415656530975]) 0) 34 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [3547612802808825217239690851718015]) 0) 33 true) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [10729974230313561943125]) 0) 71 false) (.node 156 (sourceLit (List.headD (raw_ints% [11333193635934017342278909529912235]) 0) 31 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [18565687119032113873323107766467925]) 0) 30 true) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [71616160971552019093252970625]) 0) 47 false) (.node 172 (sourceLit (List.headD (raw_ints% [89988209561214603930549477375]) 0) 47 false) (.node 171 (sourceLit (List.headD (raw_ints% [154326026375171393753712028725]) 0) 48 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [18513837532378599929160387975]) 0) 51 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [13719737870642781731332960875]) 0) 49 false) (.node 175 (sourceLit (List.headD (raw_ints% [35795620279590832274674404825]) 0) 50 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [8693855213667993539471547675]) 0) 52 false) .empty .empty))))

#time def treeG_J022_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [177971817688623020095605]) 0) 67 false) treeG_J022_part022 treeG_J022_part023)

#time def treeG_J022_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [27971229878243242895095590825]) 0) 50 false) treeG_J022_part019 treeG_J022_part024)

#time def treeG_J022_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [231205881299438172362875657875]) 0) 44 false) treeG_J022_part012 treeG_J022_part025)

#time def treeG_J022_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [19339739890757504833296615860475]) 0) 39 true) (.node 181 (sourceLit (List.headD (raw_ints% [129480361084105915328520075]) 0) 58 false) (.node 180 (sourceLit (List.headD (raw_ints% [68696827013551861619202825]) 0) 56 false) (.node 179 (sourceLit (List.headD (raw_ints% [2119079086484510953994194575]) 0) 54 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [116994592164765312034078275]) 0) 55 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [2105081695262478796171144765238925]) 0) 38 false) (.node 184 (sourceLit (List.headD (raw_ints% [1127394861213306463446377475]) 0) 57 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [205478268713215042289878575]) 0) 61 true) .empty .empty)))

#time def treeG_J022_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [19768601721454688328021756516431025]) 0) 32 true) (.node 189 (sourceLit (List.headD (raw_ints% [4226652283370822150479825440768975]) 0) 35 true) (.node 188 (sourceLit (List.headD (raw_ints% [7414615529093439898616385]) 0) 62 false) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [7305343463656422922093785]) 0) 62 false) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [27483977826916653231667883185194285]) 0) 31 true) (.node 192 (sourceLit (List.headD (raw_ints% [1801024634010287875261215]) 0) 64 false) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [444362903071052764871085]) 0) 66 false) .empty .empty)))

#time def treeG_J022_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [6612227403418756534642590554294625]) 0) 36 true) treeG_J022_part027 treeG_J022_part028)

#time def treeG_J022_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [96644385299430799150518283725]) 0) 49 false) (.node 198 (sourceLit (List.headD (raw_ints% [13552241778955553418375]) 0) 71 false) (.node 197 (sourceLit (List.headD (raw_ints% [130801119815869970761586743124087655]) 0) 28 true) (.node 196 (sourceLit (List.headD (raw_ints% [857128336573292911455]) 0) 75 false) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [1700234520301730400262766699944665105]) 0) 24 true) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [46084120251271156821545961075]) 0) 50 false) (.node 213 (sourceLit (List.headD (raw_ints% [145140384842063111999890796625]) 0) 47 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [63209274870709522354499870625]) 0) 48 false) .empty .empty)))

#time def treeG_J022_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [1304834427726750372027779775]) 0) 55 false) (.node 218 (sourceLit (List.headD (raw_ints% [2683790559433496304366421275]) 0) 54 false) (.node 217 (sourceLit (List.headD (raw_ints% [6997231449290513803451464125]) 0) 51 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [3210988952386285303744716075]) 0) 52 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [159112682526239607393753525]) 0) 58 false) (.node 221 (sourceLit (List.headD (raw_ints% [370372413191705577519407775]) 0) 55 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [269513948384804584468966725]) 0) 56 true) .empty .empty)))

#time def treeG_J022_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [22175345613246618432941545725]) 0) 51 false) treeG_J022_part030 treeG_J022_part031)

#time def treeG_J022_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [82866149608003824056724112798141965]) 0) 29 true) treeG_J022_part029 treeG_J022_part032)

#time def treeG_J022_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [9057743624183398878919185]) 0) 62 false) (.node 227 (sourceLit (List.headD (raw_ints% [52832978137993255289301825]) 0) 64 true) (.node 226 (sourceLit (List.headD (raw_ints% [2569575907778226967347338959217775]) 0) 39 false) (.node 225 (sourceLit (List.headD (raw_ints% [239311769943931015838840775]) 0) 61 false) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [5953076940312099258599910317584275]) 0) 37 true) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [4457794380638454600564105]) 0) 63 false) (.node 230 (sourceLit (List.headD (raw_ints% [3417785710218405459827283036194325]) 0) 36 true) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [15144259629170016532992925203369075]) 0) 33 true) .empty .empty)))

#time def treeG_J022_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [16698132540031811223435]) 0) 71 false) (.node 235 (sourceLit (List.headD (raw_ints% [270713428172467842282045]) 0) 67 false) (.node 234 (sourceLit (List.headD (raw_ints% [20388752221299002797188501481758255]) 0) 32 true) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [60199762336135789372166293738317495]) 0) 30 true) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [8245403863587003557775]) 0) 72 false) (.node 238 (sourceLit (List.headD (raw_ints% [93669745577805743014940527591151805]) 0) 29 true) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [59616710234673599292197507775]) 0) 50 false) .empty .empty)))

#time def treeG_J022_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [549029028663748787863995]) 0) 66 false) treeG_J022_part034 treeG_J022_part035)

#time def treeG_J022_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [623750234218645843004737275]) 0) 55 false) (.node 258 (sourceLit (List.headD (raw_ints% [11427907685790416717031369975]) 0) 51 false) (.node 256 (sourceLit (List.headD (raw_ints% [24744768500033370311583454875]) 0) 50 false) (.node 255 (sourceLit (List.headD (raw_ints% [56372620222951481368417517325]) 0) 50 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [6740745199789312446734999025]) 0) 53 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [2661414336277870410791093475]) 0) 53 false) (.node 259 (sourceLit (List.headD (raw_ints% [3248502032382481654738647975]) 0) 54 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [786912983390326710713699475]) 0) 56 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [684101808601077073967560125]) 0) 61 false) (.node 264 (sourceLit (List.headD (raw_ints% [174613601199763880989418025]) 0) 60 true) (.node 263 (sourceLit (List.headD (raw_ints% [186181480083391727395809112090875]) 0) 39 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [3839124001475283764063071209506325]) 0) 38 true) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [430078440633039482213030985]) 0) 62 true) (.node 267 (sourceLit (List.headD (raw_ints% [47725441927870388012200013901779025]) 0) 36 false) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [43397963239125971918319457099905225]) 0) 35 true) .empty .empty))))

#time def treeG_J022_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [218664608712574204906528622625]) 0) 47 false) treeG_J022_part036 treeG_J022_part037)

#time def treeG_J022_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [216755288276600620986490805533425]) 0) 40 true) treeG_J022_part033 treeG_J022_part038)

#time def treeG_J022_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [243353885932780220698291910909990115]) 0) 29 true) (.node 273 (sourceLit (List.headD (raw_ints% [93670099206443479032275518441758315]) 0) 31 true) (.node 272 (sourceLit (List.headD (raw_ints% [1328384873314083362651445]) 0) 65 false) (.node 271 (sourceLit (List.headD (raw_ints% [89600541005534286386451300641787375]) 0) 32 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [653695154256444810856905]) 0) 66 false) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [350796978873216344215743606782452305]) 0) 28 true) (.node 276 (sourceLit (List.headD (raw_ints% [161001001091086349615805]) 0) 68 false) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [19844023301108069028495]) 0) 71 false) .empty .empty)))

#time def treeG_J022_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [8873768525371428254065995375]) 0) 52 false) (.node 295 (sourceLit (List.headD (raw_ints% [1214494795639567832437724625]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [73149300218076041762849054475]) 0) 50 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [2137329663106553933467248225]) 0) 55 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [2054229683351032853321663475]) 0) 54 false) (.node 298 (sourceLit (List.headD (raw_ints% [2028477320177908071184288875]) 0) 55 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [242958450581966410338858525]) 0) 58 false) .empty .empty)))

#time def treeG_J022_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [4294629196677837152693427065889050415]) 0) 24 true) treeG_J022_part040 treeG_J022_part041)

#time def treeG_J022_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [1602174977313377682852602542181025]) 0) 41 true) (.node 304 (sourceLit (List.headD (raw_ints% [100734192089998087095574979406075]) 0) 42 false) (.node 303 (sourceLit (List.headD (raw_ints% [13957252853178912929276625]) 0) 62 false) (.node 302 (sourceLit (List.headD (raw_ints% [468687618337847495926192425]) 0) 57 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [25870335696480931051766175]) 0) 65 true) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [13419629717045621817699981054840825]) 0) 39 false) (.node 307 (sourceLit (List.headD (raw_ints% [895433721153050095124767425]) 0) 62 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [869214624890262363304981155]) 0) 62 true) .empty .empty)))

#time def treeG_J022_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [18320336746286119058771754240000015]) 0) 34 true) (.node 312 (sourceLit (List.headD (raw_ints% [18614070344091067463364593859604575]) 0) 35 true) (.node 311 (sourceLit (List.headD (raw_ints% [99255459438623753674695]) 0) 69 false) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [389677922325167287393725]) 0) 67 false) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [45788530899161107831531404292918155]) 0) 32 true) (.node 315 (sourceLit (List.headD (raw_ints% [95745431520994242143715]) 0) 69 false) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [94208470930959104722065]) 0) 69 false) .empty .empty)))

#time def treeG_J022_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [9995044382226891614623043515927725]) 0) 38 true) treeG_J022_part043 treeG_J022_part044)

#time def treeG_J022_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [1920669509894459255752277925]) 0) 54 false) treeG_J022_part042 treeG_J022_part045)

#time def treeG_J022_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [24067166415695296299232611525]) 0) 51 false) (.node 336 (sourceLit (List.headD (raw_ints% [52982898420898970964430921125]) 0) 50 false) (.node 335 (sourceLit (List.headD (raw_ints% [89925980213200602157280591625]) 0) 50 false) (.node 319 (sourceLit (List.headD (raw_ints% [45307107177816661995]) 0) 80 false) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [10357892105063119021002986775]) 0) 53 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [5555504397126261002495560425]) 0) 53 false) (.node 339 (sourceLit (List.headD (raw_ints% [4865407248329150629998507525]) 0) 54 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [1156754621265404571997168725]) 0) 56 false) .empty .empty)))

#time def treeG_J022_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [1511952550888466867624077725]) 0) 61 true) (.node 344 (sourceLit (List.headD (raw_ints% [286271624025195184423631025]) 0) 60 false) (.node 343 (sourceLit (List.headD (raw_ints% [59545813959721660548342462027525]) 0) 39 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [7062618148355222551121470550500725]) 0) 38 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [2220945882939139672462565835]) 0) 62 false) (.node 347 (sourceLit (List.headD (raw_ints% [150264640475926559714766576601364625]) 0) 36 true) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [472826114184585870084718850854811625]) 0) 35 false) .empty .empty)))

#time def treeG_J022_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [648459637837906706373770325]) 0) 56 false) treeG_J022_part047 treeG_J022_part048)

#time def treeG_J022_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [54520424328742966665075]) 0) 70 false) (.node 354 (sourceLit (List.headD (raw_ints% [905016535044224338717995]) 0) 66 false) (.node 352 (sourceLit (List.headD (raw_ints% [1847789828721876754938795]) 0) 65 false) (.node 351 (sourceLit (List.headD (raw_ints% [1189765139919507840285298269396961425]) 0) 32 true) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [501980151804470679795391485065588085]) 0) 31 true) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [221980724992890618959055]) 0) 68 false) (.node 355 (sourceLit (List.headD (raw_ints% [929147665829531399063100360450010845]) 0) 29 true) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [1114436009899939106393261330590928655]) 0) 28 true) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [6300937464707302878634409025]) 0) 54 false) (.node 376 (sourceLit (List.headD (raw_ints% [55728705603495739221804620025]) 0) 51 false) (.node 359 (sourceLit (List.headD (raw_ints% [12161513734228441324157970002354181585]) 0) 24 true) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [35235361370156114456298930375]) 0) 51 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [2921739643673419347287639325]) 0) 55 false) (.node 379 (sourceLit (List.headD (raw_ints% [15850247682291164885945957625]) 0) 52 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [908708721807950436685820625]) 0) 56 false) .empty .empty))))

#time def treeG_J022_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [1749239393565235101445706895]) 0) 62 true) treeG_J022_part049 treeG_J022_part050)

#time def treeG_J022_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [64281808323852650300200769797825125]) 0) 31 true) treeG_J022_part046 treeG_J022_part051)

#time def treeG_J022_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [10810143784710374835744585]) 0) 62 false) treeG_J022_part039 treeG_J022_part052)

#time def treeG_J022_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [2566555212790610889871558275]) 0) 51 false) treeG_J022_part026 treeG_J022_part053)

#time def treeG_J022_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [1203693136020758481374422575]) 0) 63 true) (.node 385 (sourceLit (List.headD (raw_ints% [700196995168890081251889825]) 0) 61 false) (.node 384 (sourceLit (List.headD (raw_ints% [343390954400270687833957455596775]) 0) 40 true) (.node 383 (sourceLit (List.headD (raw_ints% [201827546536181492636918325]) 0) 57 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [13471318057608733282531880719224825]) 0) 39 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [5311106390768541708230112825]) 0) 62 false) (.node 388 (sourceLit (List.headD (raw_ints% [203943159344109046985566500820727925]) 0) 37 true) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [512806291713493436543211024918522525]) 0) 36 false) .empty .empty)))

#time def treeG_J022_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [522034808960247370143135]) 0) 67 false) (.node 393 (sourceLit (List.headD (raw_ints% [1068433984071542180151345]) 0) 66 false) (.node 392 (sourceLit (List.headD (raw_ints% [1115308858543143570431839893958543125]) 0) 33 true) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [428698804819326203560304468105588025]) 0) 32 true) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [63886127030965757118495]) 0) 70 false) (.node 396 (sourceLit (List.headD (raw_ints% [745993542232886967736974743278338225]) 0) 30 true) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [857308776604528505192458251399628155]) 0) 29 true) .empty .empty)))

#time def treeG_J022_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [1755591742969307021680887375]) 0) 63 true) treeG_J022_part055 treeG_J022_part056)

#time def treeG_J022_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [220623127801001846911308825]) 0) 59 false) (.node 419 (sourceLit (List.headD (raw_ints% [7736467681085455127270310525]) 0) 54 false) (.node 418 (sourceLit (List.headD (raw_ints% [46403556324616932613365249225]) 0) 51 false) (.node 417 (sourceLit (List.headD (raw_ints% [35012921393369501179798646475]) 0) 52 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [643421455322806492715649825]) 0) 57 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [301199458871161383750757560346875]) 0) 39 false) (.node 422 (sourceLit (List.headD (raw_ints% [1168957805777994166997870925]) 0) 56 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [943258949564599245057605775]) 0) 58 true) .empty .empty)))

#time def treeG_J022_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [2104371388937458245969250857420635025]) 0) 35 true) (.node 427 (sourceLit (List.headD (raw_ints% [365805729397666292235276668108961825]) 0) 36 false) (.node 426 (sourceLit (List.headD (raw_ints% [2912346541226247030127857375]) 0) 61 false) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [7035718427022173597960256135]) 0) 62 true) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [17599566474751297809668051066789682225]) 0) 32 false) (.node 430 (sourceLit (List.headD (raw_ints% [12371452175102318517905932545]) 0) 62 false) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [1759287322626750775190764965]) 0) 64 true) .empty .empty)))

#time def treeG_J022_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [9809745783557388053793130195274925]) 0) 38 true) treeG_J022_part058 treeG_J022_part059)

#time def treeG_J022_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [31323185453700835723635]) 0) 71 false) treeG_J022_part057 treeG_J022_part060)

#time def treeG_J022_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [73251829733188547571915]) 0) 70 false) (.node 436 (sourceLit (List.headD (raw_ints% [18753380247959796949005]) 0) 72 false) (.node 435 (sourceLit (List.headD (raw_ints% [5930033211279687857901771129239397555]) 0) 29 true) (.node 434 (sourceLit (List.headD (raw_ints% [1231851433098860021584695]) 0) 66 false) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [4853512327963156635502536615635777145]) 0) 28 true) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [22411046463954895422529828425]) 0) 53 false) (.node 439 (sourceLit (List.headD (raw_ints% [42706247968461383008159358087222020335]) 0) 24 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [1909581790145360482963705725]) 0) 56 false) .empty .empty)))

#time def treeG_J022_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [322295206635716035792357507971825]) 0) 41 false) (.node 462 (sourceLit (List.headD (raw_ints% [269229504870114424804873575]) 0) 59 false) (.node 461 (sourceLit (List.headD (raw_ints% [1664977099483275534176778675]) 0) 56 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [120891282405226584295119075]) 0) 60 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [11640531920583060668162505457249875]) 0) 40 true) (.node 465 (sourceLit (List.headD (raw_ints% [3744046930240159570065165075]) 0) 59 true) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [5319732813267763992876702525]) 0) 62 false) .empty .empty)))

#time def treeG_J022_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [150460251169126118124458475]) 0) 60 false) treeG_J022_part062 treeG_J022_part063)

#time def treeG_J022_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [2592019834523400445082398192980529665]) 0) 31 true) (.node 472 (sourceLit (List.headD (raw_ints% [9357437666647220690049945480374112675]) 0) 34 false) (.node 470 (sourceLit (List.headD (raw_ints% [1308588840325475841256230941169578775]) 0) 37 true) (.node 469 (sourceLit (List.headD (raw_ints% [19382543244812888904150625095]) 0) 62 true) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [882940244879476596224176245]) 0) 67 false) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [3995895955860675840049511599248584445]) 0) 33 true) (.node 473 (sourceLit (List.headD (raw_ints% [1761424190594893859551067655]) 0) 65 true) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [88727078017326581430195]) 0) 70 false) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [3668644695717360073814879475]) 0) 56 false) (.node 478 (sourceLit (List.headD (raw_ints% [1998101775679314065155039182118074495]) 0) 30 true) (.node 477 (sourceLit (List.headD (raw_ints% [86140914952712618473545]) 0) 70 false) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [5241080534935963981035]) 0) 74 false) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [381217876875502625586525075]) 0) 59 false) (.node 500 (sourceLit (List.headD (raw_ints% [316540083705638497562013975]) 0) 59 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [2160996393188556901355686425]) 0) 56 false) .empty .empty))))

#time def treeG_J022_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [284874444370887669610421584464844875]) 0) 38 false) treeG_J022_part064 treeG_J022_part065)

#time def treeG_J022_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [8420490716540677883659327666602756915]) 0) 31 true) treeG_J022_part061 treeG_J022_part066)

#time def treeG_J022_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [17675184053557701583713661185]) 0) 62 false) (.node 506 (sourceLit (List.headD (raw_ints% [9568740012692653630320879825]) 0) 60 true) (.node 505 (sourceLit (List.headD (raw_ints% [14966469089728844626470850322824125]) 0) 38 false) (.node 504 (sourceLit (List.headD (raw_ints% [1910389208806411919418558375]) 0) 58 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [738302750856324233616476842740957825]) 0) 36 true) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [51136538664728096326207182735]) 0) 62 true) (.node 509 (sourceLit (List.headD (raw_ints% [6662362498871660959735996208858153025]) 0) 35 false) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [101349252255581751650066831301642723825]) 0) 32 true) .empty .empty)))

#time def treeG_J022_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [51220317521406987532185]) 0) 71 false) (.node 514 (sourceLit (List.headD (raw_ints% [881328021013996359786326175]) 0) 67 true) (.node 513 (sourceLit (List.headD (raw_ints% [158139493382896208924458455352588559715]) 0) 31 false) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [121938637376261939023682600046715304685]) 0) 29 true) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [99030000172236689375175]) 0) 70 false) (.node 517 (sourceLit (List.headD (raw_ints% [36618805024411250485815834472052697495]) 0) 28 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [213050779318490817331685657223891515025]) 0) 24 true) .empty .empty)))

#time def treeG_J022_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [15886331240698376314777584885]) 0) 64 false) treeG_J022_part068 treeG_J022_part069)

#time def treeG_J022_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [2827218069523285744741861725]) 0) 60 false) (.node 543 (sourceLit (List.headD (raw_ints% [1193866133946744226994733825]) 0) 57 false) (.node 542 (sourceLit (List.headD (raw_ints% [493206248880890826368176575]) 0) 59 false) (.node 541 (sourceLit (List.headD (raw_ints% [3399664239806940426815444925]) 0) 56 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [381174677545223249127082348732125]) 0) 40 true) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [20208205639228181616074284875]) 0) 61 true) (.node 546 (sourceLit (List.headD (raw_ints% [38247532930894965962795861237323875]) 0) 39 false) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [1308051639598099572837320011670647575]) 0) 37 true) .empty .empty)))

#time def treeG_J022_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [4411938857823317543582163135]) 0) 67 false) (.node 551 (sourceLit (List.headD (raw_ints% [65263582582799721865794002655]) 0) 63 true) (.node 550 (sourceLit (List.headD (raw_ints% [9279540179522612642248458091197310575]) 0) 36 false) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [120064127588876193030166722262390949175]) 0) 33 true) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [881682929326065666112046955]) 0) 68 true) (.node 554 (sourceLit (List.headD (raw_ints% [166131285294617560604557478551085728605]) 0) 32 false) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [116754597707215138133517803660754245355]) 0) 30 true) .empty .empty)))

#time def treeG_J022_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [54732911351928292071577947465]) 0) 62 false) treeG_J022_part071 treeG_J022_part072)

#time def treeG_J022_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [2464962686364351128819211675]) 0) 57 false) treeG_J022_part070 treeG_J022_part073)

#time def treeG_J022_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [770912735526849135842041573402875]) 0) 39 false) (.node 581 (sourceLit (List.headD (raw_ints% [1702526932613345877646161525]) 0) 58 false) (.node 559 (sourceLit (List.headD (raw_ints% [57101355892748977526895]) 0) 71 false) (.node 558 (sourceLit (List.headD (raw_ints% [32622601473052622355505756107816548505]) 0) 29 true) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [4638332086425323952275203425]) 0) 56 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [18015866510090630619487509112681125]) 0) 38 true) (.node 584 (sourceLit (List.headD (raw_ints% [358261537429833846211912275]) 0) 59 true) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [15223176151739225119804603275]) 0) 60 false) .empty .empty)))

#time def treeG_J022_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [398294538000305356202017490219956662225]) 0) 32 false) (.node 589 (sourceLit (List.headD (raw_ints% [17126775615656457542434556302223333625]) 0) 35 true) (.node 588 (sourceLit (List.headD (raw_ints% [9470847423196470799946986515]) 0) 64 true) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [160602361368584680469363077665]) 0) 62 false) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [1118652514093905753165792233451716153115]) 0) 31 true) (.node 592 (sourceLit (List.headD (raw_ints% [20287478455874524545142896885]) 0) 66 true) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [9705205736660631446950652445]) 0) 67 false) .empty .empty)))

#time def treeG_J022_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [1350263277750643689021210622538139825]) 0) 36 false) treeG_J022_part075 treeG_J022_part076)

#time def treeG_J022_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [199092475434569974434610875]) 0) 64 true) (.node 599 (sourceLit (List.headD (raw_ints% [1874795714956877013420682733676367589295]) 0) 24 true) (.node 597 (sourceLit (List.headD (raw_ints% [897417976633309854582326594813981265345]) 0) 28 true) (.node 596 (sourceLit (List.headD (raw_ints% [881887810596151294062175695]) 0) 69 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [138450710093593973935215]) 0) 70 false) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [107639561014955616415014675]) 0) 62 false) (.node 622 (sourceLit (List.headD (raw_ints% [604660341866227525638992475]) 0) 60 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [144010926634009048121140490266875]) 0) 43 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [130499690737500058471153839585]) 0) 62 true) (.node 627 (sourceLit (List.headD (raw_ints% [17715690895483703367939444075]) 0) 62 false) (.node 626 (sourceLit (List.headD (raw_ints% [7032924930123199572785421293750625]) 0) 42 true) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [332289364668592907732316329276098425]) 0) 40 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [882288843560095321621707345]) 0) 71 false) (.node 630 (sourceLit (List.headD (raw_ints% [3300789474397383773085376799177580525]) 0) 39 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [64794833198647693654023026560293451425]) 0) 36 false) .empty .empty))))

#time def treeG_J022_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [2780039202090142908696602256864086962365]) 0) 29 false) treeG_J022_part077 treeG_J022_part078)

#time def treeG_J022_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [118740355132915331655195]) 0) 70 false) treeG_J022_part074 treeG_J022_part079)

#time def treeG_J022_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [263415735726208822457632667211525]) 0) 39 false) treeG_J022_part067 treeG_J022_part080)

#time def treeG_J022_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [108099421895032154028352604838270589605]) 0) 32 true) (.node 636 (sourceLit (List.headD (raw_ints% [362099224974669755853765007565605150965]) 0) 33 false) (.node 635 (sourceLit (List.headD (raw_ints% [1323361083248337139132837425]) 0) 71 false) (.node 634 (sourceLit (List.headD (raw_ints% [160597974923565414221293714000350235215]) 0) 35 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [441003275475642104696915445]) 0) 71 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [1765216555004036439855687120459525]) 0) 39 false) (.node 639 (sourceLit (List.headD (raw_ints% [79442728711762691805]) 0) 81 false) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [2080494513669123708852147075]) 0) 59 false) .empty .empty)))

#time def treeG_J022_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [38393294954446403637302801375893632825]) 0) 35 false) (.node 667 (sourceLit (List.headD (raw_ints% [2250477668806413234337744548138219825]) 0) 36 true) (.node 666 (sourceLit (List.headD (raw_ints% [21594135365645464301712151275]) 0) 60 true) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [36657385741876644967833417105]) 0) 63 false) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [1243296643446035602111873950809417276625]) 0) 32 true) (.node 670 (sourceLit (List.headD (raw_ints% [421601742843584797411670756835]) 0) 62 true) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [76753964443720625128932166965]) 0) 66 false) .empty .empty)))

#time def treeG_J022_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [27232565814667209699240500489761125]) 0) 38 false) treeG_J022_part082 treeG_J022_part083)

#time def treeG_J022_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [1764151552612662012761596995]) 0) 70 true) (.node 676 (sourceLit (List.headD (raw_ints% [11468776476582848407124875095]) 0) 69 false) (.node 675 (sourceLit (List.headD (raw_ints% [23336579992306515929022197648908917069885]) 0) 29 true) (.node 674 (sourceLit (List.headD (raw_ints% [59104040364056315624400772485]) 0) 67 true) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [24071768375012174229223287079012710927105]) 0) 28 false) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [613129141931964054886563198324525]) 0) 40 false) (.node 679 (sourceLit (List.headD (raw_ints% [53472108295299585849095850943518174288465]) 0) 24 true) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [5265974120622243299805921075]) 0) 60 false) .empty .empty)))

#time def treeG_J022_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [64799610749625473821985815769314277025]) 0) 36 false) (.node 708 (sourceLit (List.headD (raw_ints% [4908792586155156496196275182347007225]) 0) 37 true) (.node 707 (sourceLit (List.headD (raw_ints% [57025517156612871037591039425]) 0) 61 true) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [277129233705006638342487508005]) 0) 62 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [1761655309035217151344058163291764888025]) 0) 33 true) (.node 711 (sourceLit (List.headD (raw_ints% [647467686794969199746827837155]) 0) 63 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [101453381757418467217657226985]) 0) 67 false) .empty .empty)))

#time def treeG_J022_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [83495965255652806281523870839766125]) 0) 39 false) treeG_J022_part085 treeG_J022_part086)

#time def treeG_J022_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [5265521838807358147023265933310497044315]) 0) 31 false) treeG_J022_part084 treeG_J022_part087)

#time def treeG_J022_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [1764232901966862857758005315]) 0) 71 true) (.node 717 (sourceLit (List.headD (raw_ints% [12350783027534132616518705985]) 0) 70 false) (.node 716 (sourceLit (List.headD (raw_ints% [26233373792103873975852317709433758277605]) 0) 30 true) (.node 715 (sourceLit (List.headD (raw_ints% [69690929030043012737463471885]) 0) 68 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [24936563750172431461450107917718875643945]) 0) 29 false) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [32126083606889950901323993425]) 0) 60 false) (.node 745 (sourceLit (List.headD (raw_ints% [22327532679211497260147994903164925]) 0) 38 true) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [3586413112896858134842126481574477825]) 0) 36 false) .empty .empty)))

#time def treeG_J022_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [954483544569851700262556505015]) 0) 64 true) (.node 750 (sourceLit (List.headD (raw_ints% [975860210253598074096645772845]) 0) 62 false) (.node 749 (sourceLit (List.headD (raw_ints% [77663635643687655606873002834669690625]) 0) 35 true) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [3316884187434050764415420055427474141425]) 0) 32 false) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [262010803878893250059715226455]) 0) 67 false) (.node 753 (sourceLit (List.headD (raw_ints% [19358764311089095357775731239644616148515]) 0) 31 true) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [128141470203440619301720047973921699886445]) 0) 29 false) .empty .empty)))

#time def treeG_J022_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [130340288640366160973257873635]) 0) 62 true) treeG_J022_part089 treeG_J022_part090)

#time def treeG_J022_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [71231623196656564714429409301991983825]) 0) 37 true) (.node 786 (sourceLit (List.headD (raw_ints% [52911748967432151770835932871465525]) 0) 40 true) (.node 758 (sourceLit (List.headD (raw_ints% [26465717607680927245799008965]) 0) 70 false) (.node 757 (sourceLit (List.headD (raw_ints% [233938758711843166036041828754482777147945]) 0) 28 true) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [1649412188306335199381902757677526215500945]) 0) 24 false) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [4247602849526007315519200831960742525]) 0) 38 false) (.node 787 (sourceLit (List.headD (raw_ints% [44575800381751410969457516425]) 0) 62 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [537809810985738960289003255275]) 0) 62 true) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [12954534974642488409284673442478957537275]) 0) 33 true) (.node 792 (sourceLit (List.headD (raw_ints% [2539269748234633957879739109359619514725]) 0) 34 false) (.node 791 (sourceLit (List.headD (raw_ints% [101457993565535454615217100625]) 0) 67 false) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [1360297071599525569133185412955]) 0) 65 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [77187421997772246638786182841677729082025]) 0) 31 false) (.node 795 (sourceLit (List.headD (raw_ints% [82925433227234065699294674585]) 0) 70 false) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [93510488534159993761107052965]) 0) 70 true) .empty .empty))))

#time def treeG_J022_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [20289926376656465286147086745]) 0) 71 true) treeG_J022_part091 treeG_J022_part092)

#time def treeG_J022_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [6550305638195881460793615645313298926035]) 0) 32 false) treeG_J022_part088 treeG_J022_part093)

#time def treeG_J022_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [2051479832225075994674652283395]) 0) 62 true) (.node 828 (sourceLit (List.headD (raw_ints% [219491889403868982912172906485]) 0) 62 false) (.node 827 (sourceLit (List.headD (raw_ints% [5279589079854686991508876333461374625]) 0) 36 true) (.node 799 (sourceLit (List.headD (raw_ints% [3528743813705973762944626785]) 0) 74 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [145625281236103772655180216146041571025]) 0) 35 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [2577811441618418974106030115015]) 0) 64 false) (.node 831 (sourceLit (List.headD (raw_ints% [7875708072020070906138902250754961106225]) 0) 32 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [59987080282843238683851556989398528384115]) 0) 31 false) .empty .empty)))

#time def treeG_J022_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [213486694676000914768013114895]) 0) 70 true) (.node 836 (sourceLit (List.headD (raw_ints% [51607679801945265492720880665]) 0) 72 false) (.node 835 (sourceLit (List.headD (raw_ints% [542686589392000248398829598133248341079245]) 0) 29 true) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [1468937510676199112256620754221326442460345]) 0) 28 false) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [13774794778906701622547277997382859675]) 0) 37 true) (.node 839 (sourceLit (List.headD (raw_ints% [18217432825875333439221386704698431994181905]) 0) 24 true) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [976793589793476926113349068245]) 0) 62 false) .empty .empty)))

#time def treeG_J022_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [1884318679357312069252615865865]) 0) 66 true) treeG_J022_part095 treeG_J022_part096)

#time def treeG_J022_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [1727812833138214709754112690893528095252235]) 0) 29 false) (.node 874 (sourceLit (List.headD (raw_ints% [85896150232128215502420903874356443458665]) 0) 32 false) (.node 872 (sourceLit (List.headD (raw_ints% [12954247568489338821898380469474200135675]) 0) 33 true) (.node 871 (sourceLit (List.headD (raw_ints% [3674807729273643268518125893395]) 0) 63 true) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [1969054256608972271619607763985]) 0) 66 false) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [697061433387544741676401963816603799243295]) 0) 30 true) (.node 875 (sourceLit (List.headD (raw_ints% [2547722145175184594846973262545]) 0) 67 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [506371926949722117702874098285]) 0) 70 false) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [17094540956161411772828151362755778343825]) 0) 32 false) (.node 909 (sourceLit (List.headD (raw_ints% [255823639467357385635558440125104448425]) 0) 35 true) (.node 879 (sourceLit (List.headD (raw_ints% [241716645185648704871570129175]) 0) 71 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [4005067011812029846901350419885]) 0) 62 false) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [163621060830757949259038600745192129469515]) 0) 31 true) (.node 912 (sourceLit (List.headD (raw_ints% [3126309585446031121312078004205]) 0) 65 true) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [5822427192575256612491831393835]) 0) 66 false) .empty .empty))))

#time def treeG_J022_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [288088527629416902084039034750025538675]) 0) 36 false) treeG_J022_part097 treeG_J022_part098)

#time def treeG_J022_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [135978041774193571929899368718782496775]) 0) 38 true) (.node 918 (sourceLit (List.headD (raw_ints% [1226230548575445150173761311465]) 0) 70 false) (.node 917 (sourceLit (List.headD (raw_ints% [7045428977776557045667836464754156836406705]) 0) 28 true) (.node 916 (sourceLit (List.headD (raw_ints% [3373445022006308842730507353185]) 0) 68 true) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [128797454146721074863484598921884230090324945]) 0) 24 false) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [7512197131162687648681632958057494619875]) 0) 35 false) (.node 951 (sourceLit (List.headD (raw_ints% [119998042829463642428429317395]) 0) 69 false) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [2547681921027501696465842884095]) 0) 67 true) .empty .empty)))

#time def treeG_J022_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [2193310452728692938855487288911921232914735]) 0) 31 true) (.node 956 (sourceLit (List.headD (raw_ints% [653521606623399109528491505984888808915295]) 0) 32 false) (.node 955 (sourceLit (List.headD (raw_ints% [2092537334437610301834701164095]) 0) 69 false) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [4386188875905753078136255549755]) 0) 69 true) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [404011369027963954016850855403031957305515]) 0) 31 false) (.node 959 (sourceLit (List.headD (raw_ints% [1433542181407318217817706485]) 0) 81 false) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [16013154876685263398355202930215]) 0) 66 true) .empty .empty)))

#time def treeG_J022_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [62379302765721541190364876154887143232045]) 0) 34 true) treeG_J022_part100 treeG_J022_part101)

#time def treeG_J022_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [2016222904457812891025695944915]) 0) 72 false) (.node 999 (sourceLit (List.headD (raw_ints% [690284930045266467210489344883336065716497105]) 0) 24 true) (.node 997 (sourceLit (List.headD (raw_ints% [27958120389725328550579564656270598721696145]) 0) 28 false) (.node 996 (sourceLit (List.headD (raw_ints% [11743594359756750050069312009565]) 0) 68 false) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [1403104856120299557077504215305]) 0) 72 true) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [24383304214435704605694007586595]) 0) 67 true) (.node 1034 (sourceLit (List.headD (raw_ints% [653528580090850118778310360022580530233695]) 0) 32 false) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [8523386796605826770734882157975283838929945]) 0) 30 true) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [282241395110878551998150934345]) 0) 75 true) (.node 1039 (sourceLit (List.headD (raw_ints% [1770091654560573020838837075465]) 0) 73 true) (.node 1038 (sourceLit (List.headD (raw_ints% [36731362200640100306001513811918283653355085]) 0) 29 false) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [16365757651565832233073881894397017087007885]) 0) 29 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [5435550665035925339128896105135]) 0) 72 false) (.node 1077 (sourceLit (List.headD (raw_ints% [96145214762571942716458621920072869433135705]) 0) 28 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [3041092110886232886794586228846106219531222545]) 0) 24 false) .empty .empty))))

#time def treeG_J022_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [5909300370112230332620916134035728603268765]) 0) 29 true) treeG_J022_part102 treeG_J022_part103)

#time def treeG_J022_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [1917024993106051696437564060122951436417885]) 0) 29 false) treeG_J022_part099 treeG_J022_part104)

#time def treeG_J022_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [129437661231007798748745968336100826395945]) 0) 30 true) treeG_J022_part094 treeG_J022_part105)

#time def treeG_J022_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [6174854328424460522181265005]) 0) 69 true) treeG_J022_part081 treeG_J022_part106)

#time def treeG_J022_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [172016750731889269017744075]) 0) 59 false) treeG_J022_part054 treeG_J022_part107)

#time def treeG_J022 : IntSourceTree := treeG_J022_part108

#time def treeG_J023_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [22540963357883944380781749375]) 0) 44 false) (.node 9 (sourceLit (List.headD (raw_ints% [126873422328661058371828703625]) 0) 43 false) (.node 8 (sourceLit (List.headD (raw_ints% [108718822757098741964122973025]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [1621017279194111085897933233625]) 0) 40 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [52928999399801682019595894625]) 0) 47 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [6147535461241075740213204375]) 0) 46 true) (.node 12 (sourceLit (List.headD (raw_ints% [12926127127578542356508362125]) 0) 49 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [6329105803933754067514077075]) 0) 50 false) .empty .empty)))

#time def treeG_J023_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [1098423250566591175784183925]) 0) 52 true) (.node 17 (sourceLit (List.headD (raw_ints% [1259531685465509779252473375]) 0) 51 true) (.node 16 (sourceLit (List.headD (raw_ints% [388120993363663857872514225]) 0) 54 false) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [190705554536378364151393725]) 0) 55 false) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [501419072714546522370793725]) 0) 54 true) (.node 20 (sourceLit (List.headD (raw_ints% [46913174305835476568304375]) 0) 57 false) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 58 false) .empty .empty)))

#time def treeG_J023_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [10350978511662324109589754375]) 0) 47 true) treeG_J023_part000 treeG_J023_part001)

#time def treeG_J023_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [164424886928414603744356287363825]) 0) 36 true) (.node 26 (sourceLit (List.headD (raw_ints% [62274389279698746168282047310075]) 0) 38 true) (.node 25 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 58 false) (.node 24 (sourceLit (List.headD (raw_ints% [73904265906398825755459471796475]) 0) 39 true) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [11399201159686590425850675]) 0) 59 false) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [245206909685330740801802275359975]) 0) 35 true) (.node 29 (sourceLit (List.headD (raw_ints% [2813856862841554753768545]) 0) 61 false) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [1390082321332570593003705]) 0) 62 false) .empty .empty)))

#time def treeG_J023_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [8429930100578660121581180762667645]) 0) 29 true) (.node 34 (sourceLit (List.headD (raw_ints% [2528474520227511259463938467321285]) 0) 31 true) (.node 33 (sourceLit (List.headD (raw_ints% [42944734040611268341905]) 0) 67 false) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [21238549678288153018275]) 0) 68 false) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [14252596686439918362983550208797855]) 0) 28 true) (.node 37 (sourceLit (List.headD (raw_ints% [5254287723987295537575]) 0) 70 false) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [2600868766303020607275]) 0) 71 false) .empty .empty)))

#time def treeG_J023_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [1549021840856513644355116680927825]) 0) 32 true) treeG_J023_part003 treeG_J023_part004)

#time def treeG_J023_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [694673342989331470622316225]) 0) 55 true) treeG_J023_part002 treeG_J023_part005)

#time def treeG_J023_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [12926127127578542356508362125]) 0) 50 false) (.node 51 (sourceLit (List.headD (raw_ints% [52928999399801682019595894625]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [126873422328661058371828703625]) 0) 44 false) (.node 49 (sourceLit (List.headD (raw_ints% [108718822757098741964122973025]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [22540963357883944380781749375]) 0) 45 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [6329105803933754067514077075]) 0) 51 false) (.node 54 (sourceLit (List.headD (raw_ints% [6147535461241075740213204375]) 0) 47 true) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [10350978511662324109589754375]) 0) 48 true) .empty .empty)))

#time def treeG_J023_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [46913174305835476568304375]) 0) 58 false) (.node 59 (sourceLit (List.headD (raw_ints% [190705554536378364151393725]) 0) 56 false) (.node 58 (sourceLit (List.headD (raw_ints% [1259531685465509779252473375]) 0) 52 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [1098423250566591175784183925]) 0) 53 true) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 59 false) (.node 62 (sourceLit (List.headD (raw_ints% [501419072714546522370793725]) 0) 55 true) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [694673342989331470622316225]) 0) 56 true) .empty .empty)))

#time def treeG_J023_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [388120993363663857872514225]) 0) 55 false) treeG_J023_part007 treeG_J023_part008)

#time def treeG_J023_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [1549021840856513644355116680927825]) 0) 33 true) (.node 69 (sourceLit (List.headD (raw_ints% [164424886928414603744356287363825]) 0) 37 true) (.node 67 (sourceLit (List.headD (raw_ints% [62274389279698746168282047310075]) 0) 39 true) (.node 66 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 59 false) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [11399201159686590425850675]) 0) 60 false) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [245206909685330740801802275359975]) 0) 36 true) (.node 70 (sourceLit (List.headD (raw_ints% [2813856862841554753768545]) 0) 62 false) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [1390082321332570593003705]) 0) 63 false) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [8429930100578660121581180762667645]) 0) 30 true) (.node 75 (sourceLit (List.headD (raw_ints% [2528474520227511259463938467321285]) 0) 32 true) (.node 74 (sourceLit (List.headD (raw_ints% [42944734040611268341905]) 0) 68 false) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [21238549678288153018275]) 0) 69 false) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [14252596686439918362983550208797855]) 0) 29 true) (.node 78 (sourceLit (List.headD (raw_ints% [5254287723987295537575]) 0) 71 false) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [1367270434536788969154275826375]) 0) 42 false) .empty .empty))))

#time def treeG_J023_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [73904265906398825755459471796475]) 0) 40 true) treeG_J023_part009 treeG_J023_part010)

#time def treeG_J023_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [1621017279194111085897933233625]) 0) 41 false) treeG_J023_part006 treeG_J023_part011)

#time def treeG_J023_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [1944092410819827370836654375]) 0) 47 true) (.node 93 (sourceLit (List.headD (raw_ints% [14344249409562510060497476875]) 0) 47 false) (.node 92 (sourceLit (List.headD (raw_ints% [10000718068055784915771883125]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [231205881299438172362875657875]) 0) 44 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [19523148451223330645502647175]) 0) 50 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [5312851769800284992579860875]) 0) 49 true) (.node 96 (sourceLit (List.headD (raw_ints% [4776621830479098636024020175]) 0) 52 false) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [585536432190949351593634725]) 0) 55 false) .empty .empty)))

#time def treeG_J023_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [308164802439761574119271225]) 0) 55 true) (.node 101 (sourceLit (List.headD (raw_ints% [74625522231505581676673775]) 0) 57 true) (.node 100 (sourceLit (List.headD (raw_ints% [71896190115271443791544675]) 0) 58 false) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [70719859774468404976100625]) 0) 58 false) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [740886320663736566943332475]) 0) 57 true) (.node 104 (sourceLit (List.headD (raw_ints% [122362085184315824035365407156475]) 0) 39 false) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [528959737971491859875393727061725]) 0) 38 true) .empty .empty)))

#time def treeG_J023_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [1420640120364428382720762825]) 0) 52 true) treeG_J023_part013 treeG_J023_part014)

#time def treeG_J023_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [6297599269074070061302556130591375]) 0) 32 true) (.node 110 (sourceLit (List.headD (raw_ints% [1070192185741986089153048023550625]) 0) 35 true) (.node 109 (sourceLit (List.headD (raw_ints% [4292672148422517836041065]) 0) 62 false) (.node 108 (sourceLit (List.headD (raw_ints% [831965341546765334948156469597375]) 0) 36 true) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [4237631404350538914533385]) 0) 62 false) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [9863700206624597895376994980101315]) 0) 31 true) (.node 113 (sourceLit (List.headD (raw_ints% [1046524449007680446268465]) 0) 64 false) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [64650918402934383665535]) 0) 68 false) .empty .empty)))

#time def treeG_J023_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [1113523589879466852410618419125]) 0) 43 false) (.node 118 (sourceLit (List.headD (raw_ints% [53186844118189362609665895892543305]) 0) 28 true) (.node 117 (sourceLit (List.headD (raw_ints% [3996065488575214370175]) 0) 72 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [7907706681671570467875]) 0) 71 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [52166229485388556995523477125]) 0) 47 false) (.node 131 (sourceLit (List.headD (raw_ints% [54482249372360410102077225]) 0) 59 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [27076745144644597306579170375]) 0) 50 false) .empty .empty)))

#time def treeG_J023_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [32025662223061520029841834714472915]) 0) 29 true) treeG_J023_part016 treeG_J023_part017)

#time def treeG_J023_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [34813776514718505895165575]) 0) 59 false) treeG_J023_part015 treeG_J023_part018)

#time def treeG_J023_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [49353859706821373430280125]) 0) 59 false) (.node 137 (sourceLit (List.headD (raw_ints% [3224137857024443204533963275]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [262715190651328023086034375]) 0) 53 false) (.node 135 (sourceLit (List.headD (raw_ints% [3298510661822394144497142525]) 0) 53 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [274725027938245875569967375]) 0) 50 true) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [96879205924707411014784975]) 0) 58 false) (.node 140 (sourceLit (List.headD (raw_ints% [80554217449459301734144725]) 0) 55 true) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [95585105137498131042596475]) 0) 55 true) .empty .empty)))

#time def treeG_J023_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [233342674345896556853555839875825]) 0) 40 true) (.node 145 (sourceLit (List.headD (raw_ints% [98133175545357324895412439476475]) 0) 41 false) (.node 144 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 59 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [787099298338141663264348725]) 0) 58 true) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [333770227309175365601900091116775]) 0) 38 true) (.node 148 (sourceLit (List.headD (raw_ints% [5853643838757978867328725]) 0) 62 false) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [5771487434003480918313585]) 0) 62 false) .empty .empty)))

#time def treeG_J023_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [11903342734316464203898125]) 0) 61 false) treeG_J023_part020 treeG_J023_part021)

#time def treeG_J023_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [19467123715874722123341172841872725]) 0) 30 true) (.node 155 (sourceLit (List.headD (raw_ints% [3667612843198543317956528256390015]) 0) 33 true) (.node 153 (sourceLit (List.headD (raw_ints% [2374288714108778208473719724831775]) 0) 34 true) (.node 152 (sourceLit (List.headD (raw_ints% [177971817688623020095605]) 0) 67 false) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [702966576682790299533225]) 0) 65 false) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [11797866061241429954130326975902635]) 0) 31 true) (.node 156 (sourceLit (List.headD (raw_ints% [10853092181161557661815]) 0) 71 false) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [10729974230313561943125]) 0) 71 false) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [34630341838065863967655693575]) 0) 50 false) (.node 172 (sourceLit (List.headD (raw_ints% [17894193610592745056491656075]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [441158854290014340023871380625]) 0) 45 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [89988209561214603930549477375]) 0) 47 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [8417420816810477941964549925]) 0) 52 false) (.node 175 (sourceLit (List.headD (raw_ints% [71616160971552019093252970625]) 0) 47 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [13719737870642781731332960875]) 0) 49 false) .empty .empty))))

#time def treeG_J023_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [412492638028327674175622874095325]) 0) 37 true) treeG_J023_part022 treeG_J023_part023)

#time def treeG_J023_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [34836034280366095861208158125]) 0) 47 false) treeG_J023_part019 treeG_J023_part024)

#time def treeG_J023_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [164508646114395801908650051425]) 0) 47 false) treeG_J023_part012 treeG_J023_part025)

#time def treeG_J023_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [116994592164765312034078275]) 0) 55 false) (.node 181 (sourceLit (List.headD (raw_ints% [68696827013551861619202825]) 0) 56 false) (.node 180 (sourceLit (List.headD (raw_ints% [125519248712014049929575825]) 0) 58 false) (.node 179 (sourceLit (List.headD (raw_ints% [2566555212790610889871558275]) 0) 51 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [123038552074946417053469325]) 0) 58 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [1127394861213306463446377475]) 0) 57 false) (.node 184 (sourceLit (List.headD (raw_ints% [22509609096486857882831964596475]) 0) 39 true) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [2099090546697209058201992758685325]) 0) 38 false) .empty .empty)))

#time def treeG_J023_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [7305343463656422922093785]) 0) 62 false) (.node 189 (sourceLit (List.headD (raw_ints% [7414615529093439898616385]) 0) 62 false) (.node 188 (sourceLit (List.headD (raw_ints% [6635000237521924484365630406429025]) 0) 36 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [4270131451204819760477353434317775]) 0) 35 true) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [1801024634010287875261215]) 0) 64 false) (.node 192 (sourceLit (List.headD (raw_ints% [20101929564738901085937307811509425]) 0) 32 true) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [28124919219115853440202520617207085]) 0) 31 true) .empty .empty)))

#time def treeG_J023_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [205478268713215042289878575]) 0) 61 true) treeG_J023_part027 treeG_J023_part028)

#time def treeG_J023_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [336826395319237226032824426375]) 0) 46 false) (.node 198 (sourceLit (List.headD (raw_ints% [135579012861673516656419335721898855]) 0) 28 true) (.node 197 (sourceLit (List.headD (raw_ints% [857128336573292911455]) 0) 75 false) (.node 196 (sourceLit (List.headD (raw_ints% [85337948759291866144767069490007565]) 0) 29 true) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [13552241778955553418375]) 0) 71 false) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [145140384842063111999890796625]) 0) 47 false) (.node 213 (sourceLit (List.headD (raw_ints% [44500029297726382919387453925]) 0) 50 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [21436299190776287389667123475]) 0) 51 false) .empty .empty)))

#time def treeG_J023_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [3210988952386285303744716075]) 0) 52 false) (.node 218 (sourceLit (List.headD (raw_ints% [6997231449290513803451464125]) 0) 51 false) (.node 217 (sourceLit (List.headD (raw_ints% [2596641479893017368715293325]) 0) 54 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [1263403237333402526462211825]) 0) 55 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [370372413191705577519407775]) 0) 55 false) (.node 221 (sourceLit (List.headD (raw_ints% [154159291499320688844366675]) 0) 58 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [75425181137680560237876825]) 0) 59 false) .empty .empty)))

#time def treeG_J023_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [63209274870709522354499870625]) 0) 48 false) treeG_J023_part030 treeG_J023_part031)

#time def treeG_J023_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [444362903071052764871085]) 0) 66 false) treeG_J023_part029 treeG_J023_part032)

#time def treeG_J023_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [5967459782903573753161830224195475]) 0) 37 true) (.node 227 (sourceLit (List.headD (raw_ints% [2565775895389002171909104438436975]) 0) 39 false) (.node 226 (sourceLit (List.headD (raw_ints% [239311769943931015838840775]) 0) 61 false) (.node 225 (sourceLit (List.headD (raw_ints% [218775960187201507673656843549425]) 0) 40 true) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [52832978137993255289301825]) 0) 64 true) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [3445146175148164412126107686127125]) 0) 36 true) (.node 230 (sourceLit (List.headD (raw_ints% [9057743624183398878919185]) 0) 62 false) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [4457794380638454600564105]) 0) 63 false) .empty .empty)))

#time def treeG_J023_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [61742216636809006236506415538202295]) 0) 30 true) (.node 235 (sourceLit (List.headD (raw_ints% [20789693532718766804289464104427055]) 0) 32 true) (.node 234 (sourceLit (List.headD (raw_ints% [549029028663748787863995]) 0) 66 false) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [270713428172467842282045]) 0) 67 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [96644765429924072409736990038153405]) 0) 29 true) (.node 238 (sourceLit (List.headD (raw_ints% [16698132540031811223435]) 0) 71 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [30854773219752827762784368625]) 0) 50 false) .empty .empty)))

#time def treeG_J023_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [15353352136521344668989868361845875]) 0) 33 true) treeG_J023_part034 treeG_J023_part035)

#time def treeG_J023_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [185280030923694960635264025]) 0) 58 false) (.node 258 (sourceLit (List.headD (raw_ints% [3140217967143490236083892825]) 0) 54 false) (.node 256 (sourceLit (List.headD (raw_ints% [6509439186982904723851286775]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [218664608712574204906528622625]) 0) 47 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [24744768500033370311583454875]) 0) 50 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [761326242485346326743908525]) 0) 56 false) (.node 259 (sourceLit (List.headD (raw_ints% [11427907685790416717031369975]) 0) 51 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [2661414336277870410791093475]) 0) 53 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [3849298228194821119591247507080725]) 0) 38 true) (.node 264 (sourceLit (List.headD (raw_ints% [180687678569735920146815823898875]) 0) 39 false) (.node 263 (sourceLit (List.headD (raw_ints% [623750234218645843004737275]) 0) 55 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [174613601199763880989418025]) 0) 60 true) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [47687414563745959234911301421420625]) 0) 36 false) (.node 267 (sourceLit (List.headD (raw_ints% [684101808601077073967560125]) 0) 61 false) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [430078440633039482213030985]) 0) 62 true) .empty .empty))))

#time def treeG_J023_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [54369716757386901871119214275]) 0) 50 false) treeG_J023_part036 treeG_J023_part037)

#time def treeG_J023_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [269513948384804584468966725]) 0) 56 true) treeG_J023_part033 treeG_J023_part038)

#time def treeG_J023_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [653695154256444810856905]) 0) 66 false) (.node 273 (sourceLit (List.headD (raw_ints% [1328384873314083362651445]) 0) 65 false) (.node 272 (sourceLit (List.headD (raw_ints% [90142748040002360102098138144558575]) 0) 32 true) (.node 271 (sourceLit (List.headD (raw_ints% [10810143784710374835744585]) 0) 62 false) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [94701897873054903911716426277559915]) 0) 31 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [161001001091086349615805]) 0) 68 false) (.node 276 (sourceLit (List.headD (raw_ints% [247297147764208402723864356180825315]) 0) 29 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [358358720232798533235631988583719505]) 0) 28 true) .empty .empty)))

#time def treeG_J023_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [1956398853544943677567996725]) 0) 55 false) (.node 295 (sourceLit (List.headD (raw_ints% [2058338597913163405090755675]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [348535986673982132204659101375]) 0) 47 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [1214494795639567832437724625]) 0) 55 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [234601841226260963702710125]) 0) 58 false) (.node 298 (sourceLit (List.headD (raw_ints% [8873768525371428254065995375]) 0) 52 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [2054229683351032853321663475]) 0) 54 false) .empty .empty)))

#time def treeG_J023_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [19844023301108069028495]) 0) 71 false) treeG_J023_part040 treeG_J023_part041)

#time def treeG_J023_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [25870335696480931051766175]) 0) 65 true) (.node 304 (sourceLit (List.headD (raw_ints% [13957252853178912929276625]) 0) 62 false) (.node 303 (sourceLit (List.headD (raw_ints% [1716482027906475006209175]) 0) 65 false) (.node 302 (sourceLit (List.headD (raw_ints% [1920669509894459255752277925]) 0) 54 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [99865909689234356955118166862075]) 0) 42 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [895433721153050095124767425]) 0) 62 false) (.node 307 (sourceLit (List.headD (raw_ints% [1603768530895955822875087986379425]) 0) 41 true) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [13413718586662383247018282911404025]) 0) 39 false) .empty .empty)))

#time def treeG_J023_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [389677922325167287393725]) 0) 67 false) (.node 312 (sourceLit (List.headD (raw_ints% [99255459438623753674695]) 0) 69 false) (.node 311 (sourceLit (List.headD (raw_ints% [10006100159218901463172795168279725]) 0) 38 true) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [18697348975870253858277067445678175]) 0) 35 true) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [95745431520994242143715]) 0) 69 false) (.node 315 (sourceLit (List.headD (raw_ints% [18478051085084034276856740543283215]) 0) 34 true) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [46388732781849849121839485160655755]) 0) 32 true) .empty .empty)))

#time def treeG_J023_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [869214624890262363304981155]) 0) 62 true) treeG_J023_part043 treeG_J023_part044)

#time def treeG_J023_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [453007659486704949055175175]) 0) 57 false) treeG_J023_part042 treeG_J023_part045)

#time def treeG_J023_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [4685377447036284474188094075]) 0) 54 false) (.node 336 (sourceLit (List.headD (raw_ints% [9957269596322402516874758625]) 0) 53 false) (.node 335 (sourceLit (List.headD (raw_ints% [478407364635390059502789580125]) 0) 47 false) (.node 319 (sourceLit (List.headD (raw_ints% [65428488700718615206473749636391525]) 0) 31 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [52982898420898970964430921125]) 0) 50 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [1115488487324741382877772475]) 0) 56 false) (.node 339 (sourceLit (List.headD (raw_ints% [24067166415695296299232611525]) 0) 51 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [5555504397126261002495560425]) 0) 53 false) .empty .empty)))

#time def treeG_J023_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [7045007338250320542155028846667125]) 0) 38 false) (.node 344 (sourceLit (List.headD (raw_ints% [49694639368703751675365537355525]) 0) 39 false) (.node 343 (sourceLit (List.headD (raw_ints% [648459637837906706373770325]) 0) 56 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [286271624025195184423631025]) 0) 60 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [150328600541087131898916932549703825]) 0) 36 true) (.node 347 (sourceLit (List.headD (raw_ints% [1511952550888466867624077725]) 0) 61 true) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [2220945882939139672462565835]) 0) 62 false) .empty .empty)))

#time def treeG_J023_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [133863814281504994209955575]) 0) 59 false) treeG_J023_part047 treeG_J023_part048)

#time def treeG_J023_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [1126080728786396638663231536557264655]) 0) 28 true) (.node 354 (sourceLit (List.headD (raw_ints% [503613269354793219553149731984141685]) 0) 31 true) (.node 352 (sourceLit (List.headD (raw_ints% [1190638072340017027184019643395246225]) 0) 32 true) (.node 351 (sourceLit (List.headD (raw_ints% [1749239393565235101445706895]) 0) 62 true) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [1847789828721876754938795]) 0) 65 false) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [935298121681169790994967038589300445]) 0) 29 true) (.node 355 (sourceLit (List.headD (raw_ints% [905016535044224338717995]) 0) 66 false) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [221980724992890618959055]) 0) 68 false) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [35235361370156114456298930375]) 0) 51 false) (.node 376 (sourceLit (List.headD (raw_ints% [322952030793525376950760828125]) 0) 48 false) (.node 359 (sourceLit (List.headD (raw_ints% [54520424328742966665075]) 0) 70 false) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [6044471889232515161738765175]) 0) 54 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [15850247682291164885945957625]) 0) 52 false) (.node 379 (sourceLit (List.headD (raw_ints% [2808562717226196764566413075]) 0) 55 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [165620206959509108455649325]) 0) 59 false) .empty .empty))))

#time def treeG_J023_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [472708541585220034169402341524174825]) 0) 35 false) treeG_J023_part049 treeG_J023_part050)

#time def treeG_J023_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [94208470930959104722065]) 0) 69 false) treeG_J023_part046 treeG_J023_part051)

#time def treeG_J023_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [43469546812023770264817288359246025]) 0) 35 true) treeG_J023_part039 treeG_J023_part052)

#time def treeG_J023_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [2053064992642544501346693825]) 0) 54 false) treeG_J023_part026 treeG_J023_part053)

#time def treeG_J023_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [13460081461834143833655380792184825]) 0) 39 false) (.node 385 (sourceLit (List.headD (raw_ints% [349768999388233676145107130092775]) 0) 40 true) (.node 384 (sourceLit (List.headD (raw_ints% [201827546536181492636918325]) 0) 57 false) (.node 383 (sourceLit (List.headD (raw_ints% [78936389388497794011261975]) 0) 60 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [700196995168890081251889825]) 0) 61 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [203983474887736664886990064195319925]) 0) 37 true) (.node 388 (sourceLit (List.headD (raw_ints% [1203693136020758481374422575]) 0) 63 true) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [5311106390768541708230112825]) 0) 62 false) .empty .empty)))

#time def treeG_J023_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [429701065014457082445722769811008825]) 0) 32 true) (.node 393 (sourceLit (List.headD (raw_ints% [1115848676436536011750911373612533525]) 0) 33 true) (.node 392 (sourceLit (List.headD (raw_ints% [1755591742969307021680887375]) 0) 63 true) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [1068433984071542180151345]) 0) 66 false) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [749743190553770394507609097946677425]) 0) 30 true) (.node 396 (sourceLit (List.headD (raw_ints% [522034808960247370143135]) 0) 67 false) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [63886127030965757118495]) 0) 70 false) .empty .empty)))

#time def treeG_J023_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [512732942222095640022093522197293725]) 0) 36 false) treeG_J023_part055 treeG_J023_part056)

#time def treeG_J023_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [643421455322806492715649825]) 0) 57 false) (.node 419 (sourceLit (List.headD (raw_ints% [46403556324616932613365249225]) 0) 51 false) (.node 418 (sourceLit (List.headD (raw_ints% [7403566331428745849289436275]) 0) 54 false) (.node 417 (sourceLit (List.headD (raw_ints% [216986233951727435021898985875]) 0) 49 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [211634278737681922711080075]) 0) 59 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [1168957805777994166997870925]) 0) 56 false) (.node 422 (sourceLit (List.headD (raw_ints% [197376599637513222701343075]) 0) 59 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [281388574389030099737246609434875]) 0) 39 false) .empty .empty)))

#time def treeG_J023_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [7035718427022173597960256135]) 0) 62 true) (.node 427 (sourceLit (List.headD (raw_ints% [2912346541226247030127857375]) 0) 61 false) (.node 426 (sourceLit (List.headD (raw_ints% [9843159333356189951315885887409325]) 0) 38 true) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [365689903930433433237403025224661025]) 0) 36 false) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [12371452175102318517905932545]) 0) 62 false) (.node 430 (sourceLit (List.headD (raw_ints% [2104576340687113353265322855086734225]) 0) 35 true) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [17598092223447077507891012353708645425]) 0) 32 false) .empty .empty)))

#time def treeG_J023_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [943258949564599245057605775]) 0) 58 true) treeG_J023_part058 treeG_J023_part059)

#time def treeG_J023_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [864366773983522177837336538011698555]) 0) 29 true) treeG_J023_part057 treeG_J023_part060)

#time def treeG_J023_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [4871864795643766517397641247016154745]) 0) 28 true) (.node 436 (sourceLit (List.headD (raw_ints% [5939918918550143528136597278386840755]) 0) 29 true) (.node 435 (sourceLit (List.headD (raw_ints% [1231851433098860021584695]) 0) 66 false) (.node 434 (sourceLit (List.headD (raw_ints% [8423176142137494874454141256916126515]) 0) 31 true) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [18753380247959796949005]) 0) 72 false) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [146515511211415206109301125125]) 0) 50 false) (.node 439 (sourceLit (List.headD (raw_ints% [73251829733188547571915]) 0) 70 false) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [143593862943829658897594475]) 0) 60 false) .empty .empty)))

#time def treeG_J023_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [120891282405226584295119075]) 0) 60 false) (.node 462 (sourceLit (List.headD (raw_ints% [1664977099483275534176778675]) 0) 56 false) (.node 461 (sourceLit (List.headD (raw_ints% [257648350515854736966510825]) 0) 59 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [29610052562253857172520275]) 0) 62 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [3744046930240159570065165075]) 0) 59 true) (.node 465 (sourceLit (List.headD (raw_ints% [315578786888631887941176869763825]) 0) 41 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [11651620397595166892485633339797075]) 0) 40 true) .empty .empty)))

#time def treeG_J023_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [1909581790145360482963705725]) 0) 56 false) treeG_J023_part062 treeG_J023_part063)

#time def treeG_J023_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [88727078017326581430195]) 0) 70 false) (.node 472 (sourceLit (List.headD (raw_ints% [882940244879476596224176245]) 0) 67 false) (.node 470 (sourceLit (List.headD (raw_ints% [19382543244812888904150625095]) 0) 62 true) (.node 469 (sourceLit (List.headD (raw_ints% [284836689409085049062196544709990475]) 0) 38 false) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [1308654641454604496643708188642013975]) 0) 37 true) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [1761424190594893859551067655]) 0) 65 true) (.node 473 (sourceLit (List.headD (raw_ints% [9356970449941806759820961863660589475]) 0) 34 false) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [3996737538561518896004209243552558845]) 0) 33 true) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [25027988721699568373983968975]) 0) 53 false) (.node 478 (sourceLit (List.headD (raw_ints% [86140914952712618473545]) 0) 70 false) (.node 477 (sourceLit (List.headD (raw_ints% [2595087863998186566814494090220081665]) 0) 31 true) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [2003749010830122169780152354502228095]) 0) 30 true) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [316540083705638497562013975]) 0) 59 false) (.node 500 (sourceLit (List.headD (raw_ints% [362741173037636712879297825]) 0) 59 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [317920101394196251231678575]) 0) 59 false) .empty .empty))))

#time def treeG_J023_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [5319732813267763992876702525]) 0) 62 false) treeG_J023_part064 treeG_J023_part065)

#time def treeG_J023_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [1759287322626750775190764965]) 0) 64 true) treeG_J023_part061 treeG_J023_part066)

#time def treeG_J023_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [738541756653478773796943292098167425]) 0) 36 true) (.node 506 (sourceLit (List.headD (raw_ints% [14892419923574300158374715803630525]) 0) 38 false) (.node 505 (sourceLit (List.headD (raw_ints% [1910389208806411919418558375]) 0) 58 false) (.node 504 (sourceLit (List.headD (raw_ints% [215385673219256308879275308619525]) 0) 39 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [9568740012692653630320879825]) 0) 60 true) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [6661963371232474138260467570446581825]) 0) 35 false) (.node 509 (sourceLit (List.headD (raw_ints% [17675184053557701583713661185]) 0) 62 false) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [51136538664728096326207182735]) 0) 62 true) .empty .empty)))

#time def treeG_J023_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [121955682315418461143998098515295042285]) 0) 29 true) (.node 514 (sourceLit (List.headD (raw_ints% [158134703341206403031589531075485558115]) 0) 31 false) (.node 513 (sourceLit (List.headD (raw_ints% [15886331240698376314777584885]) 0) 64 false) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [881328021013996359786326175]) 0) 67 true) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [36649541028327218551634264196505151895]) 0) 28 true) (.node 517 (sourceLit (List.headD (raw_ints% [51220317521406987532185]) 0) 71 false) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [99030000172236689375175]) 0) 70 false) .empty .empty)))

#time def treeG_J023_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [101351989276541765293088336426797539825]) 0) 32 true) treeG_J023_part068 treeG_J023_part069)

#time def treeG_J023_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [415771900558007467003078430908125]) 0) 40 true) (.node 543 (sourceLit (List.headD (raw_ints% [199479891145180822541597475]) 0) 60 false) (.node 542 (sourceLit (List.headD (raw_ints% [3399664239806940426815444925]) 0) 56 false) (.node 541 (sourceLit (List.headD (raw_ints% [467833995559418688792084825]) 0) 59 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [1193866133946744226994733825]) 0) 57 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [38195660718764633943345982483224675]) 0) 39 false) (.node 546 (sourceLit (List.headD (raw_ints% [2827218069523285744741861725]) 0) 60 false) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [20208205639228181616074284875]) 0) 61 true) .empty .empty)))

#time def treeG_J023_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [120065930176425378812730260154118718775]) 0) 33 true) (.node 551 (sourceLit (List.headD (raw_ints% [9279272654141683131547883947730609775]) 0) 36 false) (.node 550 (sourceLit (List.headD (raw_ints% [54732911351928292071577947465]) 0) 62 false) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [65263582582799721865794002655]) 0) 63 true) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [166128178418329440823597949562590675805]) 0) 32 false) (.node 554 (sourceLit (List.headD (raw_ints% [4411938857823317543582163135]) 0) 67 false) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [881682929326065666112046955]) 0) 68 true) .empty .empty)))

#time def treeG_J023_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [1308215135471648871921336381518148375]) 0) 37 true) treeG_J023_part071 treeG_J023_part072)

#time def treeG_J023_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [17389661561118126442129146075]) 0) 54 false) treeG_J023_part070 treeG_J023_part073)

#time def treeG_J023_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [4638332086425323952275203425]) 0) 56 false) (.node 581 (sourceLit (List.headD (raw_ints% [12325020221827910481136922475]) 0) 55 false) (.node 559 (sourceLit (List.headD (raw_ints% [32642043006666974212073959487500695705]) 0) 29 true) (.node 558 (sourceLit (List.headD (raw_ints% [118740355132915331655195]) 0) 70 false) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [617747889724641126352491075]) 0) 59 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [358261537429833846211912275]) 0) 59 true) (.node 584 (sourceLit (List.headD (raw_ints% [621293632130540195830237147162875]) 0) 39 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [18218595128038359894399343250895525]) 0) 38 true) .empty .empty)))

#time def treeG_J023_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [160602361368584680469363077665]) 0) 62 false) (.node 589 (sourceLit (List.headD (raw_ints% [9470847423196470799946986515]) 0) 64 true) (.node 588 (sourceLit (List.headD (raw_ints% [1349672328153712916890479011829762225]) 0) 36 false) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [17127684455005665113631158622591768825]) 0) 35 true) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [20287478455874524545142896885]) 0) 66 true) (.node 592 (sourceLit (List.headD (raw_ints% [398288714209075625502620622754177052625]) 0) 32 false) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [1118662144752609433533431612308435308315]) 0) 31 true) .empty .empty)))

#time def treeG_J023_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [15223176151739225119804603275]) 0) 60 false) treeG_J023_part075 treeG_J023_part076)

#time def treeG_J023_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [129633191586068457854164447258875]) 0) 43 false) (.node 599 (sourceLit (List.headD (raw_ints% [138450710093593973935215]) 0) 70 false) (.node 597 (sourceLit (List.headD (raw_ints% [881887810596151294062175695]) 0) 69 true) (.node 596 (sourceLit (List.headD (raw_ints% [2780006537008689514321565291516745855165]) 0) 29 false) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [897474511671049485531318618482333879745]) 0) 28 true) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [13070874955608134494090425]) 0) 65 false) (.node 622 (sourceLit (List.headD (raw_ints% [4462677991010485027160738775]) 0) 57 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [107639561014955616415014675]) 0) 62 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [332235932953170223601476924168488825]) 0) 40 false) (.node 627 (sourceLit (List.headD (raw_ints% [7051781980850374229718165716765025]) 0) 42 true) (.node 626 (sourceLit (List.headD (raw_ints% [199092475434569974434610875]) 0) 64 true) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [17715690895483703367939444075]) 0) 62 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [3300869638643418530647380321290297325]) 0) 39 true) (.node 630 (sourceLit (List.headD (raw_ints% [130499690737500058471153839585]) 0) 62 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [882288843560095321621707345]) 0) 71 false) .empty .empty))))

#time def treeG_J023_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [9705205736660631446950652445]) 0) 67 false) treeG_J023_part077 treeG_J023_part078)

#time def treeG_J023_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [116765506587422088010369110334854878955]) 0) 30 true) treeG_J023_part074 treeG_J023_part079)

#time def treeG_J023_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [2160996393188556901355686425]) 0) 56 false) treeG_J023_part067 treeG_J023_part080)

#time def treeG_J023_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [441003275475642104696915445]) 0) 71 true) (.node 636 (sourceLit (List.headD (raw_ints% [1323361083248337139132837425]) 0) 71 false) (.node 635 (sourceLit (List.headD (raw_ints% [160598790396367359294628695233878248015]) 0) 35 true) (.node 634 (sourceLit (List.headD (raw_ints% [6174854328424460522181265005]) 0) 69 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [362096505449513950291491800231450091765]) 0) 33 false) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [13212379877616616156367751675]) 0) 56 false) (.node 639 (sourceLit (List.headD (raw_ints% [108104058583047813914905582374354148005]) 0) 32 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [1133049507383284474285009122891525]) 0) 39 false) .empty .empty)))

#time def treeG_J023_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [36657385741876644967833417105]) 0) 63 false) (.node 667 (sourceLit (List.headD (raw_ints% [21594135365645464301712151275]) 0) 60 true) (.node 666 (sourceLit (List.headD (raw_ints% [26515119389546741197065867875463525]) 0) 38 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [2252300421702560818294404223575685425]) 0) 36 true) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [421601742843584797411670756835]) 0) 62 true) (.node 670 (sourceLit (List.headD (raw_ints% [38390784164008559424125681769375053625]) 0) 35 false) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [1243311341701790769348349985004493167825]) 0) 32 true) .empty .empty)))

#time def treeG_J023_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [2080494513669123708852147075]) 0) 59 false) treeG_J023_part082 treeG_J023_part083)

#time def treeG_J023_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [24071650860439942304186793833295139752705]) 0) 28 false) (.node 676 (sourceLit (List.headD (raw_ints% [23336651707743711504034038281453161601085]) 0) 29 true) (.node 675 (sourceLit (List.headD (raw_ints% [59104040364056315624400772485]) 0) 67 true) (.node 674 (sourceLit (List.headD (raw_ints% [5265499299836617468056238675574801479515]) 0) 31 false) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [11468776476582848407124875095]) 0) 69 false) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [9767913925138036431087282075]) 0) 57 false) (.node 679 (sourceLit (List.headD (raw_ints% [1764151552612662012761596995]) 0) 70 true) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [95983974694736811451693544820525]) 0) 40 false) .empty .empty)))

#time def treeG_J023_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [277129233705006638342487508005]) 0) 62 false) (.node 708 (sourceLit (List.headD (raw_ints% [57025517156612871037591039425]) 0) 61 true) (.node 707 (sourceLit (List.headD (raw_ints% [82929375236349735034811193609583725]) 0) 39 false) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [4910187885327922607106219616923596025]) 0) 37 true) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [647467686794969199746827837155]) 0) 63 true) (.node 711 (sourceLit (List.headD (raw_ints% [64797741273155907669304724339697432225]) 0) 36 false) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [1761665986087291773663700867912788939225]) 0) 33 true) .empty .empty)))

#time def treeG_J023_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [5265974120622243299805921075]) 0) 60 false) treeG_J023_part085 treeG_J023_part086)

#time def treeG_J023_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [76753964443720625128932166965]) 0) 66 false) treeG_J023_part084 treeG_J023_part087)

#time def treeG_J023_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [24936483329104324815506038492289972936745]) 0) 29 false) (.node 717 (sourceLit (List.headD (raw_ints% [26233423751339823106365972683304762335205]) 0) 30 true) (.node 716 (sourceLit (List.headD (raw_ints% [69690929030043012737463471885]) 0) 68 true) (.node 715 (sourceLit (List.headD (raw_ints% [6550289623007556342413268237445827463635]) 0) 32 false) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [12350783027534132616518705985]) 0) 70 false) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [25747247591988846705452319516899325]) 0) 38 true) (.node 745 (sourceLit (List.headD (raw_ints% [5606924897799789013382987925]) 0) 58 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [32126083606889950901323993425]) 0) 60 false) .empty .empty)))

#time def treeG_J023_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [3316839062442779814766101163874810999025]) 0) 32 false) (.node 750 (sourceLit (List.headD (raw_ints% [77672287246631940280975438704763821825]) 0) 35 true) (.node 749 (sourceLit (List.headD (raw_ints% [130340288640366160973257873635]) 0) 62 true) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [975860210253598074096645772845]) 0) 62 false) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [19358827188534951657365845618877112993315]) 0) 31 true) (.node 753 (sourceLit (List.headD (raw_ints% [954483544569851700262556505015]) 0) 64 true) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [262010803878893250059715226455]) 0) 67 false) .empty .empty)))

#time def treeG_J023_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [3579170425484156578851383321329025025]) 0) 36 false) treeG_J023_part089 treeG_J023_part090)

#time def treeG_J023_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [537809810985738960289003255275]) 0) 62 true) (.node 786 (sourceLit (List.headD (raw_ints% [4925023343444697586228854225]) 0) 59 true) (.node 758 (sourceLit (List.headD (raw_ints% [233939040871158527155114575299733238434345]) 0) 28 true) (.node 757 (sourceLit (List.headD (raw_ints% [20289926376656465286147086745]) 0) 71 true) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [26465717607680927245799008965]) 0) 70 false) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [44575800381751410969457516425]) 0) 62 false) (.node 787 (sourceLit (List.headD (raw_ints% [54338311414169290870131756563241525]) 0) 40 true) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [4244679155406039592978801469126310525]) 0) 38 false) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [1360297071599525569133185412955]) 0) 65 true) (.node 792 (sourceLit (List.headD (raw_ints% [101457993565535454615217100625]) 0) 67 false) (.node 791 (sourceLit (List.headD (raw_ints% [71235014259893923975140081522230627025]) 0) 37 true) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [2539252524265035794214901015893799969125]) 0) 34 false) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [82925433227234065699294674585]) 0) 70 false) (.node 795 (sourceLit (List.headD (raw_ints% [12954558405771253999889556928161470228475]) 0) 33 true) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [77187354713602218044506151381945581677225]) 0) 31 false) .empty .empty))))

#time def treeG_J023_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [128141285675864612982646330080586401019245]) 0) 29 false) treeG_J023_part091 treeG_J023_part092)

#time def treeG_J023_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [101453381757418467217657226985]) 0) 67 false) treeG_J023_part088 treeG_J023_part093)

#time def treeG_J023_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [145587153733128573768636262210784790225]) 0) 35 false) (.node 828 (sourceLit (List.headD (raw_ints% [5317996390737573886695599531352753825]) 0) 36 true) (.node 827 (sourceLit (List.headD (raw_ints% [18525553475167324243776423825]) 0) 61 true) (.node 799 (sourceLit (List.headD (raw_ints% [129437762100131425985310306896011605685545]) 0) 30 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [219491889403868982912172906485]) 0) 62 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [7875879975075990949175066381297571128625]) 0) 32 true) (.node 831 (sourceLit (List.headD (raw_ints% [2051479832225075994674652283395]) 0) 62 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [2577811441618418974106030115015]) 0) 64 false) .empty .empty)))

#time def treeG_J023_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [1468936716288794015867212997410862545269945]) 0) 28 false) (.node 836 (sourceLit (List.headD (raw_ints% [542687154660544740979112151781753448330445]) 0) 29 true) (.node 835 (sourceLit (List.headD (raw_ints% [1884318679357312069252615865865]) 0) 66 true) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [51607679801945265492720880665]) 0) 72 false) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [31550676928459367606616970125]) 0) 63 true) (.node 839 (sourceLit (List.headD (raw_ints% [213486694676000914768013114895]) 0) 70 true) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [13807354701549653072653202469605374875]) 0) 37 true) .empty .empty)))

#time def treeG_J023_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [59986867576775524364804261873177912499315]) 0) 31 false) treeG_J023_part095 treeG_J023_part096)

#time def treeG_J023_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [506371926949722117702874098285]) 0) 70 false) (.node 874 (sourceLit (List.headD (raw_ints% [1969054256608972271619607763985]) 0) 66 false) (.node 872 (sourceLit (List.headD (raw_ints% [3674807729273643268518125893395]) 0) 63 true) (.node 871 (sourceLit (List.headD (raw_ints% [288057182252916421718916425255246044275]) 0) 36 false) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [12954385023606062537604868413085171066875]) 0) 33 true) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [2547722145175184594846973262545]) 0) 67 true) (.node 875 (sourceLit (List.headD (raw_ints% [85895984388318032364583375729500852956265]) 0) 32 false) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [697061864087749177068124454545644611684895]) 0) 30 true) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [4005067011812029846901350419885]) 0) 62 false) (.node 909 (sourceLit (List.headD (raw_ints% [345694597117706453338640786985]) 0) 62 true) (.node 879 (sourceLit (List.headD (raw_ints% [1727812240489056867837833611202885756641035]) 0) 29 false) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [256045991345525798349861881967627789225]) 0) 35 true) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [3126309585446031121312078004205]) 0) 65 true) (.node 912 (sourceLit (List.headD (raw_ints% [17093709807169316444180391989465444545425]) 0) 32 false) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [163621947765624024665643209177859281034315]) 0) 31 true) .empty .empty))))

#time def treeG_J023_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [976793589793476926113349068245]) 0) 62 false) treeG_J023_part097 treeG_J023_part098)

#time def treeG_J023_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [1668182784028889832790630642215]) 0) 62 true) (.node 918 (sourceLit (List.headD (raw_ints% [7045431628990787432412208633776019438749105]) 0) 28 true) (.node 917 (sourceLit (List.headD (raw_ints% [3373445022006308842730507353185]) 0) 68 true) (.node 916 (sourceLit (List.headD (raw_ints% [1917022904873633258812446163453767095630685]) 0) 29 false) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [1226230548575445150173761311465]) 0) 70 false) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [119998042829463642428429317395]) 0) 69 false) (.node 951 (sourceLit (List.headD (raw_ints% [136025793399610555017194576805718458375]) 0) 38 true) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [7512023707693844745446315100637653903075]) 0) 35 false) .empty .empty)))

#time def treeG_J023_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [4386188875905753078136255549755]) 0) 69 true) (.node 956 (sourceLit (List.headD (raw_ints% [2092537334437610301834701164095]) 0) 69 false) (.node 955 (sourceLit (List.headD (raw_ints% [62379483038485514257556646226840033497645]) 0) 34 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [653521192240345608970142654499852926828895]) 0) 32 false) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [6966246955988867679021816160845]) 0) 65 false) (.node 959 (sourceLit (List.headD (raw_ints% [2193310967369961075062510561244726298847535]) 0) 31 true) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [404006706411827056519925292398264205932715]) 0) 31 false) .empty .empty)))

#time def treeG_J023_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [2547681921027501696465842884095]) 0) 67 true) treeG_J023_part100 treeG_J023_part101)

#time def treeG_J023_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [8523394588298088607176642139970940946795545]) 0) 30 true) (.node 999 (sourceLit (List.headD (raw_ints% [1403104856120299557077504215305]) 0) 72 true) (.node 997 (sourceLit (List.headD (raw_ints% [11743594359756750050069312009565]) 0) 68 false) (.node 996 (sourceLit (List.headD (raw_ints% [5909309819336706171296071521971529239479965]) 0) 29 true) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [27958109780681846919456773577771313097273745]) 0) 28 false) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [653524638565769113550151877305624339923295]) 0) 32 false) (.node 1034 (sourceLit (List.headD (raw_ints% [12061610798043871071953501929035]) 0) 66 false) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [24383304214435704605694007586595]) 0) 67 true) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [16365704036389011988098501558861518678252685]) 0) 29 false) (.node 1039 (sourceLit (List.headD (raw_ints% [36731353650161691219706815822750218292663885]) 0) 29 false) (.node 1038 (sourceLit (List.headD (raw_ints% [2016222904457812891025695944915]) 0) 72 false) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [40136376472773005542262206788285]) 0) 66 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [96145266487066555776869910697538840671638105]) 0) 28 true) (.node 1077 (sourceLit (List.headD (raw_ints% [282241395110878551998150934345]) 0) 75 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [5435550665035925339128896105135]) 0) 72 false) .empty .empty))))

#time def treeG_J023_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [16013154876685263398355202930215]) 0) 66 true) treeG_J023_part102 treeG_J023_part103)

#time def treeG_J023_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [5822427192575256612491831393835]) 0) 66 false) treeG_J023_part099 treeG_J023_part104)

#time def treeG_J023_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [93510488534159993761107052965]) 0) 70 true) treeG_J023_part094 treeG_J023_part105)

#time def treeG_J023_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [64794330548187625539418860363536971425]) 0) 36 false) treeG_J023_part081 treeG_J023_part106)

#time def treeG_J023_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [908708721807950436685820625]) 0) 56 false) treeG_J023_part054 treeG_J023_part107)

#time def treeG_J023 : IntSourceTree := treeG_J023_part108

#time def treeG_J024_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [52928999399801682019595894625]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [108718822757098741964122973025]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [36709568897125280848701706125]) 0) 45 false) (.node 7 (sourceLit (List.headD (raw_ints% [897349560962761486330951556475]) 0) 43 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 46 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [12926127127578542356508362125]) 0) 49 false) (.node 12 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 49 true) .empty .empty)))

#time def treeG_J024_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [190705554536378364151393725]) 0) 55 false) (.node 17 (sourceLit (List.headD (raw_ints% [388120993363663857872514225]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [199663544895009297545386125]) 0) 53 true) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [175290639812734832210345625]) 0) 54 true) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [46913174305835476568304375]) 0) 57 false) (.node 20 (sourceLit (List.headD (raw_ints% [36439445161336434614756775]) 0) 57 true) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [64690449404680658507302575]) 0) 57 true) .empty .empty)))

#time def treeG_J024_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [6329105803933754067514077075]) 0) 50 false) treeG_J024_part000 treeG_J024_part001)

#time def treeG_J024_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [171159176571870727114875]) 0) 65 false) (.node 26 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 61 false) (.node 25 (sourceLit (List.headD (raw_ints% [73904265906398825755459471796475]) 0) 39 true) (.node 24 (sourceLit (List.headD (raw_ints% [21949234560470801666952675]) 0) 60 true) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [62274389279698746168282047310075]) 0) 38 true) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [338304965555159657869815]) 0) 64 false) (.node 29 (sourceLit (List.headD (raw_ints% [164424886928414603744356287363825]) 0) 36 true) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [245206909685330740801802275359975]) 0) 35 true) .empty .empty)))

#time def treeG_J024_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [639797951524784037375]) 0) 73 false) (.node 34 (sourceLit (List.headD (raw_ints% [5171212835721061235535]) 0) 70 false) (.node 33 (sourceLit (List.headD (raw_ints% [1549021840856513644355116680927825]) 0) 32 true) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [2528474520227511259463938467321285]) 0) 31 true) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [633525367304305271925]) 0) 73 false) (.node 37 (sourceLit (List.headD (raw_ints% [8429930100578660121581180762667645]) 0) 29 true) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [14252596686439918362983550208797855]) 0) 28 true) .empty .empty)))

#time def treeG_J024_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [10453955364240303936735]) 0) 69 false) treeG_J024_part003 treeG_J024_part004)

#time def treeG_J024_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 58 false) treeG_J024_part002 treeG_J024_part005)

#time def treeG_J024_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 51 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 47 false) (.node 50 (sourceLit (List.headD (raw_ints% [108718822757098741964122973025]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [36709568897125280848701706125]) 0) 46 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [52928999399801682019595894625]) 0) 48 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 50 true) (.node 54 (sourceLit (List.headD (raw_ints% [12926127127578542356508362125]) 0) 50 false) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [6329105803933754067514077075]) 0) 51 false) .empty .empty)))

#time def treeG_J024_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [36439445161336434614756775]) 0) 58 true) (.node 59 (sourceLit (List.headD (raw_ints% [175290639812734832210345625]) 0) 55 true) (.node 58 (sourceLit (List.headD (raw_ints% [388120993363663857872514225]) 0) 55 false) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [190705554536378364151393725]) 0) 56 false) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [64690449404680658507302575]) 0) 58 true) (.node 62 (sourceLit (List.headD (raw_ints% [46913174305835476568304375]) 0) 58 false) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 59 false) .empty .empty)))

#time def treeG_J024_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [199663544895009297545386125]) 0) 54 true) treeG_J024_part007 treeG_J024_part008)

#time def treeG_J024_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [10453955364240303936735]) 0) 70 false) (.node 69 (sourceLit (List.headD (raw_ints% [171159176571870727114875]) 0) 66 false) (.node 67 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 62 false) (.node 66 (sourceLit (List.headD (raw_ints% [73904265906398825755459471796475]) 0) 40 true) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [62274389279698746168282047310075]) 0) 39 true) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [338304965555159657869815]) 0) 65 false) (.node 70 (sourceLit (List.headD (raw_ints% [164424886928414603744356287363825]) 0) 37 true) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [245206909685330740801802275359975]) 0) 36 true) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [639797951524784037375]) 0) 74 false) (.node 75 (sourceLit (List.headD (raw_ints% [5171212835721061235535]) 0) 71 false) (.node 74 (sourceLit (List.headD (raw_ints% [1549021840856513644355116680927825]) 0) 33 true) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [2528474520227511259463938467321285]) 0) 32 true) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [633525367304305271925]) 0) 74 false) (.node 78 (sourceLit (List.headD (raw_ints% [8429930100578660121581180762667645]) 0) 30 true) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [679911915448564002402705610425]) 0) 45 false) .empty .empty))))

#time def treeG_J024_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [21949234560470801666952675]) 0) 61 true) treeG_J024_part009 treeG_J024_part010)

#time def treeG_J024_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [897349560962761486330951556475]) 0) 44 false) treeG_J024_part006 treeG_J024_part011)

#time def treeG_J024_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [19523148451223330645502647175]) 0) 50 false) (.node 93 (sourceLit (List.headD (raw_ints% [10000718068055784915771883125]) 0) 51 false) (.node 92 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 48 false) (.node 91 (sourceLit (List.headD (raw_ints% [164508646114395801908650051425]) 0) 47 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 49 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [4776621830479098636024020175]) 0) 52 false) (.node 96 (sourceLit (List.headD (raw_ints% [620007849937134134483041125]) 0) 51 true) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [224036449977283762880426625]) 0) 54 true) .empty .empty)))

#time def treeG_J024_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [70719859774468404976100625]) 0) 58 false) (.node 101 (sourceLit (List.headD (raw_ints% [71896190115271443791544675]) 0) 58 false) (.node 100 (sourceLit (List.headD (raw_ints% [102411749490061962980832075]) 0) 56 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [81067331240665079951724525]) 0) 57 true) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [122362085184315824035365407156475]) 0) 39 false) (.node 104 (sourceLit (List.headD (raw_ints% [20791980283739055173397225]) 0) 59 true) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [46671247781405909113166325]) 0) 61 true) .empty .empty)))

#time def treeG_J024_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [585536432190949351593634725]) 0) 55 false) treeG_J024_part013 treeG_J024_part014)

#time def treeG_J024_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [254673322641237226375935]) 0) 66 false) (.node 110 (sourceLit (List.headD (raw_ints% [1030968447019806159049185]) 0) 64 false) (.node 109 (sourceLit (List.headD (raw_ints% [831965341546765334948156469597375]) 0) 36 true) (.node 108 (sourceLit (List.headD (raw_ints% [2088141954176822870801475]) 0) 63 false) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [1070192185741986089153048023550625]) 0) 35 true) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [15736697892759546637935]) 0) 70 false) (.node 113 (sourceLit (List.headD (raw_ints% [6297599269074070061302556130591375]) 0) 32 true) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [9863700206624597895376994980101315]) 0) 31 true) .empty .empty)))

#time def treeG_J024_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [462474269934366518474459664375]) 0) 46 false) (.node 118 (sourceLit (List.headD (raw_ints% [1925666438794830877575]) 0) 73 false) (.node 117 (sourceLit (List.headD (raw_ints% [32025662223061520029841834714472915]) 0) 29 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [53186844118189362609665895892543305]) 0) 28 true) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [54482249372360410102077225]) 0) 59 false) (.node 131 (sourceLit (List.headD (raw_ints% [13524578014730366628469049625]) 0) 49 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 49 false) .empty .empty)))

#time def treeG_J024_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [3891616932671493160785]) 0) 72 false) treeG_J024_part016 treeG_J024_part017)

#time def treeG_J024_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [528959737971491859875393727061725]) 0) 38 true) treeG_J024_part015 treeG_J024_part018)

#time def treeG_J024_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [6093226270568616333760125]) 0) 58 true) (.node 137 (sourceLit (List.headD (raw_ints% [178646329642903055698503375]) 0) 52 false) (.node 136 (sourceLit (List.headD (raw_ints% [3298510661822394144497142525]) 0) 53 false) (.node 135 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 51 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [3224137857024443204533963275]) 0) 53 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [29532859167389093751318525]) 0) 57 true) (.node 140 (sourceLit (List.headD (raw_ints% [49353859706821373430280125]) 0) 59 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [96879205924707411014784975]) 0) 58 false) .empty .empty)))

#time def treeG_J024_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [12361006610467553723106825]) 0) 64 true) (.node 145 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 60 false) (.node 144 (sourceLit (List.headD (raw_ints% [11903342734316464203898125]) 0) 61 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [98133175545357324895412439476475]) 0) 41 false) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [1403505247889339962341975]) 0) 64 false) (.node 148 (sourceLit (List.headD (raw_ints% [233342674345896556853555839875825]) 0) 40 true) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [333770227309175365601900091116775]) 0) 38 true) .empty .empty)))

#time def treeG_J024_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [8188440917992210722210975]) 0) 59 true) treeG_J024_part020 treeG_J024_part021)

#time def treeG_J024_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [646070535745262802825]) 0) 75 false) (.node 155 (sourceLit (List.headD (raw_ints% [330171408032452668825]) 0) 76 false) (.node 153 (sourceLit (List.headD (raw_ints% [171041679727314794882055]) 0) 67 false) (.node 152 (sourceLit (List.headD (raw_ints% [412492638028327674175622874095325]) 0) 37 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [2374288714108778208473719724831775]) 0) 34 true) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [2612021029621925086035]) 0) 73 false) (.node 156 (sourceLit (List.headD (raw_ints% [3667612843198543317956528256390015]) 0) 33 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [11797866061241429954130326975902635]) 0) 31 true) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [17902163705811923858862628125]) 0) 49 false) (.node 172 (sourceLit (List.headD (raw_ints% [44437899191256918922112591625]) 0) 48 false) (.node 171 (sourceLit (List.headD (raw_ints% [148982811909985358282904806475]) 0) 48 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [17894193610592745056491656075]) 0) 51 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [3457331908971476783812212375]) 0) 51 false) (.node 175 (sourceLit (List.headD (raw_ints% [34630341838065863967655693575]) 0) 50 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [8417420816810477941964549925]) 0) 52 false) .empty .empty))))

#time def treeG_J024_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [346331740732323250589685]) 0) 66 false) treeG_J024_part022 treeG_J024_part023)

#time def treeG_J024_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [27076745144644597306579170375]) 0) 50 false) treeG_J024_part019 treeG_J024_part024)

#time def treeG_J024_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [63758724926586014105639805375]) 0) 46 false) treeG_J024_part012 treeG_J024_part025)

#time def treeG_J024_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [123038552074946417053469325]) 0) 58 false) (.node 181 (sourceLit (List.headD (raw_ints% [125519248712014049929575825]) 0) 58 false) (.node 180 (sourceLit (List.headD (raw_ints% [53665939325513032310751075]) 0) 56 false) (.node 179 (sourceLit (List.headD (raw_ints% [2053064992642544501346693825]) 0) 54 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [22001612905886892449087475]) 0) 57 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [22509609096486857882831964596475]) 0) 39 true) (.node 184 (sourceLit (List.headD (raw_ints% [4415098447754633728975275]) 0) 59 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [34888868309304228636837225]) 0) 62 false) .empty .empty)))

#time def treeG_J024_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [4270131451204819760477353434317775]) 0) 35 true) (.node 189 (sourceLit (List.headD (raw_ints% [6635000237521924484365630406429025]) 0) 36 true) (.node 188 (sourceLit (List.headD (raw_ints% [51532168396047037763228775]) 0) 63 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [1776042048758873765634765]) 0) 64 false) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [20101929564738901085937307811509425]) 0) 32 true) (.node 192 (sourceLit (List.headD (raw_ints% [437990158823409274803435]) 0) 66 false) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [108094888156276608330315]) 0) 68 false) .empty .empty)))

#time def treeG_J024_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [2099090546697209058201992758685325]) 0) 38 false) treeG_J024_part027 treeG_J024_part028)

#time def treeG_J024_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [93192988552688298338377728075]) 0) 49 false) (.node 198 (sourceLit (List.headD (raw_ints% [3298375620449019294495]) 0) 73 false) (.node 197 (sourceLit (List.headD (raw_ints% [85337948759291866144767069490007565]) 0) 29 true) (.node 196 (sourceLit (List.headD (raw_ints% [6673868124366992241615]) 0) 72 false) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [135579012861673516656419335721898855]) 0) 28 true) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [44500029297726382919387453925]) 0) 50 false) (.node 213 (sourceLit (List.headD (raw_ints% [17388743161796185665174492375]) 0) 50 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [15064839646777581209533456875]) 0) 50 false) .empty .empty)))

#time def treeG_J024_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [1263403237333402526462211825]) 0) 55 false) (.node 218 (sourceLit (List.headD (raw_ints% [2596641479893017368715293325]) 0) 54 false) (.node 217 (sourceLit (List.headD (raw_ints% [409835697416071716014213625]) 0) 55 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [724210849926568442799518625]) 0) 54 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [154159291499320688844366675]) 0) 58 false) (.node 221 (sourceLit (List.headD (raw_ints% [2599962452903191439439675]) 0) 62 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [38378494741871313893509425]) 0) 58 false) .empty .empty)))

#time def treeG_J024_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [21436299190776287389667123475]) 0) 51 false) treeG_J024_part030 treeG_J024_part031)

#time def treeG_J024_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [28124919219115853440202520617207085]) 0) 31 true) treeG_J024_part029 treeG_J024_part032)

#time def treeG_J024_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [26467836821968188862785375]) 0) 65 true) (.node 227 (sourceLit (List.headD (raw_ints% [59610881530239336083050875]) 0) 63 false) (.node 226 (sourceLit (List.headD (raw_ints% [218775960187201507673656843549425]) 0) 40 true) (.node 225 (sourceLit (List.headD (raw_ints% [9345695194723957215766425]) 0) 61 true) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [2565775895389002171909104438436975]) 0) 39 false) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [1083378567294227264455395]) 0) 65 false) (.node 230 (sourceLit (List.headD (raw_ints% [5967459782903573753161830224195475]) 0) 37 true) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [3445146175148164412126107686127125]) 0) 36 true) .empty .empty)))

#time def treeG_J024_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [1015461773686266788895]) 0) 75 false) (.node 235 (sourceLit (List.headD (raw_ints% [65832947928122666720715]) 0) 69 false) (.node 234 (sourceLit (List.headD (raw_ints% [15353352136521344668989868361845875]) 0) 33 true) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [20789693532718766804289464104427055]) 0) 32 true) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [2006234548958493688845]) 0) 74 false) (.node 238 (sourceLit (List.headD (raw_ints% [61742216636809006236506415538202295]) 0) 30 true) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [57404601331502808225394415925]) 0) 50 false) .empty .empty)))

#time def treeG_J024_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [66737119774023619980345]) 0) 69 false) treeG_J024_part034 treeG_J024_part035)

#time def treeG_J024_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [144395984079917359675051725]) 0) 57 false) (.node 258 (sourceLit (List.headD (raw_ints% [2651966349731103146654352375]) 0) 53 false) (.node 256 (sourceLit (List.headD (raw_ints% [2901876934451526106430311125]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [54369716757386901871119214275]) 0) 50 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [6509439186982904723851286775]) 0) 53 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [616878971275542378178016475]) 0) 55 false) (.node 259 (sourceLit (List.headD (raw_ints% [3140217967143490236083892825]) 0) 54 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [761326242485346326743908525]) 0) 56 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [22117281752014092926301825]) 0) 63 true) (.node 264 (sourceLit (List.headD (raw_ints% [16981698147058340082267075]) 0) 60 false) (.node 263 (sourceLit (List.headD (raw_ints% [185280030923694960635264025]) 0) 58 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [180687678569735920146815823898875]) 0) 39 false) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [170753931456525709929330525]) 0) 63 false) (.node 267 (sourceLit (List.headD (raw_ints% [3849298228194821119591247507080725]) 0) 38 true) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [47687414563745959234911301421420625]) 0) 36 false) .empty .empty))))

#time def treeG_J024_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [51652808941372818801835341375]) 0) 49 false) treeG_J024_part036 treeG_J024_part037)

#time def treeG_J024_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [75425181137680560237876825]) 0) 59 false) treeG_J024_part033 treeG_J024_part038)

#time def treeG_J024_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [94701897873054903911716426277559915]) 0) 31 true) (.node 273 (sourceLit (List.headD (raw_ints% [90142748040002360102098138144558575]) 0) 32 true) (.node 272 (sourceLit (List.headD (raw_ints% [80673551058852248706495]) 0) 69 false) (.node 271 (sourceLit (List.headD (raw_ints% [43469546812023770264817288359246025]) 0) 35 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [158853590939817871591065]) 0) 68 false) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [247297147764208402723864356180825315]) 0) 29 true) (.node 276 (sourceLit (List.headD (raw_ints% [39137475430654697754255]) 0) 70 false) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [4825318569041115016665]) 0) 73 false) .empty .empty)))

#time def treeG_J024_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [2082205539619382674401883875]) 0) 54 false) (.node 295 (sourceLit (List.headD (raw_ints% [9146992323648809398075471125]) 0) 52 false) (.node 294 (sourceLit (List.headD (raw_ints% [70309173365279233531401377925]) 0) 50 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [2058338597913163405090755675]) 0) 55 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [963877749902267351927416875]) 0) 55 false) (.node 298 (sourceLit (List.headD (raw_ints% [1956398853544943677567996725]) 0) 55 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [234601841226260963702710125]) 0) 58 false) .empty .empty)))

#time def treeG_J024_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [358358720232798533235631988583719505]) 0) 28 true) treeG_J024_part040 treeG_J024_part041)

#time def treeG_J024_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [99865909689234356955118166862075]) 0) 42 false) (.node 304 (sourceLit (List.headD (raw_ints% [1716482027906475006209175]) 0) 65 false) (.node 303 (sourceLit (List.headD (raw_ints% [26504372334511511445385575]) 0) 60 false) (.node 302 (sourceLit (List.headD (raw_ints% [453007659486704949055175175]) 0) 57 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [6581848335445574324508375]) 0) 63 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [1603768530895955822875087986379425]) 0) 41 true) (.node 307 (sourceLit (List.headD (raw_ints% [103845445034267521935654525]) 0) 63 true) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [223689605100462087654901275]) 0) 64 false) .empty .empty)))

#time def treeG_J024_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [18697348975870253858277067445678175]) 0) 35 true) (.node 312 (sourceLit (List.headD (raw_ints% [10006100159218901463172795168279725]) 0) 38 true) (.node 311 (sourceLit (List.headD (raw_ints% [27182691975981464120307915]) 0) 67 true) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [94609982343680877432645]) 0) 69 false) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [18478051085084034276856740543283215]) 0) 34 true) (.node 315 (sourceLit (List.headD (raw_ints% [46510321505847602435175]) 0) 70 false) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [22890087051674429131935]) 0) 71 false) .empty .empty)))

#time def treeG_J024_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [13413718586662383247018282911404025]) 0) 39 false) treeG_J024_part043 treeG_J024_part044)

#time def treeG_J024_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [450481374289738126053877275]) 0) 56 false) treeG_J024_part042 treeG_J024_part045)

#time def treeG_J024_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [5676855808746427550953183125]) 0) 53 false) (.node 336 (sourceLit (List.headD (raw_ints% [97579927956207551431955625]) 0) 59 false) (.node 335 (sourceLit (List.headD (raw_ints% [86248629973171565191683541575]) 0) 50 false) (.node 319 (sourceLit (List.headD (raw_ints% [704771005020655331955]) 0) 76 false) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [9957269596322402516874758625]) 0) 53 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [1310876528528992325676817275]) 0) 55 false) (.node 339 (sourceLit (List.headD (raw_ints% [4685377447036284474188094075]) 0) 54 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [1115488487324741382877772475]) 0) 56 false) .empty .empty)))

#time def treeG_J024_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [35280978422905241575318575]) 0) 63 false) (.node 344 (sourceLit (List.headD (raw_ints% [36027046521964682808504075]) 0) 60 false) (.node 343 (sourceLit (List.headD (raw_ints% [133863814281504994209955575]) 0) 59 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [49694639368703751675365537355525]) 0) 39 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [378444821525060753800639575]) 0) 63 true) (.node 347 (sourceLit (List.headD (raw_ints% [7045007338250320542155028846667125]) 0) 38 false) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [150328600541087131898916932549703825]) 0) 36 true) .empty .empty)))

#time def treeG_J024_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [153042695104910383189412775]) 0) 58 false) treeG_J024_part047 treeG_J024_part048)

#time def treeG_J024_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [13239449913592199098605]) 0) 72 false) (.node 354 (sourceLit (List.headD (raw_ints% [219586338434905638139515]) 0) 68 false) (.node 352 (sourceLit (List.headD (raw_ints% [27344039078099168617720905]) 0) 68 true) (.node 351 (sourceLit (List.headD (raw_ints% [472708541585220034169402341524174825]) 0) 35 false) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [1190638072340017027184019643395246225]) 0) 32 true) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [53883167581040507116095]) 0) 70 false) (.node 355 (sourceLit (List.headD (raw_ints% [503613269354793219553149731984141685]) 0) 31 true) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [935298121681169790994967038589300445]) 0) 29 true) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [6044471889232515161738765175]) 0) 54 false) (.node 376 (sourceLit (List.headD (raw_ints% [53315212406560950710231450775]) 0) 51 false) (.node 359 (sourceLit (List.headD (raw_ints% [1126080728786396638663231536557264655]) 0) 28 true) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [4162909849577900617243276125]) 0) 54 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [2808562717226196764566413075]) 0) 55 false) (.node 379 (sourceLit (List.headD (raw_ints% [3749100308941892847098349375]) 0) 54 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [26887348569976693738216875]) 0) 61 false) .empty .empty))))

#time def treeG_J024_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [555026599537555804526578815]) 0) 64 false) treeG_J024_part049 treeG_J024_part050)

#time def treeG_J024_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [46388732781849849121839485160655755]) 0) 32 true) treeG_J024_part046 treeG_J024_part051)

#time def treeG_J024_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [107647389336631629216776265]) 0) 64 true) treeG_J024_part039 treeG_J024_part052)

#time def treeG_J024_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [626719229597470581459356625]) 0) 53 false) treeG_J024_part026 treeG_J024_part053)

#time def treeG_J024_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [174407401880078005086291675]) 0) 63 false) (.node 385 (sourceLit (List.headD (raw_ints% [9699653180182385510470575]) 0) 61 false) (.node 384 (sourceLit (List.headD (raw_ints% [78936389388497794011261975]) 0) 60 false) (.node 383 (sourceLit (List.headD (raw_ints% [100033950435887360298641625]) 0) 59 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [349768999388233676145107130092775]) 0) 40 true) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [301067213312761420727770425]) 0) 65 true) (.node 388 (sourceLit (List.headD (raw_ints% [13460081461834143833655380792184825]) 0) 39 false) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [203983474887736664886990064195319925]) 0) 37 true) .empty .empty)))

#time def treeG_J024_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [126565695423210433269165]) 0) 69 false) (.node 393 (sourceLit (List.headD (raw_ints% [13719324530221424747576775]) 0) 70 true) (.node 392 (sourceLit (List.headD (raw_ints% [512732942222095640022093522197293725]) 0) 36 false) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [1115848676436536011750911373612533525]) 0) 33 true) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [968533766542689937005]) 0) 76 false) (.node 396 (sourceLit (List.headD (raw_ints% [429701065014457082445722769811008825]) 0) 32 true) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [749743190553770394507609097946677425]) 0) 30 true) .empty .empty)))

#time def treeG_J024_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [663757367441481661007810475]) 0) 65 false) treeG_J024_part055 treeG_J024_part056)

#time def treeG_J024_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [211634278737681922711080075]) 0) 59 false) (.node 419 (sourceLit (List.headD (raw_ints% [7403566331428745849289436275]) 0) 54 false) (.node 418 (sourceLit (List.headD (raw_ints% [10974783589565174918019921375]) 0) 53 false) (.node 417 (sourceLit (List.headD (raw_ints% [33400673213916145676481933525]) 0) 52 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [609555945103225130355383025]) 0) 57 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [197376599637513222701343075]) 0) 59 false) (.node 422 (sourceLit (List.headD (raw_ints% [277154882014716716622057225]) 0) 58 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [32003451956961338745068775]) 0) 61 false) .empty .empty)))

#time def treeG_J024_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [365689903930433433237403025224661025]) 0) 36 false) (.node 427 (sourceLit (List.headD (raw_ints% [9843159333356189951315885887409325]) 0) 38 true) (.node 426 (sourceLit (List.headD (raw_ints% [60862303665628097640166575]) 0) 62 true) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [727259625285216763973222925]) 0) 63 false) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [2104576340687113353265322855086734225]) 0) 35 true) (.node 430 (sourceLit (List.headD (raw_ints% [1759295452788601487437660515]) 0) 64 true) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [773133523753878335478694095]) 0) 66 false) .empty .empty)))

#time def treeG_J024_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [281388574389030099737246609434875]) 0) 39 false) treeG_J024_part058 treeG_J024_part059)

#time def treeG_J024_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [7601281873426956442965]) 0) 73 false) treeG_J024_part057 treeG_J024_part060)

#time def treeG_J024_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [17753630615773878885555]) 0) 72 false) (.node 436 (sourceLit (List.headD (raw_ints% [36341263921084963076535]) 0) 71 false) (.node 435 (sourceLit (List.headD (raw_ints% [8423176142137494874454141256916126515]) 0) 31 true) (.node 434 (sourceLit (List.headD (raw_ints% [109974182580206303618753715]) 0) 68 true) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [5939918918550143528136597278386840755]) 0) 29 true) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [21311729435451115353004403175]) 0) 53 false) (.node 439 (sourceLit (List.headD (raw_ints% [4871864795643766517397641247016154745]) 0) 28 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [225802602519477564716299125]) 0) 59 false) .empty .empty)))

#time def treeG_J024_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [29610052562253857172520275]) 0) 62 false) (.node 462 (sourceLit (List.headD (raw_ints% [257648350515854736966510825]) 0) 59 false) (.node 461 (sourceLit (List.headD (raw_ints% [394457156543411580449648025]) 0) 58 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [11070058223676834770213475]) 0) 63 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [315578786888631887941176869763825]) 0) 41 false) (.node 465 (sourceLit (List.headD (raw_ints% [54307250733740291979666975]) 0) 61 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [117634852772853051363229125]) 0) 64 true) .empty .empty)))

#time def treeG_J024_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [143593862943829658897594475]) 0) 60 false) treeG_J024_part062 treeG_J024_part063)

#time def treeG_J024_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [3996737538561518896004209243552558845]) 0) 33 true) (.node 472 (sourceLit (List.headD (raw_ints% [1308654641454604496643708188642013975]) 0) 37 true) (.node 470 (sourceLit (List.headD (raw_ints% [284836689409085049062196544709990475]) 0) 38 false) (.node 469 (sourceLit (List.headD (raw_ints% [1329394051910739605428763775]) 0) 64 false) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [1211526410115041574222735495]) 0) 66 true) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [9356970449941806759820961863660589475]) 0) 34 false) (.node 473 (sourceLit (List.headD (raw_ints% [882888119995649733459308295]) 0) 67 false) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [3440648383613422314125715]) 0) 74 true) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [3477040776005592375928741725]) 0) 56 false) (.node 478 (sourceLit (List.headD (raw_ints% [2595087863998186566814494090220081665]) 0) 31 true) (.node 477 (sourceLit (List.headD (raw_ints% [20844723656401924084455]) 0) 72 false) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [5076174371173461221295]) 0) 74 false) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [362741173037636712879297825]) 0) 59 false) (.node 500 (sourceLit (List.headD (raw_ints% [1196864875052595387375009975]) 0) 57 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [511759431072106444277238825]) 0) 58 false) .empty .empty))))

#time def treeG_J024_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [11651620397595166892485633339797075]) 0) 40 true) treeG_J024_part064 treeG_J024_part065)

#time def treeG_J024_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [17598092223447077507891012353708645425]) 0) 32 false) treeG_J024_part061 treeG_J024_part066)

#time def treeG_J024_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [1197799036376628969426139425]) 0) 63 true) (.node 506 (sourceLit (List.headD (raw_ints% [57584777199684194809916775]) 0) 63 false) (.node 505 (sourceLit (List.headD (raw_ints% [215385673219256308879275308619525]) 0) 39 false) (.node 504 (sourceLit (List.headD (raw_ints% [56557013832453339416639025]) 0) 61 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [14892419923574300158374715803630525]) 0) 38 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [4418083556610080698295188065]) 0) 64 false) (.node 509 (sourceLit (List.headD (raw_ints% [738541756653478773796943292098167425]) 0) 36 true) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [6661963371232474138260467570446581825]) 0) 35 false) .empty .empty)))

#time def treeG_J024_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [55086715401735841989087975]) 0) 71 true) (.node 514 (sourceLit (List.headD (raw_ints% [496431151287928018539031005]) 0) 69 false) (.node 513 (sourceLit (List.headD (raw_ints% [101351989276541765293088336426797539825]) 0) 32 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [158134703341206403031589531075485558115]) 0) 31 false) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [23935816697029969283355]) 0) 72 false) (.node 517 (sourceLit (List.headD (raw_ints% [121955682315418461143998098515295042285]) 0) 29 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [36649541028327218551634264196505151895]) 0) 28 true) .empty .empty)))

#time def treeG_J024_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [3196186343983961483924165085]) 0) 66 true) treeG_J024_part068 treeG_J024_part069)

#time def treeG_J024_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [58806776931166386853611075]) 0) 61 false) (.node 543 (sourceLit (List.headD (raw_ints% [334638499493277087953823225]) 0) 59 false) (.node 542 (sourceLit (List.headD (raw_ints% [467833995559418688792084825]) 0) 59 false) (.node 541 (sourceLit (List.headD (raw_ints% [401203859254591903462680975]) 0) 59 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [199479891145180822541597475]) 0) 60 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [43804907493134311543286475]) 0) 66 false) (.node 546 (sourceLit (List.headD (raw_ints% [415771900558007467003078430908125]) 0) 40 true) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [38195660718764633943345982483224675]) 0) 39 false) .empty .empty)))

#time def treeG_J024_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [1019768615994902804345868345]) 0) 69 true) (.node 551 (sourceLit (List.headD (raw_ints% [6841136376840163846740659055]) 0) 65 false) (.node 550 (sourceLit (List.headD (raw_ints% [1308215135471648871921336381518148375]) 0) 37 true) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [9279272654141683131547883947730609775]) 0) 36 false) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [551481525425742775565042445]) 0) 70 false) (.node 554 (sourceLit (List.headD (raw_ints% [120065930176425378812730260154118718775]) 0) 33 true) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [166128178418329440823597949562590675805]) 0) 32 false) .empty .empty)))

#time def treeG_J024_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [78974784008980267964215725]) 0) 69 true) treeG_J024_part071 treeG_J024_part072)

#time def treeG_J024_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [2328289872454955104747985925]) 0) 57 false) treeG_J024_part070 treeG_J024_part073)

#time def treeG_J024_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [617747889724641126352491075]) 0) 59 false) (.node 581 (sourceLit (List.headD (raw_ints% [1602807526379681678989390275]) 0) 58 false) (.node 559 (sourceLit (List.headD (raw_ints% [13783467954683046840765]) 0) 73 false) (.node 558 (sourceLit (List.headD (raw_ints% [116765506587422088010369110334854878955]) 0) 30 true) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [1093056005946261169573485075]) 0) 58 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [621293632130540195830237147162875]) 0) 39 false) (.node 584 (sourceLit (List.headD (raw_ints% [221524471828370409120545175]) 0) 60 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [56362777468202002766222475]) 0) 62 true) .empty .empty)))

#time def treeG_J024_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [17127684455005665113631158622591768825]) 0) 35 true) (.node 589 (sourceLit (List.headD (raw_ints% [1349672328153712916890479011829762225]) 0) 36 false) (.node 588 (sourceLit (List.headD (raw_ints% [1898677556266777954118723025]) 0) 63 false) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [9472469733184817848004994465]) 0) 64 true) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [398288714209075625502620622754177052625]) 0) 32 false) (.node 592 (sourceLit (List.headD (raw_ints% [2509330680206031332666206035]) 0) 68 false) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [2535968383277733627230767695]) 0) 69 true) .empty .empty)))

#time def treeG_J024_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [18218595128038359894399343250895525]) 0) 38 true) treeG_J024_part075 treeG_J024_part076)

#time def treeG_J024_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [40679423724301005566733525]) 0) 63 false) (.node 599 (sourceLit (List.headD (raw_ints% [897474511671049485531318618482333879745]) 0) 28 true) (.node 597 (sourceLit (List.headD (raw_ints% [2780006537008689514321565291516745855165]) 0) 29 false) (.node 596 (sourceLit (List.headD (raw_ints% [151642060206869654388532605]) 0) 73 false) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [110239056067481517795628215]) 0) 72 true) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [379208753226492040809830925]) 0) 60 false) (.node 622 (sourceLit (List.headD (raw_ints% [567486765410131495098652725]) 0) 60 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [13070874955608134494090425]) 0) 65 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [4425870644554146528973626225]) 0) 64 false) (.node 627 (sourceLit (List.headD (raw_ints% [406802037413276495112514275]) 0) 63 true) (.node 626 (sourceLit (List.headD (raw_ints% [129633191586068457854164447258875]) 0) 43 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [7051781980850374229718165716765025]) 0) 42 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [1019600381876561355921603345]) 0) 69 true) (.node 630 (sourceLit (List.headD (raw_ints% [332235932953170223601476924168488825]) 0) 40 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [3300869638643418530647380321290297325]) 0) 39 true) .empty .empty))))

#time def treeG_J024_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [1118662144752609433533431612308435308315]) 0) 31 true) treeG_J024_part077 treeG_J024_part078)

#time def treeG_J024_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [27553780062696121956586215]) 0) 73 true) treeG_J024_part074 treeG_J024_part079)

#time def treeG_J024_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [317920101394196251231678575]) 0) 59 false) treeG_J024_part067 treeG_J024_part080)

#time def treeG_J024_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [362096505449513950291491800231450091765]) 0) 33 false) (.node 636 (sourceLit (List.headD (raw_ints% [160598790396367359294628695233878248015]) 0) 35 true) (.node 635 (sourceLit (List.headD (raw_ints% [771862477175869100698952535]) 0) 72 true) (.node 634 (sourceLit (List.headD (raw_ints% [64794330548187625539418860363536971425]) 0) 36 false) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [330837900476435430733651425]) 0) 73 false) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [1652199171915884854042119825]) 0) 59 false) (.node 639 (sourceLit (List.headD (raw_ints% [27563209883859050210617245]) 0) 75 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [536893034624613672499116675]) 0) 60 false) .empty .empty)))

#time def treeG_J024_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [2252300421702560818294404223575685425]) 0) 36 true) (.node 667 (sourceLit (List.headD (raw_ints% [26515119389546741197065867875463525]) 0) 38 false) (.node 666 (sourceLit (List.headD (raw_ints% [219080472365406025033156575]) 0) 62 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [2712281631093330944343751575]) 0) 63 true) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [38390784164008559424125681769375053625]) 0) 35 false) (.node 670 (sourceLit (List.headD (raw_ints% [18324211022293110905952246915]) 0) 64 false) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [6587732207712276756352619415]) 0) 68 true) .empty .empty)))

#time def treeG_J024_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [1133049507383284474285009122891525]) 0) 39 false) treeG_J024_part082 treeG_J024_part083)

#time def treeG_J024_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [1433590657973223240730233915]) 0) 72 false) (.node 676 (sourceLit (List.headD (raw_ints% [230876134345684688771871285]) 0) 75 true) (.node 675 (sourceLit (List.headD (raw_ints% [5265499299836617468056238675574801479515]) 0) 31 false) (.node 674 (sourceLit (List.headD (raw_ints% [9594166975679601901254916455]) 0) 69 false) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [23336651707743711504034038281453161601085]) 0) 29 true) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [1233931173336424550231226225]) 0) 60 false) (.node 679 (sourceLit (List.headD (raw_ints% [24071650860439942304186793833295139752705]) 0) 28 false) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [374175339727409650232182575]) 0) 61 false) .empty .empty)))

#time def treeG_J024_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [4910187885327922607106219616923596025]) 0) 37 true) (.node 708 (sourceLit (List.headD (raw_ints% [82929375236349735034811193609583725]) 0) 39 false) (.node 707 (sourceLit (List.headD (raw_ints% [312941254889341260072835425]) 0) 64 false) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [892269034455934684164672225]) 0) 67 true) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [64797741273155907669304724339697432225]) 0) 36 false) (.node 711 (sourceLit (List.headD (raw_ints% [34637817132318092600697900435]) 0) 65 false) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [10116831503913210893364693795]) 0) 69 true) .empty .empty)))

#time def treeG_J024_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [95983974694736811451693544820525]) 0) 40 false) treeG_J024_part085 treeG_J024_part086)

#time def treeG_J024_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [1243311341701790769348349985004493167825]) 0) 32 true) treeG_J024_part084 treeG_J024_part087)

#time def treeG_J024_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [1543843497508659441572702895]) 0) 73 false) (.node 717 (sourceLit (List.headD (raw_ints% [2177846975241912940908621705]) 0) 73 true) (.node 716 (sourceLit (List.headD (raw_ints% [6550289623007556342413268237445827463635]) 0) 32 false) (.node 715 (sourceLit (List.headD (raw_ints% [12681616884383078304050726595]) 0) 70 false) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [26233423751339823106365972683304762335205]) 0) 30 true) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [9693429210125226574939125]) 0) 66 false) (.node 745 (sourceLit (List.headD (raw_ints% [4042432948666374362448023957530875]) 0) 39 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [25747247591988846705452319516899325]) 0) 38 true) .empty .empty)))

#time def treeG_J024_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [60988745963167199626108378095]) 0) 66 false) (.node 750 (sourceLit (List.headD (raw_ints% [32600515573588065852587002515]) 0) 64 true) (.node 749 (sourceLit (List.headD (raw_ints% [3579170425484156578851383321329025025]) 0) 36 false) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [77672287246631940280975438704763821825]) 0) 35 true) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [29827829983506023687984304045]) 0) 69 true) (.node 753 (sourceLit (List.headD (raw_ints% [3316839062442779814766101163874810999025]) 0) 32 false) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [19358827188534951657365845618877112993315]) 0) 31 true) .empty .empty)))

#time def treeG_J024_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [3964046650650695984635093275]) 0) 63 false) treeG_J024_part089 treeG_J024_part090)

#time def treeG_J024_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [4244679155406039592978801469126310525]) 0) 38 false) (.node 786 (sourceLit (List.headD (raw_ints% [1973224486985818775498165206355175]) 0) 41 false) (.node 758 (sourceLit (List.headD (raw_ints% [10144978558940875004364720735]) 0) 72 true) (.node 757 (sourceLit (List.headD (raw_ints% [128141285675864612982646330080586401019245]) 0) 29 false) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [233939040871158527155114575299733238434345]) 0) 28 true) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [54338311414169290870131756563241525]) 0) 40 true) (.node 787 (sourceLit (List.headD (raw_ints% [235393821208339447473322425]) 0) 64 true) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [11102198926298173457952471075]) 0) 64 false) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [2539252524265035794214901015893799969125]) 0) 34 false) (.node 792 (sourceLit (List.headD (raw_ints% [71235014259893923975140081522230627025]) 0) 37 true) (.node 791 (sourceLit (List.headD (raw_ints% [33619166352953079226642451475]) 0) 66 true) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [101456071978820043199567153275]) 0) 67 false) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [12954558405771253999889556928161470228475]) 0) 33 true) (.node 795 (sourceLit (List.headD (raw_ints% [2656840429243068874502189415]) 0) 74 true) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [20731328984397859206217910565]) 0) 72 false) .empty .empty))))

#time def treeG_J024_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [16375635033914033324400667155]) 0) 71 false) treeG_J024_part091 treeG_J024_part092)

#time def treeG_J024_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [1761665986087291773663700867912788939225]) 0) 33 true) treeG_J024_part088 treeG_J024_part093)

#time def treeG_J024_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [54804913426184412768491944665]) 0) 64 false) (.node 828 (sourceLit (List.headD (raw_ints% [4905621935484053774528382975]) 0) 63 true) (.node 827 (sourceLit (List.headD (raw_ints% [57318839383761947113422962818582125]) 0) 38 false) (.node 799 (sourceLit (List.headD (raw_ints% [5844411028224767222968711815]) 0) 74 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [5317996390737573886695599531352753825]) 0) 36 true) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [128227078669073358079393281045]) 0) 66 true) (.node 831 (sourceLit (List.headD (raw_ints% [145587153733128573768636262210784790225]) 0) 35 false) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [7875879975075990949175066381297571128625]) 0) 32 true) .empty .empty)))

#time def treeG_J024_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [51607636527736593416800541865]) 0) 72 false) (.node 836 (sourceLit (List.headD (raw_ints% [58885081901803135316435697795]) 0) 71 true) (.node 835 (sourceLit (List.headD (raw_ints% [59986867576775524364804261873177912499315]) 0) 31 false) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [542687154660544740979112151781753448330445]) 0) 29 true) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [165995462212100528853686475945065175]) 0) 39 false) (.node 839 (sourceLit (List.headD (raw_ints% [1468936716288794015867212997410862545269945]) 0) 28 false) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [8003910430891113616240427025]) 0) 65 true) .empty .empty)))

#time def treeG_J024_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [161111731945832090575535761365]) 0) 68 false) treeG_J024_part095 treeG_J024_part096)

#time def treeG_J024_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [697061864087749177068124454545644611684895]) 0) 30 true) (.node 874 (sourceLit (List.headD (raw_ints% [12954385023606062537604868413085171066875]) 0) 33 true) (.node 872 (sourceLit (List.headD (raw_ints% [288057182252916421718916425255246044275]) 0) 36 false) (.node 871 (sourceLit (List.headD (raw_ints% [122043246132090571221776847615]) 0) 65 false) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [14355196915493337579935027145]) 0) 71 true) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [85895984388318032364583375729500852956265]) 0) 32 false) (.node 875 (sourceLit (List.headD (raw_ints% [246130625681610294559605822645]) 0) 69 false) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [9952051360775124315331701045]) 0) 75 true) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [256045991345525798349861881967627789225]) 0) 35 true) (.node 909 (sourceLit (List.headD (raw_ints% [7973923786131182348354583146473796625]) 0) 36 false) (.node 879 (sourceLit (List.headD (raw_ints% [63296458584186127862737965495]) 0) 73 false) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [86820555149748867233453652765]) 0) 64 true) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [17093709807169316444180391989465444545425]) 0) 32 false) (.node 912 (sourceLit (List.headD (raw_ints% [62567581200290982325292532165]) 0) 68 false) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [390794882593725491854496195685]) 0) 68 true) .empty .empty))))

#time def treeG_J024_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [13807354701549653072653202469605374875]) 0) 37 true) treeG_J024_part097 treeG_J024_part098)

#time def treeG_J024_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [5445319621920208855251946404019792875]) 0) 39 false) (.node 918 (sourceLit (List.headD (raw_ints% [210840458300138582462107758585]) 0) 72 true) (.node 917 (sourceLit (List.headD (raw_ints% [1917022904873633258812446163453767095630685]) 0) 29 false) (.node 916 (sourceLit (List.headD (raw_ints% [363900789485216565192477218235]) 0) 70 false) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [7045431628990787432412208633776019438749105]) 0) 28 true) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [136025793399610555017194576805718458375]) 0) 38 true) (.node 951 (sourceLit (List.headD (raw_ints% [52215950320459859613807625095]) 0) 67 true) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [119988368862264332645032640745]) 0) 69 false) .empty .empty)))

#time def treeG_J024_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [653521192240345608970142654499852926828895]) 0) 32 false) (.node 956 (sourceLit (List.headD (raw_ints% [62379483038485514257556646226840033497645]) 0) 34 true) (.node 955 (sourceLit (List.headD (raw_ints% [318462754137667893207051009165]) 0) 70 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [523133611257618554237784434955]) 0) 71 false) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [34505011362319467486381297820597407217425]) 0) 32 true) (.node 959 (sourceLit (List.headD (raw_ints% [17133557305270294395302857755]) 0) 77 true) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [870748358042782822434626758665]) 0) 68 false) .empty .empty)))

#time def treeG_J024_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [7512023707693844745446315100637653903075]) 0) 35 false) treeG_J024_part100 treeG_J024_part101)

#time def treeG_J024_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [47623747156817840807636364735]) 0) 76 true) (.node 999 (sourceLit (List.headD (raw_ints% [27958109780681846919456773577771313097273745]) 0) 28 false) (.node 997 (sourceLit (List.headD (raw_ints% [5909309819336706171296071521971529239479965]) 0) 29 true) (.node 996 (sourceLit (List.headD (raw_ints% [1000826297760552351606579236565]) 0) 70 true) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [183493517389439284174973048385]) 0) 74 false) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [1507673866318118608848728776995]) 0) 69 false) (.node 1034 (sourceLit (List.headD (raw_ints% [64553106193094846468166558223148022829725]) 0) 33 true) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [653524638565769113550151877305624339923295]) 0) 32 false) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [313562520509833870056913501695]) 0) 73 false) (.node 1039 (sourceLit (List.headD (raw_ints% [252027746610520461756184479405]) 0) 75 false) (.node 1038 (sourceLit (List.headD (raw_ints% [8523394588298088607176642139970940946795545]) 0) 30 true) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [920431555956585828265257758183448388570515]) 0) 31 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [564483494643982010636063966265]) 0) 74 true) (.node 1077 (sourceLit (List.headD (raw_ints% [16365704036389011988098501558861518678252685]) 0) 29 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [96145266487066555776869910697538840671638105]) 0) 28 true) .empty .empty))))

#time def treeG_J024_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [404006706411827056519925292398264205932715]) 0) 31 false) treeG_J024_part102 treeG_J024_part103)

#time def treeG_J024_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [163621947765624024665643209177859281034315]) 0) 31 true) treeG_J024_part099 treeG_J024_part104)

#time def treeG_J024_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [77187354713602218044506151381945581677225]) 0) 31 false) treeG_J024_part094 treeG_J024_part105)

#time def treeG_J024_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [882274824050233534253018595]) 0) 71 false) treeG_J024_part081 treeG_J024_part106)

#time def treeG_J024_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [165620206959509108455649325]) 0) 59 false) treeG_J024_part054 treeG_J024_part107)

#time def treeG_J024 : IntSourceTree := treeG_J024_part108

#time def treeG_J025_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 46 false) (.node 9 (sourceLit (List.headD (raw_ints% [36709568897125280848701706125]) 0) 45 false) (.node 8 (sourceLit (List.headD (raw_ints% [105474029003053654310276764995]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [426131545384758377103350214375]) 0) 42 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [51384004215308690323798295595]) 0) 47 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 12 (sourceLit (List.headD (raw_ints% [12556020949213902173475521175]) 0) 49 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [6150957917295493486827972225]) 0) 50 false) .empty .empty)))

#time def treeG_J025_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [175290639812734832210345625]) 0) 54 true) (.node 17 (sourceLit (List.headD (raw_ints% [199663544895009297545386125]) 0) 53 true) (.node 16 (sourceLit (List.headD (raw_ints% [377362950033722597219767635]) 0) 54 false) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [185492890699649796230439615]) 0) 55 false) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [36439445161336434614756775]) 0) 57 true) (.node 20 (sourceLit (List.headD (raw_ints% [45647218796209349081207445]) 0) 57 false) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [22490315801543813542894575]) 0) 58 false) .empty .empty)))

#time def treeG_J025_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 49 true) treeG_J025_part000 treeG_J025_part001)

#time def treeG_J025_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [63170320516126011558701641492731]) 0) 38 true) (.node 26 (sourceLit (List.headD (raw_ints% [74369460971466828938946568775931]) 0) 39 true) (.node 25 (sourceLit (List.headD (raw_ints% [21949234560470801666952675]) 0) 60 true) (.node 24 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 61 false) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 61 false) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [167885035151857835597011271793393]) 0) 36 true) (.node 29 (sourceLit (List.headD (raw_ints% [171159176571870727114875]) 0) 65 false) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [338304965555159657869815]) 0) 64 false) .empty .empty)))

#time def treeG_J025_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [2629411697058176999038329701422533]) 0) 31 true) (.node 34 (sourceLit (List.headD (raw_ints% [1600974799519356304430170992597585]) 0) 32 true) (.node 33 (sourceLit (List.headD (raw_ints% [10453955364240303936735]) 0) 69 false) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [5171212835721061235535]) 0) 70 false) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [8822766680676386243168000700791421]) 0) 29 true) (.node 37 (sourceLit (List.headD (raw_ints% [639797951524784037375]) 0) 73 false) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [633525367304305271925]) 0) 73 false) .empty .empty)))

#time def treeG_J025_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [251903970762962802452102245223655]) 0) 35 true) treeG_J025_part003 treeG_J025_part004)

#time def treeG_J025_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [64690449404680658507302575]) 0) 57 true) treeG_J025_part002 treeG_J025_part005)

#time def treeG_J025_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [12556020949213902173475521175]) 0) 50 false) (.node 51 (sourceLit (List.headD (raw_ints% [51384004215308690323798295595]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [36709568897125280848701706125]) 0) 46 false) (.node 49 (sourceLit (List.headD (raw_ints% [105474029003053654310276764995]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 47 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [6150957917295493486827972225]) 0) 51 false) (.node 54 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 50 true) .empty .empty)))

#time def treeG_J025_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [45647218796209349081207445]) 0) 58 false) (.node 59 (sourceLit (List.headD (raw_ints% [185492890699649796230439615]) 0) 56 false) (.node 58 (sourceLit (List.headD (raw_ints% [199663544895009297545386125]) 0) 54 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [175290639812734832210345625]) 0) 55 true) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [22490315801543813542894575]) 0) 59 false) (.node 62 (sourceLit (List.headD (raw_ints% [36439445161336434614756775]) 0) 58 true) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [64690449404680658507302575]) 0) 58 true) .empty .empty)))

#time def treeG_J025_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [377362950033722597219767635]) 0) 55 false) treeG_J025_part007 treeG_J025_part008)

#time def treeG_J025_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [251903970762962802452102245223655]) 0) 36 true) (.node 69 (sourceLit (List.headD (raw_ints% [63170320516126011558701641492731]) 0) 39 true) (.node 67 (sourceLit (List.headD (raw_ints% [74369460971466828938946568775931]) 0) 40 true) (.node 66 (sourceLit (List.headD (raw_ints% [21949234560470801666952675]) 0) 61 true) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 62 false) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [167885035151857835597011271793393]) 0) 37 true) (.node 70 (sourceLit (List.headD (raw_ints% [171159176571870727114875]) 0) 66 false) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [338304965555159657869815]) 0) 65 false) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [2629411697058176999038329701422533]) 0) 32 true) (.node 75 (sourceLit (List.headD (raw_ints% [1600974799519356304430170992597585]) 0) 33 true) (.node 74 (sourceLit (List.headD (raw_ints% [10453955364240303936735]) 0) 70 false) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [5171212835721061235535]) 0) 71 false) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [8822766680676386243168000700791421]) 0) 30 true) (.node 78 (sourceLit (List.headD (raw_ints% [639797951524784037375]) 0) 74 false) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [352712407590507815405946802125]) 0) 44 false) .empty .empty))))

#time def treeG_J025_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 62 false) treeG_J025_part009 treeG_J025_part010)

#time def treeG_J025_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [426131545384758377103350214375]) 0) 43 false) treeG_J025_part006 treeG_J025_part011)

#time def treeG_J025_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 49 false) (.node 93 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 48 false) (.node 92 (sourceLit (List.headD (raw_ints% [9706995816523697037580693605]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [63758724926586014105639805375]) 0) 46 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [18961083981132310860123070125]) 0) 50 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [620007849937134134483041125]) 0) 51 true) (.node 96 (sourceLit (List.headD (raw_ints% [4641506117160603097948901685]) 0) 52 false) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [569233009367795398209095655]) 0) 55 false) .empty .empty)))

#time def treeG_J025_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [81067331240665079951724525]) 0) 57 true) (.node 101 (sourceLit (List.headD (raw_ints% [102411749490061962980832075]) 0) 56 true) (.node 100 (sourceLit (List.headD (raw_ints% [69922835951720223574616085]) 0) 58 false) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [68804121790874884619520315]) 0) 58 false) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [20791980283739055173397225]) 0) 59 true) (.node 104 (sourceLit (List.headD (raw_ints% [16944758480615201984372625]) 0) 60 false) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [120888967478267147287656266721531]) 0) 39 false) .empty .empty)))

#time def treeG_J025_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [224036449977283762880426625]) 0) 54 true) treeG_J025_part013 treeG_J025_part014)

#time def treeG_J025_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [1091176310451899882323987929123489]) 0) 35 true) (.node 110 (sourceLit (List.headD (raw_ints% [842840093106158349342214992090303]) 0) 36 true) (.node 109 (sourceLit (List.headD (raw_ints% [2088141954176822870801475]) 0) 63 false) (.node 108 (sourceLit (List.headD (raw_ints% [531785367255608619952870908714717]) 0) 38 true) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [1030968447019806159049185]) 0) 64 false) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [6459952264895453374037100854559375]) 0) 32 true) (.node 113 (sourceLit (List.headD (raw_ints% [254673322641237226375935]) 0) 66 false) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [15736697892759546637935]) 0) 70 false) .empty .empty)))

#time def treeG_J025_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [279293269796257253708543389875]) 0) 45 false) (.node 118 (sourceLit (List.headD (raw_ints% [33247820472254445741445274521969107]) 0) 29 true) (.node 117 (sourceLit (List.headD (raw_ints% [3891616932671493160785]) 0) 72 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [1925666438794830877575]) 0) 73 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [13524578014730366628469049625]) 0) 49 false) (.node 131 (sourceLit (List.headD (raw_ints% [6761253098468120498309808675]) 0) 52 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [26271962316880885976847253245]) 0) 50 false) .empty .empty)))

#time def treeG_J025_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [10178386699096673436403038239358147]) 0) 31 true) treeG_J025_part016 treeG_J025_part017)

#time def treeG_J025_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [46671247781405909113166325]) 0) 61 true) treeG_J025_part015 treeG_J025_part018)

#time def treeG_J025_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [47967514833518200247332005]) 0) 59 false) (.node 137 (sourceLit (List.headD (raw_ints% [3132054317025712709069831145]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [1418662029517171324664585625]) 0) 51 false) (.node 135 (sourceLit (List.headD (raw_ints% [3202531515959204343323774475]) 0) 53 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [178646329642903055698503375]) 0) 52 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [94198453107231098068024725]) 0) 58 false) (.node 140 (sourceLit (List.headD (raw_ints% [6093226270568616333760125]) 0) 58 true) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [29532859167389093751318525]) 0) 57 true) .empty .empty)))

#time def treeG_J025_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [97629214224866988113301417748731]) 0) 41 false) (.node 145 (sourceLit (List.headD (raw_ints% [11399201159686590425850675]) 0) 61 false) (.node 144 (sourceLit (List.headD (raw_ints% [8188440917992210722210975]) 0) 59 true) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [23106488837202548160508125]) 0) 60 false) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [234307523369741304197084633610993]) 0) 40 true) (.node 148 (sourceLit (List.headD (raw_ints% [12361006610467553723106825]) 0) 64 true) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [1403505247889339962341975]) 0) 64 false) .empty .empty)))

#time def treeG_J025_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [11578451497332767769156435]) 0) 61 false) treeG_J025_part020 treeG_J025_part021)

#time def treeG_J025_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [12212526895789029749138636910588843]) 0) 31 true) (.node 155 (sourceLit (List.headD (raw_ints% [2429488732688048534803464930980895]) 0) 34 true) (.node 153 (sourceLit (List.headD (raw_ints% [419636169844468539935942841949917]) 0) 37 true) (.node 152 (sourceLit (List.headD (raw_ints% [346331740732323250589685]) 0) 66 false) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [171041679727314794882055]) 0) 67 false) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [3774487501019248218682354268967807]) 0) 33 true) (.node 156 (sourceLit (List.headD (raw_ints% [330171408032452668825]) 0) 76 false) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [2612021029621925086035]) 0) 73 false) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [33582840652629461093571436365]) 0) 50 false) (.node 172 (sourceLit (List.headD (raw_ints% [17338016577348784955658541095]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [53883636217417809900725896125]) 0) 48 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [44437899191256918922112591625]) 0) 48 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [8168619946676214275346196215]) 0) 52 false) (.node 175 (sourceLit (List.headD (raw_ints% [17902163705811923858862628125]) 0) 49 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [3457331908971476783812212375]) 0) 51 false) .empty .empty))))

#time def treeG_J025_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [337477528977150256872601860148455]) 0) 38 true) treeG_J025_part022 treeG_J025_part023)

#time def treeG_J025_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [9660412867664547591763606875]) 0) 49 false) treeG_J025_part019 treeG_J025_part024)

#time def treeG_J025_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [159564053790798618296755234395]) 0) 47 false) treeG_J025_part012 treeG_J025_part025)

#time def treeG_J025_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [22001612905886892449087475]) 0) 57 false) (.node 181 (sourceLit (List.headD (raw_ints% [53665939325513032310751075]) 0) 56 false) (.node 180 (sourceLit (List.headD (raw_ints% [121947223382352577414711935]) 0) 58 false) (.node 179 (sourceLit (List.headD (raw_ints% [626719229597470581459356625]) 0) 53 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [119592784423587311516529135]) 0) 58 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [4415098447754633728975275]) 0) 59 false) (.node 184 (sourceLit (List.headD (raw_ints% [29369047508715869092253115]) 0) 60 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [25265537436510937348641887611131]) 0) 39 true) .empty .empty)))

#time def treeG_J025_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [1776042048758873765634765]) 0) 64 false) (.node 189 (sourceLit (List.headD (raw_ints% [51532168396047037763228775]) 0) 63 true) (.node 188 (sourceLit (List.headD (raw_ints% [2093852794853480429765693592694413]) 0) 38 false) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [6655000654725563384964493283461473]) 0) 36 true) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [437990158823409274803435]) 0) 66 false) (.node 192 (sourceLit (List.headD (raw_ints% [4308464153182504227637641833251791]) 0) 35 true) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [20396762605150533181863241030235313]) 0) 32 true) .empty .empty)))

#time def treeG_J025_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [34888868309304228636837225]) 0) 62 false) treeG_J025_part027 treeG_J025_part028)

#time def treeG_J025_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [10089764550671860818064211625]) 0) 51 false) (.node 198 (sourceLit (List.headD (raw_ints% [87535779560361497256390062085000717]) 0) 29 true) (.node 197 (sourceLit (List.headD (raw_ints% [6673868124366992241615]) 0) 72 false) (.node 196 (sourceLit (List.headD (raw_ints% [28693433023912103120452400656336173]) 0) 31 true) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [3298375620449019294495]) 0) 73 false) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [17388743161796185665174492375]) 0) 50 false) (.node 213 (sourceLit (List.headD (raw_ints% [43080103992514253845786911135]) 0) 50 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [20772714588792643720276338465]) 0) 51 false) .empty .empty)))

#time def treeG_J025_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [724210849926568442799518625]) 0) 54 false) (.node 218 (sourceLit (List.headD (raw_ints% [409835697416071716014213625]) 0) 55 false) (.node 217 (sourceLit (List.headD (raw_ints% [2518282814825250783138182535]) 0) 54 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [1226108060953830708694327755]) 0) 55 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [2599962452903191439439675]) 0) 62 false) (.node 221 (sourceLit (List.headD (raw_ints% [149695993657474056761399145]) 0) 58 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [73278978434256240439903395]) 0) 59 false) .empty .empty)))

#time def treeG_J025_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [15064839646777581209533456875]) 0) 50 false) treeG_J025_part030 treeG_J025_part031)

#time def treeG_J025_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [108094888156276608330315]) 0) 68 false) treeG_J025_part029 treeG_J025_part032)

#time def treeG_J025_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [2562467841592963038159862859916399]) 0) 39 false) (.node 227 (sourceLit (List.headD (raw_ints% [220523965886244913575244723108593]) 0) 40 true) (.node 226 (sourceLit (List.headD (raw_ints% [9345695194723957215766425]) 0) 61 true) (.node 225 (sourceLit (List.headD (raw_ints% [2246230793628659833300305]) 0) 64 false) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [59610881530239336083050875]) 0) 63 false) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [5980045596771262871219289563164563]) 0) 37 true) (.node 230 (sourceLit (List.headD (raw_ints% [26467836821968188862785375]) 0) 65 true) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [1083378567294227264455395]) 0) 65 false) .empty .empty)))

#time def treeG_J025_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [21144458021873606683087692118400559]) 0) 32 true) (.node 235 (sourceLit (List.headD (raw_ints% [15537785139774436112256311168273523]) 0) 33 true) (.node 234 (sourceLit (List.headD (raw_ints% [66737119774023619980345]) 0) 69 false) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [65832947928122666720715]) 0) 69 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [63110725768783437758112788263823031]) 0) 30 true) (.node 238 (sourceLit (List.headD (raw_ints% [1015461773686266788895]) 0) 75 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [116998333619492854166914794375]) 0) 48 false) .empty .empty)))

#time def treeG_J025_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [3469191813493567147765756149351957]) 0) 36 true) treeG_J025_part034 treeG_J025_part035)

#time def treeG_J025_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [179799202891360802006269155]) 0) 58 false) (.node 258 (sourceLit (List.headD (raw_ints% [3042977331360379653624725235]) 0) 54 false) (.node 256 (sourceLit (List.headD (raw_ints% [6302047321058214722465071125]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [51652808941372818801835341375]) 0) 49 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [2901876934451526106430311125]) 0) 53 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [738319167424420399035480015]) 0) 56 false) (.node 259 (sourceLit (List.headD (raw_ints% [2651966349731103146654352375]) 0) 53 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [616878971275542378178016475]) 0) 55 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [176007534278748736603854727014651]) 0) 39 false) (.node 264 (sourceLit (List.headD (raw_ints% [5488741365692546418456285]) 0) 63 false) (.node 263 (sourceLit (List.headD (raw_ints% [144395984079917359675051725]) 0) 57 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [16981698147058340082267075]) 0) 60 false) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [3858044521943439738367651377563157]) 0) 38 true) (.node 267 (sourceLit (List.headD (raw_ints% [22117281752014092926301825]) 0) 63 true) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [170753931456525709929330525]) 0) 63 false) .empty .empty))))

#time def treeG_J025_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [52577367332399046598002385905]) 0) 50 false) treeG_J025_part036 treeG_J025_part037)

#time def treeG_J025_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [38378494741871313893509425]) 0) 58 false) treeG_J025_part033 treeG_J025_part038)

#time def treeG_J025_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [158853590939817871591065]) 0) 68 false) (.node 273 (sourceLit (List.headD (raw_ints% [80673551058852248706495]) 0) 69 false) (.node 272 (sourceLit (List.headD (raw_ints% [43531900620987598742116674672064713]) 0) 35 true) (.node 271 (sourceLit (List.headD (raw_ints% [107647389336631629216776265]) 0) 64 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [90617375426643615546640955749027311]) 0) 32 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [39137475430654697754255]) 0) 70 false) (.node 276 (sourceLit (List.headD (raw_ints% [95608848094283385777598088689852011]) 0) 31 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [250775548789616209673013011809408227]) 0) 29 true) .empty .empty)))

#time def treeG_J025_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [1891882253116481969663444295]) 0) 55 false) (.node 295 (sourceLit (List.headD (raw_ints% [1987790796475400179857877965]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [82220847295900482836565809625]) 0) 49 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [9146992323648809398075471125]) 0) 52 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [227108658800818618116299685]) 0) 58 false) (.node 298 (sourceLit (List.headD (raw_ints% [2082205539619382674401883875]) 0) 54 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [963877749902267351927416875]) 0) 55 false) .empty .empty)))

#time def treeG_J025_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [4825318569041115016665]) 0) 73 false) treeG_J025_part040 treeG_J025_part041)

#time def treeG_J025_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [6581848335445574324508375]) 0) 63 false) (.node 304 (sourceLit (List.headD (raw_ints% [26504372334511511445385575]) 0) 60 false) (.node 303 (sourceLit (List.headD (raw_ints% [1664378507142258774474465]) 0) 65 false) (.node 302 (sourceLit (List.headD (raw_ints% [450481374289738126053877275]) 0) 56 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [810627643015971646288995]) 0) 66 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [103845445034267521935654525]) 0) 63 true) (.node 307 (sourceLit (List.headD (raw_ints% [99132875041248412544774862530811]) 0) 42 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [1605128090884100694131878559369889]) 0) 41 true) .empty .empty)))

#time def treeG_J025_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [94609982343680877432645]) 0) 69 false) (.node 312 (sourceLit (List.headD (raw_ints% [27182691975981464120307915]) 0) 67 true) (.node 311 (sourceLit (List.headD (raw_ints% [13408632929246058716685397151322105]) 0) 39 false) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [10015677201873507898587729630678189]) 0) 38 true) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [46510321505847602435175]) 0) 70 false) (.node 315 (sourceLit (List.headD (raw_ints% [18769897571717294858596161145188447]) 0) 35 true) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [18616097518102444773627599142862863]) 0) 34 true) .empty .empty)))

#time def treeG_J025_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [223689605100462087654901275]) 0) 64 false) treeG_J025_part043 treeG_J025_part044)

#time def treeG_J025_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [438927180109472285512681725]) 0) 57 false) treeG_J025_part042 treeG_J025_part045)

#time def treeG_J025_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [4524551681105548225029051945]) 0) 54 false) (.node 336 (sourceLit (List.headD (raw_ints% [9600279050744986716397952595]) 0) 53 false) (.node 335 (sourceLit (List.headD (raw_ints% [112788885650428146871296277875]) 0) 49 false) (.node 319 (sourceLit (List.headD (raw_ints% [46916205755208192978725055886396299]) 0) 32 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [97579927956207551431955625]) 0) 59 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [1078550102982128545894917465]) 0) 56 false) (.node 339 (sourceLit (List.headD (raw_ints% [5676855808746427550953183125]) 0) 53 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [1310876528528992325676817275]) 0) 55 false) .empty .empty)))

#time def treeG_J025_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [41593666720448827550802353592069]) 0) 39 false) (.node 344 (sourceLit (List.headD (raw_ints% [7826286691445523777339435]) 0) 63 false) (.node 343 (sourceLit (List.headD (raw_ints% [153042695104910383189412775]) 0) 58 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [36027046521964682808504075]) 0) 60 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [7030296523263388939800446978549109]) 0) 38 false) (.node 347 (sourceLit (List.headD (raw_ints% [35280978422905241575318575]) 0) 63 false) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [378444821525060753800639575]) 0) 63 true) .empty .empty)))

#time def treeG_J025_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [129563988609055741753206285]) 0) 59 false) treeG_J025_part047 treeG_J025_part048)

#time def treeG_J025_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [940654692368940255839153333333815005]) 0) 29 true) (.node 354 (sourceLit (List.headD (raw_ints% [1191389306413165395472588436977780881]) 0) 32 true) (.node 352 (sourceLit (List.headD (raw_ints% [472608154356861477676049383514372073]) 0) 35 false) (.node 351 (sourceLit (List.headD (raw_ints% [555026599537555804526578815]) 0) 64 false) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [27344039078099168617720905]) 0) 68 true) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [505027874200670049697479067956178293]) 0) 31 true) (.node 355 (sourceLit (List.headD (raw_ints% [219586338434905638139515]) 0) 68 false) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [53883167581040507116095]) 0) 70 false) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [4162909849577900617243276125]) 0) 54 false) (.node 376 (sourceLit (List.headD (raw_ints% [76200916355832909278994393375]) 0) 50 false) (.node 359 (sourceLit (List.headD (raw_ints% [13239449913592199098605]) 0) 72 false) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [5816514544512022777071064005]) 0) 54 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [3749100308941892847098349375]) 0) 54 false) (.node 379 (sourceLit (List.headD (raw_ints% [2707682410698999280098654465]) 0) 55 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [159905730718164065095558935]) 0) 59 false) .empty .empty))))

#time def treeG_J025_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [150382683936795416419962526841796753]) 0) 36 true) treeG_J025_part049 treeG_J025_part050)

#time def treeG_J025_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [22890087051674429131935]) 0) 71 false) treeG_J025_part046 treeG_J025_part051)

#time def treeG_J025_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [47654486120212971995522299042123857]) 0) 36 false) treeG_J025_part039 treeG_J025_part052)

#time def treeG_J025_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [1993588298290121912651639835]) 0) 54 false) treeG_J025_part026 treeG_J025_part053)

#time def treeG_J025_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [354937833444544822628297096531175]) 0) 40 true) (.node 385 (sourceLit (List.headD (raw_ints% [4583776119381637192183455]) 0) 64 false) (.node 384 (sourceLit (List.headD (raw_ints% [100033950435887360298641625]) 0) 59 false) (.node 383 (sourceLit (List.headD (raw_ints% [76303876380503460970023405]) 0) 60 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [9699653180182385510470575]) 0) 61 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [13450808886799791716327961216028665]) 0) 39 false) (.node 388 (sourceLit (List.headD (raw_ints% [174407401880078005086291675]) 0) 63 false) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [301067213312761420727770425]) 0) 65 true) .empty .empty)))

#time def treeG_J025_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [1116309716126296216038203792397027093]) 0) 33 true) (.node 393 (sourceLit (List.headD (raw_ints% [512670863164355509270400302037084829]) 0) 36 false) (.node 392 (sourceLit (List.headD (raw_ints% [663757367441481661007810475]) 0) 65 false) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [13719324530221424747576775]) 0) 70 true) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [430563484128260270602968671384726841]) 0) 32 true) (.node 396 (sourceLit (List.headD (raw_ints% [126565695423210433269165]) 0) 69 false) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [968533766542689937005]) 0) 76 false) .empty .empty)))

#time def treeG_J025_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [204017215653779651286704115447085173]) 0) 37 true) treeG_J025_part055 treeG_J025_part056)

#time def treeG_J025_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [609555945103225130355383025]) 0) 57 false) (.node 419 (sourceLit (List.headD (raw_ints% [10974783589565174918019921375]) 0) 53 false) (.node 418 (sourceLit (List.headD (raw_ints% [7108477407918497329113076065]) 0) 54 false) (.node 417 (sourceLit (List.headD (raw_ints% [51220454799043776112413753375]) 0) 51 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [203641538464608841775467125]) 0) 59 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [277154882014716716622057225]) 0) 58 false) (.node 422 (sourceLit (List.headD (raw_ints% [190247472827272388437911585]) 0) 59 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [44998729614721365860665665]) 0) 61 false) .empty .empty)))

#time def treeG_J025_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [727259625285216763973222925]) 0) 63 false) (.node 427 (sourceLit (List.headD (raw_ints% [60862303665628097640166575]) 0) 62 true) (.node 426 (sourceLit (List.headD (raw_ints% [266018341481581226876778991053051]) 0) 39 false) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [9869799190819747520826823750798509]) 0) 38 true) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [1759295452788601487437660515]) 0) 64 true) (.node 430 (sourceLit (List.headD (raw_ints% [365595626125592083881209906298255393]) 0) 36 false) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [2104745879587098687969682307091053457]) 0) 35 true) .empty .empty)))

#time def treeG_J025_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [32003451956961338745068775]) 0) 61 false) treeG_J025_part058 treeG_J025_part059)

#time def treeG_J025_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [752989869348107483924253109788229809]) 0) 30 true) treeG_J025_part057 treeG_J025_part060)

#time def treeG_J025_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [5948361053683224073808345408821814451]) 0) 29 true) (.node 436 (sourceLit (List.headD (raw_ints% [8425449854809699678608151271220038451]) 0) 31 true) (.node 435 (sourceLit (List.headD (raw_ints% [109974182580206303618753715]) 0) 68 true) (.node 434 (sourceLit (List.headD (raw_ints% [17596856927672541692125398102164495409]) 0) 32 false) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [36341263921084963076535]) 0) 71 false) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [34568815400732173643440648875]) 0) 52 false) (.node 439 (sourceLit (List.headD (raw_ints% [17753630615773878885555]) 0) 72 false) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [137524843663109314031700675]) 0) 60 false) .empty .empty)))

#time def treeG_J025_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [11070058223676834770213475]) 0) 63 false) (.node 462 (sourceLit (List.headD (raw_ints% [394457156543411580449648025]) 0) 58 false) (.node 461 (sourceLit (List.headD (raw_ints% [247377346211053618455375315]) 0) 59 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [28485899111692231866972045]) 0) 62 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [54307250733740291979666975]) 0) 61 false) (.node 465 (sourceLit (List.headD (raw_ints% [26663625137194817091931845]) 0) 62 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [310478087463063024752538043792113]) 0) 41 false) .empty .empty)))

#time def treeG_J025_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [225802602519477564716299125]) 0) 59 false) treeG_J025_part062 treeG_J025_part063)

#time def treeG_J025_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [3440648383613422314125715]) 0) 74 true) (.node 472 (sourceLit (List.headD (raw_ints% [1211526410115041574222735495]) 0) 66 true) (.node 470 (sourceLit (List.headD (raw_ints% [1329394051910739605428763775]) 0) 64 false) (.node 469 (sourceLit (List.headD (raw_ints% [11660304038809769618577392483413587]) 0) 40 true) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [284806420889685867583957010872670283]) 0) 38 false) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [882888119995649733459308295]) 0) 67 false) (.node 473 (sourceLit (List.headD (raw_ints% [1308708371375727098620041304564069143]) 0) 37 true) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [9356583321899418954081800947280761251]) 0) 34 false) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [5898507952791749681355181875]) 0) 55 false) (.node 478 (sourceLit (List.headD (raw_ints% [20844723656401924084455]) 0) 72 false) (.node 477 (sourceLit (List.headD (raw_ints% [3997443185340719704002591299917655805]) 0) 33 true) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [2597685592167558294942046149516792321]) 0) 31 true) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [1196864875052595387375009975]) 0) 57 false) (.node 500 (sourceLit (List.headD (raw_ints% [346457836187828414351335575]) 0) 59 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [304507219594834848472839045]) 0) 59 false) .empty .empty))))

#time def treeG_J025_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [117634852772853051363229125]) 0) 64 true) treeG_J025_part064 treeG_J025_part065)

#time def treeG_J025_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [773133523753878335478694095]) 0) 66 false) treeG_J025_part061 treeG_J025_part066)

#time def treeG_J025_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [14837448590228755916867432451472317]) 0) 38 false) (.node 506 (sourceLit (List.headD (raw_ints% [181323056788165853555053429790469]) 0) 39 false) (.node 505 (sourceLit (List.headD (raw_ints% [56557013832453339416639025]) 0) 61 false) (.node 504 (sourceLit (List.headD (raw_ints% [68944866832047561607222515]) 0) 61 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [57584777199684194809916775]) 0) 63 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [738725355367504711675686465767490177]) 0) 36 true) (.node 509 (sourceLit (List.headD (raw_ints% [1197799036376628969426139425]) 0) 63 true) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [4418083556610080698295188065]) 0) 64 false) .empty .empty)))

#time def treeG_J025_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [158130783005200402943916966427712218467]) 0) 31 false) (.node 514 (sourceLit (List.headD (raw_ints% [101354192695719076003808041594264920561]) 0) 32 true) (.node 513 (sourceLit (List.headD (raw_ints% [3196186343983961483924165085]) 0) 66 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [496431151287928018539031005]) 0) 69 false) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [121969820877219806454274576188543171309]) 0) 29 true) (.node 517 (sourceLit (List.headD (raw_ints% [55086715401735841989087975]) 0) 71 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [23935816697029969283355]) 0) 72 false) .empty .empty)))

#time def treeG_J025_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [6661648613822072569312994481053777985]) 0) 35 false) treeG_J025_part068 treeG_J025_part069)

#time def treeG_J025_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [21140620847426372257645335]) 0) 63 false) (.node 543 (sourceLit (List.headD (raw_ints% [190563623148065921004950865]) 0) 60 false) (.node 542 (sourceLit (List.headD (raw_ints% [401203859254591903462680975]) 0) 59 false) (.node 541 (sourceLit (List.headD (raw_ints% [445538326164603210247295835]) 0) 59 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [334638499493277087953823225]) 0) 59 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [439633118137960195950022657793757]) 0) 40 true) (.node 546 (sourceLit (List.headD (raw_ints% [58806776931166386853611075]) 0) 61 false) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [43804907493134311543286475]) 0) 66 false) .empty .empty)))

#time def treeG_J025_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [9279065356573526766553077090181916271]) 0) 36 false) (.node 551 (sourceLit (List.headD (raw_ints% [1308338197146876446843600487512830743]) 0) 37 true) (.node 550 (sourceLit (List.headD (raw_ints% [78974784008980267964215725]) 0) 69 true) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [6841136376840163846740659055]) 0) 65 false) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [120067359339517913911971643488826443063]) 0) 33 true) (.node 554 (sourceLit (List.headD (raw_ints% [1019768615994902804345868345]) 0) 69 true) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [551481525425742775565042445]) 0) 70 false) .empty .empty)))

#time def treeG_J025_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [38158056667848295154022217418299491]) 0) 39 false) treeG_J025_part071 treeG_J025_part072)

#time def treeG_J025_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [4092087132635929163624788875]) 0) 56 false) treeG_J025_part070 treeG_J025_part073)

#time def treeG_J025_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [1093056005946261169573485075]) 0) 58 false) (.node 581 (sourceLit (List.headD (raw_ints% [723805564395833444062444725]) 0) 59 false) (.node 559 (sourceLit (List.headD (raw_ints% [116774449692884689864390483889509586667]) 0) 30 true) (.node 558 (sourceLit (List.headD (raw_ints% [27553780062696121956586215]) 0) 73 true) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [586569432734371572021752625]) 0) 59 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [221524471828370409120545175]) 0) 60 false) (.node 584 (sourceLit (List.headD (raw_ints% [60809378158009179698864175]) 0) 62 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [528038467874584729370793443584251]) 0) 39 false) .empty .empty)))

#time def treeG_J025_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [9472469733184817848004994465]) 0) 64 true) (.node 589 (sourceLit (List.headD (raw_ints% [1898677556266777954118723025]) 0) 63 false) (.node 588 (sourceLit (List.headD (raw_ints% [18354513535332437484467613713822373]) 0) 38 true) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [1349254262053077434140041944460282033]) 0) 36 false) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [2509330680206031332666206035]) 0) 68 false) (.node 592 (sourceLit (List.headD (raw_ints% [17128354190997084144061798381156423929]) 0) 35 true) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [398284284106071932533506508480086241233]) 0) 32 false) .empty .empty)))

#time def treeG_J025_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [56362777468202002766222475]) 0) 62 true) treeG_J025_part075 treeG_J025_part076)

#time def treeG_J025_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [4958594663822850930152355]) 0) 66 false) (.node 599 (sourceLit (List.headD (raw_ints% [110239056067481517795628215]) 0) 72 true) (.node 597 (sourceLit (List.headD (raw_ints% [151642060206869654388532605]) 0) 73 false) (.node 596 (sourceLit (List.headD (raw_ints% [1118669657721343714239690114338323762971]) 0) 31 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [2779980530891329284085028960629303652541]) 0) 29 false) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [12375181549572051594275055]) 0) 65 false) (.node 622 (sourceLit (List.headD (raw_ints% [1046407269537074984662208475]) 0) 59 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [379208753226492040809830925]) 0) 60 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [7064071275397591579811228891515233]) 0) 42 true) (.node 627 (sourceLit (List.headD (raw_ints% [120958948251568115665102012672251]) 0) 43 false) (.node 626 (sourceLit (List.headD (raw_ints% [40679423724301005566733525]) 0) 63 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [406802037413276495112514275]) 0) 63 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [332199057399994235122955303996639097]) 0) 40 false) (.node 630 (sourceLit (List.headD (raw_ints% [4425870644554146528973626225]) 0) 64 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [1019600381876561355921603345]) 0) 69 true) .empty .empty))))

#time def treeG_J025_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [2535968383277733627230767695]) 0) 69 true) treeG_J025_part077 treeG_J025_part078)

#time def treeG_J025_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [166125669375881842351922149027547530077]) 0) 32 false) treeG_J025_part074 treeG_J025_part079)

#time def treeG_J025_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [511759431072106444277238825]) 0) 58 false) treeG_J025_part067 treeG_J025_part080)

#time def treeG_J025_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [330837900476435430733651425]) 0) 73 false) (.node 636 (sourceLit (List.headD (raw_ints% [771862477175869100698952535]) 0) 72 true) (.node 635 (sourceLit (List.headD (raw_ints% [64793955430698730805684768996114085537]) 0) 36 false) (.node 634 (sourceLit (List.headD (raw_ints% [882274824050233534253018595]) 0) 71 false) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [160599415887153194573951532920733911631]) 0) 35 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [3092573072202038769075348825]) 0) 58 false) (.node 639 (sourceLit (List.headD (raw_ints% [362094372573026746743677430564851654901]) 0) 33 false) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [137193526635143645809536705]) 0) 62 false) .empty .empty)))

#time def treeG_J025_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [2712281631093330944343751575]) 0) 63 true) (.node 667 (sourceLit (List.headD (raw_ints% [219080472365406025033156575]) 0) 62 false) (.node 666 (sourceLit (List.headD (raw_ints% [803024151827868963284678120314629]) 0) 39 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [26095886223432796887034142524846437]) 0) 38 false) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [18324211022293110905952246915]) 0) 64 false) (.node 670 (sourceLit (List.headD (raw_ints% [2253455385303969156355879242574231857]) 0) 36 true) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [38389093864596715191930937836941326137]) 0) 35 false) .empty .empty)))

#time def treeG_J025_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [536893034624613672499116675]) 0) 60 false) treeG_J025_part082 treeG_J025_part083)

#time def treeG_J025_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [23336705764446938189550825174483244341309]) 0) 29 true) (.node 676 (sourceLit (List.headD (raw_ints% [5265482805286062485803515330089625237339]) 0) 31 false) (.node 675 (sourceLit (List.headD (raw_ints% [9594166975679601901254916455]) 0) 69 false) (.node 674 (sourceLit (List.headD (raw_ints% [1243321709628331481673182523562913127633]) 0) 32 true) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [230876134345684688771871285]) 0) 75 true) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [2334155565749054687455686975]) 0) 59 false) (.node 679 (sourceLit (List.headD (raw_ints% [1433590657973223240730233915]) 0) 72 false) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [97524769324560838368317865]) 0) 63 false) .empty .empty)))

#time def treeG_J025_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [892269034455934684164672225]) 0) 67 true) (.node 708 (sourceLit (List.headD (raw_ints% [312941254889341260072835425]) 0) 64 false) (.node 707 (sourceLit (List.headD (raw_ints% [164647434184675962036137981063379]) 0) 40 true) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [82608456426613529525523973656968301]) 0) 39 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [34637817132318092600697900435]) 0) 65 false) (.node 711 (sourceLit (List.headD (raw_ints% [4911047844503923037339521674547344633]) 0) 37 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [64796513412167326102545813308279666337]) 0) 36 false) .empty .empty)))

#time def treeG_J025_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [374175339727409650232182575]) 0) 61 false) treeG_J025_part085 treeG_J025_part086)

#time def treeG_J025_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [6587732207712276756352619415]) 0) 68 true) treeG_J025_part084 treeG_J025_part087)

#time def treeG_J025_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [26233460745031152163500244619002057580517]) 0) 30 true) (.node 717 (sourceLit (List.headD (raw_ints% [6550278132383288042395127593455496530387]) 0) 32 false) (.node 716 (sourceLit (List.headD (raw_ints% [12681616884383078304050726595]) 0) 70 false) (.node 715 (sourceLit (List.headD (raw_ints% [1761673353073921328118660675531825811929]) 0) 33 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [2177846975241912940908621705]) 0) 73 true) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [2469364088788793617608034635213051]) 0) 39 false) (.node 745 (sourceLit (List.headD (raw_ints% [449315632781110253739142575]) 0) 62 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [9693429210125226574939125]) 0) 66 false) .empty .empty)))

#time def treeG_J025_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [77677476620628099490647111233320083201]) 0) 35 true) (.node 750 (sourceLit (List.headD (raw_ints% [3575190688129785628764262821085724673]) 0) 36 false) (.node 749 (sourceLit (List.headD (raw_ints% [3964046650650695984635093275]) 0) 63 false) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [32600515573588065852587002515]) 0) 64 true) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [3316810138817685916954648549427862450417]) 0) 32 false) (.node 753 (sourceLit (List.headD (raw_ints% [60988745963167199626108378095]) 0) 66 false) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [29827829983506023687984304045]) 0) 69 true) .empty .empty)))

#time def treeG_J025_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [27413065696910204583323246373353469]) 0) 38 true) treeG_J025_part089 treeG_J025_part090)

#time def treeG_J025_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [11102198926298173457952471075]) 0) 64 false) (.node 786 (sourceLit (List.headD (raw_ints% [1423087191397031364724387725]) 0) 61 false) (.node 758 (sourceLit (List.headD (raw_ints% [128141155882579546867872866669771188827501]) 0) 29 false) (.node 757 (sourceLit (List.headD (raw_ints% [16375635033914033324400667155]) 0) 71 false) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [10144978558940875004364720735]) 0) 72 true) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [235393821208339447473322425]) 0) 64 true) (.node 787 (sourceLit (List.headD (raw_ints% [1317005761486734789822086308138215]) 0) 41 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [55010761061761867054423610015160885]) 0) 40 true) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [101456071978820043199567153275]) 0) 67 false) (.node 792 (sourceLit (List.headD (raw_ints% [33619166352953079226642451475]) 0) 66 true) (.node 791 (sourceLit (List.headD (raw_ints% [4243119266316854333051892247816534653]) 0) 38 false) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [71236995016397712796596462270799874769]) 0) 37 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [2656840429243068874502189415]) 0) 74 true) (.node 795 (sourceLit (List.headD (raw_ints% [2539241745945803622536654612479844131173]) 0) 34 false) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [12954573881130360576573964163899864131579]) 0) 33 true) .empty .empty))))

#time def treeG_J025_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [19358869629877433110752800734344231732771]) 0) 31 true) treeG_J025_part091 treeG_J025_part092)

#time def treeG_J025_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [10116831503913210893364693795]) 0) 69 true) treeG_J025_part088 treeG_J025_part093)

#time def treeG_J025_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [5335535042106165374505818341570872993]) 0) 36 true) (.node 828 (sourceLit (List.headD (raw_ints% [48485157880697961220476627303564909]) 0) 38 false) (.node 827 (sourceLit (List.headD (raw_ints% [1267992324035027739525361725]) 0) 62 false) (.node 799 (sourceLit (List.headD (raw_ints% [77187308313805349515686555644386623204009]) 0) 31 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [4905621935484053774528382975]) 0) 63 true) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [145567384881697768819477387198384637649]) 0) 35 false) (.node 831 (sourceLit (List.headD (raw_ints% [54804913426184412768491944665]) 0) 64 false) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [128227078669073358079393281045]) 0) 66 true) .empty .empty)))

#time def treeG_J025_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [542687520078751085318239719914566841038029]) 0) 29 true) (.node 836 (sourceLit (List.headD (raw_ints% [59986737565010291071339274534021737831539]) 0) 31 false) (.node 835 (sourceLit (List.headD (raw_ints% [161111731945832090575535761365]) 0) 68 false) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [58885081901803135316435697795]) 0) 71 true) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [1738779966451706634472006575]) 0) 63 false) (.node 839 (sourceLit (List.headD (raw_ints% [51607636527736593416800541865]) 0) 72 false) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [158506680004221695329323847333886679]) 0) 39 false) .empty .empty)))

#time def treeG_J025_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [7875977819867139535936822134759054435633]) 0) 32 true) treeG_J025_part095 treeG_J025_part096)

#time def treeG_J025_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [9952051360775124315331701045]) 0) 75 true) (.node 874 (sourceLit (List.headD (raw_ints% [14355196915493337579935027145]) 0) 71 true) (.node 872 (sourceLit (List.headD (raw_ints% [122043246132090571221776847615]) 0) 65 false) (.node 871 (sourceLit (List.headD (raw_ints% [13821773574739874040609602837203942299]) 0) 37 true) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [288041374914493194412670311739984387187]) 0) 36 false) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [246130625681610294559605822645]) 0) 69 false) (.node 875 (sourceLit (List.headD (raw_ints% [12954461311758746781010131359718742697979]) 0) 33 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [85895885327271012224487202861821466094697]) 0) 32 false) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [86820555149748867233453652765]) 0) 64 true) (.node 909 (sourceLit (List.headD (raw_ints% [8383181868387467043472396125]) 0) 63 false) (.node 879 (sourceLit (List.headD (raw_ints% [697062136706361784349612831203340087446047]) 0) 30 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [7871641922173712499774999898913059857]) 0) 36 false) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [62567581200290982325292532165]) 0) 68 false) (.node 912 (sourceLit (List.headD (raw_ints% [256141573479616761144354209896016176041]) 0) 35 true) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [17093301817130921757142272110438554825617]) 0) 32 false) .empty .empty))))

#time def treeG_J025_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [8003910430891113616240427025]) 0) 65 true) treeG_J025_part097 treeG_J025_part098)

#time def treeG_J025_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [24391002730169694275953250175]) 0) 64 false) (.node 918 (sourceLit (List.headD (raw_ints% [1917021685315087280910034965703710298553181]) 0) 29 false) (.node 917 (sourceLit (List.headD (raw_ints% [363900789485216565192477218235]) 0) 70 false) (.node 916 (sourceLit (List.headD (raw_ints% [163622428059080265319420325411771679415371]) 0) 31 true) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [210840458300138582462107758585]) 0) 72 true) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [52215950320459859613807625095]) 0) 67 true) (.node 951 (sourceLit (List.headD (raw_ints% [5423353874228396635096150684029250539]) 0) 39 false) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [136045737098527488889256130409000140807]) 0) 38 true) .empty .empty)))

#time def treeG_J025_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [523133611257618554237784434955]) 0) 71 false) (.node 956 (sourceLit (List.headD (raw_ints% [318462754137667893207051009165]) 0) 70 true) (.node 955 (sourceLit (List.headD (raw_ints% [7511940782222417134538100867539324380899]) 0) 35 false) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [62379578346587819385976882068398286377517]) 0) 34 true) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [28695882880187710484775039315]) 0) 70 true) (.node 959 (sourceLit (List.headD (raw_ints% [653520955505362266314911949226762596499807]) 0) 32 false) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [34507156165742440334967056802790572848913]) 0) 32 true) .empty .empty)))

#time def treeG_J025_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [119988368862264332645032640745]) 0) 69 false) treeG_J025_part100 treeG_J025_part101)

#time def treeG_J025_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [653522846476548891168547081446623205114207]) 0) 32 false) (.node 999 (sourceLit (List.headD (raw_ints% [183493517389439284174973048385]) 0) 74 false) (.node 997 (sourceLit (List.headD (raw_ints% [1000826297760552351606579236565]) 0) 70 true) (.node 996 (sourceLit (List.headD (raw_ints% [404004533090197613624639553173030059604139]) 0) 31 false) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [5909314699496707721612555418081200626714269]) 0) 29 true) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [64554919294632108873119460272947870372509]) 0) 33 true) (.node 1034 (sourceLit (List.headD (raw_ints% [234771900383015174584132798005]) 0) 69 true) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [1507673866318118608848728776995]) 0) 69 false) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [920443887447254484609595235356613022584211]) 0) 31 true) (.node 1039 (sourceLit (List.headD (raw_ints% [8523398521518156786872203214988251012713497]) 0) 30 true) (.node 1038 (sourceLit (List.headD (raw_ints% [47623747156817840807636364735]) 0) 76 true) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [1809835959574843520771157950685]) 0) 68 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [16365680243121489980309308721227171908541581]) 0) 29 false) (.node 1077 (sourceLit (List.headD (raw_ints% [313562520509833870056913501695]) 0) 73 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [564483494643982010636063966265]) 0) 74 true) .empty .empty))))

#time def treeG_J025_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [870748358042782822434626758665]) 0) 68 false) treeG_J025_part102 treeG_J025_part103)

#time def treeG_J025_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [390794882593725491854496195685]) 0) 68 true) treeG_J025_part099 treeG_J025_part104)

#time def treeG_J025_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [20731328984397859206217910565]) 0) 72 false) treeG_J025_part094 treeG_J025_part105)

#time def treeG_J025_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [3300927443446326363826859433917292525]) 0) 39 true) treeG_J025_part081 treeG_J025_part106)

#time def treeG_J025_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [26887348569976693738216875]) 0) 61 false) treeG_J025_part054 treeG_J025_part107)

#time def treeG_J025 : IntSourceTree := treeG_J025_part108

#time def treeG_J026_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [51384004215308690323798295595]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [105474029003053654310276764995]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [20196042627613233683293831125]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [869852284205159606152541582745]) 0) 43 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [12632847596176716081537024375]) 0) 46 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [12556020949213902173475521175]) 0) 49 false) (.node 12 (sourceLit (List.headD (raw_ints% [2229326046384126367330063125]) 0) 47 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [1200406332668375736254649375]) 0) 48 true) .empty .empty)))

#time def treeG_J026_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [185492890699649796230439615]) 0) 55 false) (.node 17 (sourceLit (List.headD (raw_ints% [377362950033722597219767635]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [123678228214317500098963875]) 0) 53 true) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [58153968898927451988094125]) 0) 55 true) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [45647218796209349081207445]) 0) 57 false) (.node 20 (sourceLit (List.headD (raw_ints% [95449819282849115938407375]) 0) 55 true) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [76595318597187964388196675]) 0) 56 true) .empty .empty)))

#time def treeG_J026_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [6150957917295493486827972225]) 0) 50 false) treeG_J026_part000 treeG_J026_part001)

#time def treeG_J026_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 62 false) (.node 26 (sourceLit (List.headD (raw_ints% [11081262613330181824986375]) 0) 61 true) (.node 25 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 61 false) (.node 24 (sourceLit (List.headD (raw_ints% [1038560494108234505715675]) 0) 63 true) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [74369460971466828938946568775931]) 0) 39 true) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [659848135887418872118725]) 0) 63 false) (.node 29 (sourceLit (List.headD (raw_ints% [63170320516126011558701641492731]) 0) 38 true) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [167885035151857835597011271793393]) 0) 36 true) .empty .empty)))

#time def treeG_J026_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [2497335429841869407505]) 0) 71 false) (.node 34 (sourceLit (List.headD (raw_ints% [1261310823755727075045]) 0) 72 false) (.node 33 (sourceLit (List.headD (raw_ints% [251903970762962802452102245223655]) 0) 35 true) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [1600974799519356304430170992597585]) 0) 32 true) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [1236653260229678837325]) 0) 72 false) (.node 37 (sourceLit (List.headD (raw_ints% [2629411697058176999038329701422533]) 0) 31 true) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [8822766680676386243168000700791421]) 0) 29 true) .empty .empty)))

#time def treeG_J026_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [10197203000210674242795]) 0) 69 false) treeG_J026_part003 treeG_J026_part004)

#time def treeG_J026_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [22490315801543813542894575]) 0) 58 false) treeG_J026_part002 treeG_J026_part005)

#time def treeG_J026_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [2229326046384126367330063125]) 0) 48 false) (.node 51 (sourceLit (List.headD (raw_ints% [12632847596176716081537024375]) 0) 47 false) (.node 50 (sourceLit (List.headD (raw_ints% [105474029003053654310276764995]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [20196042627613233683293831125]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [51384004215308690323798295595]) 0) 48 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [1200406332668375736254649375]) 0) 49 true) (.node 54 (sourceLit (List.headD (raw_ints% [12556020949213902173475521175]) 0) 50 false) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [6150957917295493486827972225]) 0) 51 false) .empty .empty)))

#time def treeG_J026_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [95449819282849115938407375]) 0) 56 true) (.node 59 (sourceLit (List.headD (raw_ints% [58153968898927451988094125]) 0) 56 true) (.node 58 (sourceLit (List.headD (raw_ints% [377362950033722597219767635]) 0) 55 false) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [185492890699649796230439615]) 0) 56 false) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [76595318597187964388196675]) 0) 57 true) (.node 62 (sourceLit (List.headD (raw_ints% [45647218796209349081207445]) 0) 58 false) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [22490315801543813542894575]) 0) 59 false) .empty .empty)))

#time def treeG_J026_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [123678228214317500098963875]) 0) 54 true) treeG_J026_part007 treeG_J026_part008)

#time def treeG_J026_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [10197203000210674242795]) 0) 70 false) (.node 69 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 63 false) (.node 67 (sourceLit (List.headD (raw_ints% [11081262613330181824986375]) 0) 62 true) (.node 66 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 62 false) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [74369460971466828938946568775931]) 0) 40 true) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [659848135887418872118725]) 0) 64 false) (.node 70 (sourceLit (List.headD (raw_ints% [63170320516126011558701641492731]) 0) 39 true) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [167885035151857835597011271793393]) 0) 37 true) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [2497335429841869407505]) 0) 72 false) (.node 75 (sourceLit (List.headD (raw_ints% [1261310823755727075045]) 0) 73 false) (.node 74 (sourceLit (List.headD (raw_ints% [251903970762962802452102245223655]) 0) 36 true) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [1600974799519356304430170992597585]) 0) 33 true) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [1236653260229678837325]) 0) 73 false) (.node 78 (sourceLit (List.headD (raw_ints% [2629411697058176999038329701422533]) 0) 32 true) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [658904226199052297531988052755]) 0) 45 false) .empty .empty))))

#time def treeG_J026_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [1038560494108234505715675]) 0) 64 true) treeG_J026_part009 treeG_J026_part010)

#time def treeG_J026_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [869852284205159606152541582745]) 0) 44 false) treeG_J026_part006 treeG_J026_part011)

#time def treeG_J026_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [18961083981132310860123070125]) 0) 50 false) (.node 93 (sourceLit (List.headD (raw_ints% [9706995816523697037580693605]) 0) 51 false) (.node 92 (sourceLit (List.headD (raw_ints% [23036369145969305795743985625]) 0) 47 false) (.node 91 (sourceLit (List.headD (raw_ints% [159564053790798618296755234395]) 0) 47 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [5659058425436628470914775625]) 0) 48 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [4641506117160603097948901685]) 0) 52 false) (.node 96 (sourceLit (List.headD (raw_ints% [210980506953835735462938375]) 0) 50 true) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [32762129657695024055434875]) 0) 56 true) .empty .empty)))

#time def treeG_J026_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [68804121790874884619520315]) 0) 58 false) (.node 101 (sourceLit (List.headD (raw_ints% [69922835951720223574616085]) 0) 58 false) (.node 100 (sourceLit (List.headD (raw_ints% [137166056312860692013969125]) 0) 55 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [114304319968510267488618075]) 0) 56 true) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [16944758480615201984372625]) 0) 60 false) (.node 104 (sourceLit (List.headD (raw_ints% [43361382785724460205295075]) 0) 58 true) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [5535705292401570266464425]) 0) 61 true) .empty .empty)))

#time def treeG_J026_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [569233009367795398209095655]) 0) 55 false) treeG_J026_part013 treeG_J026_part014)

#time def treeG_J026_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [496692887884048084234005]) 0) 65 false) (.node 110 (sourceLit (List.headD (raw_ints% [2010235018633764470873325]) 0) 63 false) (.node 109 (sourceLit (List.headD (raw_ints% [531785367255608619952870908714717]) 0) 38 true) (.node 108 (sourceLit (List.headD (raw_ints% [23497566803920955321468775]) 0) 62 true) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [842840093106158349342214992090303]) 0) 36 true) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [7674581352699220092705]) 0) 71 false) (.node 113 (sourceLit (List.headD (raw_ints% [1091176310451899882323987929123489]) 0) 35 true) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [6459952264895453374037100854559375]) 0) 32 true) .empty .empty)))

#time def treeG_J026_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [447956168192944988911434522765]) 0) 46 false) (.node 118 (sourceLit (List.headD (raw_ints% [3758017599454059977685]) 0) 72 false) (.node 117 (sourceLit (List.headD (raw_ints% [10178386699096673436403038239358147]) 0) 31 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [33247820472254445741445274521969107]) 0) 29 true) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [6761253098468120498309808675]) 0) 52 false) (.node 131 (sourceLit (List.headD (raw_ints% [27759237659049751285050637875]) 0) 48 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [5201760774896294857103480625]) 0) 50 false) .empty .empty)))

#time def treeG_J026_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [7593151160203947192855]) 0) 71 false) treeG_J026_part016 treeG_J026_part017)

#time def treeG_J026_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [120888967478267147287656266721531]) 0) 39 false) treeG_J026_part015 treeG_J026_part018)

#time def treeG_J026_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [7370290416462596122775625]) 0) 56 true) (.node 137 (sourceLit (List.headD (raw_ints% [778445318760704265328772625]) 0) 51 false) (.node 136 (sourceLit (List.headD (raw_ints% [3202531515959204343323774475]) 0) 53 false) (.node 135 (sourceLit (List.headD (raw_ints% [857433094763125525896178125]) 0) 52 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [3132054317025712709069831145]) 0) 53 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [20858118515005788037780875]) 0) 57 true) (.node 140 (sourceLit (List.headD (raw_ints% [47967514833518200247332005]) 0) 59 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [94198453107231098068024725]) 0) 58 false) .empty .empty)))

#time def treeG_J026_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 63 false) (.node 145 (sourceLit (List.headD (raw_ints% [10127446974260956022393475]) 0) 59 true) (.node 144 (sourceLit (List.headD (raw_ints% [11578451497332767769156435]) 0) 61 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [11399201159686590425850675]) 0) 61 false) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [388009505955961671765075]) 0) 69 true) (.node 148 (sourceLit (List.headD (raw_ints% [97629214224866988113301417748731]) 0) 41 false) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [234307523369741304197084633610993]) 0) 40 true) .empty .empty)))

#time def treeG_J026_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [4713625171415287887552675]) 0) 60 true) treeG_J026_part020 treeG_J026_part021)

#time def treeG_J026_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [315170542403047642545]) 0) 76 false) (.node 155 (sourceLit (List.headD (raw_ints% [5151959705187765942615]) 0) 72 false) (.node 153 (sourceLit (List.headD (raw_ints% [333537639880677296349285]) 0) 66 false) (.node 152 (sourceLit (List.headD (raw_ints% [337477528977150256872601860148455]) 0) 38 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [419636169844468539935942841949917]) 0) 37 true) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [2547907865181038892675]) 0) 73 false) (.node 156 (sourceLit (List.headD (raw_ints% [2429488732688048534803464930980895]) 0) 34 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [3774487501019248218682354268967807]) 0) 33 true) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [35955027773733730385913069375]) 0) 48 false) (.node 172 (sourceLit (List.headD (raw_ints% [88000581490229699344458565875]) 0) 47 false) (.node 171 (sourceLit (List.headD (raw_ints% [144196057201073185307339644185]) 0) 48 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [17338016577348784955658541095]) 0) 51 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [7070445265058839942632363375]) 0) 50 false) (.node 175 (sourceLit (List.headD (raw_ints% [33582840652629461093571436365]) 0) 50 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [8168619946676214275346196215]) 0) 52 false) .empty .empty))))

#time def treeG_J026_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [168798360343293199844325]) 0) 67 false) treeG_J026_part022 treeG_J026_part023)

#time def treeG_J026_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [26271962316880885976847253245]) 0) 50 false) treeG_J026_part019 treeG_J026_part024)

#time def treeG_J026_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [68151322914276218651638300125]) 0) 46 false) treeG_J026_part012 treeG_J026_part025)

#time def treeG_J026_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [119592784423587311516529135]) 0) 58 false) (.node 181 (sourceLit (List.headD (raw_ints% [121947223382352577414711935]) 0) 58 false) (.node 180 (sourceLit (List.headD (raw_ints% [107684894647010307522866625]) 0) 55 false) (.node 179 (sourceLit (List.headD (raw_ints% [1993588298290121912651639835]) 0) 54 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [30871845908487115337494575]) 0) 56 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [29369047508715869092253115]) 0) 60 false) (.node 184 (sourceLit (List.headD (raw_ints% [5652381414402157104873675]) 0) 58 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [943963610542184510535375]) 0) 60 false) .empty .empty)))

#time def treeG_J026_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [6655000654725563384964493283461473]) 0) 36 true) (.node 189 (sourceLit (List.headD (raw_ints% [2093852794853480429765693592694413]) 0) 38 false) (.node 188 (sourceLit (List.headD (raw_ints% [34588681445778178438512675]) 0) 62 false) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [51675451780996858456802925]) 0) 63 true) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [4308464153182504227637641833251791]) 0) 35 true) (.node 192 (sourceLit (List.headD (raw_ints% [853693994862297514520595]) 0) 65 false) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [210744338237489774866005]) 0) 67 false) .empty .empty)))

#time def treeG_J026_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [25265537436510937348641887611131]) 0) 39 true) treeG_J026_part027 treeG_J026_part028)

#time def treeG_J026_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [90106032413328221320861174785]) 0) 49 false) (.node 198 (sourceLit (List.headD (raw_ints% [6433613861270095593015]) 0) 72 false) (.node 197 (sourceLit (List.headD (raw_ints% [28693433023912103120452400656336173]) 0) 31 true) (.node 196 (sourceLit (List.headD (raw_ints% [13014687660547116577605]) 0) 71 false) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [87535779560361497256390062085000717]) 0) 29 true) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [43080103992514253845786911135]) 0) 50 false) (.node 213 (sourceLit (List.headD (raw_ints% [67193538390644519916044643375]) 0) 48 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [29095563015628726178743644375]) 0) 49 false) .empty .empty)))

#time def treeG_J026_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [1226108060953830708694327755]) 0) 55 false) (.node 218 (sourceLit (List.headD (raw_ints% [2518282814825250783138182535]) 0) 54 false) (.node 217 (sourceLit (List.headD (raw_ints% [3145999973149067838651795375]) 0) 52 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [1361601716615525419197935625]) 0) 53 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [149695993657474056761399145]) 0) 58 false) (.node 221 (sourceLit (List.headD (raw_ints% [149401131677021883598428375]) 0) 56 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [68580847279809418437915975]) 0) 57 false) .empty .empty)))

#time def treeG_J026_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [20772714588792643720276338465]) 0) 51 false) treeG_J026_part030 treeG_J026_part031)

#time def treeG_J026_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [20396762605150533181863241030235313]) 0) 32 true) treeG_J026_part029 treeG_J026_part032)

#time def treeG_J026_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [59421289826959725431477475]) 0) 63 false) (.node 227 (sourceLit (List.headD (raw_ints% [10147151031315038606508525]) 0) 61 true) (.node 226 (sourceLit (List.headD (raw_ints% [2246230793628659833300305]) 0) 64 false) (.node 225 (sourceLit (List.headD (raw_ints% [7889914194331556563633575]) 0) 60 false) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [220523965886244913575244723108593]) 0) 40 true) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [53025838663743204055557525]) 0) 64 true) (.node 230 (sourceLit (List.headD (raw_ints% [2562467841592963038159862859916399]) 0) 39 false) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [5980045596771262871219289563164563]) 0) 37 true) .empty .empty)))

#time def treeG_J026_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [7918871930185038792255]) 0) 72 false) (.node 235 (sourceLit (List.headD (raw_ints% [128312982954485519784165]) 0) 68 false) (.node 234 (sourceLit (List.headD (raw_ints% [3469191813493567147765756149351957]) 0) 36 true) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [15537785139774436112256311168273523]) 0) 33 true) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [3912249522045714452655]) 0) 73 false) (.node 238 (sourceLit (List.headD (raw_ints% [21144458021873606683087692118400559]) 0) 32 true) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [55429999258630651409544092595]) 0) 50 false) .empty .empty)))

#time def treeG_J026_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [260078177490810109085655]) 0) 67 false) treeG_J026_part034 treeG_J026_part035)

#time def treeG_J026_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [267930417445556651859362175]) 0) 56 false) (.node 258 (sourceLit (List.headD (raw_ints% [4989360553014311027087860125]) 0) 52 false) (.node 256 (sourceLit (List.headD (raw_ints% [2753139718821235779513910125]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [52577367332399046598002385905]) 0) 50 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [6302047321058214722465071125]) 0) 53 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [1146231927321504804152202375]) 0) 54 false) (.node 259 (sourceLit (List.headD (raw_ints% [3042977331360379653624725235]) 0) 54 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [738319167424420399035480015]) 0) 56 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [14835864778120928616731775]) 0) 60 false) (.node 264 (sourceLit (List.headD (raw_ints% [15732116466351815333260575]) 0) 60 false) (.node 263 (sourceLit (List.headD (raw_ints% [179799202891360802006269155]) 0) 58 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [5488741365692546418456285]) 0) 63 false) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [2795989529818326065313825]) 0) 66 true) (.node 267 (sourceLit (List.headD (raw_ints% [176007534278748736603854727014651]) 0) 39 false) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [3858044521943439738367651377563157]) 0) 38 true) .empty .empty))))

#time def treeG_J026_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [98432049007555309446176217375]) 0) 48 false) treeG_J026_part036 treeG_J026_part037)

#time def treeG_J026_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [73278978434256240439903395]) 0) 59 false) treeG_J026_part033 treeG_J026_part038)

#time def treeG_J026_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [90617375426643615546640955749027311]) 0) 32 true) (.node 273 (sourceLit (List.headD (raw_ints% [43531900620987598742116674672064713]) 0) 35 true) (.node 272 (sourceLit (List.headD (raw_ints% [6734941582325687696259765]) 0) 68 true) (.node 271 (sourceLit (List.headD (raw_ints% [47654486120212971995522299042123857]) 0) 36 false) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [309412016744130443305305]) 0) 67 false) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [95608848094283385777598088689852011]) 0) 31 true) (.node 276 (sourceLit (List.headD (raw_ints% [76254232312297053473745]) 0) 69 false) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [9404129999099981991495]) 0) 72 false) .empty .empty)))

#time def treeG_J026_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [7866558902135875279403845125]) 0) 52 false) (.node 295 (sourceLit (List.headD (raw_ints% [8667060748990822908429071625]) 0) 52 false) (.node 294 (sourceLit (List.headD (raw_ints% [67779894524747048973301274055]) 0) 50 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [1987790796475400179857877965]) 0) 55 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [906939709099696401972481125]) 0) 55 false) (.node 298 (sourceLit (List.headD (raw_ints% [1891882253116481969663444295]) 0) 55 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [227108658800818618116299685]) 0) 58 false) .empty .empty)))

#time def treeG_J026_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [250775548789616209673013011809408227]) 0) 29 true) treeG_J026_part040 treeG_J026_part041)

#time def treeG_J026_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [810627643015971646288995]) 0) 66 false) (.node 304 (sourceLit (List.headD (raw_ints% [1664378507142258774474465]) 0) 65 false) (.node 303 (sourceLit (List.headD (raw_ints% [24918696270718404177680775]) 0) 60 false) (.node 302 (sourceLit (List.headD (raw_ints% [438927180109472285512681725]) 0) 57 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [23574318738372074102887575]) 0) 60 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [99132875041248412544774862530811]) 0) 42 false) (.node 307 (sourceLit (List.headD (raw_ints% [6245753952358991805810075]) 0) 63 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [104157122304052942476498675]) 0) 63 true) .empty .empty)))

#time def treeG_J026_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [10015677201873507898587729630678189]) 0) 38 true) (.node 312 (sourceLit (List.headD (raw_ints% [13408632929246058716685397151322105]) 0) 39 false) (.node 311 (sourceLit (List.headD (raw_ints% [27942983762332439171914425]) 0) 67 false) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [27199844506793560894124715]) 0) 67 true) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [18769897571717294858596161145188447]) 0) 35 true) (.node 315 (sourceLit (List.headD (raw_ints% [45274758447411230880285]) 0) 70 false) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [44578744591556898304725]) 0) 70 false) .empty .empty)))

#time def treeG_J026_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [1605128090884100694131878559369889]) 0) 41 true) treeG_J026_part043 treeG_J026_part044)

#time def treeG_J026_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [847429663967461036955345625]) 0) 55 false) treeG_J026_part042 treeG_J026_part045)

#time def treeG_J026_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [10743757251257439531719830125]) 0) 52 false) (.node 336 (sourceLit (List.headD (raw_ints% [1478480257542396782228790375]) 0) 55 false) (.node 335 (sourceLit (List.headD (raw_ints% [82982421717095051348600162205]) 0) 50 false) (.node 319 (sourceLit (List.headD (raw_ints% [686485059631783442355]) 0) 76 false) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [9600279050744986716397952595]) 0) 53 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [2481526909077280803737722125]) 0) 54 false) (.node 339 (sourceLit (List.headD (raw_ints% [4524551681105548225029051945]) 0) 54 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [1078550102982128545894917465]) 0) 56 false) .empty .empty)))

#time def treeG_J026_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [32312772698623219589043375]) 0) 60 false) (.node 344 (sourceLit (List.headD (raw_ints% [34105276075084993022100975]) 0) 60 false) (.node 343 (sourceLit (List.headD (raw_ints% [129563988609055741753206285]) 0) 59 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [7826286691445523777339435]) 0) 63 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [17429712071632296067065375]) 0) 64 false) (.node 347 (sourceLit (List.headD (raw_ints% [41593666720448827550802353592069]) 0) 39 false) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [7030296523263388939800446978549109]) 0) 38 false) .empty .empty)))

#time def treeG_J026_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [289749623260952192547991725]) 0) 57 false) treeG_J026_part047 treeG_J026_part048)

#time def treeG_J026_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [25770484593356934321735]) 0) 71 false) (.node 354 (sourceLit (List.headD (raw_ints% [54709101030331252231554735]) 0) 67 true) (.node 352 (sourceLit (List.headD (raw_ints% [17338962672329063434087095]) 0) 69 false) (.node 351 (sourceLit (List.headD (raw_ints% [150382683936795416419962526841796753]) 0) 36 true) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [472608154356861477676049383514372073]) 0) 35 false) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [104844801477347870047395]) 0) 69 false) (.node 355 (sourceLit (List.headD (raw_ints% [1191389306413165395472588436977780881]) 0) 32 true) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [505027874200670049697479067956178293]) 0) 31 true) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [5816514544512022777071064005]) 0) 54 false) (.node 376 (sourceLit (List.headD (raw_ints% [51177768973488648470874114765]) 0) 51 false) (.node 359 (sourceLit (List.headD (raw_ints% [940654692368940255839153333333815005]) 0) 29 true) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [15789125218542473236256800875]) 0) 52 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [2707682410698999280098654465]) 0) 55 false) (.node 379 (sourceLit (List.headD (raw_ints% [7115998414858653923829905625]) 0) 53 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [408524311277454941695594125]) 0) 57 false) .empty .empty))))

#time def treeG_J026_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [378832276043022194272755225]) 0) 63 true) treeG_J026_part049 treeG_J026_part050)

#time def treeG_J026_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [18616097518102444773627599142862863]) 0) 34 true) treeG_J026_part046 treeG_J026_part051)

#time def treeG_J026_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [170518031434916309319757875]) 0) 63 false) treeG_J026_part039 treeG_J026_part052)

#time def treeG_J026_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [1302639393283824650215730625]) 0) 52 false) treeG_J026_part026 treeG_J026_part053)

#time def treeG_J026_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [7329756889187252365803075]) 0) 61 false) (.node 385 (sourceLit (List.headD (raw_ints% [44636233411797911941314375]) 0) 60 false) (.node 384 (sourceLit (List.headD (raw_ints% [76303876380503460970023405]) 0) 60 false) (.node 383 (sourceLit (List.headD (raw_ints% [190074838178078575837268625]) 0) 58 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [4583776119381637192183455]) 0) 64 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [173875970590582126744760175]) 0) 63 false) (.node 388 (sourceLit (List.headD (raw_ints% [354937833444544822628297096531175]) 0) 40 true) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [13450808886799791716327961216028665]) 0) 39 false) .empty .empty)))

#time def treeG_J026_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [54890200064120897155075875]) 0) 68 true) (.node 393 (sourceLit (List.headD (raw_ints% [165911545885426068366821475]) 0) 67 false) (.node 392 (sourceLit (List.headD (raw_ints% [204017215653779651286704115447085173]) 0) 37 true) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [512670863164355509270400302037084829]) 0) 36 false) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [30133028442895485871335]) 0) 71 false) (.node 396 (sourceLit (List.headD (raw_ints% [1116309716126296216038203792397027093]) 0) 33 true) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [430563484128260270602968671384726841]) 0) 32 true) .empty .empty)))

#time def treeG_J026_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [602376146141681707648070625]) 0) 64 true) treeG_J026_part055 treeG_J026_part056)

#time def treeG_J026_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [203641538464608841775467125]) 0) 59 false) (.node 419 (sourceLit (List.headD (raw_ints% [7108477407918497329113076065]) 0) 54 false) (.node 418 (sourceLit (List.headD (raw_ints% [20834493185827506940793771625]) 0) 52 false) (.node 417 (sourceLit (List.headD (raw_ints% [31977210871998675038078209575]) 0) 52 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [1158617876445343280023045875]) 0) 56 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [190247472827272388437911585]) 0) 59 false) (.node 422 (sourceLit (List.headD (raw_ints% [527298999293957690843196525]) 0) 57 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [121864286027908589793066675]) 0) 59 false) .empty .empty)))

#time def treeG_J026_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [9869799190819747520826823750798509]) 0) 38 true) (.node 427 (sourceLit (List.headD (raw_ints% [266018341481581226876778991053051]) 0) 39 false) (.node 426 (sourceLit (List.headD (raw_ints% [56959694124972604293585375]) 0) 60 false) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [62389091397341931902458425]) 0) 62 true) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [365595626125592083881209906298255393]) 0) 36 false) (.node 430 (sourceLit (List.headD (raw_ints% [726584217224186447762275575]) 0) 63 false) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [879799548898946722593464145]) 0) 65 true) .empty .empty)))

#time def treeG_J026_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [44998729614721365860665665]) 0) 61 false) treeG_J026_part058 treeG_J026_part059)

#time def treeG_J026_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [14786723639248399244055]) 0) 72 false) treeG_J026_part057 treeG_J026_part060)

#time def treeG_J026_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [34495572292434037420935]) 0) 71 false) (.node 436 (sourceLit (List.headD (raw_ints% [27497522432799122512561635]) 0) 70 true) (.node 435 (sourceLit (List.headD (raw_ints% [17596856927672541692125398102164495409]) 0) 32 false) (.node 434 (sourceLit (List.headD (raw_ints% [386532192801183388965197685]) 0) 67 false) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [8425449854809699678608151271220038451]) 0) 31 true) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [20344181782974629483936081565]) 0) 53 false) (.node 439 (sourceLit (List.headD (raw_ints% [5948361053683224073808345408821814451]) 0) 29 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [857405923185553313560241625]) 0) 57 false) .empty .empty)))

#time def treeG_J026_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [28485899111692231866972045]) 0) 62 false) (.node 462 (sourceLit (List.headD (raw_ints% [247377346211053618455375315]) 0) 59 false) (.node 461 (sourceLit (List.headD (raw_ints% [375046782583944169163725875]) 0) 58 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [84306040278969778751481975]) 0) 60 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [26663625137194817091931845]) 0) 62 false) (.node 465 (sourceLit (List.headD (raw_ints% [19307013154027669462938075]) 0) 62 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [12407484308946337981945575]) 0) 63 false) .empty .empty)))

#time def treeG_J026_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [137524843663109314031700675]) 0) 60 false) treeG_J026_part062 treeG_J026_part063)

#time def treeG_J026_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [9356583321899418954081800947280761251]) 0) 34 false) (.node 472 (sourceLit (List.headD (raw_ints% [284806420889685867583957010872670283]) 0) 38 false) (.node 470 (sourceLit (List.headD (raw_ints% [11660304038809769618577392483413587]) 0) 40 true) (.node 469 (sourceLit (List.headD (raw_ints% [29533132748490507330902325]) 0) 66 true) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [166120045420733519426293275]) 0) 67 false) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [1308708371375727098620041304564069143]) 0) 37 true) (.node 473 (sourceLit (List.headD (raw_ints% [1211622640669798859327107095]) 0) 66 true) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [55177799108163035765034195]) 0) 71 false) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [3308926093764033038705751375]) 0) 56 false) (.node 478 (sourceLit (List.headD (raw_ints% [3997443185340719704002591299917655805]) 0) 33 true) (.node 477 (sourceLit (List.headD (raw_ints% [13763827730621008999216485]) 0) 72 true) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [1231803040824102386055]) 0) 76 false) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [346457836187828414351335575]) 0) 59 false) (.node 500 (sourceLit (List.headD (raw_ints% [2271005816296869974217920625]) 0) 56 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [972888131041818985811706975]) 0) 57 false) .empty .empty))))

#time def treeG_J026_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [310478087463063024752538043792113]) 0) 41 false) treeG_J026_part064 treeG_J026_part065)

#time def treeG_J026_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [2104745879587098687969682307091053457]) 0) 35 true) treeG_J026_part061 treeG_J026_part066)

#time def treeG_J026_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [112019028633127283830240725]) 0) 62 false) (.node 506 (sourceLit (List.headD (raw_ints% [97496411107248751409919225]) 0) 60 false) (.node 505 (sourceLit (List.headD (raw_ints% [68944866832047561607222515]) 0) 61 false) (.node 504 (sourceLit (List.headD (raw_ints% [215359875087970525212861225]) 0) 59 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [181323056788165853555053429790469]) 0) 39 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [1199114341200034565056712775]) 0) 63 true) (.node 509 (sourceLit (List.headD (raw_ints% [14837448590228755916867432451472317]) 0) 38 false) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [738725355367504711675686465767490177]) 0) 36 true) .empty .empty)))

#time def treeG_J026_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [248208718865451265572698415]) 0) 70 false) (.node 514 (sourceLit (List.headD (raw_ints% [399538708367745562073076195]) 0) 69 true) (.node 513 (sourceLit (List.headD (raw_ints% [6661648613822072569312994481053777985]) 0) 35 false) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [101354192695719076003808041594264920561]) 0) 32 true) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [55089806494776470034286875]) 0) 71 true) (.node 517 (sourceLit (List.headD (raw_ints% [158130783005200402943916966427712218467]) 0) 31 false) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [121969820877219806454274576188543171309]) 0) 29 true) .empty .empty)))

#time def treeG_J026_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [2208759912264814878003810345]) 0) 65 false) treeG_J026_part068 treeG_J026_part069)

#time def treeG_J026_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [138131822471859847361108925]) 0) 60 false) (.node 543 (sourceLit (List.headD (raw_ints% [635663969925939870805779075]) 0) 58 false) (.node 542 (sourceLit (List.headD (raw_ints% [445538326164603210247295835]) 0) 59 false) (.node 541 (sourceLit (List.headD (raw_ints% [1520912251128981635890468875]) 0) 57 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [190563623148065921004950865]) 0) 60 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [47866473871463399482136925]) 0) 61 false) (.node 546 (sourceLit (List.headD (raw_ints% [21140620847426372257645335]) 0) 63 false) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [439633118137960195950022657793757]) 0) 40 true) .empty .empty)))

#time def treeG_J026_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [53443477389603339645795585]) 0) 72 false) (.node 551 (sourceLit (List.headD (raw_ints% [2528074704565902720467058975]) 0) 64 true) (.node 550 (sourceLit (List.headD (raw_ints% [38158056667848295154022217418299491]) 0) 39 false) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [1308338197146876446843600487512830743]) 0) 37 true) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [509894306584071633603144585]) 0) 70 true) (.node 554 (sourceLit (List.headD (raw_ints% [9279065356573526766553077090181916271]) 0) 36 false) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [120067359339517913911971643488826443063]) 0) 33 true) .empty .empty)))

#time def treeG_J026_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [348284090621051342477459325]) 0) 63 false) treeG_J026_part071 treeG_J026_part072)

#time def treeG_J026_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [2208727344459158526452145975]) 0) 57 false) treeG_J026_part070 treeG_J026_part073)

#time def treeG_J026_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [586569432734371572021752625]) 0) 59 false) (.node 581 (sourceLit (List.headD (raw_ints% [1515811672083501697749474825]) 0) 58 false) (.node 559 (sourceLit (List.headD (raw_ints% [55109515343429655672463755]) 0) 72 true) (.node 558 (sourceLit (List.headD (raw_ints% [166125669375881842351922149027547530077]) 0) 32 false) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [2068936371216144285969230775]) 0) 57 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [60809378158009179698864175]) 0) 62 false) (.node 584 (sourceLit (List.headD (raw_ints% [210152047418984672796458925]) 0) 60 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [178767233836470943312298625]) 0) 60 false) .empty .empty)))

#time def treeG_J026_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [1349254262053077434140041944460282033]) 0) 36 false) (.node 589 (sourceLit (List.headD (raw_ints% [18354513535332437484467613713822373]) 0) 38 true) (.node 588 (sourceLit (List.headD (raw_ints% [8019069345207985543512975]) 0) 65 true) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [1895682522442137250011631425]) 0) 63 false) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [17128354190997084144061798381156423929]) 0) 35 true) (.node 592 (sourceLit (List.headD (raw_ints% [592104327103839699808858665]) 0) 68 true) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [1254634346601398996405805555]) 0) 69 false) .empty .empty)))

#time def treeG_J026_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [528038467874584729370793443584251]) 0) 39 false) treeG_J026_part075 treeG_J026_part076)

#time def treeG_J026_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [282172272366109498231808925]) 0) 60 false) (.node 599 (sourceLit (List.headD (raw_ints% [2779980530891329284085028960629303652541]) 0) 29 false) (.node 597 (sourceLit (List.headD (raw_ints% [1118669657721343714239690114338323762971]) 0) 31 true) (.node 596 (sourceLit (List.headD (raw_ints% [1267997332033594532778987585]) 0) 70 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [606562555148163037176549645]) 0) 71 false) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [358318100322551103790862925]) 0) 60 false) (.node 622 (sourceLit (List.headD (raw_ints% [535136672959449243751089495]) 0) 60 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [12375181549572051594275055]) 0) 65 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [412436645382715226825563125]) 0) 63 true) (.node 627 (sourceLit (List.headD (raw_ints% [32725189991251885957540425]) 0) 63 false) (.node 626 (sourceLit (List.headD (raw_ints% [4958594663822850930152355]) 0) 66 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [120958948251568115665102012672251]) 0) 43 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [138242413344001249077459075]) 0) 69 false) (.node 630 (sourceLit (List.headD (raw_ints% [7064071275397591579811228891515233]) 0) 42 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [332199057399994235122955303996639097]) 0) 40 false) .empty .empty))))

#time def treeG_J026_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [398284284106071932533506508480086241233]) 0) 32 false) treeG_J026_part077 treeG_J026_part078)

#time def treeG_J026_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [275736374326693283571131385]) 0) 71 false) treeG_J026_part074 treeG_J026_part079)

#time def treeG_J026_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [304507219594834848472839045]) 0) 59 false) treeG_J026_part067 treeG_J026_part080)

#time def treeG_J026_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [160599415887153194573951532920733911631]) 0) 35 true) (.node 636 (sourceLit (List.headD (raw_ints% [64793955430698730805684768996114085537]) 0) 36 false) (.node 635 (sourceLit (List.headD (raw_ints% [441132163296367657502237535]) 0) 72 false) (.node 634 (sourceLit (List.headD (raw_ints% [3300927443446326363826859433917292525]) 0) 39 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [771866853180143908175059485]) 0) 72 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [1553977259103425402982605355]) 0) 59 false) (.node 639 (sourceLit (List.headD (raw_ints% [82709008811449086606126675]) 0) 75 false) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [506484153226117534785266925]) 0) 60 false) .empty .empty)))

#time def treeG_J026_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [26095886223432796887034142524846437]) 0) 38 false) (.node 667 (sourceLit (List.headD (raw_ints% [803024151827868963284678120314629]) 0) 39 false) (.node 666 (sourceLit (List.headD (raw_ints% [385577310895748053151319225]) 0) 60 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [48763328681667857044566375]) 0) 64 false) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [2253455385303969156355879242574231857]) 0) 36 true) (.node 670 (sourceLit (List.headD (raw_ints% [2720555813207567703662757675]) 0) 63 true) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [1145073980479844696118694965]) 0) 68 false) .empty .empty)))

#time def treeG_J026_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [137193526635143645809536705]) 0) 62 false) treeG_J026_part082 treeG_J026_part083)

#time def treeG_J026_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [3694029967868738669876787585]) 0) 71 true) (.node 676 (sourceLit (List.headD (raw_ints% [4797054638404535792796887865]) 0) 70 false) (.node 675 (sourceLit (List.headD (raw_ints% [1243321709628331481673182523562913127633]) 0) 32 true) (.node 674 (sourceLit (List.headD (raw_ints% [3293938639042731830356252245]) 0) 69 true) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [5265482805286062485803515330089625237339]) 0) 31 false) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [1157971449517119751965803595]) 0) 60 false) (.node 679 (sourceLit (List.headD (raw_ints% [23336705764446938189550825174483244341309]) 0) 29 true) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [730796034086125571338724925]) 0) 60 false) .empty .empty)))

#time def treeG_J026_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [82608456426613529525523973656968301]) 0) 39 false) (.node 708 (sourceLit (List.headD (raw_ints% [164647434184675962036137981063379]) 0) 40 true) (.node 707 (sourceLit (List.headD (raw_ints% [254676550930740509321157525]) 0) 61 false) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [607489960109386655003828625]) 0) 63 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [4911047844503923037339521674547344633]) 0) 37 true) (.node 711 (sourceLit (List.headD (raw_ints% [7144313040215607674141448075]) 0) 64 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [1082363063350255556546959155]) 0) 70 false) .empty .empty)))

#time def treeG_J026_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [97524769324560838368317865]) 0) 63 false) treeG_J026_part085 treeG_J026_part086)

#time def treeG_J026_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [38389093864596715191930937836941326137]) 0) 35 false) treeG_J026_part084 treeG_J026_part087)

#time def treeG_J026_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [4355702038360331362725800985]) 0) 72 true) (.node 717 (sourceLit (List.headD (raw_ints% [6340788344764823609147006835]) 0) 71 false) (.node 716 (sourceLit (List.headD (raw_ints% [1761673353073921328118660675531825811929]) 0) 33 true) (.node 715 (sourceLit (List.headD (raw_ints% [5058467292228202460365202385]) 0) 70 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [6550278132383288042395127593455496530387]) 0) 32 false) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [1076014757276503089526130625]) 0) 60 false) (.node 745 (sourceLit (List.headD (raw_ints% [883584396246832460346730185]) 0) 61 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [2469364088788793617608034635213051]) 0) 39 false) .empty .empty)))

#time def treeG_J026_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [16304904884054365243091007795]) 0) 65 true) (.node 750 (sourceLit (List.headD (raw_ints% [3935535733426341013670414925]) 0) 63 false) (.node 749 (sourceLit (List.headD (raw_ints% [27413065696910204583323246373353469]) 0) 38 true) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [3575190688129785628764262821085724673]) 0) 36 false) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [7623390892443754056544088865]) 0) 69 false) (.node 753 (sourceLit (List.headD (raw_ints% [77677476620628099490647111233320083201]) 0) 35 true) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [3316810138817685916954648549427862450417]) 0) 32 false) .empty .empty)))

#time def treeG_J026_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [59623236204069081142892025]) 0) 62 false) treeG_J026_part089 treeG_J026_part090)

#time def treeG_J026_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [55010761061761867054423610015160885]) 0) 40 true) (.node 786 (sourceLit (List.headD (raw_ints% [688534857597710783610094455]) 0) 62 false) (.node 758 (sourceLit (List.headD (raw_ints% [16375606657398385888170801255]) 0) 71 false) (.node 757 (sourceLit (List.headD (raw_ints% [19358869629877433110752800734344231732771]) 0) 31 true) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [128141155882579546867872866669771188827501]) 0) 29 false) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [1317005761486734789822086308138215]) 0) 41 false) (.node 787 (sourceLit (List.headD (raw_ints% [205334551586440645051243275]) 0) 63 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [68483340488164696732617075]) 0) 66 true) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [71236995016397712796596462270799874769]) 0) 37 true) (.node 792 (sourceLit (List.headD (raw_ints% [4243119266316854333051892247816534653]) 0) 38 false) (.node 791 (sourceLit (List.headD (raw_ints% [1384981096705243585976482875]) 0) 67 false) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [33622713897658454147842354275]) 0) 66 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [2539241745945803622536654612479844131173]) 0) 34 false) (.node 795 (sourceLit (List.headD (raw_ints% [6340929092335978258454645625]) 0) 71 false) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [10627388783812882161337149735]) 0) 72 true) .empty .empty))))

#time def treeG_J026_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [14913989222860940713527292635]) 0) 70 true) treeG_J026_part091 treeG_J026_part092)

#time def treeG_J026_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [64796513412167326102545813308279666337]) 0) 36 false) treeG_J026_part088 treeG_J026_part093)

#time def treeG_J026_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [5031269181236976161392288125]) 0) 63 true) (.node 828 (sourceLit (List.headD (raw_ints% [761714970141693499062081075]) 0) 62 false) (.node 827 (sourceLit (List.headD (raw_ints% [9082333940657241304547779816724229]) 0) 39 false) (.node 799 (sourceLit (List.headD (raw_ints% [161963349185614978522629705]) 0) 79 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [48485157880697961220476627303564909]) 0) 38 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [27384753657696313930902870795]) 0) 65 false) (.node 831 (sourceLit (List.headD (raw_ints% [5335535042106165374505818341570872993]) 0) 36 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [145567384881697768819477387198384637649]) 0) 35 false) .empty .empty)))

#time def treeG_J026_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [58885161792649914533519400195]) 0) 71 true) (.node 836 (sourceLit (List.headD (raw_ints% [40277705592204853747345875135]) 0) 70 false) (.node 835 (sourceLit (List.headD (raw_ints% [7875977819867139535936822134759054435633]) 0) 32 true) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [59986737565010291071339274534021737831539]) 0) 31 false) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [6448322417683771724903607200447799]) 0) 40 false) (.node 839 (sourceLit (List.headD (raw_ints% [542687520078751085318239719914566841038029]) 0) 29 true) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [1309581694047011072923017675]) 0) 63 false) .empty .empty)))

#time def treeG_J026_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [64116277467433470374018709735]) 0) 67 true) treeG_J026_part095 treeG_J026_part096)

#time def treeG_J026_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [85895885327271012224487202861821466094697]) 0) 32 false) (.node 874 (sourceLit (List.headD (raw_ints% [288041374914493194412670311739984387187]) 0) 36 false) (.node 872 (sourceLit (List.headD (raw_ints% [13821773574739874040609602837203942299]) 0) 37 true) (.node 871 (sourceLit (List.headD (raw_ints% [16111117954878924849204151125]) 0) 64 true) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [30503733777677384039372612535]) 0) 67 false) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [12954461311758746781010131359718742697979]) 0) 33 true) (.node 875 (sourceLit (List.headD (raw_ints% [114843710206121296441655874735]) 0) 68 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [61532483159830618070020174605]) 0) 71 false) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [7871641922173712499774999898913059857]) 0) 36 false) (.node 909 (sourceLit (List.headD (raw_ints% [3101421460772212578752230300017483]) 0) 38 false) (.node 879 (sourceLit (List.headD (raw_ints% [79616470488408631784416002435]) 0) 72 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [7650432569330998307238323475]) 0) 63 false) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [256141573479616761144354209896016176041]) 0) 35 true) (.node 912 (sourceLit (List.headD (raw_ints% [1359245987892976211878344435]) 0) 70 true) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [125123745022788238452763934805]) 0) 67 false) .empty .empty))))

#time def treeG_J026_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [158506680004221695329323847333886679]) 0) 39 false) treeG_J026_part097 treeG_J026_part098)

#time def treeG_J026_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [38851314635862370687642904258467299]) 0) 41 true) (.node 918 (sourceLit (List.headD (raw_ints% [181950128112311150673559749405]) 0) 71 false) (.node 917 (sourceLit (List.headD (raw_ints% [163622428059080265319420325411771679415371]) 0) 31 true) (.node 916 (sourceLit (List.headD (raw_ints% [195399121390531003936347625005]) 0) 69 true) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [1917021685315087280910034965703710298553181]) 0) 29 false) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [5423353874228396635096150684029250539]) 0) 39 false) (.node 951 (sourceLit (List.headD (raw_ints% [2970193815526240394555309325]) 0) 67 false) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [52251669583965003429426123495]) 0) 67 true) .empty .empty)))

#time def treeG_J026_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [62379578346587819385976882068398286377517]) 0) 34 true) (.node 956 (sourceLit (List.headD (raw_ints% [7511940782222417134538100867539324380899]) 0) 35 false) (.node 955 (sourceLit (List.headD (raw_ints% [59991863807227383723604952385]) 0) 70 false) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [318464087710192240076387974215]) 0) 70 true) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [429688897454925453467431031784952193289]) 0) 35 false) (.node 959 (sourceLit (List.headD (raw_ints% [8173956206272493201811742245]) 0) 77 false) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [229627084190718245311616181795]) 0) 67 true) .empty .empty)))

#time def treeG_J026_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [136045737098527488889256130409000140807]) 0) 38 true) treeG_J026_part100 treeG_J026_part101)

#time def treeG_J026_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [94228833041204097363394426095]) 0) 73 false) (.node 999 (sourceLit (List.headD (raw_ints% [5909314699496707721612555418081200626714269]) 0) 29 true) (.node 997 (sourceLit (List.headD (raw_ints% [404004533090197613624639553173030059604139]) 0) 31 false) (.node 996 (sourceLit (List.headD (raw_ints% [435366576619440538830767434545]) 0) 69 false) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [125103553955625847687486930905]) 0) 73 true) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [469594539419627780206035991335]) 0) 68 true) (.node 1034 (sourceLit (List.headD (raw_ints% [973871845849035409024455553420952756517]) 0) 36 false) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [64554919294632108873119460272947870372509]) 0) 33 true) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [113120139504883539879600428235]) 0) 72 true) (.node 1039 (sourceLit (List.headD (raw_ints% [190495203605805793301980868865]) 0) 74 true) (.node 1038 (sourceLit (List.headD (raw_ints% [653522846476548891168547081446623205114207]) 0) 32 false) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [65671055232911573423749634512261061057457]) 0) 32 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [313561220038034042414275783095]) 0) 73 false) (.node 1077 (sourceLit (List.headD (raw_ints% [920443887447254484609595235356613022584211]) 0) 31 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [16365680243121489980309308721227171908541581]) 0) 29 false) .empty .empty))))

#time def treeG_J026_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [34507156165742440334967056802790572848913]) 0) 32 true) treeG_J026_part102 treeG_J026_part103)

#time def treeG_J026_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [17093301817130921757142272110438554825617]) 0) 32 false) treeG_J026_part099 treeG_J026_part104)

#time def treeG_J026_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [12954573881130360576573964163899864131579]) 0) 33 true) treeG_J026_part094 treeG_J026_part105)

#time def treeG_J026_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [1019652146220666416975223345]) 0) 69 true) treeG_J026_part081 treeG_J026_part106)

#time def treeG_J026_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [159905730718164065095558935]) 0) 59 false) treeG_J026_part054 treeG_J026_part107)

#time def treeG_J026 : IntSourceTree := treeG_J026_part108

#time def treeG_J027_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [12632847596176716081537024375]) 0) 46 false) (.node 9 (sourceLit (List.headD (raw_ints% [20196042627613233683293831125]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [102532770602226866064352716765]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [881746340571103563215819648775]) 0) 41 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [49982007868896567286376168685]) 0) 47 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [2229326046384126367330063125]) 0) 47 false) (.node 12 (sourceLit (List.headD (raw_ints% [12219863182774840792594525305]) 0) 49 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [5989023764890490261343122775]) 0) 50 false) .empty .empty)))

#time def treeG_J027_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [58153968898927451988094125]) 0) 55 true) (.node 17 (sourceLit (List.headD (raw_ints% [123678228214317500098963875]) 0) 53 true) (.node 16 (sourceLit (List.headD (raw_ints% [367577311764174794778727725]) 0) 54 false) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [180748506514840805363756505]) 0) 55 false) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [95449819282849115938407375]) 0) 55 true) (.node 20 (sourceLit (List.headD (raw_ints% [44494361713907595394053435]) 0) 57 false) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [21928913702388077557957785]) 0) 58 false) .empty .empty)))

#time def treeG_J027_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [1200406332668375736254649375]) 0) 48 true) treeG_J027_part000 treeG_J027_part001)

#time def treeG_J027_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [74784243951294266619696380897531]) 0) 39 true) (.node 26 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 62 false) (.node 25 (sourceLit (List.headD (raw_ints% [1038560494108234505715675]) 0) 63 true) (.node 24 (sourceLit (List.headD (raw_ints% [2704314989835557488415025]) 0) 61 false) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [11081262613330181824986375]) 0) 61 true) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [63971280753034167080149554555131]) 0) 38 true) (.node 29 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 62 false) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [659848135887418872118725]) 0) 63 false) .empty .empty)))

#time def treeG_J027_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [1647704973977997850529426193570385]) 0) 32 true) (.node 34 (sourceLit (List.headD (raw_ints% [257917044682273295516344642407655]) 0) 35 true) (.node 33 (sourceLit (List.headD (raw_ints% [10197203000210674242795]) 0) 69 false) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [1261310823755727075045]) 0) 72 false) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [2720346090599317304961204687099333]) 0) 31 true) (.node 37 (sourceLit (List.headD (raw_ints% [2497335429841869407505]) 0) 71 false) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [1236653260229678837325]) 0) 72 false) .empty .empty)))

#time def treeG_J027_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [170985526391502308583261257841393]) 0) 36 true) treeG_J027_part003 treeG_J027_part004)

#time def treeG_J027_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [76595318597187964388196675]) 0) 56 true) treeG_J027_part002 treeG_J027_part005)

#time def treeG_J027_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [12219863182774840792594525305]) 0) 50 false) (.node 51 (sourceLit (List.headD (raw_ints% [49982007868896567286376168685]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [20196042627613233683293831125]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [102532770602226866064352716765]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [12632847596176716081537024375]) 0) 47 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [5989023764890490261343122775]) 0) 51 false) (.node 54 (sourceLit (List.headD (raw_ints% [2229326046384126367330063125]) 0) 48 false) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [1200406332668375736254649375]) 0) 49 true) .empty .empty)))

#time def treeG_J027_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [44494361713907595394053435]) 0) 58 false) (.node 59 (sourceLit (List.headD (raw_ints% [180748506514840805363756505]) 0) 56 false) (.node 58 (sourceLit (List.headD (raw_ints% [123678228214317500098963875]) 0) 54 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [58153968898927451988094125]) 0) 56 true) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [21928913702388077557957785]) 0) 59 false) (.node 62 (sourceLit (List.headD (raw_ints% [95449819282849115938407375]) 0) 56 true) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [76595318597187964388196675]) 0) 57 true) .empty .empty)))

#time def treeG_J027_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [367577311764174794778727725]) 0) 55 false) treeG_J027_part007 treeG_J027_part008)

#time def treeG_J027_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [170985526391502308583261257841393]) 0) 37 true) (.node 69 (sourceLit (List.headD (raw_ints% [74784243951294266619696380897531]) 0) 40 true) (.node 67 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 63 false) (.node 66 (sourceLit (List.headD (raw_ints% [1038560494108234505715675]) 0) 64 true) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [11081262613330181824986375]) 0) 62 true) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [63971280753034167080149554555131]) 0) 39 true) (.node 70 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 63 false) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [659848135887418872118725]) 0) 64 false) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [1647704973977997850529426193570385]) 0) 33 true) (.node 75 (sourceLit (List.headD (raw_ints% [257917044682273295516344642407655]) 0) 36 true) (.node 74 (sourceLit (List.headD (raw_ints% [10197203000210674242795]) 0) 70 false) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [1261310823755727075045]) 0) 73 false) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [2720346090599317304961204687099333]) 0) 32 true) (.node 78 (sourceLit (List.headD (raw_ints% [2497335429841869407505]) 0) 72 false) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [720177999550197693749468999775]) 0) 43 false) .empty .empty))))

#time def treeG_J027_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [2704314989835557488415025]) 0) 62 false) treeG_J027_part009 treeG_J027_part010)

#time def treeG_J027_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [881746340571103563215819648775]) 0) 42 false) treeG_J027_part006 treeG_J027_part011)

#time def treeG_J027_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [5659058425436628470914775625]) 0) 48 false) (.node 93 (sourceLit (List.headD (raw_ints% [23036369145969305795743985625]) 0) 47 false) (.node 92 (sourceLit (List.headD (raw_ints% [9440536171530431623445410845]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [68151322914276218651638300125]) 0) 46 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [18450702600659191323845927835]) 0) 50 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [210980506953835735462938375]) 0) 50 true) (.node 96 (sourceLit (List.headD (raw_ints% [4518714517833791082228211875]) 0) 52 false) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [554406117013508784193698945]) 0) 55 false) .empty .empty)))

#time def treeG_J027_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [114304319968510267488618075]) 0) 56 true) (.node 101 (sourceLit (List.headD (raw_ints% [137166056312860692013969125]) 0) 55 true) (.node 100 (sourceLit (List.headD (raw_ints% [68127072400466604984851535]) 0) 58 false) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [67059809725427113230149085]) 0) 58 false) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [43361382785724460205295075]) 0) 58 true) (.node 104 (sourceLit (List.headD (raw_ints% [16520283722716962581127735]) 0) 60 false) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [4073588402410523305334025]) 0) 62 false) .empty .empty)))

#time def treeG_J027_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [32762129657695024055434875]) 0) 56 true) treeG_J027_part013 treeG_J027_part014)

#time def treeG_J027_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [852554965657044364699131615040703]) 0) 36 true) (.node 110 (sourceLit (List.headD (raw_ints% [534302670857319965877421492625117]) 0) 38 true) (.node 109 (sourceLit (List.headD (raw_ints% [23497566803920955321468775]) 0) 62 true) (.node 108 (sourceLit (List.headD (raw_ints% [119580805772657536140676090030331]) 0) 39 false) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [2010235018633764470873325]) 0) 63 false) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [1109967166449745173149745420323489]) 0) 35 true) (.node 113 (sourceLit (List.headD (raw_ints% [496692887884048084234005]) 0) 65 false) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [7674581352699220092705]) 0) 71 false) .empty .empty)))

#time def treeG_J027_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [558609658529291824283118350775]) 0) 44 false) (.node 118 (sourceLit (List.headD (raw_ints% [10461293701224665499274204861463747]) 0) 31 true) (.node 117 (sourceLit (List.headD (raw_ints% [7593151160203947192855]) 0) 71 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [3758017599454059977685]) 0) 72 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [27759237659049751285050637875]) 0) 48 false) (.node 131 (sourceLit (List.headD (raw_ints% [3284422670833143673623534255]) 0) 53 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [25542281503346885701187118075]) 0) 50 false) .empty .empty)))

#time def treeG_J027_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [6605640455854747605993602363474575]) 0) 32 true) treeG_J027_part016 treeG_J027_part017)

#time def treeG_J027_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [5535705292401570266464425]) 0) 61 true) treeG_J027_part015 treeG_J027_part018)

#time def treeG_J027_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [46707201312333497353742805]) 0) 59 false) (.node 137 (sourceLit (List.headD (raw_ints% [3048405270777091903113300975]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [857433094763125525896178125]) 0) 52 false) (.node 135 (sourceLit (List.headD (raw_ints% [3115419708942175265625701265]) 0) 53 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [778445318760704265328772625]) 0) 51 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [91759783087025614575649635]) 0) 58 false) (.node 140 (sourceLit (List.headD (raw_ints% [7370290416462596122775625]) 0) 56 true) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [20858118515005788037780875]) 0) 57 true) .empty .empty)))

#time def treeG_J027_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [171159176571870727114875]) 0) 67 false) (.node 145 (sourceLit (List.headD (raw_ints% [11111653743045847604297685]) 0) 61 false) (.node 144 (sourceLit (List.headD (raw_ints% [4713625171415287887552675]) 0) 60 true) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [10127446974260956022393475]) 0) 59 true) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [97182524861975901380186235463931]) 0) 41 false) (.node 148 (sourceLit (List.headD (raw_ints% [2772778660464305779260975]) 0) 63 false) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [388009505955961671765075]) 0) 69 true) .empty .empty)))

#time def treeG_J027_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [11282724005759758918047825]) 0) 61 false) treeG_J027_part020 treeG_J027_part021)

#time def treeG_J027_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [3870473805312674097156500087182207]) 0) 33 true) (.node 155 (sourceLit (List.headD (raw_ints% [426025060883735938816700388957917]) 0) 37 true) (.node 153 (sourceLit (List.headD (raw_ints% [340784719632771028057935178599655]) 0) 38 true) (.node 152 (sourceLit (List.headD (raw_ints% [168798360343293199844325]) 0) 67 false) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [333537639880677296349285]) 0) 66 false) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [2478967740938374877732088084952095]) 0) 34 true) (.node 156 (sourceLit (List.headD (raw_ints% [5151959705187765942615]) 0) 72 false) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [2547907865181038892675]) 0) 73 false) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [32633860406034580078528308315]) 0) 50 false) (.node 172 (sourceLit (List.headD (raw_ints% [16834845195134717765542863195]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [422307012700739386979841750525]) 0) 45 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [88000581490229699344458565875]) 0) 47 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [7942964317934909980274593185]) 0) 52 false) (.node 175 (sourceLit (List.headD (raw_ints% [35955027773733730385913069375]) 0) 48 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [7070445265058839942632363375]) 0) 50 false) .empty .empty))))

#time def treeG_J027_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [235165695052142899398635969034993]) 0) 40 true) treeG_J027_part022 treeG_J027_part023)

#time def treeG_J027_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [5201760774896294857103480625]) 0) 50 false) treeG_J027_part019 treeG_J027_part024)

#time def treeG_J027_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [155083533335557164842329264845]) 0) 47 false) treeG_J027_part012 treeG_J027_part025)

#time def treeG_J027_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [30871845908487115337494575]) 0) 56 false) (.node 181 (sourceLit (List.headD (raw_ints% [107684894647010307522866625]) 0) 55 false) (.node 180 (sourceLit (List.headD (raw_ints% [118701732848867384430119685]) 0) 58 false) (.node 179 (sourceLit (List.headD (raw_ints% [1302639393283824650215730625]) 0) 52 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [116459756448624115921150185]) 0) 58 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [5652381414402157104873675]) 0) 58 false) (.node 184 (sourceLit (List.headD (raw_ints% [28610612300322073091063565]) 0) 60 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [1759516335158831074740915]) 0) 64 false) .empty .empty)))

#time def treeG_J027_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [51675451780996858456802925]) 0) 63 true) (.node 189 (sourceLit (List.headD (raw_ints% [34588681445778178438512675]) 0) 62 false) (.node 188 (sourceLit (List.headD (raw_ints% [27690422549348265328410020014331]) 0) 39 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [2089223068648934387960401260048013]) 0) 38 false) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [853693994862297514520595]) 0) 65 false) (.node 192 (sourceLit (List.headD (raw_ints% [6672747276011528416057219394079073]) 0) 36 true) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [4342588347674591275777217437270991]) 0) 35 true) .empty .empty)))

#time def treeG_J027_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [943963610542184510535375]) 0) 60 false) treeG_J027_part027 treeG_J027_part028)

#time def treeG_J027_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [311270062064540381839639199025]) 0) 46 false) (.node 198 (sourceLit (List.headD (raw_ints% [29202190153789332544439204497769773]) 0) 31 true) (.node 197 (sourceLit (List.headD (raw_ints% [13014687660547116577605]) 0) 71 false) (.node 196 (sourceLit (List.headD (raw_ints% [20659963440704352478275222529832113]) 0) 32 true) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [6433613861270095593015]) 0) 72 false) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [67193538390644519916044643375]) 0) 48 false) (.node 213 (sourceLit (List.headD (raw_ints% [41797099277191985360984334705]) 0) 50 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [20172181570265879016025503255]) 0) 51 false) .empty .empty)))

#time def treeG_J027_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [1361601716615525419197935625]) 0) 53 false) (.node 218 (sourceLit (List.headD (raw_ints% [3145999973149067838651795375]) 0) 52 false) (.node 217 (sourceLit (List.headD (raw_ints% [2447279523578909038580646105]) 0) 54 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [1192277815752738377066018205]) 0) 55 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [149401131677021883598428375]) 0) 56 false) (.node 221 (sourceLit (List.headD (raw_ints% [145643682610709154284589735]) 0) 58 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [71328860425585080248958885]) 0) 59 false) .empty .empty)))

#time def treeG_J027_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [29095563015628726178743644375]) 0) 49 false) treeG_J027_part030 treeG_J027_part031)

#time def treeG_J027_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [210744338237489774866005]) 0) 67 false) treeG_J027_part029 treeG_J027_part032)

#time def treeG_J027_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [222055472273300068088782490942193]) 0) 40 true) (.node 227 (sourceLit (List.headD (raw_ints% [1074879628871348166281415]) 0) 65 false) (.node 226 (sourceLit (List.headD (raw_ints% [7889914194331556563633575]) 0) 60 false) (.node 225 (sourceLit (List.headD (raw_ints% [2187369819659528185845735]) 0) 64 false) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [10147151031315038606508525]) 0) 61 true) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [2559554458753220186757673198117999]) 0) 39 false) (.node 230 (sourceLit (List.headD (raw_ints% [59421289826959725431477475]) 0) 63 false) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [53025838663743204055557525]) 0) 64 true) .empty .empty)))

#time def treeG_J027_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [15702027958827602722811046359927923]) 0) 33 true) (.node 235 (sourceLit (List.headD (raw_ints% [3490538225907119398143816659355157]) 0) 36 true) (.node 234 (sourceLit (List.headD (raw_ints% [260078177490810109085655]) 0) 67 false) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [128312982954485519784165]) 0) 68 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [21461242543163984350126204323405359]) 0) 32 true) (.node 238 (sourceLit (List.headD (raw_ints% [7918871930185038792255]) 0) 72 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [111634740287155341247590316575]) 0) 48 false) .empty .empty)))

#time def treeG_J027_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [5991177836745986359941349036879763]) 0) 37 true) treeG_J027_part034 treeG_J027_part035)

#time def treeG_J027_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [174827608772794192648029285]) 0) 58 false) (.node 258 (sourceLit (List.headD (raw_ints% [2954966010407743742435389125]) 0) 54 false) (.node 256 (sourceLit (List.headD (raw_ints% [6114608626165484517875455035]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [98432049007555309446176217375]) 0) 48 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [2753139718821235779513910125]) 0) 53 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [717470884357268839345539465]) 0) 56 false) (.node 259 (sourceLit (List.headD (raw_ints% [4989360553014311027087860125]) 0) 52 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [1146231927321504804152202375]) 0) 54 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [2615223304160225296950555]) 0) 64 false) (.node 264 (sourceLit (List.headD (raw_ints% [5339781015657875894736915]) 0) 63 false) (.node 263 (sourceLit (List.headD (raw_ints% [267930417445556651859362175]) 0) 56 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [15732116466351815333260575]) 0) 60 false) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [171958324209943820503667749939451]) 0) 39 false) (.node 267 (sourceLit (List.headD (raw_ints% [14835864778120928616731775]) 0) 60 false) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [2795989529818326065313825]) 0) 66 true) .empty .empty))))

#time def treeG_J027_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [50960338148349390643440361095]) 0) 50 false) treeG_J027_part036 treeG_J027_part037)

#time def treeG_J027_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [68580847279809418437915975]) 0) 57 false) treeG_J027_part033 treeG_J027_part038)

#time def treeG_J027_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [309412016744130443305305]) 0) 67 false) (.node 273 (sourceLit (List.headD (raw_ints% [6734941582325687696259765]) 0) 68 true) (.node 272 (sourceLit (List.headD (raw_ints% [47625618616063051404179990563967057]) 0) 36 false) (.node 271 (sourceLit (List.headD (raw_ints% [170518031434916309319757875]) 0) 63 false) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [43586834346293299603753574857767113]) 0) 35 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [76254232312297053473745]) 0) 69 false) (.node 276 (sourceLit (List.headD (raw_ints% [91037259788323468262326910569532911]) 0) 32 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [96414033516831489238049166381653611]) 0) 31 true) .empty .empty)))

#time def treeG_J027_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [1833664551293287739647404465]) 0) 55 false) (.node 295 (sourceLit (List.headD (raw_ints% [1924259786130219476713428615]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [156075942183666162579135989775]) 0) 48 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [8667060748990822908429071625]) 0) 52 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [220336024331875670671171365]) 0) 58 false) (.node 298 (sourceLit (List.headD (raw_ints% [7866558902135875279403845125]) 0) 52 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [906939709099696401972481125]) 0) 55 false) .empty .empty)))

#time def treeG_J027_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [9404129999099981991495]) 0) 72 false) treeG_J027_part040 treeG_J027_part041)

#time def treeG_J027_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [23574318738372074102887575]) 0) 60 false) (.node 304 (sourceLit (List.headD (raw_ints% [24918696270718404177680775]) 0) 60 false) (.node 303 (sourceLit (List.headD (raw_ints% [1617167942925142381235475]) 0) 65 false) (.node 302 (sourceLit (List.headD (raw_ints% [847429663967461036955345625]) 0) 55 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [788102798999586927222795]) 0) 66 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [6245753952358991805810075]) 0) 63 false) (.node 307 (sourceLit (List.headD (raw_ints% [385085918822219282667285]) 0) 67 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [98503449120810972148112560220411]) 0) 42 false) .empty .empty)))

#time def treeG_J027_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [27199844506793560894124715]) 0) 67 true) (.node 312 (sourceLit (List.headD (raw_ints% [27942983762332439171914425]) 0) 67 false) (.node 311 (sourceLit (List.headD (raw_ints% [1606305326397138779857083596425889]) 0) 41 true) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [13404199113202259441030334900211705]) 0) 39 false) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [45274758447411230880285]) 0) 70 false) (.node 315 (sourceLit (List.headD (raw_ints% [10024074030096545051402439549602989]) 0) 38 true) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [18833807957373966384878966052401247]) 0) 35 true) .empty .empty)))

#time def treeG_J027_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [104157122304052942476498675]) 0) 63 true) treeG_J027_part043 treeG_J027_part044)

#time def treeG_J027_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [426183519135850530776359995]) 0) 57 false) treeG_J027_part042 treeG_J027_part045)

#time def treeG_J027_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [4379692194765407216154228735]) 0) 54 false) (.node 336 (sourceLit (List.headD (raw_ints% [9279469662876271295831973885]) 0) 53 false) (.node 335 (sourceLit (List.headD (raw_ints% [213719835359777015712095762175]) 0) 48 false) (.node 319 (sourceLit (List.headD (raw_ints% [18738197743416876221980740514562063]) 0) 34 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [1478480257542396782228790375]) 0) 55 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [1045217310297736526023831455]) 0) 56 false) (.node 339 (sourceLit (List.headD (raw_ints% [10743757251257439531719830125]) 0) 52 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [2481526909077280803737722125]) 0) 54 false) .empty .empty)))

#time def treeG_J027_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [3689599087836470120831805]) 0) 64 false) (.node 344 (sourceLit (List.headD (raw_ints% [7597562527743263155146885]) 0) 63 false) (.node 343 (sourceLit (List.headD (raw_ints% [289749623260952192547991725]) 0) 57 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [34105276075084993022100975]) 0) 60 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [34783104226499011645903340574469]) 0) 39 false) (.node 347 (sourceLit (List.headD (raw_ints% [32312772698623219589043375]) 0) 60 false) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [17429712071632296067065375]) 0) 64 false) .empty .empty)))

#time def treeG_J027_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [125677955181528169064165355]) 0) 59 false) treeG_J027_part047 treeG_J027_part048)

#time def treeG_J027_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [506267821119135435078077747295186293]) 0) 31 true) (.node 354 (sourceLit (List.headD (raw_ints% [472521205968765601716724291664541673]) 0) 35 false) (.node 352 (sourceLit (List.headD (raw_ints% [150429159505479933315033340735223953]) 0) 36 true) (.node 351 (sourceLit (List.headD (raw_ints% [378832276043022194272755225]) 0) 63 true) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [17338962672329063434087095]) 0) 69 false) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [1192044216064034298317185351779649681]) 0) 32 true) (.node 355 (sourceLit (List.headD (raw_ints% [54709101030331252231554735]) 0) 67 true) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [104844801477347870047395]) 0) 69 false) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [15789125218542473236256800875]) 0) 52 false) (.node 376 (sourceLit (List.headD (raw_ints% [144383349367850432444663189175]) 0) 49 false) (.node 359 (sourceLit (List.headD (raw_ints% [25770484593356934321735]) 0) 71 false) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [5612140560289695816537164955]) 0) 54 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [7115998414858653923829905625]) 0) 53 false) (.node 379 (sourceLit (List.headD (raw_ints% [2617004000110401850784857815]) 0) 55 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [154758447790471498811867865]) 0) 59 false) .empty .empty))))

#time def treeG_J027_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [7017777218701286041410263114638709]) 0) 38 false) treeG_J027_part049 treeG_J027_part050)

#time def treeG_J027_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [44578744591556898304725]) 0) 70 false) treeG_J027_part046 treeG_J027_part051)

#time def treeG_J027_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [3865666846835334932670661187585557]) 0) 38 true) treeG_J027_part039 treeG_J027_part052)

#time def treeG_J027_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [1939593036750074334725903085]) 0) 54 false) treeG_J027_part026 treeG_J027_part053)

#time def treeG_J027_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [2149255412547592990162665]) 0) 65 false) (.node 385 (sourceLit (List.headD (raw_ints% [4445151331744915446255705]) 0) 64 false) (.node 384 (sourceLit (List.headD (raw_ints% [190074838178078575837268625]) 0) 58 false) (.node 383 (sourceLit (List.headD (raw_ints% [73928581007923612864630155]) 0) 60 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [44636233411797911941314375]) 0) 60 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [359230692256744876946546900307175]) 0) 40 true) (.node 388 (sourceLit (List.headD (raw_ints% [7329756889187252365803075]) 0) 61 false) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [173875970590582126744760175]) 0) 63 false) .empty .empty)))

#time def treeG_J027_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [512617502089151781922334049862953629]) 0) 36 false) (.node 393 (sourceLit (List.headD (raw_ints% [204045955958288971079154680336070773]) 0) 37 true) (.node 392 (sourceLit (List.headD (raw_ints% [602376146141681707648070625]) 0) 64 true) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [165911545885426068366821475]) 0) 67 false) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [1116708984234538432777669487570044693]) 0) 33 true) (.node 396 (sourceLit (List.headD (raw_ints% [54890200064120897155075875]) 0) 68 true) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [30133028442895485871335]) 0) 71 false) .empty .empty)))

#time def treeG_J027_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [13442998524289841160838597500342265]) 0) 39 false) treeG_J027_part055 treeG_J027_part056)

#time def treeG_J027_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [1158617876445343280023045875]) 0) 56 false) (.node 419 (sourceLit (List.headD (raw_ints% [20834493185827506940793771625]) 0) 52 false) (.node 418 (sourceLit (List.headD (raw_ints% [6844588925813984416920101175]) 0) 54 false) (.node 417 (sourceLit (List.headD (raw_ints% [97071981126493735413341897175]) 0) 50 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [196473336226583165595128295]) 0) 59 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [527298999293957690843196525]) 0) 57 false) (.node 422 (sourceLit (List.headD (raw_ints% [183838940399414828559570375]) 0) 59 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [43538330896950560244042615]) 0) 61 false) .empty .empty)))

#time def treeG_J027_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [62389091397341931902458425]) 0) 62 true) (.node 427 (sourceLit (List.headD (raw_ints% [56959694124972604293585375]) 0) 60 false) (.node 426 (sourceLit (List.headD (raw_ints% [5200703575653360771679605]) 0) 64 false) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [253685074137341611362455906150651]) 0) 39 false) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [726584217224186447762275575]) 0) 63 false) (.node 430 (sourceLit (List.headD (raw_ints% [9891622756755245056982638317096109]) 0) 38 true) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [365517135894117391888450900740700193]) 0) 36 false) .empty .empty)))

#time def treeG_J027_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [121864286027908589793066675]) 0) 59 false) treeG_J027_part058 treeG_J027_part059)

#time def treeG_J027_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [431315030145467930190154785236938041]) 0) 32 true) treeG_J027_part057 treeG_J027_part060)

#time def treeG_J027_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [8427404052757172027143278153265171251]) 0) 31 true) (.node 436 (sourceLit (List.headD (raw_ints% [17595804282916891319831874947394165809]) 0) 32 false) (.node 435 (sourceLit (List.headD (raw_ints% [386532192801183388965197685]) 0) 67 false) (.node 434 (sourceLit (List.headD (raw_ints% [2104888853635077370349961734353107857]) 0) 35 true) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [27497522432799122512561635]) 0) 70 true) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [65493730689408788940828295425]) 0) 51 false) (.node 439 (sourceLit (List.headD (raw_ints% [34495572292434037420935]) 0) 71 false) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [132112028928236955191726355]) 0) 60 false) .empty .empty)))

#time def treeG_J027_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [84306040278969778751481975]) 0) 60 false) (.node 462 (sourceLit (List.headD (raw_ints% [375046782583944169163725875]) 0) 58 false) (.node 461 (sourceLit (List.headD (raw_ints% [238188224662694832378388725]) 0) 59 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [27477589847872803923735055]) 0) 62 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [19307013154027669462938075]) 0) 62 false) (.node 465 (sourceLit (List.headD (raw_ints% [25757725569970898459019795]) 0) 62 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [762862040776441945379235]) 0) 67 false) .empty .empty)))

#time def treeG_J027_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [857405923185553313560241625]) 0) 57 false) treeG_J027_part062 treeG_J027_part063)

#time def treeG_J027_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [55177799108163035765034195]) 0) 71 false) (.node 472 (sourceLit (List.headD (raw_ints% [166120045420733519426293275]) 0) 67 false) (.node 470 (sourceLit (List.headD (raw_ints% [29533132748490507330902325]) 0) 66 true) (.node 469 (sourceLit (List.headD (raw_ints% [306457883197043244154501403228913]) 0) 41 false) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [11667310640522543108910617908719187]) 0) 40 true) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [1211622640669798859327107095]) 0) 66 true) (.node 473 (sourceLit (List.headD (raw_ints% [284781545926203181483802790538385483]) 0) 38 false) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [1308753177862114576136147892108030743]) 0) 37 true) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [5582404687947660250004315475]) 0) 55 false) (.node 478 (sourceLit (List.headD (raw_ints% [13763827730621008999216485]) 0) 72 true) (.node 477 (sourceLit (List.headD (raw_ints% [9356256633575714876304772217482105251]) 0) 34 false) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [3998044511305852048476561684014116605]) 0) 33 true) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [2271005816296869974217920625]) 0) 56 false) (.node 500 (sourceLit (List.headD (raw_ints% [331974779486364655171777125]) 0) 59 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [292537508925974836197207075]) 0) 59 false) .empty .empty))))

#time def treeG_J027_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [12407484308946337981945575]) 0) 63 false) treeG_J027_part064 treeG_J027_part065)

#time def treeG_J027_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [879799548898946722593464145]) 0) 65 true) treeG_J027_part061 treeG_J027_part066)

#time def treeG_J027_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [155873365424487963968348174161669]) 0) 39 false) (.node 506 (sourceLit (List.headD (raw_ints% [15356318418664176915660585]) 0) 63 false) (.node 505 (sourceLit (List.headD (raw_ints% [215359875087970525212861225]) 0) 59 false) (.node 504 (sourceLit (List.headD (raw_ints% [66372028494540655450897605]) 0) 61 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [97496411107248751409919225]) 0) 60 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [14794948887907936963454660768758717]) 0) 38 false) (.node 509 (sourceLit (List.headD (raw_ints% [112019028633127283830240725]) 0) 62 false) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [1199114341200034565056712775]) 0) 63 true) .empty .empty)))

#time def treeG_J027_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [101356007666092224192545340042308133361]) 0) 32 true) (.node 514 (sourceLit (List.headD (raw_ints% [6661393588454328274090806382967275585]) 0) 35 false) (.node 513 (sourceLit (List.headD (raw_ints% [2208759912264814878003810345]) 0) 65 false) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [399538708367745562073076195]) 0) 69 true) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [158127510189968610048019633632978855267]) 0) 31 false) (.node 517 (sourceLit (List.headD (raw_ints% [248208718865451265572698415]) 0) 70 false) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [55089806494776470034286875]) 0) 71 true) .empty .empty)))

#time def treeG_J027_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [738871076390838771373590673819714177]) 0) 36 true) treeG_J027_part068 treeG_J027_part069)

#time def treeG_J027_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [20307151462284878495938905]) 0) 63 false) (.node 543 (sourceLit (List.headD (raw_ints% [182627149534483620502266855]) 0) 60 false) (.node 542 (sourceLit (List.headD (raw_ints% [1520912251128981635890468875]) 0) 57 false) (.node 541 (sourceLit (List.headD (raw_ints% [425761334310034477965165525]) 0) 59 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [635663969925939870805779075]) 0) 58 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [9253422092452641352626705]) 0) 64 false) (.node 546 (sourceLit (List.headD (raw_ints% [138131822471859847361108925]) 0) 60 false) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [47866473871463399482136925]) 0) 61 false) .empty .empty)))

#time def treeG_J027_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [1308434168243245134341196254896485143]) 0) 37 true) (.node 551 (sourceLit (List.headD (raw_ints% [38129570168953023181275896586197091]) 0) 39 false) (.node 550 (sourceLit (List.headD (raw_ints% [348284090621051342477459325]) 0) 63 false) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [2528074704565902720467058975]) 0) 64 true) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [9278899944178557426363102167183337071]) 0) 36 false) (.node 554 (sourceLit (List.headD (raw_ints% [53443477389603339645795585]) 0) 72 false) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [509894306584071633603144585]) 0) 70 true) .empty .empty)))

#time def treeG_J027_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [457042400969598524340654632296157]) 0) 40 true) treeG_J027_part071 treeG_J027_part072)

#time def treeG_J027_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [3867592841576553622883832225]) 0) 56 false) treeG_J027_part070 treeG_J027_part073)

#time def treeG_J027_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [2068936371216144285969230775]) 0) 57 false) (.node 581 (sourceLit (List.headD (raw_ints% [5464179866856237271549743825]) 0) 56 false) (.node 559 (sourceLit (List.headD (raw_ints% [166123599212580314144972757001007088477]) 0) 32 false) (.node 558 (sourceLit (List.headD (raw_ints% [275736374326693283571131385]) 0) 71 false) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [558985159694094119733123975]) 0) 59 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [210152047418984672796458925]) 0) 60 false) (.node 584 (sourceLit (List.headD (raw_ints% [58127560519971482525684625]) 0) 62 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [25257984505905580076217225]) 0) 63 false) .empty .empty)))

#time def treeG_J027_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [1895682522442137250011631425]) 0) 63 false) (.node 589 (sourceLit (List.headD (raw_ints% [8019069345207985543512975]) 0) 65 true) (.node 588 (sourceLit (List.headD (raw_ints% [465113279312511771005853414451451]) 0) 39 false) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [18451288095664725158179897827127973]) 0) 38 true) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [592104327103839699808858665]) 0) 68 true) (.node 592 (sourceLit (List.headD (raw_ints% [1348944199094087142274005019198867633]) 0) 36 false) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [17128866934400289348820376422139156729]) 0) 35 true) .empty .empty)))

#time def treeG_J027_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [178767233836470943312298625]) 0) 60 false) treeG_J027_part075 treeG_J027_part076)

#time def treeG_J027_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [4727551132210825503718215]) 0) 66 false) (.node 599 (sourceLit (List.headD (raw_ints% [606562555148163037176549645]) 0) 71 false) (.node 597 (sourceLit (List.headD (raw_ints% [1267997332033594532778987585]) 0) 70 true) (.node 596 (sourceLit (List.headD (raw_ints% [398280805879806061836164609392174919633]) 0) 32 false) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [1118675677655917841609258709451157606171]) 0) 31 true) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [11761187817487828100964285]) 0) 65 false) (.node 622 (sourceLit (List.headD (raw_ints% [1971633807863627817829637475]) 0) 58 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [358318100322551103790862925]) 0) 60 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [115269460035263786918313505843451]) 0) 43 false) (.node 627 (sourceLit (List.headD (raw_ints% [2000570301681617340448815]) 0) 67 false) (.node 626 (sourceLit (List.headD (raw_ints% [282172272366109498231808925]) 0) 60 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [32725189991251885957540425]) 0) 63 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [7072607283077218542431974301665633]) 0) 42 true) (.node 630 (sourceLit (List.headD (raw_ints% [412436645382715226825563125]) 0) 63 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [138242413344001249077459075]) 0) 69 false) .empty .empty))))

#time def treeG_J027_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [1254634346601398996405805555]) 0) 69 false) treeG_J027_part077 treeG_J027_part078)

#time def treeG_J027_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [120068520933243653945154884477272343863]) 0) 33 true) treeG_J027_part074 treeG_J027_part079)

#time def treeG_J027_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [972888131041818985811706975]) 0) 57 false) treeG_J027_part067 treeG_J027_part080)

#time def treeG_J027_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [771866853180143908175059485]) 0) 72 true) (.node 636 (sourceLit (List.headD (raw_ints% [441132163296367657502237535]) 0) 72 false) (.node 635 (sourceLit (List.headD (raw_ints% [3300970859822355846897934823665311725]) 0) 39 true) (.node 634 (sourceLit (List.headD (raw_ints% [1019652146220666416975223345]) 0) 69 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [64793665851631214472664936733680907937]) 0) 36 false) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [5817598860238366985349319125]) 0) 57 false) (.node 639 (sourceLit (List.headD (raw_ints% [160599909608562269469278933306520586831]) 0) 35 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [130051444559833767089743935]) 0) 62 false) .empty .empty)))

#time def treeG_J027_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [48763328681667857044566375]) 0) 64 false) (.node 667 (sourceLit (List.headD (raw_ints% [385577310895748053151319225]) 0) 60 false) (.node 666 (sourceLit (List.headD (raw_ints% [50382833609467627983274215]) 0) 63 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [608934723071413264195916383917829]) 0) 39 false) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [2720555813207567703662757675]) 0) 63 true) (.node 670 (sourceLit (List.headD (raw_ints% [25828533537921607520951962201108837]) 0) 38 false) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [2254237931327971115705297729812068657]) 0) 36 true) .empty .empty)))

#time def treeG_J027_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [506484153226117534785266925]) 0) 60 false) treeG_J027_part082 treeG_J027_part083)

#time def treeG_J027_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [5265470292160315567859814660406735714139]) 0) 31 false) (.node 676 (sourceLit (List.headD (raw_ints% [1243329345994329158642035924250494721233]) 0) 32 true) (.node 675 (sourceLit (List.headD (raw_ints% [3293938639042731830356252245]) 0) 69 true) (.node 674 (sourceLit (List.headD (raw_ints% [38387893873098947561741986614901978937]) 0) 35 false) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [4797054638404535792796887865]) 0) 70 false) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [4384326458948162570185867425]) 0) 58 false) (.node 679 (sourceLit (List.headD (raw_ints% [3694029967868738669876787585]) 0) 71 true) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [92231035502147163059998215]) 0) 63 false) .empty .empty)))

#time def treeG_J027_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [607489960109386655003828625]) 0) 63 false) (.node 708 (sourceLit (List.headD (raw_ints% [254676550930740509321157525]) 0) 61 false) (.node 707 (sourceLit (List.headD (raw_ints% [34378271196014689259683695]) 0) 64 false) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [313220957210697031150591662829779]) 0) 40 true) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [7144313040215607674141448075]) 0) 64 true) (.node 711 (sourceLit (List.headD (raw_ints% [82409391802539355860407756614433901]) 0) 39 false) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [4911616298665303392320499003907421433]) 0) 37 true) .empty .empty)))

#time def treeG_J027_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [730796034086125571338724925]) 0) 60 false) treeG_J027_part085 treeG_J027_part086)

#time def treeG_J027_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [1145073980479844696118694965]) 0) 68 false) treeG_J027_part084 treeG_J027_part087)

#time def treeG_J027_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [6550269569028813723614046126858900408787]) 0) 32 false) (.node 717 (sourceLit (List.headD (raw_ints% [1761678672807378874423355418119941984729]) 0) 33 true) (.node 716 (sourceLit (List.headD (raw_ints% [5058467292228202460365202385]) 0) 70 true) (.node 715 (sourceLit (List.headD (raw_ints% [64795660751677794336925465204224472737]) 0) 36 false) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [6340788344764823609147006835]) 0) 71 false) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [134079237394826698136722215]) 0) 63 false) (.node 745 (sourceLit (List.headD (raw_ints% [3371358152495927500615333575]) 0) 59 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [1076014757276503089526130625]) 0) 60 false) .empty .empty)))

#time def treeG_J027_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [3572788200168600809471821835643011073]) 0) 36 false) (.node 750 (sourceLit (List.headD (raw_ints% [28334301195607183770156695503747069]) 0) 38 true) (.node 749 (sourceLit (List.headD (raw_ints% [59623236204069081142892025]) 0) 62 false) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [3935535733426341013670414925]) 0) 63 false) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [77680824262421374700305978646161350401]) 0) 35 true) (.node 753 (sourceLit (List.headD (raw_ints% [16304904884054365243091007795]) 0) 65 true) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [7623390892443754056544088865]) 0) 69 false) .empty .empty)))

#time def treeG_J027_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [1698152003177053859334457386854651]) 0) 39 false) treeG_J027_part089 treeG_J027_part090)

#time def treeG_J027_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [68483340488164696732617075]) 0) 66 true) (.node 786 (sourceLit (List.headD (raw_ints% [1320281059204900964638304325]) 0) 61 false) (.node 758 (sourceLit (List.headD (raw_ints% [19358899674619346563246658005366271591971]) 0) 31 true) (.node 757 (sourceLit (List.headD (raw_ints% [14913989222860940713527292635]) 0) 70 true) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [16375606657398385888170801255]) 0) 71 false) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [205334551586440645051243275]) 0) 63 false) (.node 787 (sourceLit (List.headD (raw_ints% [12462620774851501109629815]) 0) 67 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [1005686480193875445242524524842215]) 0) 41 false) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [33622713897658454147842354275]) 0) 66 true) (.node 792 (sourceLit (List.headD (raw_ints% [1384981096705243585976482875]) 0) 67 false) (.node 791 (sourceLit (List.headD (raw_ints% [55371846499073269815282226059090485]) 0) 40 true) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [4242202249416952100896160419775216253]) 0) 38 false) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [6340929092335978258454645625]) 0) 71 false) (.node 795 (sourceLit (List.headD (raw_ints% [71238242507049584518615721925192911569]) 0) 37 true) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [2539234581427698725923503114452809916773]) 0) 34 false) .empty .empty))))

#time def treeG_J027_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [3316790490048018577423650810785677848817]) 0) 32 false) treeG_J027_part091 treeG_J027_part092)

#time def treeG_J027_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [1082363063350255556546959155]) 0) 70 false) treeG_J027_part088 treeG_J027_part093)

#time def treeG_J027_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [44425284878709190894037087901222509]) 0) 38 false) (.node 828 (sourceLit (List.headD (raw_ints% [4992666578127618205961513374586629]) 0) 39 false) (.node 827 (sourceLit (List.headD (raw_ints% [4205109479543100769027086675]) 0) 60 false) (.node 799 (sourceLit (List.headD (raw_ints% [12954584621824080143430352066112586000379]) 0) 33 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [761714970141693499062081075]) 0) 62 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [5344687288138945443560853069533906593]) 0) 36 true) (.node 831 (sourceLit (List.headD (raw_ints% [5031269181236976161392288125]) 0) 63 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [27384753657696313930902870795]) 0) 65 false) .empty .empty)))

#time def treeG_J027_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [59986652977462526178022707836611230260339]) 0) 31 false) (.node 836 (sourceLit (List.headD (raw_ints% [7876038010499191986615057013998024189233]) 0) 32 true) (.node 835 (sourceLit (List.headD (raw_ints% [64116277467433470374018709735]) 0) 67 true) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [40277705592204853747345875135]) 0) 70 false) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [3383771273197338188822113575]) 0) 61 false) (.node 839 (sourceLit (List.headD (raw_ints% [58885161792649914533519400195]) 0) 71 true) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [2981293617739867315476464324902199]) 0) 40 false) .empty .empty)))

#time def treeG_J027_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [145556060253092608314644545362564810449]) 0) 35 false) treeG_J027_part095 treeG_J027_part096)

#time def treeG_J027_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [61532483159830618070020174605]) 0) 71 false) (.node 874 (sourceLit (List.headD (raw_ints% [30503733777677384039372612535]) 0) 67 false) (.node 872 (sourceLit (List.headD (raw_ints% [16111117954878924849204151125]) 0) 64 true) (.node 871 (sourceLit (List.headD (raw_ints% [155168977876855730524601540019403479]) 0) 39 false) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [13829091786972849645353173909084339099]) 0) 37 true) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [114843710206121296441655874735]) 0) 68 true) (.node 875 (sourceLit (List.headD (raw_ints% [288032545267191777351875989212950633587]) 0) 36 false) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [12954507173354589438462063242903644022779]) 0) 33 true) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [7650432569330998307238323475]) 0) 63 false) (.node 909 (sourceLit (List.headD (raw_ints% [655514075763911172440008125]) 0) 64 false) (.node 879 (sourceLit (List.headD (raw_ints% [85895822221110686464883411968836402261097]) 0) 32 false) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [20574935936790252370225373302004917]) 0) 38 true) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [1359245987892976211878344435]) 0) 70 true) (.node 912 (sourceLit (List.headD (raw_ints% [7827390934168637131954477709844362257]) 0) 36 false) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [256188794548875405477469936635239523241]) 0) 35 true) .empty .empty))))

#time def treeG_J027_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [1309581694047011072923017675]) 0) 63 false) treeG_J027_part097 treeG_J027_part098)

#time def treeG_J027_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [1312474609008633616837014825]) 0) 63 false) (.node 918 (sourceLit (List.headD (raw_ints% [163622710364299241685719213779840382442571]) 0) 31 true) (.node 917 (sourceLit (List.headD (raw_ints% [195399121390531003936347625005]) 0) 69 true) (.node 916 (sourceLit (List.headD (raw_ints% [17093079459049328861875088668812444464017]) 0) 32 false) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [181950128112311150673559749405]) 0) 71 false) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [2970193815526240394555309325]) 0) 67 false) (.node 951 (sourceLit (List.headD (raw_ints% [43935978453411495723706728330352099]) 0) 41 true) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [5414120680285371694326912904732175339]) 0) 39 false) .empty .empty)))

#time def treeG_J027_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [318464087710192240076387974215]) 0) 70 true) (.node 956 (sourceLit (List.headD (raw_ints% [59991863807227383723604952385]) 0) 70 false) (.node 955 (sourceLit (List.headD (raw_ints% [136055334954016795707336481462047539207]) 0) 38 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [7511896658100979575084287977929022121699]) 0) 35 false) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [8407177767098145242068687065]) 0) 68 false) (.node 959 (sourceLit (List.headD (raw_ints% [62379633146352482037650656437169196175917]) 0) 34 true) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [429440656318007299695931149586669134089]) 0) 35 false) .empty .empty)))

#time def treeG_J027_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [52251669583965003429426123495]) 0) 67 true) treeG_J027_part100 treeG_J027_part101)

#time def treeG_J027_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [64555748965567397012751310207670617969309]) 0) 33 true) (.node 999 (sourceLit (List.headD (raw_ints% [125103553955625847687486930905]) 0) 73 true) (.node 997 (sourceLit (List.headD (raw_ints% [435366576619440538830767434545]) 0) 69 false) (.node 996 (sourceLit (List.headD (raw_ints% [34508162333163478712414158295954529482513]) 0) 32 true) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [404003403423530588088416429073569090336939]) 0) 31 false) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [973661996134074482525277075434859290917]) 0) 36 false) (.node 1034 (sourceLit (List.headD (raw_ints% [85880380652357584397700871755]) 0) 67 false) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [469594539419627780206035991335]) 0) 68 true) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [65665346209453862153223024709870026791857]) 0) 32 false) (.node 1039 (sourceLit (List.headD (raw_ints% [653521936008940516239019054822245875040607]) 0) 32 false) (.node 1038 (sourceLit (List.headD (raw_ints% [94228833041204097363394426095]) 0) 73 false) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [401387845495433414107017925305]) 0) 67 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [920449395148069764190426910734934034091411]) 0) 31 true) (.node 1077 (sourceLit (List.headD (raw_ints% [113120139504883539879600428235]) 0) 72 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [313561220038034042414275783095]) 0) 73 false) .empty .empty))))

#time def treeG_J027_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [229627084190718245311616181795]) 0) 67 true) treeG_J027_part102 treeG_J027_part103)

#time def treeG_J027_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [125123745022788238452763934805]) 0) 67 false) treeG_J027_part099 treeG_J027_part104)

#time def treeG_J027_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [10627388783812882161337149735]) 0) 72 true) treeG_J027_part094 treeG_J027_part105)

#time def treeG_J027_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [332172295917166534576900159261919097]) 0) 40 false) treeG_J027_part081 treeG_J027_part106)

#time def treeG_J027_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [408524311277454941695594125]) 0) 57 false) treeG_J027_part054 treeG_J027_part107)

#time def treeG_J027 : IntSourceTree := treeG_J027_part108

#time def treeG_J028_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [49982007868896567286376168685]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [102532770602226866064352716765]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [345235082895672760449450116325]) 0) 42 false) (.node 7 (sourceLit (List.headD (raw_ints% [844960786657838326976898599775]) 0) 43 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [59531262201590930031295389375]) 0) 44 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [12219863182774840792594525305]) 0) 49 false) (.node 12 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 45 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)))

#time def treeG_J028_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [180748506514840805363756505]) 0) 55 false) (.node 17 (sourceLit (List.headD (raw_ints% [367577311764174794778727725]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 50 true) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [308553642015650233810909875]) 0) 52 true) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [44494361713907595394053435]) 0) 57 false) (.node 20 (sourceLit (List.headD (raw_ints% [261604016136927550190104875]) 0) 53 true) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [51175878753474289187980875]) 0) 56 true) .empty .empty)))

#time def treeG_J028_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [5989023764890490261343122775]) 0) 50 false) treeG_J028_part000 treeG_J028_part001)

#time def treeG_J028_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [22353245451983305317329325]) 0) 60 true) (.node 26 (sourceLit (List.headD (raw_ints% [17013079142940938631345225]) 0) 59 true) (.node 25 (sourceLit (List.headD (raw_ints% [2704314989835557488415025]) 0) 61 false) (.node 24 (sourceLit (List.headD (raw_ints% [39948122786965592776991775]) 0) 57 true) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 62 false) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 64 false) (.node 29 (sourceLit (List.headD (raw_ints% [74784243951294266619696380897531]) 0) 39 true) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [63971280753034167080149554555131]) 0) 38 true) .empty .empty)))

#time def treeG_J028_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [9762622920262217819385]) 0) 69 false) (.node 34 (sourceLit (List.headD (raw_ints% [19719392562631586289465]) 0) 68 false) (.node 33 (sourceLit (List.headD (raw_ints% [170985526391502308583261257841393]) 0) 36 true) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [257917044682273295516344642407655]) 0) 35 true) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [1208792403731037554715]) 0) 72 false) (.node 37 (sourceLit (List.headD (raw_ints% [1647704973977997850529426193570385]) 0) 32 true) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [2720346090599317304961204687099333]) 0) 31 true) .empty .empty)))

#time def treeG_J028_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [79696586555044589955825]) 0) 66 false) treeG_J028_part003 treeG_J028_part004)

#time def treeG_J028_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [21928913702388077557957785]) 0) 58 false) treeG_J028_part002 treeG_J028_part005)

#time def treeG_J028_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 46 false) (.node 51 (sourceLit (List.headD (raw_ints% [59531262201590930031295389375]) 0) 45 false) (.node 50 (sourceLit (List.headD (raw_ints% [102532770602226866064352716765]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [345235082895672760449450116325]) 0) 43 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [49982007868896567286376168685]) 0) 48 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 54 (sourceLit (List.headD (raw_ints% [12219863182774840792594525305]) 0) 50 false) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [5989023764890490261343122775]) 0) 51 false) .empty .empty)))

#time def treeG_J028_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [261604016136927550190104875]) 0) 54 true) (.node 59 (sourceLit (List.headD (raw_ints% [308553642015650233810909875]) 0) 53 true) (.node 58 (sourceLit (List.headD (raw_ints% [367577311764174794778727725]) 0) 55 false) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [180748506514840805363756505]) 0) 56 false) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [51175878753474289187980875]) 0) 57 true) (.node 62 (sourceLit (List.headD (raw_ints% [44494361713907595394053435]) 0) 58 false) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [21928913702388077557957785]) 0) 59 false) .empty .empty)))

#time def treeG_J028_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 51 true) treeG_J028_part007 treeG_J028_part008)

#time def treeG_J028_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [79696586555044589955825]) 0) 67 false) (.node 69 (sourceLit (List.headD (raw_ints% [22353245451983305317329325]) 0) 61 true) (.node 67 (sourceLit (List.headD (raw_ints% [17013079142940938631345225]) 0) 60 true) (.node 66 (sourceLit (List.headD (raw_ints% [2704314989835557488415025]) 0) 62 false) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 63 false) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 65 false) (.node 70 (sourceLit (List.headD (raw_ints% [74784243951294266619696380897531]) 0) 40 true) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [63971280753034167080149554555131]) 0) 39 true) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [9762622920262217819385]) 0) 70 false) (.node 75 (sourceLit (List.headD (raw_ints% [19719392562631586289465]) 0) 69 false) (.node 74 (sourceLit (List.headD (raw_ints% [170985526391502308583261257841393]) 0) 37 true) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [257917044682273295516344642407655]) 0) 36 true) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [1208792403731037554715]) 0) 73 false) (.node 78 (sourceLit (List.headD (raw_ints% [1647704973977997850529426193570385]) 0) 33 true) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [639895245453384594848193166245]) 0) 45 false) .empty .empty))))

#time def treeG_J028_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [39948122786965592776991775]) 0) 58 true) treeG_J028_part009 treeG_J028_part010)

#time def treeG_J028_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [844960786657838326976898599775]) 0) 44 false) treeG_J028_part006 treeG_J028_part011)

#time def treeG_J028_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [18450702600659191323845927835]) 0) 50 false) (.node 93 (sourceLit (List.headD (raw_ints% [9440536171530431623445410845]) 0) 51 false) (.node 92 (sourceLit (List.headD (raw_ints% [103457242078492975491280336875]) 0) 45 false) (.node 91 (sourceLit (List.headD (raw_ints% [155083533335557164842329264845]) 0) 47 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 47 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [4518714517833791082228211875]) 0) 52 false) (.node 96 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 50 false) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [62908994974064610776981625]) 0) 54 true) .empty .empty)))

#time def treeG_J028_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [67059809725427113230149085]) 0) 58 false) (.node 101 (sourceLit (List.headD (raw_ints% [68127072400466604984851535]) 0) 58 false) (.node 100 (sourceLit (List.headD (raw_ints% [355503267894372917431714875]) 0) 53 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [159252258629978971814143125]) 0) 55 true) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [16520283722716962581127735]) 0) 60 false) (.node 104 (sourceLit (List.headD (raw_ints% [62403634719982985598969975]) 0) 57 true) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [11467521822012327072823275]) 0) 60 true) .empty .empty)))

#time def treeG_J028_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [554406117013508784193698945]) 0) 55 false) treeG_J028_part013 treeG_J028_part014)

#time def treeG_J028_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [121277414322893941237125]) 0) 67 false) (.node 110 (sourceLit (List.headD (raw_ints% [23642251112786635207049625]) 0) 62 true) (.node 109 (sourceLit (List.headD (raw_ints% [119580805772657536140676090030331]) 0) 39 false) (.node 108 (sourceLit (List.headD (raw_ints% [11672912833898571945361125]) 0) 60 true) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [534302670857319965877421492625117]) 0) 38 true) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [7497149249051625458295]) 0) 71 false) (.node 113 (sourceLit (List.headD (raw_ints% [852554965657044364699131615040703]) 0) 36 true) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [1109967166449745173149745420323489]) 0) 35 true) .empty .empty)))

#time def treeG_J028_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [434829704248930862719487732715]) 0) 46 false) (.node 118 (sourceLit (List.headD (raw_ints% [7345038112800142709955]) 0) 71 false) (.node 117 (sourceLit (List.headD (raw_ints% [6605640455854747605993602363474575]) 0) 32 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [10461293701224665499274204861463747]) 0) 31 true) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [3284422670833143673623534255]) 0) 53 false) (.node 131 (sourceLit (List.headD (raw_ints% [226172558492490900386859337575]) 0) 45 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [10981494969225511364996236875]) 0) 49 false) .empty .empty)))

#time def treeG_J028_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [29676162205000954759545]) 0) 69 false) treeG_J028_part016 treeG_J028_part017)

#time def treeG_J028_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [4073588402410523305334025]) 0) 62 false) treeG_J028_part015 treeG_J028_part018)

#time def treeG_J028_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [56917662119391790702983375]) 0) 53 false) (.node 137 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 52 false) (.node 136 (sourceLit (List.headD (raw_ints% [3115419708942175265625701265]) 0) 53 false) (.node 135 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 48 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [3048405270777091903113300975]) 0) 53 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [5868703234840335452600625]) 0) 58 true) (.node 140 (sourceLit (List.headD (raw_ints% [46707201312333497353742805]) 0) 59 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [91759783087025614575649635]) 0) 58 false) .empty .empty)))

#time def treeG_J028_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [5921964501083715514301325]) 0) 60 true) (.node 145 (sourceLit (List.headD (raw_ints% [2806938991627174102747275]) 0) 61 true) (.node 144 (sourceLit (List.headD (raw_ints% [11282724005759758918047825]) 0) 61 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [11111653743045847604297685]) 0) 61 false) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 64 false) (.node 148 (sourceLit (List.headD (raw_ints% [171159176571870727114875]) 0) 67 false) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [97182524861975901380186235463931]) 0) 41 false) .empty .empty)))

#time def treeG_J028_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [56900501123030393438181375]) 0) 56 true) treeG_J028_part020 treeG_J028_part021)

#time def treeG_J028_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [4927453305338067600525]) 0) 72 false) (.node 155 (sourceLit (List.headD (raw_ints% [40257801429781417376895]) 0) 69 false) (.node 153 (sourceLit (List.headD (raw_ints% [162858242090743292518425]) 0) 67 false) (.node 152 (sourceLit (List.headD (raw_ints% [235165695052142899398635969034993]) 0) 40 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [340784719632771028057935178599655]) 0) 38 true) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [155574525662021382345]) 0) 77 false) (.node 156 (sourceLit (List.headD (raw_ints% [426025060883735938816700388957917]) 0) 37 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [2478967740938374877732088084952095]) 0) 34 true) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [72246677429115206348659453125]) 0) 47 false) (.node 172 (sourceLit (List.headD (raw_ints% [348887874906488825282438338275]) 0) 45 false) (.node 171 (sourceLit (List.headD (raw_ints% [139873085456686848938579233935]) 0) 48 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [16834845195134717765542863195]) 0) 51 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [14484903080865067217472769125]) 0) 49 false) (.node 175 (sourceLit (List.headD (raw_ints% [32633860406034580078528308315]) 0) 50 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [7942964317934909980274593185]) 0) 52 false) .empty .empty))))

#time def treeG_J028_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [24931256773589965096769925]) 0) 63 true) treeG_J028_part022 treeG_J028_part023)

#time def treeG_J028_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [25542281503346885701187118075]) 0) 50 false) treeG_J028_part019 treeG_J028_part024)

#time def treeG_J028_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [142851910347040915209077363475]) 0) 45 false) treeG_J028_part012 treeG_J028_part025)

#time def treeG_J028_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [116459756448624115921150185]) 0) 58 false) (.node 181 (sourceLit (List.headD (raw_ints% [118701732848867384430119685]) 0) 58 false) (.node 180 (sourceLit (List.headD (raw_ints% [469338592133156498837681625]) 0) 53 false) (.node 179 (sourceLit (List.headD (raw_ints% [1939593036750074334725903085]) 0) 54 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [65353006872533604572533125]) 0) 55 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [28610612300322073091063565]) 0) 60 false) (.node 184 (sourceLit (List.headD (raw_ints% [687891699619074020098575]) 0) 60 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [239765855503630661834175]) 0) 60 false) .empty .empty)))

#time def treeG_J028_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [2089223068648934387960401260048013]) 0) 38 false) (.node 189 (sourceLit (List.headD (raw_ints% [27690422549348265328410020014331]) 0) 39 true) (.node 188 (sourceLit (List.headD (raw_ints% [171016168268859083241525]) 0) 60 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [34322583730871368579017825]) 0) 62 false) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [6672747276011528416057219394079073]) 0) 36 true) (.node 192 (sourceLit (List.headD (raw_ints% [25901476088173116626666925]) 0) 64 true) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [102881048098330288852065]) 0) 68 false) .empty .empty)))

#time def treeG_J028_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [1759516335158831074740915]) 0) 64 false) treeG_J028_part027 treeG_J028_part028)

#time def treeG_J028_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [87322322723356550160602685855]) 0) 49 false) (.node 198 (sourceLit (List.headD (raw_ints% [12568501171938594230205]) 0) 71 false) (.node 197 (sourceLit (List.headD (raw_ints% [20659963440704352478275222529832113]) 0) 32 true) (.node 196 (sourceLit (List.headD (raw_ints% [50839440654561879994245]) 0) 69 false) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [29202190153789332544439204497769773]) 0) 31 true) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [41797099277191985360984334705]) 0) 50 false) (.node 213 (sourceLit (List.headD (raw_ints% [261035915152684734362468443275]) 0) 46 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [28320697552213160888674505625]) 0) 49 false) .empty .empty)))

#time def treeG_J028_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [1192277815752738377066018205]) 0) 55 false) (.node 218 (sourceLit (List.headD (raw_ints% [2447279523578909038580646105]) 0) 54 false) (.node 217 (sourceLit (List.headD (raw_ints% [12244144593217432509797423625]) 0) 50 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [1315097561600684006242615875]) 0) 53 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [145643682610709154284589735]) 0) 58 false) (.node 221 (sourceLit (List.headD (raw_ints% [563237843890601866079291625]) 0) 54 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [30563376998890999502678625]) 0) 58 false) .empty .empty)))

#time def treeG_J028_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [20172181570265879016025503255]) 0) 51 false) treeG_J028_part030 treeG_J028_part031)

#time def treeG_J028_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [4342588347674591275777217437270991]) 0) 35 true) treeG_J028_part029 treeG_J028_part032)

#time def treeG_J028_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [10851348786353592455209725]) 0) 61 true) (.node 227 (sourceLit (List.headD (raw_ints% [6401496212090976837969675]) 0) 60 false) (.node 226 (sourceLit (List.headD (raw_ints% [2187369819659528185845735]) 0) 64 false) (.node 225 (sourceLit (List.headD (raw_ints% [1747415345623124061422925]) 0) 62 false) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [1074879628871348166281415]) 0) 65 false) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [29626920252230666837893875]) 0) 64 false) (.node 230 (sourceLit (List.headD (raw_ints% [222055472273300068088782490942193]) 0) 40 true) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [2559554458753220186757673198117999]) 0) 39 false) .empty .empty)))

#time def treeG_J028_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [30925901369823143054085]) 0) 70 false) (.node 235 (sourceLit (List.headD (raw_ints% [31311623334274435737585]) 0) 70 false) (.node 234 (sourceLit (List.headD (raw_ints% [5991177836745986359941349036879763]) 0) 37 true) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [3490538225907119398143816659355157]) 0) 36 true) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [477565491662532914355]) 0) 76 false) (.node 238 (sourceLit (List.headD (raw_ints% [15702027958827602722811046359927923]) 0) 33 true) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [53652632333087114629516959465]) 0) 50 false) .empty .empty)))

#time def treeG_J028_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [26552909056536089796740625]) 0) 65 true) treeG_J028_part034 treeG_J028_part035)

#time def treeG_J028_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [124471209254517065376689625]) 0) 57 false) (.node 258 (sourceLit (List.headD (raw_ints% [9500114145777280915906225125]) 0) 51 false) (.node 256 (sourceLit (List.headD (raw_ints% [42156492023561254559876242125]) 0) 49 false) (.node 255 (sourceLit (List.headD (raw_ints% [50960338148349390643440361095]) 0) 50 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [6114608626165484517875455035]) 0) 53 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [2160856531068211513647550125]) 0) 53 false) (.node 259 (sourceLit (List.headD (raw_ints% [2954966010407743742435389125]) 0) 54 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [717470884357268839345539465]) 0) 56 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [13739556909481361829549225]) 0) 60 false) (.node 264 (sourceLit (List.headD (raw_ints% [29187593599652851462481475]) 0) 59 false) (.node 263 (sourceLit (List.headD (raw_ints% [174827608772794192648029285]) 0) 58 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [5339781015657875894736915]) 0) 63 false) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [12974008592450812759180875]) 0) 60 false) (.node 267 (sourceLit (List.headD (raw_ints% [2615223304160225296950555]) 0) 64 false) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [171958324209943820503667749939451]) 0) 39 false) .empty .empty))))

#time def treeG_J028_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [94394618861784764006904495075]) 0) 48 false) treeG_J028_part036 treeG_J028_part037)

#time def treeG_J028_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [71328860425585080248958885]) 0) 59 false) treeG_J028_part033 treeG_J028_part038)

#time def treeG_J028_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [43586834346293299603753574857767113]) 0) 35 true) (.node 273 (sourceLit (List.headD (raw_ints% [47625618616063051404179990563967057]) 0) 36 false) (.node 272 (sourceLit (List.headD (raw_ints% [85155316592634450302454675]) 0) 64 false) (.node 271 (sourceLit (List.headD (raw_ints% [3865666846835334932670661187585557]) 0) 38 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [26964433248929410952148885]) 0) 66 true) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [91037259788323468262326910569532911]) 0) 32 true) (.node 276 (sourceLit (List.headD (raw_ints% [74407052682535862956095]) 0) 69 false) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [2294675024735568602985]) 0) 74 false) .empty .empty)))

#time def treeG_J028_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [7478086857585955512519704625]) 0) 52 false) (.node 295 (sourceLit (List.headD (raw_ints% [33036960654785801559114994725]) 0) 50 false) (.node 294 (sourceLit (List.headD (raw_ints% [65508165388982243898049584225]) 0) 50 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [1924259786130219476713428615]) 0) 55 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [6869919022575912903420993375]) 0) 52 false) (.node 298 (sourceLit (List.headD (raw_ints% [1833664551293287739647404465]) 0) 55 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [220336024331875670671171365]) 0) 58 false) .empty .empty)))

#time def treeG_J028_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [96414033516831489238049166381653611]) 0) 31 true) treeG_J028_part040 treeG_J028_part041)

#time def treeG_J028_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [788102798999586927222795]) 0) 66 false) (.node 304 (sourceLit (List.headD (raw_ints% [1617167942925142381235475]) 0) 65 false) (.node 303 (sourceLit (List.headD (raw_ints% [11738479031953258234251375]) 0) 61 false) (.node 302 (sourceLit (List.headD (raw_ints% [426183519135850530776359995]) 0) 57 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [22197932217160355216789775]) 0) 60 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [385085918822219282667285]) 0) 67 false) (.node 307 (sourceLit (List.headD (raw_ints% [21077617606871746821128775]) 0) 60 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [2978169672350550651798825]) 0) 64 false) .empty .empty)))

#time def treeG_J028_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [13404199113202259441030334900211705]) 0) 39 false) (.node 312 (sourceLit (List.headD (raw_ints% [1606305326397138779857083596425889]) 0) 41 true) (.node 311 (sourceLit (List.headD (raw_ints% [26106943255421573677503825]) 0) 65 true) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [27927056412292635024798825]) 0) 67 false) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [10024074030096545051402439549602989]) 0) 38 true) (.node 315 (sourceLit (List.headD (raw_ints% [27214926235603606438049565]) 0) 67 true) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [21740575656356359951005]) 0) 71 false) .empty .empty)))

#time def treeG_J028_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [98503449120810972148112560220411]) 0) 42 false) treeG_J028_part043 treeG_J028_part044)

#time def treeG_J028_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [399404671794402411892064625]) 0) 56 false) treeG_J028_part042 treeG_J028_part045)

#time def treeG_J028_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [20412233284566541134172593375]) 0) 51 false) (.node 336 (sourceLit (List.headD (raw_ints% [89991350595581951676583736775]) 0) 49 false) (.node 335 (sourceLit (List.headD (raw_ints% [80055992629615097152658807355]) 0) 50 false) (.node 319 (sourceLit (List.headD (raw_ints% [1339544041410502774275]) 0) 75 false) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [9279469662876271295831973885]) 0) 53 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [2354531245753850694886721625]) 0) 54 false) (.node 339 (sourceLit (List.headD (raw_ints% [4379692194765407216154228735]) 0) 54 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [1045217310297736526023831455]) 0) 56 false) .empty .empty)))

#time def treeG_J028_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [30656307524839348604030325]) 0) 60 false) (.node 344 (sourceLit (List.headD (raw_ints% [64720238655973214411529525]) 0) 59 false) (.node 343 (sourceLit (List.headD (raw_ints% [125677955181528169064165355]) 0) 59 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [7597562527743263155146885]) 0) 63 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [29181226621292680883076675]) 0) 60 false) (.node 347 (sourceLit (List.headD (raw_ints% [3689599087836470120831805]) 0) 64 false) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [34783104226499011645903340574469]) 0) 39 false) .empty .empty)))

#time def treeG_J028_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [34366682817485668314421875]) 0) 60 false) treeG_J028_part047 treeG_J028_part048)

#time def treeG_J028_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [12561875557414085539065]) 0) 72 false) (.node 354 (sourceLit (List.headD (raw_ints% [138672658898099951051344185]) 0) 66 false) (.node 352 (sourceLit (List.headD (raw_ints% [189583089614320745012469975]) 0) 64 true) (.node 351 (sourceLit (List.headD (raw_ints% [7017777218701286041410263114638709]) 0) 38 false) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [150429159505479933315033340735223953]) 0) 36 true) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [27363740340968678163961755]) 0) 68 true) (.node 355 (sourceLit (List.headD (raw_ints% [472521205968765601716724291664541673]) 0) 35 false) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [1192044216064034298317185351779649681]) 0) 32 true) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [5612140560289695816537164955]) 0) 54 false) (.node 376 (sourceLit (List.headD (raw_ints% [49267836051531585525243949515]) 0) 51 false) (.node 359 (sourceLit (List.headD (raw_ints% [506267821119135435078077747295186293]) 0) 31 true) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [60079003165238129626504918275]) 0) 50 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [2617004000110401850784857815]) 0) 55 false) (.node 379 (sourceLit (List.headD (raw_ints% [105799330171801783052746875]) 0) 59 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [1555721902165045871102592375]) 0) 55 false) .empty .empty))))

#time def treeG_J028_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [34499644948014683124309075]) 0) 63 false) treeG_J028_part049 treeG_J028_part050)

#time def treeG_J028_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [18833807957373966384878966052401247]) 0) 35 true) treeG_J028_part046 treeG_J028_part051)

#time def treeG_J028_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [22586966258612480517113775]) 0) 63 true) treeG_J028_part039 treeG_J028_part052)

#time def treeG_J028_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [686007611860037898472799625]) 0) 53 false) treeG_J028_part026 treeG_J028_part053)

#time def treeG_J028_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [40234997442806950386931875]) 0) 60 false) (.node 385 (sourceLit (List.headD (raw_ints% [21261153219406429597369875]) 0) 61 false) (.node 384 (sourceLit (List.headD (raw_ints% [73928581007923612864630155]) 0) 60 false) (.node 383 (sourceLit (List.headD (raw_ints% [5657050946383102520042625]) 0) 63 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [4445151331744915446255705]) 0) 64 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [5355869242488275668686075]) 0) 61 false) (.node 388 (sourceLit (List.headD (raw_ints% [2149255412547592990162665]) 0) 65 false) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [359230692256744876946546900307175]) 0) 40 true) .empty .empty)))

#time def treeG_J028_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [82943792566851778744696875]) 0) 68 false) (.node 393 (sourceLit (List.headD (raw_ints% [301291315263491285111665275]) 0) 65 true) (.node 392 (sourceLit (List.headD (raw_ints% [13442998524289841160838597500342265]) 0) 39 false) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [204045955958288971079154680336070773]) 0) 37 true) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [27450702643594103603765775]) 0) 69 true) (.node 396 (sourceLit (List.headD (raw_ints% [512617502089151781922334049862953629]) 0) 36 false) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [1116708984234538432777669487570044693]) 0) 33 true) .empty .empty)))

#time def treeG_J028_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [86713531458857830479316725]) 0) 64 false) treeG_J028_part055 treeG_J028_part056)

#time def treeG_J028_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [196473336226583165595128295]) 0) 59 false) (.node 419 (sourceLit (List.headD (raw_ints% [6844588925813984416920101175]) 0) 54 false) (.node 418 (sourceLit (List.headD (raw_ints% [9916692470167897123083081225]) 0) 53 false) (.node 417 (sourceLit (List.headD (raw_ints% [30708896725779042933580001745]) 0) 52 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [4416625885241463420489078375]) 0) 54 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [183838940399414828559570375]) 0) 59 false) (.node 422 (sourceLit (List.headD (raw_ints% [1005854977085275178071842375]) 0) 56 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [116305391628286066229834475]) 0) 59 false) .empty .empty)))

#time def treeG_J028_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [253685074137341611362455906150651]) 0) 39 false) (.node 427 (sourceLit (List.headD (raw_ints% [5200703575653360771679605]) 0) 64 false) (.node 426 (sourceLit (List.headD (raw_ints% [54388305352786369785449175]) 0) 60 false) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [51288768264321219890787075]) 0) 60 false) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [9891622756755245056982638317096109]) 0) 38 true) (.node 430 (sourceLit (List.headD (raw_ints% [63643420653541090579932075]) 0) 62 true) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [363010152532036405971103425]) 0) 64 false) .empty .empty)))

#time def treeG_J028_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [43538330896950560244042615]) 0) 61 false) treeG_J028_part058 treeG_J028_part059)

#time def treeG_J028_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [7203699391772074441965]) 0) 73 false) treeG_J028_part057 treeG_J028_part060)

#time def treeG_J028_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [27500950145823759945922035]) 0) 70 true) (.node 436 (sourceLit (List.headD (raw_ints% [193251325474672235653355505]) 0) 68 false) (.node 435 (sourceLit (List.headD (raw_ints% [2104888853635077370349961734353107857]) 0) 35 true) (.node 434 (sourceLit (List.headD (raw_ints% [109990993540397809040752365]) 0) 68 true) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [17595804282916891319831874947394165809]) 0) 32 false) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [19484615605199651300505671835]) 0) 53 false) (.node 439 (sourceLit (List.headD (raw_ints% [8427404052757172027143278153265171251]) 0) 31 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [6531113904670240065395181225]) 0) 54 false) .empty .empty)))

#time def treeG_J028_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [27477589847872803923735055]) 0) 62 false) (.node 462 (sourceLit (List.headD (raw_ints% [238188224662694832378388725]) 0) 59 false) (.node 461 (sourceLit (List.headD (raw_ints% [178806498942276096836655375]) 0) 59 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [643803716516756616789114375]) 0) 57 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [25757725569970898459019795]) 0) 62 false) (.node 465 (sourceLit (List.headD (raw_ints% [73783085189473207035094725]) 0) 60 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [68541613262765789183966475]) 0) 60 false) .empty .empty)))

#time def treeG_J028_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [132112028928236955191726355]) 0) 60 false) treeG_J028_part062 treeG_J028_part063)

#time def treeG_J028_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [1308753177862114576136147892108030743]) 0) 37 true) (.node 472 (sourceLit (List.headD (raw_ints% [11667310640522543108910617908719187]) 0) 40 true) (.node 470 (sourceLit (List.headD (raw_ints% [306457883197043244154501403228913]) 0) 41 false) (.node 469 (sourceLit (List.headD (raw_ints% [5741612377729118027762625]) 0) 64 false) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [237070483571256751538565525]) 0) 63 true) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [284781545926203181483802790538385483]) 0) 38 false) (.node 473 (sourceLit (List.headD (raw_ints% [166075366948881922770692175]) 0) 67 false) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [302925779647647396826201605]) 0) 68 true) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [3160006669846416720896392665]) 0) 56 false) (.node 478 (sourceLit (List.headD (raw_ints% [9356256633575714876304772217482105251]) 0) 34 false) (.node 477 (sourceLit (List.headD (raw_ints% [431058648668488943861565]) 0) 78 false) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [27529764943390848243689895]) 0) 71 true) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [331974779486364655171777125]) 0) 59 false) (.node 500 (sourceLit (List.headD (raw_ints% [8645601924099016710301284075]) 0) 54 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [1855049005991142371314643625]) 0) 56 false) .empty .empty))))

#time def treeG_J028_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [762862040776441945379235]) 0) 67 false) treeG_J028_part064 treeG_J028_part065)

#time def treeG_J028_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [365517135894117391888450900740700193]) 0) 36 false) treeG_J028_part061 treeG_J028_part066)

#time def treeG_J028_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [85794458261210358477145875]) 0) 60 false) (.node 506 (sourceLit (List.headD (raw_ints% [93177865026160044284740275]) 0) 60 false) (.node 505 (sourceLit (List.headD (raw_ints% [66372028494540655450897605]) 0) 61 false) (.node 504 (sourceLit (List.headD (raw_ints% [411192933260184484329445425]) 0) 58 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [15356318418664176915660585]) 0) 63 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [109576319675374034802033075]) 0) 62 false) (.node 509 (sourceLit (List.headD (raw_ints% [155873365424487963968348174161669]) 0) 39 false) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [14794948887907936963454660768758717]) 0) 38 false) .empty .empty)))

#time def treeG_J028_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [799102884769967029305758715]) 0) 68 true) (.node 514 (sourceLit (List.headD (raw_ints% [69016590122319932952861135]) 0) 70 false) (.node 513 (sourceLit (List.headD (raw_ints% [738871076390838771373590673819714177]) 0) 36 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [6661393588454328274090806382967275585]) 0) 35 false) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [248202978264090099203043315]) 0) 70 false) (.node 517 (sourceLit (List.headD (raw_ints% [101356007666092224192545340042308133361]) 0) 32 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [158127510189968610048019633632978855267]) 0) 31 false) .empty .empty)))

#time def treeG_J028_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [300040318051646578754834475]) 0) 65 true) treeG_J028_part068 treeG_J028_part069)

#time def treeG_J028_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [263626762881238070259255975]) 0) 59 false) (.node 543 (sourceLit (List.headD (raw_ints% [605622644737192877262764625]) 0) 58 false) (.node 542 (sourceLit (List.headD (raw_ints% [425761334310034477965165525]) 0) 59 false) (.node 541 (sourceLit (List.headD (raw_ints% [5784697941022599160914798075]) 0) 55 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [182627149534483620502266855]) 0) 60 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [117814116789554299385514075]) 0) 60 false) (.node 546 (sourceLit (List.headD (raw_ints% [20307151462284878495938905]) 0) 63 false) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [9253422092452641352626705]) 0) 64 false) .empty .empty)))

#time def treeG_J028_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [632191051949410424296218825]) 0) 66 true) (.node 551 (sourceLit (List.headD (raw_ints% [43330850405828848292574825]) 0) 66 false) (.node 550 (sourceLit (List.headD (raw_ints% [457042400969598524340654632296157]) 0) 40 true) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [38129570168953023181275896586197091]) 0) 39 false) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [855058500626206860449090685]) 0) 68 false) (.node 554 (sourceLit (List.headD (raw_ints% [1308434168243245134341196254896485143]) 0) 37 true) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [9278899944178557426363102167183337071]) 0) 36 false) .empty .empty)))

#time def treeG_J028_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [39861559239377414255044875]) 0) 61 false) treeG_J028_part071 treeG_J028_part072)

#time def treeG_J028_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [2103110438420521079362581825]) 0) 57 false) treeG_J028_part070 treeG_J028_part073)

#time def treeG_J028_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [558985159694094119733123975]) 0) 59 false) (.node 581 (sourceLit (List.headD (raw_ints% [1439160879447791769019027575]) 0) 58 false) (.node 559 (sourceLit (List.headD (raw_ints% [137866371603740473723366605]) 0) 72 false) (.node 558 (sourceLit (List.headD (raw_ints% [120068520933243653945154884477272343863]) 0) 33 true) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [1964824467515728394800077225]) 0) 57 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [58127560519971482525684625]) 0) 62 false) (.node 584 (sourceLit (List.headD (raw_ints% [800052356214201270196083825]) 0) 58 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [42612224463769506493628925]) 0) 62 false) .empty .empty)))

#time def treeG_J028_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [18451288095664725158179897827127973]) 0) 38 true) (.node 589 (sourceLit (List.headD (raw_ints% [465113279312511771005853414451451]) 0) 39 false) (.node 588 (sourceLit (List.headD (raw_ints% [149833775317898240293882275]) 0) 60 false) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [8714345054499577568373525]) 0) 65 true) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [1348944199094087142274005019198867633]) 0) 36 false) (.node 592 (sourceLit (List.headD (raw_ints% [473363719674961971925133775]) 0) 65 false) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [1184323772927969887919107905]) 0) 67 true) .empty .empty)))

#time def treeG_J028_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [25257984505905580076217225]) 0) 63 false) treeG_J028_part075 treeG_J028_part076)

#time def treeG_J028_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [268212796666481599968413925]) 0) 60 false) (.node 599 (sourceLit (List.headD (raw_ints% [1118675677655917841609258709451157606171]) 0) 31 true) (.node 597 (sourceLit (List.headD (raw_ints% [398280805879806061836164609392174919633]) 0) 32 false) (.node 596 (sourceLit (List.headD (raw_ints% [2509219886022380750203940085]) 0) 68 false) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [634003945576161733882961655]) 0) 71 true) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [169900227847316939692164075]) 0) 61 false) (.node 622 (sourceLit (List.headD (raw_ints% [506699772568878645526931025]) 0) 60 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [11761187817487828100964285]) 0) 65 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [13746527009815103254854675]) 0) 64 false) (.node 627 (sourceLit (List.headD (raw_ints% [223083678920601752563517325]) 0) 60 false) (.node 626 (sourceLit (List.headD (raw_ints% [4727551132210825503718215]) 0) 66 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [2000570301681617340448815]) 0) 67 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [26022597730164212930474175]) 0) 67 true) (.node 630 (sourceLit (List.headD (raw_ints% [115269460035263786918313505843451]) 0) 43 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [7072607283077218542431974301665633]) 0) 42 true) .empty .empty))))

#time def treeG_J028_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [17128866934400289348820376422139156729]) 0) 35 true) treeG_J028_part077 treeG_J028_part078)

#time def treeG_J028_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [1019804912888233368562879995]) 0) 69 true) treeG_J028_part074 treeG_J028_part079)

#time def treeG_J028_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [292537508925974836197207075]) 0) 59 false) treeG_J028_part067 treeG_J028_part080)

#time def treeG_J028_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [64793665851631214472664936733680907937]) 0) 36 false) (.node 636 (sourceLit (List.headD (raw_ints% [3300970859822355846897934823665311725]) 0) 39 true) (.node 635 (sourceLit (List.headD (raw_ints% [1019691136777088374184099295]) 0) 69 true) (.node 634 (sourceLit (List.headD (raw_ints% [332172295917166534576900159261919097]) 0) 40 false) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [220564049931913382422926255]) 0) 73 false) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [1467813930581420462374600125]) 0) 59 false) (.node 639 (sourceLit (List.headD (raw_ints% [192967579294975551901582065]) 0) 74 true) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [1918351289342869764878541375]) 0) 58 false) .empty .empty)))

#time def treeG_J028_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [608934723071413264195916383917829]) 0) 39 false) (.node 667 (sourceLit (List.headD (raw_ints% [50382833609467627983274215]) 0) 63 false) (.node 666 (sourceLit (List.headD (raw_ints% [182988347738942586981156075]) 0) 61 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [296333582523305264833152375]) 0) 60 false) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [25828533537921607520951962201108837]) 0) 38 false) (.node 670 (sourceLit (List.headD (raw_ints% [2807609008039335102903525]) 0) 68 false) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [681544501516275675368927175]) 0) 65 true) .empty .empty)))

#time def treeG_J028_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [130051444559833767089743935]) 0) 62 false) treeG_J028_part082 treeG_J028_part083)

#time def treeG_J028_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [2398516345031468793266371695]) 0) 71 false) (.node 676 (sourceLit (List.headD (raw_ints% [6587984433130734246940337265]) 0) 68 true) (.node 675 (sourceLit (List.headD (raw_ints% [38387893873098947561741986614901978937]) 0) 35 false) (.node 674 (sourceLit (List.headD (raw_ints% [2289878544552342284140460505]) 0) 67 false) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [1243329345994329158642035924250494721233]) 0) 32 true) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [1091455920421809963143743005]) 0) 60 false) (.node 679 (sourceLit (List.headD (raw_ints% [5265470292160315567859814660406735714139]) 0) 31 false) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [1381925696009906564941713525]) 0) 59 false) .empty .empty)))

#time def treeG_J028_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [313220957210697031150591662829779]) 0) 40 true) (.node 708 (sourceLit (List.headD (raw_ints% [34378271196014689259683695]) 0) 64 false) (.node 707 (sourceLit (List.headD (raw_ints% [508869712035168595361106975]) 0) 60 false) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [186361366444784438794314975]) 0) 61 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [82409391802539355860407756614433901]) 0) 39 false) (.node 711 (sourceLit (List.headD (raw_ints% [37253033762321553342088275]) 0) 67 false) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [1787099273140648071590279775]) 0) 66 true) .empty .empty)))

#time def treeG_J028_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [92231035502147163059998215]) 0) 63 false) treeG_J028_part085 treeG_J028_part086)

#time def treeG_J028_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [2254237931327971115705297729812068657]) 0) 36 true) treeG_J028_part084 treeG_J028_part087)

#time def treeG_J028_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [3170386662211371000872699955]) 0) 72 false) (.node 717 (sourceLit (List.headD (raw_ints% [10117009232041348365707157345]) 0) 69 true) (.node 716 (sourceLit (List.headD (raw_ints% [64795660751677794336925465204224472737]) 0) 36 false) (.node 715 (sourceLit (List.headD (raw_ints% [4329260818106519032508659095]) 0) 68 false) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [1761678672807378874423355418119941984729]) 0) 33 true) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [1015949000532021390979401375]) 0) 60 false) (.node 745 (sourceLit (List.headD (raw_ints% [831353031302142428964255135]) 0) 61 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [134079237394826698136722215]) 0) 63 false) .empty .empty)))

#time def treeG_J028_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [979568771614848102105633375]) 0) 65 false) (.node 750 (sourceLit (List.headD (raw_ints% [6674389930266992208489375]) 0) 62 false) (.node 749 (sourceLit (List.headD (raw_ints% [1698152003177053859334457386854651]) 0) 39 false) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [28334301195607183770156695503747069]) 0) 38 true) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [509622227211623794466342535]) 0) 70 true) (.node 753 (sourceLit (List.headD (raw_ints% [3572788200168600809471821835643011073]) 0) 36 false) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [77680824262421374700305978646161350401]) 0) 35 true) .empty .empty)))

#time def treeG_J028_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [721405841547031925889061575]) 0) 60 false) treeG_J028_part089 treeG_J028_part090)

#time def treeG_J028_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [1005686480193875445242524524842215]) 0) 41 false) (.node 786 (sourceLit (List.headD (raw_ints% [646890960297848102844258705]) 0) 62 false) (.node 758 (sourceLit (List.headD (raw_ints% [14914041922104285952239900735]) 0) 70 true) (.node 757 (sourceLit (List.headD (raw_ints% [3316790490048018577423650810785677848817]) 0) 32 false) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [19358899674619346563246658005366271591971]) 0) 31 true) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [12462620774851501109629815]) 0) 67 false) (.node 787 (sourceLit (List.headD (raw_ints% [1523028289028874186597695775]) 0) 60 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [66880559387780935886843325]) 0) 64 false) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [4242202249416952100896160419775216253]) 0) 38 false) (.node 792 (sourceLit (List.headD (raw_ints% [55371846499073269815282226059090485]) 0) 40 true) (.node 791 (sourceLit (List.headD (raw_ints% [589374150266877861264923025]) 0) 63 true) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [1383334022377748086847956575]) 0) 67 false) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [71238242507049584518615721925192911569]) 0) 37 true) (.node 795 (sourceLit (List.headD (raw_ints% [8406238635799509388239399375]) 0) 68 true) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [99076231646035627647128175]) 0) 77 false) .empty .empty))))

#time def treeG_J028_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [15246506069343772311957655455]) 0) 68 false) treeG_J028_part091 treeG_J028_part092)

#time def treeG_J028_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [4911616298665303392320499003907421433]) 0) 37 true) treeG_J028_part088 treeG_J028_part093)

#time def treeG_J028_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [528370085171980494886257225]) 0) 62 false) (.node 828 (sourceLit (List.headD (raw_ints% [2324650736510716447306329975]) 0) 60 false) (.node 827 (sourceLit (List.headD (raw_ints% [256405861451510702353768245]) 0) 64 false) (.node 799 (sourceLit (List.headD (raw_ints% [21254815246527027953985300645]) 0) 71 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [4992666578127618205961513374586629]) 0) 39 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [2548511693496574065476189775]) 0) 64 true) (.node 831 (sourceLit (List.headD (raw_ints% [44425284878709190894037087901222509]) 0) 38 false) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [5344687288138945443560853069533906593]) 0) 36 true) .empty .empty)))

#time def treeG_J028_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [40277557223489406629904713535]) 0) 70 false) (.node 836 (sourceLit (List.headD (raw_ints% [32058983340942791088436454205]) 0) 68 true) (.node 835 (sourceLit (List.headD (raw_ints% [145556060253092608314644545362564810449]) 0) 35 false) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [7876038010499191986615057013998024189233]) 0) 32 true) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [206555378352104697915248985]) 0) 65 false) (.node 839 (sourceLit (List.headD (raw_ints% [59986652977462526178022707836611230260339]) 0) 31 false) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [1789606261408468960211583375]) 0) 61 false) .empty .empty)))

#time def treeG_J028_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [3421822931224243264713326715]) 0) 68 false) treeG_J028_part095 treeG_J028_part096)

#time def treeG_J028_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [12954507173354589438462063242903644022779]) 0) 33 true) (.node 874 (sourceLit (List.headD (raw_ints% [13829091786972849645353173909084339099]) 0) 37 true) (.node 872 (sourceLit (List.headD (raw_ints% [155168977876855730524601540019403479]) 0) 39 false) (.node 871 (sourceLit (List.headD (raw_ints% [558872117719429178075590125]) 0) 64 false) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [8081847783007566412868016075]) 0) 65 true) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [288032545267191777351875989212950633587]) 0) 36 false) (.node 875 (sourceLit (List.headD (raw_ints% [15249884498247995917666052805]) 0) 68 false) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [57422498642327911766101267005]) 0) 69 true) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [20574935936790252370225373302004917]) 0) 38 true) (.node 909 (sourceLit (List.headD (raw_ints% [22730727010472258366349541946419451]) 0) 39 false) (.node 879 (sourceLit (List.headD (raw_ints% [15383093117504108645972503545]) 0) 73 false) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [630618088118244232662663075]) 0) 63 false) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [7827390934168637131954477709844362257]) 0) 36 false) (.node 912 (sourceLit (List.headD (raw_ints% [3666255928935432421627370025]) 0) 64 false) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [21769139507904539471721322935]) 0) 66 true) .empty .empty))))

#time def treeG_J028_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [2981293617739867315476464324902199]) 0) 40 false) treeG_J028_part097 treeG_J028_part098)

#time def treeG_J028_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [4937358348183097762718269405379313]) 0) 42 false) (.node 918 (sourceLit (List.headD (raw_ints% [24425013966454329599001495135]) 0) 72 true) (.node 917 (sourceLit (List.headD (raw_ints% [17093079459049328861875088668812444464017]) 0) 32 false) (.node 916 (sourceLit (List.headD (raw_ints% [62558752337438782923768559815]) 0) 68 false) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [163622710364299241685719213779840382442571]) 0) 31 true) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [43935978453411495723706728330352099]) 0) 41 true) (.node 951 (sourceLit (List.headD (raw_ints% [35872985199407527293536475]) 0) 65 false) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [2937025927985749708623846525]) 0) 67 false) .empty .empty)))

#time def treeG_J028_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [7511896658100979575084287977929022121699]) 0) 35 false) (.node 956 (sourceLit (List.headD (raw_ints% [136055334954016795707336481462047539207]) 0) 38 true) (.node 955 (sourceLit (List.headD (raw_ints% [52268908504400531307053428545]) 0) 67 true) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [29995312744941673672467456705]) 0) 71 false) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [10639293555186972858271708322986896593]) 0) 36 true) (.node 959 (sourceLit (List.headD (raw_ints% [4976013385494804780621749835]) 0) 76 true) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [33517243219847538306216709035]) 0) 66 false) .empty .empty)))

#time def treeG_J028_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [5414120680285371694326912904732175339]) 0) 39 false) treeG_J028_part100 treeG_J028_part101)

#time def treeG_J028_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [58702227955401502230172953795]) 0) 71 true) (.node 999 (sourceLit (List.headD (raw_ints% [404003403423530588088416429073569090336939]) 0) 31 false) (.node 997 (sourceLit (List.headD (raw_ints% [34508162333163478712414158295954529482513]) 0) 32 true) (.node 996 (sourceLit (List.headD (raw_ints% [14353457605229914278852748545]) 0) 71 true) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [1700635209731125102233404745]) 0) 77 false) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [21446537931062017403317534395]) 0) 69 false) (.node 1034 (sourceLit (List.headD (raw_ints% [32295776276328459635579359941915597949]) 0) 37 true) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [973661996134074482525277075434859290917]) 0) 36 false) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [50153453141521845961023031485]) 0) 70 false) (.node 1039 (sourceLit (List.headD (raw_ints% [11778554224419305189555368815]) 0) 76 false) (.node 1038 (sourceLit (List.headD (raw_ints% [64555748965567397012751310207670617969309]) 0) 33 true) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [687806866528634976780566029121993917681]) 0) 35 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [113122554666797505501641905635]) 0) 72 true) (.node 1077 (sourceLit (List.headD (raw_ints% [65665346209453862153223024709870026791857]) 0) 32 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [920449395148069764190426910734934034091411]) 0) 31 true) .empty .empty))))

#time def treeG_J028_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [429440656318007299695931149586669134089]) 0) 35 false) treeG_J028_part102 treeG_J028_part103)

#time def treeG_J028_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [256188794548875405477469936635239523241]) 0) 35 true) treeG_J028_part099 treeG_J028_part104)

#time def treeG_J028_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [2539234581427698725923503114452809916773]) 0) 34 false) treeG_J028_part094 treeG_J028_part105)

#time def treeG_J028_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [138194346453046549527669075]) 0) 69 false) treeG_J028_part081 treeG_J028_part106)

#time def treeG_J028_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [154758447790471498811867865]) 0) 59 false) treeG_J028_part054 treeG_J028_part107)

#time def treeG_J028 : IntSourceTree := treeG_J028_part108

#time def treeG_J029_part000 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [59531262201590930031295389375]) 0) 44 false) (.node 9 (sourceLit (List.headD (raw_ints% [345235082895672760449450116325]) 0) 42 false) (.node 8 (sourceLit (List.headD (raw_ints% [99848834438012953388412170175]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [902527562520521869261393115325]) 0) 41 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [48701379125905949706087400695]) 0) 47 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 45 false) (.node 12 (sourceLit (List.headD (raw_ints% [11912546018313350156573824515]) 0) 49 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [5840874999582439627826392965]) 0) 50 false) .empty .empty)))

#time def treeG_J029_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [308553642015650233810909875]) 0) 52 true) (.node 17 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 50 true) (.node 16 (sourceLit (List.headD (raw_ints% [358619017450365096506477775]) 0) 54 false) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [176402788656068317470555675]) 0) 55 false) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [261604016136927550190104875]) 0) 53 true) (.node 20 (sourceLit (List.headD (raw_ints% [43437842285705682412800345]) 0) 57 false) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [21414188312665931540770155]) 0) 58 false) .empty .empty)))

#time def treeG_J029_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) treeG_J029_part000 treeG_J029_part001)

#time def treeG_J029_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 64 false) (.node 26 (sourceLit (List.headD (raw_ints% [1304350966289083816978875]) 0) 62 false) (.node 25 (sourceLit (List.headD (raw_ints% [39948122786965592776991775]) 0) 57 true) (.node 24 (sourceLit (List.headD (raw_ints% [2641517278155395263018395]) 0) 61 false) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [17013079142940938631345225]) 0) 59 true) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [75157104751234270052094547323131]) 0) 39 true) (.node 29 (sourceLit (List.headD (raw_ints% [22353245451983305317329325]) 0) 60 true) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 64 false) .empty .empty)))

#time def treeG_J029_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [263355470158063475450309687348455]) 0) 35 true) (.node 34 (sourceLit (List.headD (raw_ints% [173784715974629607078684442737393]) 0) 36 true) (.node 33 (sourceLit (List.headD (raw_ints% [79696586555044589955825]) 0) 66 false) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [19719392562631586289465]) 0) 68 false) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [1690036502005770061907316273109585]) 0) 32 true) (.node 37 (sourceLit (List.headD (raw_ints% [9762622920262217819385]) 0) 69 false) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [1208792403731037554715]) 0) 72 false) .empty .empty)))

#time def treeG_J029_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [64692946817434173723500844411131]) 0) 38 true) treeG_J029_part003 treeG_J029_part004)

#time def treeG_J029_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [51175878753474289187980875]) 0) 56 true) treeG_J029_part002 treeG_J029_part005)

#time def treeG_J029_part007 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [11912546018313350156573824515]) 0) 50 false) (.node 51 (sourceLit (List.headD (raw_ints% [48701379125905949706087400695]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [345235082895672760449450116325]) 0) 43 false) (.node 49 (sourceLit (List.headD (raw_ints% [99848834438012953388412170175]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [59531262201590930031295389375]) 0) 45 false) .empty .empty)) (.node 55 (sourceLit (List.headD (raw_ints% [5840874999582439627826392965]) 0) 51 false) (.node 54 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 46 false) .empty .empty) (.node 56 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)))

#time def treeG_J029_part008 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [43437842285705682412800345]) 0) 58 false) (.node 59 (sourceLit (List.headD (raw_ints% [176402788656068317470555675]) 0) 56 false) (.node 58 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 51 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [308553642015650233810909875]) 0) 53 true) .empty .empty)) (.node 63 (sourceLit (List.headD (raw_ints% [21414188312665931540770155]) 0) 59 false) (.node 62 (sourceLit (List.headD (raw_ints% [261604016136927550190104875]) 0) 54 true) .empty .empty) (.node 64 (sourceLit (List.headD (raw_ints% [51175878753474289187980875]) 0) 57 true) .empty .empty)))

#time def treeG_J029_part009 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [358619017450365096506477775]) 0) 55 false) treeG_J029_part007 treeG_J029_part008)

#time def treeG_J029_part010 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [64692946817434173723500844411131]) 0) 39 true) (.node 69 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 65 false) (.node 67 (sourceLit (List.headD (raw_ints% [1304350966289083816978875]) 0) 63 false) (.node 66 (sourceLit (List.headD (raw_ints% [39948122786965592776991775]) 0) 58 true) .empty .empty) (.node 68 (sourceLit (List.headD (raw_ints% [17013079142940938631345225]) 0) 60 true) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [75157104751234270052094547323131]) 0) 40 true) (.node 70 (sourceLit (List.headD (raw_ints% [22353245451983305317329325]) 0) 61 true) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 65 false) .empty .empty))) (.node 77 (sourceLit (List.headD (raw_ints% [263355470158063475450309687348455]) 0) 36 true) (.node 75 (sourceLit (List.headD (raw_ints% [173784715974629607078684442737393]) 0) 37 true) (.node 74 (sourceLit (List.headD (raw_ints% [79696586555044589955825]) 0) 67 false) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [19719392562631586289465]) 0) 69 false) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [1690036502005770061907316273109585]) 0) 33 true) (.node 78 (sourceLit (List.headD (raw_ints% [9762622920262217819385]) 0) 70 false) .empty .empty) (.node 89 (sourceLit (List.headD (raw_ints% [1459820042145370978073336114325]) 0) 42 false) .empty .empty))))

#time def treeG_J029_part011 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [2641517278155395263018395]) 0) 62 false) treeG_J029_part009 treeG_J029_part010)

#time def treeG_J029_part012 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [902527562520521869261393115325]) 0) 42 false) treeG_J029_part006 treeG_J029_part011)

#time def treeG_J029_part013 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 47 false) (.node 93 (sourceLit (List.headD (raw_ints% [103457242078492975491280336875]) 0) 45 false) (.node 92 (sourceLit (List.headD (raw_ints% [9197208276898149887378394045]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [142851910347040915209077363475]) 0) 45 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [17984217037044260685321256065]) 0) 50 false) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 50 false) (.node 96 (sourceLit (List.headD (raw_ints% [4406398929780979241800481865]) 0) 52 false) .empty .empty) (.node 98 (sourceLit (List.headD (raw_ints% [540835246244661875542399875]) 0) 55 false) .empty .empty)))

#time def treeG_J029_part014 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [159252258629978971814143125]) 0) 55 true) (.node 101 (sourceLit (List.headD (raw_ints% [355503267894372917431714875]) 0) 53 true) (.node 100 (sourceLit (List.headD (raw_ints% [66482473185181317528877665]) 0) 58 false) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [65461496258745433284830535]) 0) 58 false) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [62403634719982985598969975]) 0) 57 true) (.node 104 (sourceLit (List.headD (raw_ints% [16131153756355141014733365]) 0) 60 false) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [3978683590021706709057915]) 0) 62 false) .empty .empty)))

#time def treeG_J029_part015 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [62908994974064610776981625]) 0) 54 true) treeG_J029_part013 treeG_J029_part014)

#time def treeG_J029_part016 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [536563891192439986693255534173917]) 0) 38 true) (.node 110 (sourceLit (List.headD (raw_ints% [118408957544274668210281852692731]) 0) 39 false) (.node 109 (sourceLit (List.headD (raw_ints% [11672912833898571945361125]) 0) 60 true) (.node 108 (sourceLit (List.headD (raw_ints% [15345305485753927258575]) 0) 70 false) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [23642251112786635207049625]) 0) 62 true) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [861302433104317172497329067840703]) 0) 36 true) (.node 113 (sourceLit (List.headD (raw_ints% [121277414322893941237125]) 0) 67 false) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [7497149249051625458295]) 0) 71 false) .empty .empty)))

#time def treeG_J029_part017 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [69661559953106138601492874875]) 0) 47 false) (.node 118 (sourceLit (List.headD (raw_ints% [6737338543052261152502593722040975]) 0) 32 true) (.node 117 (sourceLit (List.headD (raw_ints% [29676162205000954759545]) 0) 69 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [7345038112800142709955]) 0) 71 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [226172558492490900386859337575]) 0) 45 false) (.node 131 (sourceLit (List.headD (raw_ints% [6393431914013375460290596185]) 0) 52 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [24876287089279249392939751665]) 0) 50 false) .empty .empty)))

#time def treeG_J029_part018 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [1126922257638973381179165854550689]) 0) 35 true) treeG_J029_part016 treeG_J029_part017)

#time def treeG_J029_part019 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [11467521822012327072823275]) 0) 60 true) treeG_J029_part015 treeG_J029_part018)

#time def treeG_J029_part020 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [45554057198574194758980525]) 0) 59 false) (.node 137 (sourceLit (List.headD (raw_ints% [2971922859979518855774570765]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 48 false) (.node 135 (sourceLit (List.headD (raw_ints% [3035835509365455264373715775]) 0) 53 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [560189621911908676918836375]) 0) 52 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [89527104084656952644954985]) 0) 58 false) (.node 140 (sourceLit (List.headD (raw_ints% [56917662119391790702983375]) 0) 53 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [5868703234840335452600625]) 0) 58 true) .empty .empty)))

#time def treeG_J029_part021 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [41786447245822232688735]) 0) 69 false) (.node 145 (sourceLit (List.headD (raw_ints% [10848119200044350488696575]) 0) 61 false) (.node 144 (sourceLit (List.headD (raw_ints% [56900501123030393438181375]) 0) 56 true) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [2806938991627174102747275]) 0) 61 true) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [659848135887418872118725]) 0) 65 false) (.node 148 (sourceLit (List.headD (raw_ints% [5921964501083715514301325]) 0) 60 true) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [1335041577260591671496025]) 0) 64 false) .empty .empty)))

#time def treeG_J029_part022 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [11011826986519875436015095]) 0) 61 false) treeG_J029_part020 treeG_J029_part021)

#time def treeG_J029_part023 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [2523651020523245545297638724465695]) 0) 34 true) (.node 155 (sourceLit (List.headD (raw_ints% [343758858564843782709322312551655]) 0) 38 true) (.node 153 (sourceLit (List.headD (raw_ints% [235935472187502906484877344881393]) 0) 40 true) (.node 152 (sourceLit (List.headD (raw_ints% [24931256773589965096769925]) 0) 63 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [162858242090743292518425]) 0) 67 false) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [431783393740454952864428083601117]) 0) 37 true) (.node 156 (sourceLit (List.headD (raw_ints% [40257801429781417376895]) 0) 69 false) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [155574525662021382345]) 0) 77 false) .empty .empty))) (.node 174 (sourceLit (List.headD (raw_ints% [31768357141514238100558247265]) 0) 50 false) (.node 172 (sourceLit (List.headD (raw_ints% [16376519379155351953783990695]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [414440569277808193602865635525]) 0) 45 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [348887874906488825282438338275]) 0) 45 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [7736943107680841815694381235]) 0) 52 false) (.node 175 (sourceLit (List.headD (raw_ints% [72246677429115206348659453125]) 0) 47 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [14484903080865067217472769125]) 0) 49 false) .empty .empty))))

#time def treeG_J029_part024 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [96783031147754469131188200007931]) 0) 41 false) treeG_J029_part022 treeG_J029_part023)

#time def treeG_J029_part025 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [10981494969225511364996236875]) 0) 49 false) treeG_J029_part019 treeG_J029_part024)

#time def treeG_J029_part026 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [150996289750119957070736939655]) 0) 47 false) treeG_J029_part012 treeG_J029_part025)

#time def treeG_J029_part027 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [65353006872533604572533125]) 0) 55 false) (.node 181 (sourceLit (List.headD (raw_ints% [469338592133156498837681625]) 0) 53 false) (.node 180 (sourceLit (List.headD (raw_ints% [115733755609115461507044435]) 0) 58 false) (.node 179 (sourceLit (List.headD (raw_ints% [686007611860037898472799625]) 0) 53 false) .empty .empty) .empty) (.node 182 (sourceLit (List.headD (raw_ints% [113592711910568472005079435]) 0) 58 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [687891699619074020098575]) 0) 60 false) (.node 184 (sourceLit (List.headD (raw_ints% [27916154189724360729327015]) 0) 60 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [1717358902505660944909665]) 0) 64 false) .empty .empty)))

#time def treeG_J029_part028 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [34322583730871368579017825]) 0) 62 false) (.node 189 (sourceLit (List.headD (raw_ints% [171016168268859083241525]) 0) 60 true) (.node 188 (sourceLit (List.headD (raw_ints% [1652571360004269089385]) 0) 74 false) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [29845639920430043410184036935931]) 0) 39 true) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [25901476088173116626666925]) 0) 64 true) (.node 192 (sourceLit (List.headD (raw_ints% [2085092389556511492792266734300813]) 0) 38 false) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [6688632676895775835018745968363873]) 0) 36 true) .empty .empty)))

#time def treeG_J029_part029 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [239765855503630661834175]) 0) 60 false) treeG_J029_part027 treeG_J029_part028)

#time def treeG_J029_part030 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [602708580063125486818871933475]) 0) 45 false) (.node 198 (sourceLit (List.headD (raw_ints% [20896798656336855830820803628430513]) 0) 32 true) (.node 197 (sourceLit (List.headD (raw_ints% [50839440654561879994245]) 0) 69 false) (.node 196 (sourceLit (List.headD (raw_ints% [4373219479398527142169991146275791]) 0) 35 true) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [12568501171938594230205]) 0) 71 false) .empty .empty)) (.node 214 (sourceLit (List.headD (raw_ints% [261035915152684734362468443275]) 0) 46 false) (.node 213 (sourceLit (List.headD (raw_ints% [40629790427342158422196211115]) 0) 50 false) .empty .empty) (.node 215 (sourceLit (List.headD (raw_ints% [19625015104052417043063384165]) 0) 51 false) .empty .empty)))

#time def treeG_J029_part031 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [1315097561600684006242615875]) 0) 53 false) (.node 218 (sourceLit (List.headD (raw_ints% [12244144593217432509797423625]) 0) 50 false) (.node 217 (sourceLit (List.headD (raw_ints% [2382510123850661479959905235]) 0) 54 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [1161387452313007988546082615]) 0) 55 false) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [563237843890601866079291625]) 0) 54 false) (.node 221 (sourceLit (List.headD (raw_ints% [141940407133573970369133885]) 0) 58 false) .empty .empty) (.node 223 (sourceLit (List.headD (raw_ints% [69545403964488970261019055]) 0) 59 false) .empty .empty)))

#time def treeG_J029_part032 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [28320697552213160888674505625]) 0) 49 false) treeG_J029_part030 treeG_J029_part031)

#time def treeG_J029_part033 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [102881048098330288852065]) 0) 68 false) treeG_J029_part029 treeG_J029_part032)

#time def treeG_J029_part034 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [1032384936756952675411515]) 0) 65 false) (.node 227 (sourceLit (List.headD (raw_ints% [1048775746572505221889905]) 0) 65 false) (.node 226 (sourceLit (List.headD (raw_ints% [1747415345623124061422925]) 0) 62 false) (.node 225 (sourceLit (List.headD (raw_ints% [2133504373710001280078805]) 0) 64 false) .empty .empty) .empty) (.node 228 (sourceLit (List.headD (raw_ints% [6401496212090976837969675]) 0) 60 false) .empty .empty)) (.node 231 (sourceLit (List.headD (raw_ints% [223411702215938981672560436951793]) 0) 40 true) (.node 230 (sourceLit (List.headD (raw_ints% [10851348786353592455209725]) 0) 61 true) .empty .empty) (.node 232 (sourceLit (List.headD (raw_ints% [29626920252230666837893875]) 0) 64 false) .empty .empty)))

#time def treeG_J029_part035 : IntSourceTree :=
  (.node 237 (sourceLit (List.headD (raw_ints% [3509652691917617236441134979073557]) 0) 36 true) (.node 235 (sourceLit (List.headD (raw_ints% [6001114959766088269600101343260563]) 0) 37 true) (.node 234 (sourceLit (List.headD (raw_ints% [26552909056536089796740625]) 0) 65 true) .empty .empty) (.node 236 (sourceLit (List.headD (raw_ints% [31311623334274435737585]) 0) 70 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [15849496615290364740225526179499123]) 0) 33 true) (.node 238 (sourceLit (List.headD (raw_ints% [30925901369823143054085]) 0) 70 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [856529285219762148355305528675]) 0) 45 false) .empty .empty)))

#time def treeG_J029_part036 : IntSourceTree :=
  (.node 233 (sourceLit (List.headD (raw_ints% [2556963333931517305762021424063599]) 0) 39 false) treeG_J029_part034 treeG_J029_part035)

#time def treeG_J029_part037 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [170288102356579468733188335]) 0) 58 false) (.node 258 (sourceLit (List.headD (raw_ints% [2874767880211127855230039455]) 0) 54 false) (.node 256 (sourceLit (List.headD (raw_ints% [5944035998185787613684501465]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [94394618861784764006904495075]) 0) 48 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [42156492023561254559876242125]) 0) 49 false) .empty .empty)) (.node 260 (sourceLit (List.headD (raw_ints% [698452429876546142517904875]) 0) 56 false) (.node 259 (sourceLit (List.headD (raw_ints% [9500114145777280915906225125]) 0) 51 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [2160856531068211513647550125]) 0) 53 false) .empty .empty))) (.node 266 (sourceLit (List.headD (raw_ints% [2549649844914341615247945]) 0) 64 false) (.node 264 (sourceLit (List.headD (raw_ints% [5203656221845576191461505]) 0) 63 false) (.node 263 (sourceLit (List.headD (raw_ints% [124471209254517065376689625]) 0) 57 false) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [29187593599652851462481475]) 0) 59 false) .empty .empty)) (.node 268 (sourceLit (List.headD (raw_ints% [625717478411412335007345]) 0) 66 false) (.node 267 (sourceLit (List.headD (raw_ints% [13739556909481361829549225]) 0) 60 false) .empty .empty) (.node 269 (sourceLit (List.headD (raw_ints% [12974008592450812759180875]) 0) 60 false) .empty .empty))))

#time def treeG_J029_part038 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [49491223713170078743834174965]) 0) 50 false) treeG_J029_part036 treeG_J029_part037)

#time def treeG_J029_part039 : IntSourceTree :=
  (.node 224 (sourceLit (List.headD (raw_ints% [30563376998890999502678625]) 0) 58 false) treeG_J029_part033 treeG_J029_part038)

#time def treeG_J029_part040 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [26964433248929410952148885]) 0) 66 true) (.node 273 (sourceLit (List.headD (raw_ints% [85155316592634450302454675]) 0) 64 false) (.node 272 (sourceLit (List.headD (raw_ints% [3872386007284023346172750229915157]) 0) 38 true) (.node 271 (sourceLit (List.headD (raw_ints% [22586966258612480517113775]) 0) 63 true) .empty .empty) .empty) (.node 274 (sourceLit (List.headD (raw_ints% [47600046019800052727211088753381457]) 0) 36 false) .empty .empty)) (.node 277 (sourceLit (List.headD (raw_ints% [74407052682535862956095]) 0) 69 false) (.node 276 (sourceLit (List.headD (raw_ints% [43635700198730179014630819599808713]) 0) 35 true) .empty .empty) (.node 278 (sourceLit (List.headD (raw_ints% [91412087485026895735295515701923311]) 0) 32 true) .empty .empty)))

#time def treeG_J029_part041 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [1780762937167563066862298115]) 0) 55 false) (.node 295 (sourceLit (List.headD (raw_ints% [1866638038069853856298174425]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [74436671258384676749104635675]) 0) 49 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [33036960654785801559114994725]) 0) 50 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [214172553487264983335494605]) 0) 58 false) (.node 298 (sourceLit (List.headD (raw_ints% [7478086857585955512519704625]) 0) 52 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [6869919022575912903420993375]) 0) 52 false) .empty .empty)))

#time def treeG_J029_part042 : IntSourceTree :=
  (.node 279 (sourceLit (List.headD (raw_ints% [2294675024735568602985]) 0) 74 false) treeG_J029_part040 treeG_J029_part041)

#time def treeG_J029_part043 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [22197932217160355216789775]) 0) 60 false) (.node 304 (sourceLit (List.headD (raw_ints% [11738479031953258234251375]) 0) 61 false) (.node 303 (sourceLit (List.headD (raw_ints% [1574104662376414038627645]) 0) 65 false) (.node 302 (sourceLit (List.headD (raw_ints% [399404671794402411892064625]) 0) 56 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [767537962033893727845675]) 0) 66 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [21077617606871746821128775]) 0) 60 false) (.node 307 (sourceLit (List.headD (raw_ints% [187609262292729549169755]) 0) 68 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [1470484976888696664617865]) 0) 65 false) .empty .empty)))

#time def treeG_J029_part044 : IntSourceTree :=
  (.node 314 (sourceLit (List.headD (raw_ints% [27927056412292635024798825]) 0) 67 false) (.node 312 (sourceLit (List.headD (raw_ints% [26106943255421573677503825]) 0) 65 true) (.node 311 (sourceLit (List.headD (raw_ints% [97955425692327725344999870556411]) 0) 42 false) .empty .empty) (.node 313 (sourceLit (List.headD (raw_ints% [1607337335303885162983692913494689]) 0) 41 true) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [27214926235603606438049565]) 0) 67 true) (.node 315 (sourceLit (List.headD (raw_ints% [13400290244891535249202797524160505]) 0) 39 false) .empty .empty) (.node 317 (sourceLit (List.headD (raw_ints% [10031511876703140444547421155183789]) 0) 38 true) .empty .empty)))

#time def treeG_J029_part045 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [2978169672350550651798825]) 0) 64 false) treeG_J029_part043 treeG_J029_part044)

#time def treeG_J029_part046 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [414571615609398201779637105]) 0) 57 false) treeG_J029_part042 treeG_J029_part045)

#time def treeG_J029_part047 : IntSourceTree :=
  (.node 338 (sourceLit (List.headD (raw_ints% [4248283868459124412219153005]) 0) 54 false) (.node 336 (sourceLit (List.headD (raw_ints% [8989068306373043236700893935]) 0) 53 false) (.node 335 (sourceLit (List.headD (raw_ints% [203352066171753942989514047625]) 0) 48 false) (.node 319 (sourceLit (List.headD (raw_ints% [18890647717434132748767497380606047]) 0) 35 true) .empty .empty) .empty) (.node 337 (sourceLit (List.headD (raw_ints% [89991350595581951676583736775]) 0) 49 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [1014927998021573724166051965]) 0) 56 false) (.node 339 (sourceLit (List.headD (raw_ints% [20412233284566541134172593375]) 0) 51 false) .empty .empty) (.node 341 (sourceLit (List.headD (raw_ints% [2354531245753850694886721625]) 0) 54 false) .empty .empty)))

#time def treeG_J029_part048 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [3590653851356808207517455]) 0) 64 false) (.node 344 (sourceLit (List.headD (raw_ints% [7389181077165736117559655]) 0) 63 false) (.node 343 (sourceLit (List.headD (raw_ints% [34366682817485668314421875]) 0) 60 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [64720238655973214411529525]) 0) 59 false) .empty .empty)) (.node 348 (sourceLit (List.headD (raw_ints% [875156619930424058350695]) 0) 66 false) (.node 347 (sourceLit (List.headD (raw_ints% [30656307524839348604030325]) 0) 60 false) .empty .empty) (.node 349 (sourceLit (List.headD (raw_ints% [29181226621292680883076675]) 0) 60 false) .empty .empty)))

#time def treeG_J029_part049 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [122141756626409366523224385]) 0) 59 false) treeG_J029_part047 treeG_J029_part048)

#time def treeG_J029_part050 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [1192621432732975081166774392161601681]) 0) 32 true) (.node 354 (sourceLit (List.headD (raw_ints% [150469635479248703158167435217041553]) 0) 36 true) (.node 352 (sourceLit (List.headD (raw_ints% [7006959629438510557212746087720309]) 0) 38 false) (.node 351 (sourceLit (List.headD (raw_ints% [34499644948014683124309075]) 0) 63 false) .empty .empty) (.node 353 (sourceLit (List.headD (raw_ints% [189583089614320745012469975]) 0) 64 true) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [472444988035259306989120340372944873]) 0) 35 false) (.node 355 (sourceLit (List.headD (raw_ints% [138672658898099951051344185]) 0) 66 false) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [27363740340968678163961755]) 0) 68 true) .empty .empty))) (.node 378 (sourceLit (List.headD (raw_ints% [60079003165238129626504918275]) 0) 50 false) (.node 376 (sourceLit (List.headD (raw_ints% [137278144862182339871284058175]) 0) 49 false) (.node 359 (sourceLit (List.headD (raw_ints% [12561875557414085539065]) 0) 72 false) .empty .empty) (.node 377 (sourceLit (List.headD (raw_ints% [5427542432037917102976297705]) 0) 54 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [105799330171801783052746875]) 0) 59 false) (.node 379 (sourceLit (List.headD (raw_ints% [2534903440561004545535196165]) 0) 55 false) .empty .empty) (.node 381 (sourceLit (List.headD (raw_ints% [150089095603043880596603715]) 0) 59 false) .empty .empty))))

#time def treeG_J029_part051 : IntSourceTree :=
  (.node 350 (sourceLit (List.headD (raw_ints% [28955152102761455498748783236869]) 0) 39 false) treeG_J029_part049 treeG_J029_part050)

#time def treeG_J029_part052 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [21740575656356359951005]) 0) 71 false) treeG_J029_part046 treeG_J029_part051)

#time def treeG_J029_part053 : IntSourceTree :=
  (.node 270 (sourceLit (List.headD (raw_ints% [168410000553371919707439045273851]) 0) 39 false) treeG_J029_part039 treeG_J029_part052)

#time def treeG_J029_part054 : IntSourceTree :=
  (.node 178 (sourceLit (List.headD (raw_ints% [1890252367490195104689771015]) 0) 54 false) treeG_J029_part026 treeG_J029_part053)

#time def treeG_J029_part055 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [2089779753014971814159415]) 0) 65 false) (.node 385 (sourceLit (List.headD (raw_ints% [4319029229030161206176955]) 0) 64 false) (.node 384 (sourceLit (List.headD (raw_ints% [5657050946383102520042625]) 0) 63 false) (.node 383 (sourceLit (List.headD (raw_ints% [71770407430364117287139745]) 0) 60 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [21261153219406429597369875]) 0) 61 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [2030141502832999568784915]) 0) 65 false) (.node 388 (sourceLit (List.headD (raw_ints% [40234997442806950386931875]) 0) 60 false) .empty .empty) (.node 390 (sourceLit (List.headD (raw_ints% [5355869242488275668686075]) 0) 61 false) .empty .empty)))

#time def treeG_J029_part056 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [204070796458814844154978625313683573]) 0) 37 true) (.node 393 (sourceLit (List.headD (raw_ints% [13436308970654051209147517741699065]) 0) 39 false) (.node 392 (sourceLit (List.headD (raw_ints% [86713531458857830479316725]) 0) 64 false) .empty .empty) (.node 394 (sourceLit (List.headD (raw_ints% [301291315263491285111665275]) 0) 65 true) .empty .empty)) (.node 397 (sourceLit (List.headD (raw_ints% [512571035542071868767310024993680029]) 0) 36 false) (.node 396 (sourceLit (List.headD (raw_ints% [82943792566851778744696875]) 0) 68 false) .empty .empty) (.node 398 (sourceLit (List.headD (raw_ints% [27450702643594103603765775]) 0) 69 true) .empty .empty)))

#time def treeG_J029_part057 : IntSourceTree :=
  (.node 391 (sourceLit (List.headD (raw_ints% [362866550666549445881250698988775]) 0) 40 true) treeG_J029_part055 treeG_J029_part056)

#time def treeG_J029_part058 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [4416625885241463420489078375]) 0) 54 false) (.node 419 (sourceLit (List.headD (raw_ints% [9916692470167897123083081225]) 0) 53 false) (.node 418 (sourceLit (List.headD (raw_ints% [6606800995616709793733442405]) 0) 54 false) (.node 417 (sourceLit (List.headD (raw_ints% [184564939128782728065984379575]) 0) 49 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [189996930317428852671143025]) 0) 59 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [1005854977085275178071842375]) 0) 56 false) (.node 422 (sourceLit (List.headD (raw_ints% [178036434579678394669983045]) 0) 59 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [42213683121701172816901125]) 0) 61 false) .empty .empty)))

#time def treeG_J029_part059 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [51288768264321219890787075]) 0) 60 false) (.node 427 (sourceLit (List.headD (raw_ints% [54388305352786369785449175]) 0) 60 false) (.node 426 (sourceLit (List.headD (raw_ints% [5047404606703514204836455]) 0) 64 false) .empty .empty) (.node 428 (sourceLit (List.headD (raw_ints% [75913945817784234738045]) 0) 70 false) .empty .empty)) (.node 431 (sourceLit (List.headD (raw_ints% [63643420653541090579932075]) 0) 62 true) (.node 430 (sourceLit (List.headD (raw_ints% [243525827925989310048542228736251]) 0) 39 false) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [9909892034770906124262751679630509]) 0) 38 true) .empty .empty)))

#time def treeG_J029_part060 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [116305391628286066229834475]) 0) 59 false) treeG_J029_part058 treeG_J029_part059)

#time def treeG_J029_part061 : IntSourceTree :=
  (.node 399 (sourceLit (List.headD (raw_ints% [1117058841863238550171704402639177493]) 0) 33 true) treeG_J029_part057 treeG_J029_part060)

#time def treeG_J029_part062 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [17594894570079274881720695191959362609]) 0) 32 false) (.node 436 (sourceLit (List.headD (raw_ints% [2105011359705778060228949342882413457]) 0) 35 true) (.node 435 (sourceLit (List.headD (raw_ints% [109990993540397809040752365]) 0) 68 true) (.node 434 (sourceLit (List.headD (raw_ints% [365450579009713522504527719084226593]) 0) 36 false) .empty .empty) .empty) (.node 437 (sourceLit (List.headD (raw_ints% [193251325474672235653355505]) 0) 68 false) .empty .empty)) (.node 458 (sourceLit (List.headD (raw_ints% [31121483990886149609869865325]) 0) 52 false) (.node 439 (sourceLit (List.headD (raw_ints% [27500950145823759945922035]) 0) 70 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [127246798595490789006195195]) 0) 60 false) .empty .empty)))

#time def treeG_J029_part063 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [643803716516756616789114375]) 0) 57 false) (.node 462 (sourceLit (List.headD (raw_ints% [178806498942276096836655375]) 0) 59 false) (.node 461 (sourceLit (List.headD (raw_ints% [229904765031813824745682335]) 0) 59 false) .empty .empty) (.node 463 (sourceLit (List.headD (raw_ints% [26566506787328569345710825]) 0) 62 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [73783085189473207035094725]) 0) 60 false) (.node 465 (sourceLit (List.headD (raw_ints% [24937566205580527992193305]) 0) 62 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [184851553355533899417315]) 0) 69 false) .empty .empty)))

#time def treeG_J029_part064 : IntSourceTree :=
  (.node 460 (sourceLit (List.headD (raw_ints% [6531113904670240065395181225]) 0) 54 false) treeG_J029_part062 treeG_J029_part063)

#time def treeG_J029_part065 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [302925779647647396826201605]) 0) 68 true) (.node 472 (sourceLit (List.headD (raw_ints% [237070483571256751538565525]) 0) 63 true) (.node 470 (sourceLit (List.headD (raw_ints% [5741612377729118027762625]) 0) 64 false) (.node 469 (sourceLit (List.headD (raw_ints% [2828351029505191454449965]) 0) 65 false) .empty .empty) (.node 471 (sourceLit (List.headD (raw_ints% [303196189296269377964896463862513]) 0) 41 false) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [166075366948881922770692175]) 0) 67 false) (.node 473 (sourceLit (List.headD (raw_ints% [11673100502712478666705134710664787]) 0) 40 true) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [284760687734264183329753172198955083]) 0) 38 false) .empty .empty))) (.node 499 (sourceLit (List.headD (raw_ints% [5301197880179563121696696025]) 0) 55 false) (.node 478 (sourceLit (List.headD (raw_ints% [431058648668488943861565]) 0) 78 false) (.node 477 (sourceLit (List.headD (raw_ints% [1308791197623924964498129683938046743]) 0) 37 true) .empty .empty) (.node 479 (sourceLit (List.headD (raw_ints% [9355976705971256715946199797299270051]) 0) 34 false) .empty .empty)) (.node 501 (sourceLit (List.headD (raw_ints% [8645601924099016710301284075]) 0) 54 false) (.node 500 (sourceLit (List.headD (raw_ints% [318990264064534303353637755]) 0) 59 false) .empty .empty) (.node 502 (sourceLit (List.headD (raw_ints% [281773095483949254821381625]) 0) 59 false) .empty .empty))))

#time def treeG_J029_part066 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [68541613262765789183966475]) 0) 60 false) treeG_J029_part064 treeG_J029_part065)

#time def treeG_J029_part067 : IntSourceTree :=
  (.node 433 (sourceLit (List.headD (raw_ints% [363010152532036405971103425]) 0) 64 false) treeG_J029_part061 treeG_J029_part066)

#time def treeG_J029_part068 : IntSourceTree :=
  (.node 508 (sourceLit (List.headD (raw_ints% [54468803768874832339635]) 0) 71 false) (.node 506 (sourceLit (List.headD (raw_ints% [14842756992173499582520395]) 0) 63 false) (.node 505 (sourceLit (List.headD (raw_ints% [411192933260184484329445425]) 0) 58 false) (.node 504 (sourceLit (List.headD (raw_ints% [64052344027613104565942175]) 0) 61 false) .empty .empty) .empty) (.node 507 (sourceLit (List.headD (raw_ints% [93177865026160044284740275]) 0) 60 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [136089021240658451172747563243269]) 0) 39 false) (.node 509 (sourceLit (List.headD (raw_ints% [85794458261210358477145875]) 0) 60 false) .empty .empty) (.node 511 (sourceLit (List.headD (raw_ints% [109576319675374034802033075]) 0) 62 false) .empty .empty)))

#time def treeG_J029_part069 : IntSourceTree :=
  (.node 516 (sourceLit (List.headD (raw_ints% [6661182363454004993505000098065694785]) 0) 35 false) (.node 514 (sourceLit (List.headD (raw_ints% [738989795096512839839092029825499777]) 0) 36 true) (.node 513 (sourceLit (List.headD (raw_ints% [300040318051646578754834475]) 0) 65 true) .empty .empty) (.node 515 (sourceLit (List.headD (raw_ints% [69016590122319932952861135]) 0) 70 false) .empty .empty)) (.node 518 (sourceLit (List.headD (raw_ints% [101357531218010472609600994963994354161]) 0) 32 true) (.node 517 (sourceLit (List.headD (raw_ints% [799102884769967029305758715]) 0) 68 true) .empty .empty) (.node 519 (sourceLit (List.headD (raw_ints% [248202978264090099203043315]) 0) 70 false) .empty .empty)))

#time def treeG_J029_part070 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [14761031063511216171701095101430717]) 0) 38 false) treeG_J029_part068 treeG_J029_part069)

#time def treeG_J029_part071 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [19557388911016288286874435]) 0) 63 false) (.node 543 (sourceLit (List.headD (raw_ints% [175507068334634977438538325]) 0) 60 false) (.node 542 (sourceLit (List.headD (raw_ints% [5784697941022599160914798075]) 0) 55 false) (.node 541 (sourceLit (List.headD (raw_ints% [408075763097254781961593175]) 0) 59 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [605622644737192877262764625]) 0) 58 false) .empty .empty)) (.node 547 (sourceLit (List.headD (raw_ints% [8927507284796414801166315]) 0) 64 false) (.node 546 (sourceLit (List.headD (raw_ints% [263626762881238070259255975]) 0) 59 false) .empty .empty) (.node 548 (sourceLit (List.headD (raw_ints% [117814116789554299385514075]) 0) 60 false) .empty .empty)))

#time def treeG_J029_part072 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [38107232068936173505111364522760291]) 0) 39 false) (.node 551 (sourceLit (List.headD (raw_ints% [470303357351880304757045364481757]) 0) 40 true) (.node 550 (sourceLit (List.headD (raw_ints% [39861559239377414255044875]) 0) 61 false) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [43330850405828848292574825]) 0) 66 false) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [1308511170565041206498598374223409943]) 0) 37 true) (.node 554 (sourceLit (List.headD (raw_ints% [632191051949410424296218825]) 0) 66 true) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [855058500626206860449090685]) 0) 68 false) .empty .empty)))

#time def treeG_J029_part073 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [4143655852910787085023315]) 0) 65 false) treeG_J029_part071 treeG_J029_part072)

#time def treeG_J029_part074 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [14673677616048012421391602875]) 0) 54 false) treeG_J029_part070 treeG_J029_part073)

#time def treeG_J029_part075 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [1964824467515728394800077225]) 0) 57 false) (.node 581 (sourceLit (List.headD (raw_ints% [20701753307997008132481921675]) 0) 54 false) (.node 559 (sourceLit (List.headD (raw_ints% [120069484629952986041493394558592894263]) 0) 33 true) (.node 558 (sourceLit (List.headD (raw_ints% [1019804912888233368562879995]) 0) 69 true) .empty .empty) .empty) (.node 582 (sourceLit (List.headD (raw_ints% [534378430710560309101804725]) 0) 59 false) .empty .empty)) (.node 585 (sourceLit (List.headD (raw_ints% [800052356214201270196083825]) 0) 58 false) (.node 584 (sourceLit (List.headD (raw_ints% [55727362153510936436298075]) 0) 62 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [24272020829859076991228475]) 0) 63 false) .empty .empty)))

#time def treeG_J029_part076 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [8714345054499577568373525]) 0) 65 true) (.node 589 (sourceLit (List.headD (raw_ints% [149833775317898240293882275]) 0) 60 false) (.node 588 (sourceLit (List.headD (raw_ints% [5441503843588425531429675]) 0) 65 false) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [420063052950929578070824603085051]) 0) 39 false) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [473363719674961971925133775]) 0) 65 false) (.node 592 (sourceLit (List.headD (raw_ints% [18523457922326258609757458017284773]) 0) 38 true) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [1348705508199491615920873862189664433]) 0) 36 false) .empty .empty)))

#time def treeG_J029_part077 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [42612224463769506493628925]) 0) 62 false) treeG_J029_part075 treeG_J029_part076)

#time def treeG_J029_part078 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [4521246655311831018677955]) 0) 66 false) (.node 599 (sourceLit (List.headD (raw_ints% [634003945576161733882961655]) 0) 71 true) (.node 597 (sourceLit (List.headD (raw_ints% [2509219886022380750203940085]) 0) 68 false) (.node 596 (sourceLit (List.headD (raw_ints% [17129271727974334645493787091852974329]) 0) 35 true) .empty .empty) (.node 598 (sourceLit (List.headD (raw_ints% [398278003496469830129641297874131578833]) 0) 32 false) .empty .empty)) (.node 623 (sourceLit (List.headD (raw_ints% [11214730074247666614477075]) 0) 65 false) (.node 622 (sourceLit (List.headD (raw_ints% [932315960435900560722945225]) 0) 59 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [169900227847316939692164075]) 0) 61 false) .empty .empty))) (.node 629 (sourceLit (List.headD (raw_ints% [6739351834266063977836035]) 0) 65 false) (.node 627 (sourceLit (List.headD (raw_ints% [959032096566416386878885]) 0) 68 false) (.node 626 (sourceLit (List.headD (raw_ints% [268212796666481599968413925]) 0) 60 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [223083678920601752563517325]) 0) 60 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [111295801287851235353483745945851]) 0) 43 false) (.node 630 (sourceLit (List.headD (raw_ints% [13746527009815103254854675]) 0) 64 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [26022597730164212930474175]) 0) 67 true) .empty .empty))))

#time def treeG_J029_part079 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [1184323772927969887919107905]) 0) 67 true) treeG_J029_part077 treeG_J029_part078)

#time def treeG_J029_part080 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [9278764758701854922501259465941788271]) 0) 36 false) treeG_J029_part074 treeG_J029_part079)

#time def treeG_J029_part081 : IntSourceTree :=
  (.node 503 (sourceLit (List.headD (raw_ints% [1855049005991142371314643625]) 0) 56 false) treeG_J029_part067 treeG_J029_part080)

#time def treeG_J029_part082 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [220564049931913382422926255]) 0) 73 false) (.node 636 (sourceLit (List.headD (raw_ints% [1019691136777088374184099295]) 0) 69 true) (.node 635 (sourceLit (List.headD (raw_ints% [332152084845566602802434029551634297]) 0) 40 false) (.node 634 (sourceLit (List.headD (raw_ints% [138194346453046549527669075]) 0) 69 false) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [3301004560834523695999380819724345325]) 0) 39 true) .empty .empty)) (.node 663 (sourceLit (List.headD (raw_ints% [5493703215971476090983484575]) 0) 57 false) (.node 639 (sourceLit (List.headD (raw_ints% [64793436015802852021391836554090559137]) 0) 36 false) .empty .empty) (.node 664 (sourceLit (List.headD (raw_ints% [123708319034451729395335125]) 0) 62 false) .empty .empty)))

#time def treeG_J029_part083 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [296333582523305264833152375]) 0) 60 false) (.node 667 (sourceLit (List.headD (raw_ints% [182988347738942586981156075]) 0) 61 false) (.node 666 (sourceLit (List.headD (raw_ints% [48067925655130219307618805]) 0) 63 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [9903009701474236658632485]) 0) 65 false) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [2807609008039335102903525]) 0) 68 false) (.node 670 (sourceLit (List.headD (raw_ints% [484477438436894076536970371143429]) 0) 39 false) .empty .empty) (.node 672 (sourceLit (List.headD (raw_ints% [25646389204748737672380417757819237]) 0) 38 false) .empty .empty)))

#time def treeG_J029_part084 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [1918351289342869764878541375]) 0) 58 false) treeG_J029_part082 treeG_J029_part083)

#time def treeG_J029_part085 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [1243335171070107896305482787723563982033]) 0) 32 true) (.node 676 (sourceLit (List.headD (raw_ints% [38387005158090597224849564983157569337]) 0) 35 false) (.node 675 (sourceLit (List.headD (raw_ints% [2289878544552342284140460505]) 0) 67 false) (.node 674 (sourceLit (List.headD (raw_ints% [2254796548059690529758775022830385457]) 0) 36 true) .empty .empty) .empty) (.node 677 (sourceLit (List.headD (raw_ints% [6587984433130734246940337265]) 0) 68 true) .empty .empty)) (.node 704 (sourceLit (List.headD (raw_ints% [4134501393192940573446171975]) 0) 58 false) (.node 679 (sourceLit (List.headD (raw_ints% [2398516345031468793266371695]) 0) 71 false) .empty .empty) (.node 705 (sourceLit (List.headD (raw_ints% [87538345791957081245911485]) 0) 63 false) .empty .empty)))

#time def treeG_J029_part086 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [186361366444784438794314975]) 0) 61 false) (.node 708 (sourceLit (List.headD (raw_ints% [508869712035168595361106975]) 0) 60 false) (.node 707 (sourceLit (List.headD (raw_ints% [32723412110067557117556645]) 0) 64 false) .empty .empty) (.node 709 (sourceLit (List.headD (raw_ints% [13066667568682409339428935]) 0) 65 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [37253033762321553342088275]) 0) 67 false) (.node 711 (sourceLit (List.headD (raw_ints% [405888971865915806290899596423379]) 0) 40 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [82277079196011169787249240297864301]) 0) 39 false) .empty .empty)))

#time def treeG_J029_part087 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [1381925696009906564941713525]) 0) 59 false) treeG_J029_part085 treeG_J029_part086)

#time def treeG_J029_part088 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [681544501516275675368927175]) 0) 65 true) treeG_J029_part084 treeG_J029_part087)

#time def treeG_J029_part089 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [1761682659196530712476617480156288455129]) 0) 33 true) (.node 717 (sourceLit (List.headD (raw_ints% [64795041644766786792844611540952331937]) 0) 36 false) (.node 716 (sourceLit (List.headD (raw_ints% [4329260818106519032508659095]) 0) 68 false) (.node 715 (sourceLit (List.headD (raw_ints% [4912013226824223352178247259243459833]) 0) 37 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [10117009232041348365707157345]) 0) 69 true) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [127008765928783943184204165]) 0) 63 false) (.node 745 (sourceLit (List.headD (raw_ints% [6350651497043011382013802575]) 0) 58 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [1015949000532021390979401375]) 0) 60 false) .empty .empty)))

#time def treeG_J029_part090 : IntSourceTree :=
  (.node 752 (sourceLit (List.headD (raw_ints% [28893500979676064122707614529206269]) 0) 38 true) (.node 750 (sourceLit (List.headD (raw_ints% [1269300995162942858567162102016251]) 0) 39 false) (.node 749 (sourceLit (List.headD (raw_ints% [721405841547031925889061575]) 0) 60 false) .empty .empty) (.node 751 (sourceLit (List.headD (raw_ints% [6674389930266992208489375]) 0) 62 false) .empty .empty)) (.node 754 (sourceLit (List.headD (raw_ints% [3571229815195869246354762867596214273]) 0) 36 false) (.node 753 (sourceLit (List.headD (raw_ints% [979568771614848102105633375]) 0) 65 false) .empty .empty) (.node 755 (sourceLit (List.headD (raw_ints% [509622227211623794466342535]) 0) 70 true) .empty .empty)))

#time def treeG_J029_part091 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [178284393817135316085345]) 0) 72 false) treeG_J029_part089 treeG_J029_part090)

#time def treeG_J029_part092 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [66880559387780935886843325]) 0) 64 false) (.node 786 (sourceLit (List.headD (raw_ints% [2484362900516552408536044525]) 0) 60 false) (.node 758 (sourceLit (List.headD (raw_ints% [3316776503702645073676510357034038604017]) 0) 32 false) (.node 757 (sourceLit (List.headD (raw_ints% [15246506069343772311957655455]) 0) 68 false) .empty .empty) (.node 759 (sourceLit (List.headD (raw_ints% [14914041922104285952239900735]) 0) 70 true) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [1523028289028874186597695775]) 0) 60 false) (.node 787 (sourceLit (List.headD (raw_ints% [2946417306834887064582735]) 0) 69 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [32574137248504231578419385]) 0) 65 false) .empty .empty))) (.node 794 (sourceLit (List.headD (raw_ints% [1383334022377748086847956575]) 0) 67 false) (.node 792 (sourceLit (List.headD (raw_ints% [589374150266877861264923025]) 0) 63 true) (.node 791 (sourceLit (List.headD (raw_ints% [837594983514429332429030849219815]) 0) 41 false) .empty .empty) (.node 793 (sourceLit (List.headD (raw_ints% [55585290087843616954978427413535285]) 0) 40 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [8406238635799509388239399375]) 0) 68 true) (.node 795 (sourceLit (List.headD (raw_ints% [4241621521010046299266505063419837053]) 0) 38 false) .empty .empty) (.node 797 (sourceLit (List.headD (raw_ints% [71239076308725585417560077299028789969]) 0) 37 true) .empty .empty))))

#time def treeG_J029_part093 : IntSourceTree :=
  (.node 756 (sourceLit (List.headD (raw_ints% [77683110972684384042275543057105248001]) 0) 35 true) treeG_J029_part091 treeG_J029_part092)

#time def treeG_J029_part094 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [1787099273140648071590279775]) 0) 66 true) treeG_J029_part088 treeG_J029_part093)

#time def treeG_J029_part095 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [3102725697891466502274141583841029]) 0) 39 false) (.node 828 (sourceLit (List.headD (raw_ints% [2233279731566345800241355]) 0) 70 false) (.node 827 (sourceLit (List.headD (raw_ints% [3952776800501083426092687675]) 0) 60 false) (.node 799 (sourceLit (List.headD (raw_ints% [2539229581449587893076563918595163529573]) 0) 34 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [2324650736510716447306329975]) 0) 60 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [42295020715906933441572108116723309]) 0) 38 false) (.node 831 (sourceLit (List.headD (raw_ints% [528370085171980494886257225]) 0) 62 false) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [2548511693496574065476189775]) 0) 64 true) .empty .empty)))

#time def treeG_J029_part096 : IntSourceTree :=
  (.node 838 (sourceLit (List.headD (raw_ints% [7876077387461082540400355304171881162033]) 0) 32 true) (.node 836 (sourceLit (List.headD (raw_ints% [145549055308845124830539624071822640849]) 0) 35 false) (.node 835 (sourceLit (List.headD (raw_ints% [3421822931224243264713326715]) 0) 68 false) .empty .empty) (.node 837 (sourceLit (List.headD (raw_ints% [32058983340942791088436454205]) 0) 68 true) .empty .empty)) (.node 868 (sourceLit (List.headD (raw_ints% [6382525311973292665587679575]) 0) 60 false) (.node 839 (sourceLit (List.headD (raw_ints% [40277557223489406629904713535]) 0) 70 false) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [110355765571741899637027335]) 0) 65 false) .empty .empty)))

#time def treeG_J029_part097 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [5349959098006864988914072544829343393]) 0) 36 true) treeG_J029_part095 treeG_J029_part096)

#time def treeG_J029_part098 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [57422498642327911766101267005]) 0) 69 true) (.node 874 (sourceLit (List.headD (raw_ints% [8081847783007566412868016075]) 0) 65 true) (.node 872 (sourceLit (List.headD (raw_ints% [558872117719429178075590125]) 0) 64 false) (.node 871 (sourceLit (List.headD (raw_ints% [1427535730862607837416079885401399]) 0) 40 false) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [153465600891594167351528962943793879]) 0) 39 false) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [15249884498247995917666052805]) 0) 68 false) (.node 875 (sourceLit (List.headD (raw_ints% [13833202140026957587447082671669017499]) 0) 37 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [288027207926296295665659778669880220787]) 0) 36 false) .empty .empty))) (.node 911 (sourceLit (List.headD (raw_ints% [630618088118244232662663075]) 0) 63 false) (.node 909 (sourceLit (List.headD (raw_ints% [10440399887435868883869029175]) 0) 60 false) (.node 879 (sourceLit (List.headD (raw_ints% [12954536550360258326553483141362208221179]) 0) 33 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [11708974428848352269411691993753851]) 0) 39 false) .empty .empty)) (.node 913 (sourceLit (List.headD (raw_ints% [3666255928935432421627370025]) 0) 64 false) (.node 912 (sourceLit (List.headD (raw_ints% [30874734869006070742243469033512117]) 0) 38 true) .empty .empty) (.node 914 (sourceLit (List.headD (raw_ints% [7805408712272371666538535951930045457]) 0) 36 false) .empty .empty))))

#time def treeG_J029_part099 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [1789606261408468960211583375]) 0) 61 false) treeG_J029_part097 treeG_J029_part098)

#time def treeG_J029_part100 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [1081349203253424990457180725]) 0) 64 false) (.node 918 (sourceLit (List.headD (raw_ints% [17092948041102564001701468221608048227217]) 0) 32 false) (.node 917 (sourceLit (List.headD (raw_ints% [62558752337438782923768559815]) 0) 68 false) (.node 916 (sourceLit (List.headD (raw_ints% [256214672429060785530116285445174780841]) 0) 35 true) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [24425013966454329599001495135]) 0) 72 true) .empty .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [35872985199407527293536475]) 0) 65 false) (.node 951 (sourceLit (List.headD (raw_ints% [2570359674496436107998903027088113]) 0) 42 false) .empty .empty) (.node 953 (sourceLit (List.headD (raw_ints% [46085083940150059523443107994326499]) 0) 41 true) .empty .empty)))

#time def treeG_J029_part101 : IntSourceTree :=
  (.node 958 (sourceLit (List.headD (raw_ints% [29995312744941673672467456705]) 0) 71 false) (.node 956 (sourceLit (List.headD (raw_ints% [52268908504400531307053428545]) 0) 67 true) (.node 955 (sourceLit (List.headD (raw_ints% [5409652713074832313496404655899765739]) 0) 39 false) .empty .empty) (.node 957 (sourceLit (List.headD (raw_ints% [136060470088839270298944016028763750407]) 0) 38 true) .empty .empty)) (.node 993 (sourceLit (List.headD (raw_ints% [3522763988137802312453224125]) 0) 64 true) (.node 959 (sourceLit (List.headD (raw_ints% [7511871147865705582063737840742564112099]) 0) 35 false) .empty .empty) (.node 994 (sourceLit (List.headD (raw_ints% [10754854084441975476038894863566941393]) 0) 36 true) .empty .empty)))

#time def treeG_J029_part102 : IntSourceTree :=
  (.node 954 (sourceLit (List.headD (raw_ints% [2937025927985749708623846525]) 0) 67 false) treeG_J029_part100 treeG_J029_part101)

#time def treeG_J029_part103 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [973565439602812500757777298549022286117]) 0) 36 false) (.node 999 (sourceLit (List.headD (raw_ints% [1700635209731125102233404745]) 0) 77 false) (.node 997 (sourceLit (List.headD (raw_ints% [14353457605229914278852748545]) 0) 71 true) (.node 996 (sourceLit (List.headD (raw_ints% [429323559247455419562001234433967284489]) 0) 35 false) .empty .empty) (.node 998 (sourceLit (List.headD (raw_ints% [34508688212473990599966302273289808279313]) 0) 32 true) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [32393464936741304730024513487166004349]) 0) 37 true) (.node 1034 (sourceLit (List.headD (raw_ints% [15270867700080801146948610225]) 0) 65 true) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [21446537931062017403317534395]) 0) 69 false) .empty .empty))) (.node 1076 (sourceLit (List.headD (raw_ints% [688471278741385857402197342331295319281]) 0) 35 true) (.node 1039 (sourceLit (List.headD (raw_ints% [64556172803936812928221253636260064727709]) 0) 33 true) (.node 1038 (sourceLit (List.headD (raw_ints% [58702227955401502230172953795]) 0) 71 true) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [12197027729982084863291329815]) 0) 68 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [65662782279763990624215175826858521435057]) 0) 32 false) (.node 1077 (sourceLit (List.headD (raw_ints% [50153453141521845961023031485]) 0) 70 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [113122554666797505501641905635]) 0) 72 true) .empty .empty))))

#time def treeG_J029_part104 : IntSourceTree :=
  (.node 995 (sourceLit (List.headD (raw_ints% [33517243219847538306216709035]) 0) 66 false) treeG_J029_part102 treeG_J029_part103)

#time def treeG_J029_part105 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [21769139507904539471721322935]) 0) 66 true) treeG_J029_part099 treeG_J029_part104)

#time def treeG_J029_part106 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [99076231646035627647128175]) 0) 77 false) treeG_J029_part094 treeG_J029_part105)

#time def treeG_J029_part107 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [7078836248907804014358602817505633]) 0) 42 true) treeG_J029_part081 treeG_J029_part106)

#time def treeG_J029_part108 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [1555721902165045871102592375]) 0) 55 false) treeG_J029_part054 treeG_J029_part107)

#time def treeG_J029 : IntSourceTree := treeG_J029_part108

#time def treeG_J030_part000 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [5840874999582439627826392965]) 0) 50 false) (.node 11 (sourceLit (List.headD (raw_ints% [48701379125905949706087400695]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [99848834438012953388412170175]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [724003132726081029765601660275]) 0) 41 false) .empty .empty) (.node 10 (sourceLit (List.headD (raw_ints% [265890891875921276229098358525]) 0) 42 false) .empty .empty)) (.node 13 (sourceLit (List.headD (raw_ints% [11912546018313350156573824515]) 0) 49 false) (.node 12 (sourceLit (List.headD (raw_ints% [41498491515283774526669989875]) 0) 44 false) .empty .empty) (.node 14 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 45 false) .empty .empty))) (.node 19 (sourceLit (List.headD (raw_ints% [176402788656068317470555675]) 0) 55 false) (.node 17 (sourceLit (List.headD (raw_ints% [358619017450365096506477775]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [485497672323654186662991525]) 0) 49 true) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [788659114770098882407302975]) 0) 50 true) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [43437842285705682412800345]) 0) 57 false) (.node 20 (sourceLit (List.headD (raw_ints% [362664837692590019321336175]) 0) 52 true) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [287371252173565543290307875]) 0) 53 true) .empty .empty))))

#time def treeG_J030_part001 : IntSourceTree :=
  (.node 31 (sourceLit (List.headD (raw_ints% [75157104751234270052094547323131]) 0) 39 true) (.node 27 (sourceLit (List.headD (raw_ints% [1304350966289083816978875]) 0) 62 false) (.node 25 (sourceLit (List.headD (raw_ints% [2641517278155395263018395]) 0) 61 false) (.node 24 (sourceLit (List.headD (raw_ints% [54256743931767962276048625]) 0) 56 true) .empty .empty) (.node 26 (sourceLit (List.headD (raw_ints% [41426938072546555859264295]) 0) 57 true) .empty .empty)) (.node 29 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 64 false) (.node 28 (sourceLit (List.headD (raw_ints% [17369090230210429743744165]) 0) 59 true) .empty .empty) (.node 30 (sourceLit (List.headD (raw_ints% [22525112873423749302625365]) 0) 60 true) .empty .empty))) (.node 35 (sourceLit (List.headD (raw_ints% [173784715974629607078684442737393]) 0) 36 true) (.node 33 (sourceLit (List.headD (raw_ints% [64692946817434173723500844411131]) 0) 38 true) (.node 32 (sourceLit (List.headD (raw_ints% [155928104129435067304875]) 0) 65 false) .empty .empty) (.node 34 (sourceLit (List.headD (raw_ints% [77176536387296144423625]) 0) 66 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [263355470158063475450309687348455]) 0) 35 true) (.node 36 (sourceLit (List.headD (raw_ints% [19107380379035535231645]) 0) 68 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [9464887263377652439905]) 0) 69 false) .empty .empty))))

#time def treeG_J030_part002 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [21414188312665931540770155]) 0) 58 false) treeG_J030_part000 treeG_J030_part001)

#time def treeG_J030_part003 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [5840874999582439627826392965]) 0) 51 false) (.node 52 (sourceLit (List.headD (raw_ints% [48701379125905949706087400695]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [99848834438012953388412170175]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [724003132726081029765601660275]) 0) 42 false) .empty .empty) (.node 51 (sourceLit (List.headD (raw_ints% [265890891875921276229098358525]) 0) 43 false) .empty .empty)) (.node 54 (sourceLit (List.headD (raw_ints% [11912546018313350156573824515]) 0) 50 false) (.node 53 (sourceLit (List.headD (raw_ints% [41498491515283774526669989875]) 0) 45 false) .empty .empty) (.node 55 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 46 false) .empty .empty))) (.node 60 (sourceLit (List.headD (raw_ints% [176402788656068317470555675]) 0) 56 false) (.node 58 (sourceLit (List.headD (raw_ints% [358619017450365096506477775]) 0) 55 false) (.node 57 (sourceLit (List.headD (raw_ints% [485497672323654186662991525]) 0) 50 true) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [788659114770098882407302975]) 0) 51 true) .empty .empty)) (.node 62 (sourceLit (List.headD (raw_ints% [43437842285705682412800345]) 0) 58 false) (.node 61 (sourceLit (List.headD (raw_ints% [362664837692590019321336175]) 0) 53 true) .empty .empty) (.node 63 (sourceLit (List.headD (raw_ints% [287371252173565543290307875]) 0) 54 true) .empty .empty))))

#time def treeG_J030_part004 : IntSourceTree :=
  (.node 72 (sourceLit (List.headD (raw_ints% [75157104751234270052094547323131]) 0) 40 true) (.node 68 (sourceLit (List.headD (raw_ints% [1304350966289083816978875]) 0) 63 false) (.node 66 (sourceLit (List.headD (raw_ints% [2641517278155395263018395]) 0) 62 false) (.node 65 (sourceLit (List.headD (raw_ints% [54256743931767962276048625]) 0) 57 true) .empty .empty) (.node 67 (sourceLit (List.headD (raw_ints% [41426938072546555859264295]) 0) 58 true) .empty .empty)) (.node 70 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 65 false) (.node 69 (sourceLit (List.headD (raw_ints% [17369090230210429743744165]) 0) 60 true) .empty .empty) (.node 71 (sourceLit (List.headD (raw_ints% [22525112873423749302625365]) 0) 61 true) .empty .empty))) (.node 76 (sourceLit (List.headD (raw_ints% [173784715974629607078684442737393]) 0) 37 true) (.node 74 (sourceLit (List.headD (raw_ints% [64692946817434173723500844411131]) 0) 39 true) (.node 73 (sourceLit (List.headD (raw_ints% [155928104129435067304875]) 0) 66 false) .empty .empty) (.node 75 (sourceLit (List.headD (raw_ints% [77176536387296144423625]) 0) 67 false) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [263355470158063475450309687348455]) 0) 36 true) (.node 77 (sourceLit (List.headD (raw_ints% [19107380379035535231645]) 0) 69 false) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [9464887263377652439905]) 0) 70 false) .empty .empty))))

#time def treeG_J030_part005 : IntSourceTree :=
  (.node 64 (sourceLit (List.headD (raw_ints% [21414188312665931540770155]) 0) 59 false) treeG_J030_part003 treeG_J030_part004)

#time def treeG_J030_part006 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [1690036502005770061907316273109585]) 0) 32 true) treeG_J030_part002 treeG_J030_part005)

#time def treeG_J030_part007 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [182336229877209490918680075]) 0) 50 true) (.node 94 (sourceLit (List.headD (raw_ints% [75714517945712736253395106875]) 0) 45 false) (.node 92 (sourceLit (List.headD (raw_ints% [112196200180318750851214184325]) 0) 45 false) (.node 91 (sourceLit (List.headD (raw_ints% [150996289750119957070736939655]) 0) 47 false) .empty .empty) (.node 93 (sourceLit (List.headD (raw_ints% [9197208276898149887378394045]) 0) 51 false) .empty .empty)) (.node 96 (sourceLit (List.headD (raw_ints% [9224455774149429546596838975]) 0) 47 false) (.node 95 (sourceLit (List.headD (raw_ints% [17984217037044260685321256065]) 0) 50 false) .empty .empty) (.node 97 (sourceLit (List.headD (raw_ints% [4406398929780979241800481865]) 0) 52 false) .empty .empty))) (.node 102 (sourceLit (List.headD (raw_ints% [437958423211614495352364475]) 0) 53 true) (.node 100 (sourceLit (List.headD (raw_ints% [26624642317344303942872925]) 0) 56 true) (.node 99 (sourceLit (List.headD (raw_ints% [540835246244661875542399875]) 0) 55 false) .empty .empty) (.node 101 (sourceLit (List.headD (raw_ints% [66482473185181317528877665]) 0) 58 false) .empty .empty)) (.node 104 (sourceLit (List.headD (raw_ints% [178857764310029618738210625]) 0) 55 true) (.node 103 (sourceLit (List.headD (raw_ints% [65461496258745433284830535]) 0) 58 false) .empty .empty) (.node 105 (sourceLit (List.headD (raw_ints% [16131153756355141014733365]) 0) 60 false) .empty .empty))))

#time def treeG_J030_part008 : IntSourceTree :=
  (.node 114 (sourceLit (List.headD (raw_ints% [234679671871573990186125]) 0) 66 false) (.node 110 (sourceLit (List.headD (raw_ints% [12213067586997110184862965]) 0) 60 true) (.node 108 (sourceLit (List.headD (raw_ints% [12028923921168063057760065]) 0) 60 true) (.node 107 (sourceLit (List.headD (raw_ints% [3978683590021706709057915]) 0) 62 false) .empty .empty) (.node 109 (sourceLit (List.headD (raw_ints% [15345305485753927258575]) 0) 70 false) .empty .empty)) (.node 112 (sourceLit (List.headD (raw_ints% [23772537706459229841064365]) 0) 62 true) (.node 111 (sourceLit (List.headD (raw_ints% [118408957544274668210281852692731]) 0) 39 false) .empty .empty) (.node 113 (sourceLit (List.headD (raw_ints% [536563891192439986693255534173917]) 0) 38 true) .empty .empty))) (.node 118 (sourceLit (List.headD (raw_ints% [28749873494693418023385]) 0) 69 false) (.node 116 (sourceLit (List.headD (raw_ints% [14517289002065152297995]) 0) 70 false) (.node 115 (sourceLit (List.headD (raw_ints% [861302433104317172497329067840703]) 0) 36 true) .empty .empty) (.node 117 (sourceLit (List.headD (raw_ints% [1126922257638973381179165854550689]) 0) 35 true) .empty .empty)) (.node 131 (sourceLit (List.headD (raw_ints% [229056120425079876768251650875]) 0) 45 false) (.node 119 (sourceLit (List.headD (raw_ints% [6737338543052261152502593722040975]) 0) 32 true) .empty .empty) (.node 132 (sourceLit (List.headD (raw_ints% [6393431914013375460290596185]) 0) 52 false) .empty .empty))))

#time def treeG_J030_part009 : IntSourceTree :=
  (.node 106 (sourceLit (List.headD (raw_ints% [67086549790989368692832955]) 0) 57 true) treeG_J030_part007 treeG_J030_part008)

#time def treeG_J030_part010 : IntSourceTree :=
  (.node 141 (sourceLit (List.headD (raw_ints% [63329439384918843764630625]) 0) 53 true) (.node 137 (sourceLit (List.headD (raw_ints% [11166446463444046293248805075]) 0) 48 false) (.node 135 (sourceLit (List.headD (raw_ints% [4277003303803620215840639625]) 0) 50 false) (.node 134 (sourceLit (List.headD (raw_ints% [24876287089279249392939751665]) 0) 50 false) .empty .empty) (.node 136 (sourceLit (List.headD (raw_ints% [3035835509365455264373715775]) 0) 53 false) .empty .empty)) (.node 139 (sourceLit (List.headD (raw_ints% [151580721223222347872155725]) 0) 53 false) (.node 138 (sourceLit (List.headD (raw_ints% [2971922859979518855774570765]) 0) 53 false) .empty .empty) (.node 140 (sourceLit (List.headD (raw_ints% [45554057198574194758980525]) 0) 59 false) .empty .empty))) (.node 145 (sourceLit (List.headD (raw_ints% [70344276446493694186113375]) 0) 56 true) (.node 143 (sourceLit (List.headD (raw_ints% [18823396379756119007757075]) 0) 57 true) (.node 142 (sourceLit (List.headD (raw_ints% [89527104084656952644954985]) 0) 58 false) .empty .empty) (.node 144 (sourceLit (List.headD (raw_ints% [11011826986519875436015095]) 0) 61 false) .empty .empty)) (.node 147 (sourceLit (List.headD (raw_ints% [6414902929610703208392165]) 0) 60 true) (.node 146 (sourceLit (List.headD (raw_ints% [10848119200044350488696575]) 0) 61 false) .empty .empty) (.node 148 (sourceLit (List.headD (raw_ints% [41786447245822232688735]) 0) 69 false) .empty .empty))))

#time def treeG_J030_part011 : IntSourceTree :=
  (.node 157 (sourceLit (List.headD (raw_ints% [38961775629225073960335]) 0) 69 false) (.node 153 (sourceLit (List.headD (raw_ints% [25019962539494710379503365]) 0) 63 true) (.node 151 (sourceLit (List.headD (raw_ints% [322251415200832472430075]) 0) 66 false) (.node 150 (sourceLit (List.headD (raw_ints% [659848135887418872118725]) 0) 65 false) .empty .empty) (.node 152 (sourceLit (List.headD (raw_ints% [96783031147754469131188200007931]) 0) 41 false) .empty .empty)) (.node 155 (sourceLit (List.headD (raw_ints% [39375783871069461440625]) 0) 69 false) (.node 154 (sourceLit (List.headD (raw_ints% [235935472187502906484877344881393]) 0) 40 true) .empty .empty) (.node 156 (sourceLit (List.headD (raw_ints% [343758858564843782709322312551655]) 0) 38 true) .empty .empty))) (.node 173 (sourceLit (List.headD (raw_ints% [16376519379155351953783990695]) 0) 51 false) (.node 159 (sourceLit (List.headD (raw_ints% [2410623278914470697935]) 0) 73 false) (.node 158 (sourceLit (List.headD (raw_ints% [431783393740454952864428083601117]) 0) 37 true) .empty .empty) (.node 172 (sourceLit (List.headD (raw_ints% [345916040669841002685289117425]) 0) 45 false) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [31768357141514238100558247265]) 0) 50 false) (.node 174 (sourceLit (List.headD (raw_ints% [290073299744994718098121650675]) 0) 45 false) .empty .empty) (.node 176 (sourceLit (List.headD (raw_ints% [59207597086708493906853395025]) 0) 47 false) .empty .empty))))

#time def treeG_J030_part012 : IntSourceTree :=
  (.node 149 (sourceLit (List.headD (raw_ints% [6688757612125696371775965]) 0) 60 true) treeG_J030_part010 treeG_J030_part011)

#time def treeG_J030_part013 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [182893908845353727175758378775]) 0) 45 false) treeG_J030_part009 treeG_J030_part012)

#time def treeG_J030_part014 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [1182115373576240783302104962025]) 0) 42 false) treeG_J030_part006 treeG_J030_part013)

#time def treeG_J030_part015 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [27916154189724360729327015]) 0) 60 false) (.node 181 (sourceLit (List.headD (raw_ints% [115733755609115461507044435]) 0) 58 false) (.node 179 (sourceLit (List.headD (raw_ints% [1890252367490195104689771015]) 0) 54 false) (.node 178 (sourceLit (List.headD (raw_ints% [11531118923198465275086165225]) 0) 49 false) .empty .empty) (.node 180 (sourceLit (List.headD (raw_ints% [258079290492599563643647425]) 0) 54 false) .empty .empty)) (.node 183 (sourceLit (List.headD (raw_ints% [113592711910568472005079435]) 0) 58 false) (.node 182 (sourceLit (List.headD (raw_ints% [311299544441776807823103225]) 0) 53 false) .empty .empty) (.node 184 (sourceLit (List.headD (raw_ints% [28270593271980666676154025]) 0) 55 false) .empty .empty))) (.node 189 (sourceLit (List.headD (raw_ints% [1652571360004269089385]) 0) 74 false) (.node 187 (sourceLit (List.headD (raw_ints% [1717358902505660944909665]) 0) 64 false) (.node 186 (sourceLit (List.headD (raw_ints% [814431663876081373320105]) 0) 59 true) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [800881938053343359024265]) 0) 60 true) .empty .empty)) (.node 191 (sourceLit (List.headD (raw_ints% [29845639920430043410184036935931]) 0) 39 true) (.node 190 (sourceLit (List.headD (raw_ints% [1164447637254282558688965]) 0) 60 true) .empty .empty) (.node 192 (sourceLit (List.headD (raw_ints% [34084582992885868958826765]) 0) 62 false) .empty .empty))))

#time def treeG_J030_part016 : IntSourceTree :=
  (.node 214 (sourceLit (List.headD (raw_ints% [40629790427342158422196211115]) 0) 50 false) (.node 197 (sourceLit (List.headD (raw_ints% [4373219479398527142169991146275791]) 0) 35 true) (.node 195 (sourceLit (List.headD (raw_ints% [6688632676895775835018745968363873]) 0) 36 true) (.node 194 (sourceLit (List.headD (raw_ints% [25958681226981006340247865]) 0) 64 true) .empty .empty) (.node 196 (sourceLit (List.headD (raw_ints% [12429247434502154571315]) 0) 71 false) .empty .empty)) (.node 199 (sourceLit (List.headD (raw_ints% [20896798656336855830820803628430513]) 0) 32 true) (.node 198 (sourceLit (List.headD (raw_ints% [49173677763756729897285]) 0) 69 false) .empty .empty) (.node 213 (sourceLit (List.headD (raw_ints% [508938172494328278194819856075]) 0) 45 false) .empty .empty))) (.node 218 (sourceLit (List.headD (raw_ints% [2382510123850661479959905235]) 0) 54 false) (.node 216 (sourceLit (List.headD (raw_ints% [19625015104052417043063384165]) 0) 51 false) (.node 215 (sourceLit (List.headD (raw_ints% [221641246884136794644671416675]) 0) 46 false) .empty .empty) (.node 217 (sourceLit (List.headD (raw_ints% [24020575311632223806802294975]) 0) 49 false) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [1161387452313007988546082615]) 0) 55 false) (.node 219 (sourceLit (List.headD (raw_ints% [10318473153412686492108919425]) 0) 50 false) .empty .empty) (.node 221 (sourceLit (List.headD (raw_ints% [1095646601355317098339220325]) 0) 53 false) .empty .empty))))

#time def treeG_J030_part017 : IntSourceTree :=
  (.node 193 (sourceLit (List.headD (raw_ints% [2085092389556511492792266734300813]) 0) 38 false) treeG_J030_part015 treeG_J030_part016)

#time def treeG_J030_part018 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [1032384936756952675411515]) 0) 65 false) (.node 226 (sourceLit (List.headD (raw_ints% [2133504373710001280078805]) 0) 64 false) (.node 224 (sourceLit (List.headD (raw_ints% [69545403964488970261019055]) 0) 59 false) (.node 223 (sourceLit (List.headD (raw_ints% [461886715479825759885159825]) 0) 54 false) .empty .empty) (.node 225 (sourceLit (List.headD (raw_ints% [12326858714809295107783425]) 0) 59 false) .empty .empty)) (.node 228 (sourceLit (List.headD (raw_ints% [1048775746572505221889905]) 0) 65 false) (.node 227 (sourceLit (List.headD (raw_ints% [1400117816433655458768015]) 0) 62 false) .empty .empty) (.node 229 (sourceLit (List.headD (raw_ints% [5086993736019009653727435]) 0) 60 false) .empty .empty))) (.node 234 (sourceLit (List.headD (raw_ints% [2556963333931517305762021424063599]) 0) 39 false) (.node 232 (sourceLit (List.headD (raw_ints% [223411702215938981672560436951793]) 0) 40 true) (.node 231 (sourceLit (List.headD (raw_ints% [11476492923680921676451365]) 0) 61 true) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [29552272766190289669165065]) 0) 64 false) .empty .empty)) (.node 236 (sourceLit (List.headD (raw_ints% [6001114959766088269600101343260563]) 0) 37 true) (.node 235 (sourceLit (List.headD (raw_ints% [26588693768918117723297865]) 0) 65 true) .empty .empty) (.node 237 (sourceLit (List.headD (raw_ints% [60472203846792162610185]) 0) 69 false) .empty .empty))))

#time def treeG_J030_part019 : IntSourceTree :=
  (.node 260 (sourceLit (List.headD (raw_ints% [8253838829471889982959740025]) 0) 51 false) (.node 256 (sourceLit (List.headD (raw_ints% [81216824898714150368909010825]) 0) 48 false) (.node 254 (sourceLit (List.headD (raw_ints% [727803045243661838291518061475]) 0) 45 false) (.node 239 (sourceLit (List.headD (raw_ints% [29888691532440964313805]) 0) 70 false) .empty .empty) (.node 255 (sourceLit (List.headD (raw_ints% [49491223713170078743834174965]) 0) 50 false) .empty .empty)) (.node 258 (sourceLit (List.headD (raw_ints% [36510031700065982338518424725]) 0) 49 false) (.node 257 (sourceLit (List.headD (raw_ints% [5944035998185787613684501465]) 0) 53 false) .empty .empty) (.node 259 (sourceLit (List.headD (raw_ints% [2874767880211127855230039455]) 0) 54 false) .empty .empty))) (.node 264 (sourceLit (List.headD (raw_ints% [54202015275980636651125725]) 0) 58 false) (.node 262 (sourceLit (List.headD (raw_ints% [1879993658268857388855337425]) 0) 53 false) (.node 261 (sourceLit (List.headD (raw_ints% [698452429876546142517904875]) 0) 56 false) .empty .empty) (.node 263 (sourceLit (List.headD (raw_ints% [170288102356579468733188335]) 0) 58 false) .empty .empty)) (.node 266 (sourceLit (List.headD (raw_ints% [25468149093494671588886955]) 0) 59 false) (.node 265 (sourceLit (List.headD (raw_ints% [5203656221845576191461505]) 0) 63 false) .empty .empty) (.node 267 (sourceLit (List.headD (raw_ints% [2549649844914341615247945]) 0) 64 false) .empty .empty))))

#time def treeG_J030_part020 : IntSourceTree :=
  (.node 238 (sourceLit (List.headD (raw_ints% [3509652691917617236441134979073557]) 0) 36 true) treeG_J030_part018 treeG_J030_part019)

#time def treeG_J030_part021 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [141940407133573970369133885]) 0) 58 false) treeG_J030_part017 treeG_J030_part020)

#time def treeG_J030_part022 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [26986429686822186669579945]) 0) 66 true) (.node 272 (sourceLit (List.headD (raw_ints% [22780537958283395317639065]) 0) 63 true) (.node 270 (sourceLit (List.headD (raw_ints% [11338435109292301866143835]) 0) 60 false) (.node 269 (sourceLit (List.headD (raw_ints% [625717478411412335007345]) 0) 66 false) .empty .empty) (.node 271 (sourceLit (List.headD (raw_ints% [168410000553371919707439045273851]) 0) 39 false) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [85063226759361585678577995]) 0) 64 false) (.node 273 (sourceLit (List.headD (raw_ints% [3872386007284023346172750229915157]) 0) 38 true) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [47600046019800052727211088753381457]) 0) 36 false) .empty .empty))) (.node 295 (sourceLit (List.headD (raw_ints% [7908778099367578806981978825]) 0) 52 false) (.node 278 (sourceLit (List.headD (raw_ints% [71770729929827595323085]) 0) 69 false) (.node 277 (sourceLit (List.headD (raw_ints% [43635700198730179014630819599808713]) 0) 35 true) .empty .empty) (.node 279 (sourceLit (List.headD (raw_ints% [91412087485026895735295515701923311]) 0) 32 true) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [28598124793540963281053357925]) 0) 50 false) (.node 296 (sourceLit (List.headD (raw_ints% [1866638038069853856298174425]) 0) 55 false) .empty .empty) (.node 298 (sourceLit (List.headD (raw_ints% [1780762937167563066862298115]) 0) 55 false) .empty .empty))))

#time def treeG_J030_part023 : IntSourceTree :=
  (.node 307 (sourceLit (List.headD (raw_ints% [19867677827760049753814895]) 0) 60 false) (.node 303 (sourceLit (List.headD (raw_ints% [22157920981078619202659025]) 0) 60 false) (.node 301 (sourceLit (List.headD (raw_ints% [6062545626761255786281299375]) 0) 52 false) (.node 300 (sourceLit (List.headD (raw_ints% [214172553487264983335494605]) 0) 58 false) .empty .empty) (.node 302 (sourceLit (List.headD (raw_ints% [414571615609398201779637105]) 0) 57 false) .empty .empty)) (.node 305 (sourceLit (List.headD (raw_ints% [10468789140292835385835575]) 0) 61 false) (.node 304 (sourceLit (List.headD (raw_ints% [1574104662376414038627645]) 0) 65 false) .empty .empty) (.node 306 (sourceLit (List.headD (raw_ints% [767537962033893727845675]) 0) 66 false) .empty .empty))) (.node 311 (sourceLit (List.headD (raw_ints% [178241625257603308926525]) 0) 68 false) (.node 309 (sourceLit (List.headD (raw_ints% [18916655203026164404609335]) 0) 60 false) (.node 308 (sourceLit (List.headD (raw_ints% [187609262292729549169755]) 0) 68 false) .empty .empty) (.node 310 (sourceLit (List.headD (raw_ints% [1470484976888696664617865]) 0) 65 false) .empty .empty)) (.node 313 (sourceLit (List.headD (raw_ints% [26166405362236842493402065]) 0) 65 true) (.node 312 (sourceLit (List.headD (raw_ints% [97955425692327725344999870556411]) 0) 42 false) .empty .empty) (.node 314 (sourceLit (List.headD (raw_ints% [1607337335303885162983692913494689]) 0) 41 true) .empty .empty))))

#time def treeG_J030_part024 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [6547889636663323961602376325]) 0) 52 false) treeG_J030_part022 treeG_J030_part023)

#time def treeG_J030_part025 : IntSourceTree :=
  (.node 339 (sourceLit (List.headD (raw_ints% [4248283868459124412219153005]) 0) 54 false) (.node 319 (sourceLit (List.headD (raw_ints% [40900428122447881845]) 0) 80 false) (.node 317 (sourceLit (List.headD (raw_ints% [27228318502209355320020685]) 0) 67 true) (.node 316 (sourceLit (List.headD (raw_ints% [13400290244891535249202797524160505]) 0) 39 false) .empty .empty) (.node 318 (sourceLit (List.headD (raw_ints% [10031511876703140444547421155183789]) 0) 38 true) .empty .empty)) (.node 337 (sourceLit (List.headD (raw_ints% [8989068306373043236700893935]) 0) 53 false) (.node 336 (sourceLit (List.headD (raw_ints% [171864074281048371454514311575]) 0) 48 false) .empty .empty) (.node 338 (sourceLit (List.headD (raw_ints% [77882467474097870785695006975]) 0) 49 false) .empty .empty))) (.node 343 (sourceLit (List.headD (raw_ints% [122141756626409366523224385]) 0) 59 false) (.node 341 (sourceLit (List.headD (raw_ints% [1014927998021573724166051965]) 0) 56 false) (.node 340 (sourceLit (List.headD (raw_ints% [17937719717181405863449765275]) 0) 51 false) .empty .empty) (.node 342 (sourceLit (List.headD (raw_ints% [2091275984246199198712980975]) 0) 54 false) .empty .empty)) (.node 345 (sourceLit (List.headD (raw_ints% [7389181077165736117559655]) 0) 63 false) (.node 344 (sourceLit (List.headD (raw_ints% [123061352572648316970146475]) 0) 58 false) .empty .empty) (.node 346 (sourceLit (List.headD (raw_ints% [58282164028848011497797645]) 0) 59 false) .empty .empty))))

#time def treeG_J030_part026 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [150469635479248703158167435217041553]) 0) 36 true) (.node 351 (sourceLit (List.headD (raw_ints% [28955152102761455498748783236869]) 0) 39 false) (.node 349 (sourceLit (List.headD (raw_ints% [875156619930424058350695]) 0) 66 false) (.node 348 (sourceLit (List.headD (raw_ints% [27733531185997512478461405]) 0) 60 false) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [26494875296760026943074835]) 0) 60 false) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [7006959629438510557212746087720309]) 0) 38 false) (.node 352 (sourceLit (List.headD (raw_ints% [34188001974770007088936665]) 0) 63 false) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [189728848208308955652186255]) 0) 64 true) .empty .empty))) (.node 359 (sourceLit (List.headD (raw_ints% [1192621432732975081166774392161601681]) 0) 32 true) (.node 357 (sourceLit (List.headD (raw_ints% [472444988035259306989120340372944873]) 0) 35 false) (.node 356 (sourceLit (List.headD (raw_ints% [138638350215101890071455805]) 0) 66 false) .empty .empty) (.node 358 (sourceLit (List.headD (raw_ints% [27371859962069010510666855]) 0) 68 true) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [5427542432037917102976297705]) 0) 54 false) (.node 377 (sourceLit (List.headD (raw_ints% [114667824693966444892407595725]) 0) 49 false) .empty .empty) (.node 379 (sourceLit (List.headD (raw_ints% [51690908927444574939285501675]) 0) 50 false) .empty .empty))))

#time def treeG_J030_part027 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [3590653851356808207517455]) 0) 64 false) treeG_J030_part025 treeG_J030_part026)

#time def treeG_J030_part028 : IntSourceTree :=
  (.node 315 (sourceLit (List.headD (raw_ints% [27912980132069925850468965]) 0) 67 false) treeG_J030_part024 treeG_J030_part027)

#time def treeG_J030_part029 : IntSourceTree :=
  (.node 268 (sourceLit (List.headD (raw_ints% [12001824469522587029168385]) 0) 60 false) treeG_J030_part021 treeG_J030_part028)

#time def treeG_J030_part030 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [7736943107680841815694381235]) 0) 52 false) treeG_J030_part014 treeG_J030_part029)

#time def treeG_J030_part031 : IntSourceTree :=
  (.node 388 (sourceLit (List.headD (raw_ints% [2089779753014971814159415]) 0) 65 false) (.node 384 (sourceLit (List.headD (raw_ints% [71770407430364117287139745]) 0) 60 false) (.node 382 (sourceLit (List.headD (raw_ints% [150089095603043880596603715]) 0) 59 false) (.node 381 (sourceLit (List.headD (raw_ints% [2968793522605037519292116475]) 0) 54 false) .empty .empty) (.node 383 (sourceLit (List.headD (raw_ints% [1382222512851683384227892175]) 0) 55 false) .empty .empty)) (.node 386 (sourceLit (List.headD (raw_ints% [4319029229030161206176955]) 0) 64 false) (.node 385 (sourceLit (List.headD (raw_ints% [81186196011476975426804175]) 0) 59 false) .empty .empty) (.node 387 (sourceLit (List.headD (raw_ints% [19207243100543980871991375]) 0) 61 false) .empty .empty))) (.node 392 (sourceLit (List.headD (raw_ints% [362866550666549445881250698988775]) 0) 40 true) (.node 390 (sourceLit (List.headD (raw_ints% [2030141502832999568784915]) 0) 65 false) (.node 389 (sourceLit (List.headD (raw_ints% [36550407168968860552313475]) 0) 60 false) .empty .empty) (.node 391 (sourceLit (List.headD (raw_ints% [3679947263786803400479635]) 0) 61 false) .empty .empty)) (.node 394 (sourceLit (List.headD (raw_ints% [13436308970654051209147517741699065]) 0) 39 false) (.node 393 (sourceLit (List.headD (raw_ints% [86520812699243692075740795]) 0) 64 false) .empty .empty) (.node 395 (sourceLit (List.headD (raw_ints% [301380768736588659054062115]) 0) 65 true) .empty .empty))))

#time def treeG_J030_part032 : IntSourceTree :=
  (.node 422 (sourceLit (List.headD (raw_ints% [3846311060963875839871251975]) 0) 54 false) (.node 418 (sourceLit (List.headD (raw_ints% [151453181913835018999120184475]) 0) 49 false) (.node 398 (sourceLit (List.headD (raw_ints% [512571035542071868767310024993680029]) 0) 36 false) (.node 397 (sourceLit (List.headD (raw_ints% [82933334358655622695738245]) 0) 68 false) .empty .empty) (.node 399 (sourceLit (List.headD (raw_ints% [27455624038863783772685415]) 0) 69 true) .empty .empty)) (.node 420 (sourceLit (List.headD (raw_ints% [2109574325641448067239733525]) 0) 55 false) (.node 419 (sourceLit (List.headD (raw_ints% [6606800995616709793733442405]) 0) 54 false) .empty .empty) (.node 421 (sourceLit (List.headD (raw_ints% [189996930317428852671143025]) 0) 59 false) .empty .empty))) (.node 426 (sourceLit (List.headD (raw_ints% [104090227994105939355810705]) 0) 59 false) (.node 424 (sourceLit (List.headD (raw_ints% [889977102561090116347306275]) 0) 56 false) (.node 423 (sourceLit (List.headD (raw_ints% [178036434579678394669983045]) 0) 59 false) .empty .empty) (.node 425 (sourceLit (List.headD (raw_ints% [42213683121701172816901125]) 0) 61 false) .empty .empty)) (.node 428 (sourceLit (List.headD (raw_ints% [49095441216178411009504095]) 0) 60 false) (.node 427 (sourceLit (List.headD (raw_ints% [5047404606703514204836455]) 0) 64 false) .empty .empty) (.node 429 (sourceLit (List.headD (raw_ints% [75913945817784234738045]) 0) 70 false) .empty .empty))))

#time def treeG_J030_part033 : IntSourceTree :=
  (.node 396 (sourceLit (List.headD (raw_ints% [204070796458814844154978625313683573]) 0) 37 true) treeG_J030_part031 treeG_J030_part032)

#time def treeG_J030_part034 : IntSourceTree :=
  (.node 438 (sourceLit (List.headD (raw_ints% [193238528679380255902143345]) 0) 68 false) (.node 434 (sourceLit (List.headD (raw_ints% [362770473606796339803667845]) 0) 64 false) (.node 432 (sourceLit (List.headD (raw_ints% [64696056685753210777393695]) 0) 62 true) (.node 431 (sourceLit (List.headD (raw_ints% [243525827925989310048542228736251]) 0) 39 false) .empty .empty) (.node 433 (sourceLit (List.headD (raw_ints% [9909892034770906124262751679630509]) 0) 38 true) .empty .empty)) (.node 436 (sourceLit (List.headD (raw_ints% [13750597467240329660172435]) 0) 71 true) (.node 435 (sourceLit (List.headD (raw_ints% [365450579009713522504527719084226593]) 0) 36 false) .empty .empty) (.node 437 (sourceLit (List.headD (raw_ints% [2105011359705778060228949342882413457]) 0) 35 true) .empty .empty))) (.node 461 (sourceLit (List.headD (raw_ints% [5469503779960754749666817625]) 0) 54 false) (.node 459 (sourceLit (List.headD (raw_ints% [6235142061649402753739667675]) 0) 54 false) (.node 439 (sourceLit (List.headD (raw_ints% [17594894570079274881720695191959362609]) 0) 32 false) .empty .empty) (.node 460 (sourceLit (List.headD (raw_ints% [127246798595490789006195195]) 0) 60 false) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [308011068514024056955419975]) 0) 58 false) (.node 462 (sourceLit (List.headD (raw_ints% [229904765031813824745682335]) 0) 59 false) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [26566506787328569345710825]) 0) 62 false) .empty .empty))))

#time def treeG_J030_part035 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [237737682084240594928875285]) 0) 63 true) (.node 469 (sourceLit (List.headD (raw_ints% [61640475263387961466694715]) 0) 60 false) (.node 467 (sourceLit (List.headD (raw_ints% [65675741793017977611827955]) 0) 60 false) (.node 466 (sourceLit (List.headD (raw_ints% [24937566205580527992193305]) 0) 62 false) .empty .empty) (.node 468 (sourceLit (List.headD (raw_ints% [184851553355533899417315]) 0) 69 false) .empty .empty)) (.node 471 (sourceLit (List.headD (raw_ints% [1341437243043465336283515]) 0) 66 false) (.node 470 (sourceLit (List.headD (raw_ints% [2828351029505191454449965]) 0) 65 false) .empty .empty) (.node 472 (sourceLit (List.headD (raw_ints% [303196189296269377964896463862513]) 0) 41 false) .empty .empty))) (.node 477 (sourceLit (List.headD (raw_ints% [302942893834500897258497205]) 0) 68 true) (.node 475 (sourceLit (List.headD (raw_ints% [83018905292923124857216245]) 0) 68 false) (.node 474 (sourceLit (List.headD (raw_ints% [11673100502712478666705134710664787]) 0) 40 true) .empty .empty) (.node 476 (sourceLit (List.headD (raw_ints% [284760687734264183329753172198955083]) 0) 38 false) .empty .empty)) (.node 479 (sourceLit (List.headD (raw_ints% [27586769089780504959353595]) 0) 72 false) (.node 478 (sourceLit (List.headD (raw_ints% [1308791197623924964498129683938046743]) 0) 37 true) .empty .empty) (.node 500 (sourceLit (List.headD (raw_ints% [2062783868003977343249967075]) 0) 56 false) .empty .empty))))

#time def treeG_J030_part036 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [565232318515182214640089575]) 0) 57 false) treeG_J030_part034 treeG_J030_part035)

#time def treeG_J030_part037 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [46605939041177694161552115]) 0) 60 false) treeG_J030_part033 treeG_J030_part036)

#time def treeG_J030_part038 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [54468803768874832339635]) 0) 71 false) (.node 505 (sourceLit (List.headD (raw_ints% [64052344027613104565942175]) 0) 61 false) (.node 503 (sourceLit (List.headD (raw_ints% [281773095483949254821381625]) 0) 59 false) (.node 502 (sourceLit (List.headD (raw_ints% [7092696498957633659462383275]) 0) 54 false) .empty .empty) (.node 504 (sourceLit (List.headD (raw_ints% [1574111445551102339296053525]) 0) 56 false) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [14842756992173499582520395]) 0) 63 false) (.node 506 (sourceLit (List.headD (raw_ints% [357051862526970335928468165]) 0) 58 false) .empty .empty) (.node 508 (sourceLit (List.headD (raw_ints% [82256042369857544214151815]) 0) 60 false) .empty .empty))) (.node 513 (sourceLit (List.headD (raw_ints% [14761031063511216171701095101430717]) 0) 38 false) (.node 511 (sourceLit (List.headD (raw_ints% [136089021240658451172747563243269]) 0) 39 false) (.node 510 (sourceLit (List.headD (raw_ints% [76675011485598228771837315]) 0) 60 false) .empty .empty) (.node 512 (sourceLit (List.headD (raw_ints% [107622048463144101538466175]) 0) 62 false) .empty .empty)) (.node 515 (sourceLit (List.headD (raw_ints% [738989795096512839839092029825499777]) 0) 36 true) (.node 514 (sourceLit (List.headD (raw_ints% [300254077845518467366271565]) 0) 65 true) .empty .empty) (.node 516 (sourceLit (List.headD (raw_ints% [138021295161884443497905985]) 0) 69 false) .empty .empty))))

#time def treeG_J030_part039 : IntSourceTree :=
  (.node 546 (sourceLit (List.headD (raw_ints% [19557388911016288286874435]) 0) 63 false) (.node 542 (sourceLit (List.headD (raw_ints% [408075763097254781961593175]) 0) 59 false) (.node 519 (sourceLit (List.headD (raw_ints% [101357531218010472609600994963994354161]) 0) 32 true) (.node 518 (sourceLit (List.headD (raw_ints% [799124316348382050419137755]) 0) 68 true) .empty .empty) (.node 541 (sourceLit (List.headD (raw_ints% [11032767164071063996332918975]) 0) 54 false) .empty .empty)) (.node 544 (sourceLit (List.headD (raw_ints% [175507068334634977438538325]) 0) 60 false) (.node 543 (sourceLit (List.headD (raw_ints% [4628607950845441203819023475]) 0) 55 false) .empty .empty) (.node 545 (sourceLit (List.headD (raw_ints% [504439563517960062327981975]) 0) 58 false) .empty .empty))) (.node 550 (sourceLit (List.headD (raw_ints% [4143655852910787085023315]) 0) 65 false) (.node 548 (sourceLit (List.headD (raw_ints% [8927507284796414801166315]) 0) 64 false) (.node 547 (sourceLit (List.headD (raw_ints% [225700378940934380704812255]) 0) 59 false) .empty .empty) (.node 549 (sourceLit (List.headD (raw_ints% [102871609476327126961608915]) 0) 60 false) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [470303357351880304757045364481757]) 0) 40 true) (.node 551 (sourceLit (List.headD (raw_ints% [33749019708207338010764835]) 0) 61 false) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [86339932636846174116835365]) 0) 65 false) .empty .empty))))

#time def treeG_J030_part040 : IntSourceTree :=
  (.node 517 (sourceLit (List.headD (raw_ints% [6661182363454004993505000098065694785]) 0) 35 false) treeG_J030_part038 treeG_J030_part039)

#time def treeG_J030_part041 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [1527248252647169432261484975]) 0) 57 false) (.node 558 (sourceLit (List.headD (raw_ints% [9278764758701854922501259465941788271]) 0) 36 false) (.node 556 (sourceLit (List.headD (raw_ints% [1308511170565041206498598374223409943]) 0) 37 true) (.node 555 (sourceLit (List.headD (raw_ints% [632329699017210966795136545]) 0) 66 true) .empty .empty) (.node 557 (sourceLit (List.headD (raw_ints% [855028074482038671250121145]) 0) 68 false) .empty .empty)) (.node 582 (sourceLit (List.headD (raw_ints% [14972837829184494333203454675]) 0) 54 false) (.node 559 (sourceLit (List.headD (raw_ints% [1019818469066626090093966515]) 0) 69 true) .empty .empty) (.node 583 (sourceLit (List.headD (raw_ints% [534378430710560309101804725]) 0) 59 false) .empty .empty))) (.node 588 (sourceLit (List.headD (raw_ints% [17930542071384604561332555]) 0) 63 false) (.node 586 (sourceLit (List.headD (raw_ints% [651827264508949788727495785]) 0) 58 false) (.node 585 (sourceLit (List.headD (raw_ints% [55727362153510936436298075]) 0) 62 false) .empty .empty) (.node 587 (sourceLit (List.headD (raw_ints% [24272020829859076991228475]) 0) 63 false) .empty .empty)) (.node 590 (sourceLit (List.headD (raw_ints% [129068207467056025151380515]) 0) 60 false) (.node 589 (sourceLit (List.headD (raw_ints% [5441503843588425531429675]) 0) 65 false) .empty .empty) (.node 591 (sourceLit (List.headD (raw_ints% [420063052950929578070824603085051]) 0) 39 false) .empty .empty))))

#time def treeG_J030_part042 : IntSourceTree :=
  (.node 623 (sourceLit (List.headD (raw_ints% [323257183698095410293263475]) 0) 60 false) (.node 596 (sourceLit (List.headD (raw_ints% [1184414879664748740786760485]) 0) 67 true) (.node 594 (sourceLit (List.headD (raw_ints% [472933943119210815599942295]) 0) 65 false) (.node 593 (sourceLit (List.headD (raw_ints% [18523457922326258609757458017284773]) 0) 38 true) .empty .empty) (.node 595 (sourceLit (List.headD (raw_ints% [1348705508199491615920873862189664433]) 0) 36 false) .empty .empty)) (.node 598 (sourceLit (List.headD (raw_ints% [2509180465312459392919380045]) 0) 68 false) (.node 597 (sourceLit (List.headD (raw_ints% [17129271727974334645493787091852974329]) 0) 35 true) .empty .empty) (.node 599 (sourceLit (List.headD (raw_ints% [398278003496469830129641297874131578833]) 0) 32 false) .empty .empty))) (.node 627 (sourceLit (List.headD (raw_ints% [213063442784007704011341765]) 0) 60 false) (.node 625 (sourceLit (List.headD (raw_ints% [127851086141151171241687875]) 0) 61 false) (.node 624 (sourceLit (List.headD (raw_ints% [11214730074247666614477075]) 0) 65 false) .empty .empty) (.node 626 (sourceLit (List.headD (raw_ints% [4521246655311831018677955]) 0) 66 false) .empty .empty)) (.node 629 (sourceLit (List.headD (raw_ints% [184017063665826546019711965]) 0) 60 false) (.node 628 (sourceLit (List.headD (raw_ints% [959032096566416386878885]) 0) 68 false) .empty .empty) (.node 630 (sourceLit (List.headD (raw_ints% [6739351834266063977836035]) 0) 65 false) .empty .empty))))

#time def treeG_J030_part043 : IntSourceTree :=
  (.node 592 (sourceLit (List.headD (raw_ints% [18468257188734190881925335]) 0) 64 true) treeG_J030_part041 treeG_J030_part042)

#time def treeG_J030_part044 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [38107232068936173505111364522760291]) 0) 39 false) treeG_J030_part040 treeG_J030_part043)

#time def treeG_J030_part045 : IntSourceTree :=
  (.node 501 (sourceLit (List.headD (raw_ints% [318990264064534303353637755]) 0) 59 false) treeG_J030_part037 treeG_J030_part044)

#time def treeG_J030_part046 : IntSourceTree :=
  (.node 639 (sourceLit (List.headD (raw_ints% [13785152087418302668020885]) 0) 77 false) (.node 635 (sourceLit (List.headD (raw_ints% [138157955267052722799384855]) 0) 69 false) (.node 633 (sourceLit (List.headD (raw_ints% [26202047456395091249690175]) 0) 67 true) (.node 632 (sourceLit (List.headD (raw_ints% [111295801287851235353483745945851]) 0) 43 false) .empty .empty) (.node 634 (sourceLit (List.headD (raw_ints% [7078836248907804014358602817505633]) 0) 42 true) .empty .empty)) (.node 637 (sourceLit (List.headD (raw_ints% [1019721477073393706018440815]) 0) 69 true) (.node 636 (sourceLit (List.headD (raw_ints% [332152084845566602802434029551634297]) 0) 40 false) .empty .empty) (.node 638 (sourceLit (List.headD (raw_ints% [3301004560834523695999380819724345325]) 0) 39 true) .empty .empty))) (.node 667 (sourceLit (List.headD (raw_ints% [48067925655130219307618805]) 0) 63 false) (.node 665 (sourceLit (List.headD (raw_ints% [123708319034451729395335125]) 0) 62 false) (.node 664 (sourceLit (List.headD (raw_ints% [3644866686522357132430730625]) 0) 57 false) .empty .empty) (.node 666 (sourceLit (List.headD (raw_ints% [1393790113749468951139510215]) 0) 58 false) .empty .empty)) (.node 669 (sourceLit (List.headD (raw_ints% [9903009701474236658632485]) 0) 65 false) (.node 668 (sourceLit (List.headD (raw_ints% [141341274498469285766011545]) 0) 61 false) .empty .empty) (.node 670 (sourceLit (List.headD (raw_ints% [238965919864597066888043415]) 0) 60 false) .empty .empty))))

#time def treeG_J030_part047 : IntSourceTree :=
  (.node 679 (sourceLit (List.headD (raw_ints% [1243335171070107896305482787723563982033]) 0) 32 true) (.node 675 (sourceLit (List.headD (raw_ints% [2254796548059690529758775022830385457]) 0) 36 true) (.node 673 (sourceLit (List.headD (raw_ints% [25646389204748737672380417757819237]) 0) 38 false) (.node 672 (sourceLit (List.headD (raw_ints% [42298054128446362667079255]) 0) 64 false) .empty .empty) (.node 674 (sourceLit (List.headD (raw_ints% [682550322770371545597463695]) 0) 65 true) .empty .empty)) (.node 677 (sourceLit (List.headD (raw_ints% [38387005158090597224849564983157569337]) 0) 35 false) (.node 676 (sourceLit (List.headD (raw_ints% [2289678521801170523181839325]) 0) 67 false) .empty .empty) (.node 678 (sourceLit (List.headD (raw_ints% [6588066373606034216993143305]) 0) 68 true) .empty .empty))) (.node 708 (sourceLit (List.headD (raw_ints% [32723412110067557117556645]) 0) 64 false) (.node 706 (sourceLit (List.headD (raw_ints% [87538345791957081245911485]) 0) 63 false) (.node 705 (sourceLit (List.headD (raw_ints% [2622057997393147762497227625]) 0) 58 false) .empty .empty) (.node 707 (sourceLit (List.headD (raw_ints% [967663228181453543116826685]) 0) 59 false) .empty .empty)) (.node 710 (sourceLit (List.headD (raw_ints% [13066667568682409339428935]) 0) 65 false) (.node 709 (sourceLit (List.headD (raw_ints% [381348034328050597044334215]) 0) 60 false) .empty .empty) (.node 711 (sourceLit (List.headD (raw_ints% [143646732105748379747427735]) 0) 61 false) .empty .empty))))

#time def treeG_J030_part048 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [484477438436894076536970371143429]) 0) 39 false) treeG_J030_part046 treeG_J030_part047)

#time def treeG_J030_part049 : IntSourceTree :=
  (.node 746 (sourceLit (List.headD (raw_ints% [3850325881036826573854945035]) 0) 58 false) (.node 716 (sourceLit (List.headD (raw_ints% [4912013226824223352178247259243459833]) 0) 37 true) (.node 714 (sourceLit (List.headD (raw_ints% [82277079196011169787249240297864301]) 0) 39 false) (.node 713 (sourceLit (List.headD (raw_ints% [147106243954026727665839955]) 0) 65 false) .empty .empty) (.node 715 (sourceLit (List.headD (raw_ints% [1787813964906793327992542535]) 0) 66 true) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [64795041644766786792844611540952331937]) 0) 36 false) (.node 717 (sourceLit (List.headD (raw_ints% [4329121475947957935218720955]) 0) 68 false) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [10117065307985119700006489865]) 0) 69 true) .empty .empty))) (.node 750 (sourceLit (List.headD (raw_ints% [523730148791504127200625015]) 0) 60 false) (.node 748 (sourceLit (List.headD (raw_ints% [684980679184514971584803595]) 0) 60 false) (.node 747 (sourceLit (List.headD (raw_ints% [127008765928783943184204165]) 0) 63 false) .empty .empty) (.node 749 (sourceLit (List.headD (raw_ints% [178284393817135316085345]) 0) 72 false) .empty .empty)) (.node 752 (sourceLit (List.headD (raw_ints% [25545484408037070920889285]) 0) 62 true) (.node 751 (sourceLit (List.headD (raw_ints% [1269300995162942858567162102016251]) 0) 39 false) .empty .empty) (.node 753 (sourceLit (List.headD (raw_ints% [28893500979676064122707614529206269]) 0) 38 true) .empty .empty))))

#time def treeG_J030_part050 : IntSourceTree :=
  (.node 789 (sourceLit (List.headD (raw_ints% [988613324040979346125272975]) 0) 60 false) (.node 758 (sourceLit (List.headD (raw_ints% [15246309325501950087430585215]) 0) 68 false) (.node 756 (sourceLit (List.headD (raw_ints% [1019373121676990962793595465]) 0) 69 true) (.node 755 (sourceLit (List.headD (raw_ints% [3571229815195869246354762867596214273]) 0) 36 false) .empty .empty) (.node 757 (sourceLit (List.headD (raw_ints% [77683110972684384042275543057105248001]) 0) 35 true) .empty .empty)) (.node 787 (sourceLit (List.headD (raw_ints% [1441331326427686515369059175]) 0) 60 false) (.node 759 (sourceLit (List.headD (raw_ints% [3316776503702645073676510357034038604017]) 0) 32 false) .empty .empty) (.node 788 (sourceLit (List.headD (raw_ints% [2946417306834887064582735]) 0) 69 false) .empty .empty))) (.node 793 (sourceLit (List.headD (raw_ints% [613970460224143981584249105]) 0) 63 true) (.node 791 (sourceLit (List.headD (raw_ints% [11877606771429867107912415]) 0) 66 false) (.node 790 (sourceLit (List.headD (raw_ints% [32574137248504231578419385]) 0) 65 false) .empty .empty) (.node 792 (sourceLit (List.headD (raw_ints% [837594983514429332429030849219815]) 0) 41 false) .empty .empty)) (.node 795 (sourceLit (List.headD (raw_ints% [691144193896304582230421535]) 0) 68 false) (.node 794 (sourceLit (List.headD (raw_ints% [55585290087843616954978427413535285]) 0) 40 true) .empty .empty) (.node 796 (sourceLit (List.headD (raw_ints% [4241621521010046299266505063419837053]) 0) 38 false) .empty .empty))))

#time def treeG_J030_part051 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [976762810678425000929143605]) 0) 65 false) treeG_J030_part049 treeG_J030_part050)

#time def treeG_J030_part052 : IntSourceTree :=
  (.node 712 (sourceLit (List.headD (raw_ints% [405888971865915806290899596423379]) 0) 40 true) treeG_J030_part048 treeG_J030_part051)

#time def treeG_J030_part053 : IntSourceTree :=
  (.node 833 (sourceLit (List.headD (raw_ints% [42295020715906933441572108116723309]) 0) 38 false) (.node 829 (sourceLit (List.headD (raw_ints% [2233279731566345800241355]) 0) 70 false) (.node 799 (sourceLit (List.headD (raw_ints% [3170421829185883723429634385]) 0) 72 false) (.node 798 (sourceLit (List.headD (raw_ints% [71239076308725585417560077299028789969]) 0) 37 true) .empty .empty) (.node 828 (sourceLit (List.headD (raw_ints% [2197681973670858059153314755]) 0) 60 false) .empty .empty)) (.node 831 (sourceLit (List.headD (raw_ints% [3102725697891466502274141583841029]) 0) 39 false) (.node 830 (sourceLit (List.headD (raw_ints% [1453496499290454565049920935]) 0) 60 false) .empty .empty) (.node 832 (sourceLit (List.headD (raw_ints% [405628901093792818374086565]) 0) 62 false) .empty .empty))) (.node 837 (sourceLit (List.headD (raw_ints% [145549055308845124830539624071822640849]) 0) 35 false) (.node 835 (sourceLit (List.headD (raw_ints% [5349959098006864988914072544829343393]) 0) 36 true) (.node 834 (sourceLit (List.headD (raw_ints% [2567496081580993983442536315]) 0) 64 true) .empty .empty) (.node 836 (sourceLit (List.headD (raw_ints% [213814664446661943128002125]) 0) 72 false) .empty .empty)) (.node 839 (sourceLit (List.headD (raw_ints% [7876077387461082540400355304171881162033]) 0) 32 true) (.node 838 (sourceLit (List.headD (raw_ints% [32059537250813793660216790845]) 0) 68 true) .empty .empty) (.node 869 (sourceLit (List.headD (raw_ints% [3406750623300736772181356535]) 0) 60 false) .empty .empty))))

#time def treeG_J030_part054 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [288027207926296295665659778669880220787]) 0) 36 false) (.node 874 (sourceLit (List.headD (raw_ints% [153465600891594167351528962943793879]) 0) 39 false) (.node 872 (sourceLit (List.headD (raw_ints% [1427535730862607837416079885401399]) 0) 40 false) (.node 871 (sourceLit (List.headD (raw_ints% [1073413082604698817596723655]) 0) 61 false) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [509799680658968399979167835]) 0) 64 false) .empty .empty)) (.node 876 (sourceLit (List.headD (raw_ints% [13833202140026957587447082671669017499]) 0) 37 true) (.node 875 (sourceLit (List.headD (raw_ints% [8096649632751430641285908595]) 0) 65 true) .empty .empty) (.node 877 (sourceLit (List.headD (raw_ints% [15248683224949103966489170815]) 0) 68 false) .empty .empty))) (.node 912 (sourceLit (List.headD (raw_ints% [333892090755452999611318545]) 0) 63 false) (.node 910 (sourceLit (List.headD (raw_ints% [5360004747311018979312792135]) 0) 60 false) (.node 879 (sourceLit (List.headD (raw_ints% [57422911884300863447653865925]) 0) 69 true) .empty .empty) (.node 911 (sourceLit (List.headD (raw_ints% [11708974428848352269411691993753851]) 0) 39 false) .empty .empty)) (.node 914 (sourceLit (List.headD (raw_ints% [3587095442898930783400871985]) 0) 64 false) (.node 913 (sourceLit (List.headD (raw_ints% [30874734869006070742243469033512117]) 0) 38 true) .empty .empty) (.node 915 (sourceLit (List.headD (raw_ints% [7805408712272371666538535951930045457]) 0) 36 false) .empty .empty))))

#time def treeG_J030_part055 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [110355765571741899637027335]) 0) 65 false) treeG_J030_part053 treeG_J030_part054)

#time def treeG_J030_part056 : IntSourceTree :=
  (.node 955 (sourceLit (List.headD (raw_ints% [2920936268912590356171695145]) 0) 67 false) (.node 951 (sourceLit (List.headD (raw_ints% [33488997380518126263406785]) 0) 68 false) (.node 918 (sourceLit (List.headD (raw_ints% [62556903700712001593195132475]) 0) 68 false) (.node 917 (sourceLit (List.headD (raw_ints% [256214672429060785530116285445174780841]) 0) 35 true) .empty .empty) (.node 919 (sourceLit (List.headD (raw_ints% [17092948041102564001701468221608048227217]) 0) 32 false) .empty .empty)) (.node 953 (sourceLit (List.headD (raw_ints% [87953794951757700183924645]) 0) 65 true) (.node 952 (sourceLit (List.headD (raw_ints% [2570359674496436107998903027088113]) 0) 42 false) .empty .empty) (.node 954 (sourceLit (List.headD (raw_ints% [46085083940150059523443107994326499]) 0) 41 true) .empty .empty))) (.node 959 (sourceLit (List.headD (raw_ints% [29291947164309781504113525]) 0) 81 false) (.node 957 (sourceLit (List.headD (raw_ints% [52278154607236002934456386225]) 0) 67 true) (.node 956 (sourceLit (List.headD (raw_ints% [5409652713074832313496404655899765739]) 0) 39 false) .empty .empty) (.node 958 (sourceLit (List.headD (raw_ints% [136060470088839270298944016028763750407]) 0) 38 true) .empty .empty)) (.node 994 (sourceLit (List.headD (raw_ints% [3938910622705961584136570565]) 0) 64 true) (.node 993 (sourceLit (List.headD (raw_ints% [113126244452892026198208365900331733]) 0) 38 false) .empty .empty) (.node 995 (sourceLit (List.headD (raw_ints% [10754854084441975476038894863566941393]) 0) 36 true) .empty .empty))))

#time def treeG_J030_part057 : IntSourceTree :=
  (.node 1038 (sourceLit (List.headD (raw_ints% [973565439602812500757777298549022286117]) 0) 36 false) (.node 1034 (sourceLit (List.headD (raw_ints% [297466580213492264291980797877637729]) 0) 39 false) (.node 998 (sourceLit (List.headD (raw_ints% [28708764576987001131912879675]) 0) 70 true) (.node 997 (sourceLit (List.headD (raw_ints% [429323559247455419562001234433967284489]) 0) 35 false) .empty .empty) (.node 999 (sourceLit (List.headD (raw_ints% [34508688212473990599966302273289808279313]) 0) 32 true) .empty .empty)) (.node 1036 (sourceLit (List.headD (raw_ints% [32393464936741304730024513487166004349]) 0) 37 true) (.node 1035 (sourceLit (List.headD (raw_ints% [15622655698356323008823351145]) 0) 65 true) .empty .empty) (.node 1037 (sourceLit (List.headD (raw_ints% [10717835980028019920077651425]) 0) 70 false) .empty .empty))) (.node 1077 (sourceLit (List.headD (raw_ints% [688471278741385857402197342331295319281]) 0) 35 true) (.node 1075 (sourceLit (List.headD (raw_ints% [15514319367857851704710587629609145057]) 0) 36 false) (.node 1039 (sourceLit (List.headD (raw_ints% [58703718473240217392125129275]) 0) 71 true) .empty .empty) (.node 1076 (sourceLit (List.headD (raw_ints% [766987327052257491171690255]) 0) 72 true) .empty .empty)) (.node 1079 (sourceLit (List.headD (raw_ints% [65662782279763990624215175826858521435057]) 0) 32 false) (.node 1078 (sourceLit (List.headD (raw_ints% [50144436537043040972068182525]) 0) 70 false) .empty .empty) .empty)))

#time def treeG_J030_part058 : IntSourceTree :=
  (.node 996 (sourceLit (List.headD (raw_ints% [33464533232988156426164825175]) 0) 66 false) treeG_J030_part056 treeG_J030_part057)

#time def treeG_J030_part059 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [21780788157337795001478044595]) 0) 66 true) treeG_J030_part055 treeG_J030_part058)

#time def treeG_J030_part060 : IntSourceTree :=
  (.node 797 (sourceLit (List.headD (raw_ints% [8406613962655921786393102815]) 0) 68 true) treeG_J030_part052 treeG_J030_part059)

#time def treeG_J030_part061 : IntSourceTree :=
  (.node 631 (sourceLit (List.headD (raw_ints% [186170288591501342071515]) 0) 70 false) treeG_J030_part045 treeG_J030_part060)

#time def treeG_J030_part062 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [2534903440561004545535196165]) 0) 55 false) treeG_J030_part030 treeG_J030_part061)

#time def treeG_J030 : IntSourceTree := treeG_J030_part062

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J021_check : treeG_J021.check 40 (sourceBaseG momentData 21) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J022_check : treeG_J022.check 40 (sourceBaseG momentData 22) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J023_check : treeG_J023.check 40 (sourceBaseG momentData 23) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J024_check : treeG_J024.check 40 (sourceBaseG momentData 24) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J025_check : treeG_J025.check 40 (sourceBaseG momentData 25) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J026_check : treeG_J026.check 40 (sourceBaseG momentData 26) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J027_check : treeG_J027.check 40 (sourceBaseG momentData 27) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J028_check : treeG_J028.check 40 (sourceBaseG momentData 28) = true := by
  decide +kernel

-- kcost: 1.602s estimated (534 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J029_check : treeG_J029.check 40 (sourceBaseG momentData 29) = true := by
  decide +kernel

-- kcost: 1.530s estimated (510 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J030_check : treeG_J030.check 40 (sourceBaseG momentData 30) = true := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
