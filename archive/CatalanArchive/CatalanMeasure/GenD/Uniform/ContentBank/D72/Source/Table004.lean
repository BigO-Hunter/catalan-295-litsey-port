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

#time def treeG_J012_part000 : IntSourceTree :=
  (.node 6 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 4 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 39 false) (.node 3 (sourceLit (List.headD (raw_ints% [10406497287226355785106167749075]) 0) 40 false) (.node 2 (sourceLit (List.headD (raw_ints% [11871874581330315826470131760825]) 0) 38 false) .empty .empty) .empty) (.node 5 (sourceLit (List.headD (raw_ints% [2438674624313238394064804919525]) 0) 42 false) .empty .empty)) (.node 9 (sourceLit (List.headD (raw_ints% [139753972818880455160846846125]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 43 true) (.node 7 (sourceLit (List.headD (raw_ints% [1162212070732496172273106997775]) 0) 43 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [188442453671909775023335424775]) 0) 45 true) .empty .empty)))

#time def treeG_J012_part001 : IntSourceTree :=
  (.node 16 (sourceLit (List.headD (raw_ints% [3814624568257282895209219125]) 0) 51 false) (.node 14 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 49 false) (.node 13 (sourceLit (List.headD (raw_ints% [69025304895041329823223257089275]) 0) 39 true) (.node 12 (sourceLit (List.headD (raw_ints% [323688233819213441308025921025]) 0) 46 true) .empty .empty) .empty) (.node 15 (sourceLit (List.headD (raw_ints% [53045495794559912022201364609275]) 0) 38 true) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [934277033295099233158193775]) 0) 53 false) (.node 17 (sourceLit (List.headD (raw_ints% [129307510396114422838029894531825]) 0) 36 true) .empty .empty) (.node 19 (sourceLit (List.headD (raw_ints% [178080075616971488129486123142375]) 0) 35 true) .empty .empty)))

#time def treeG_J012_part002 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 47 false) treeG_J012_part000 treeG_J012_part001)

#time def treeG_J012_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [4600393246616255153658899313932925]) 0) 29 true) (.node 23 (sourceLit (List.headD (raw_ints% [1536589106694132122808243436803525]) 0) 31 true) (.node 22 (sourceLit (List.headD (raw_ints% [28149682860660474208277325]) 0) 58 false) (.node 21 (sourceLit (List.headD (raw_ints% [1033786650125764869913724982188625]) 0) 32 true) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [27691210676709753658480125]) 0) 58 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [3359207212647079442034015]) 0) 61 false) (.node 27 (sourceLit (List.headD (raw_ints% [6842302648610062214328001201007775]) 0) 28 true) (.node 26 (sourceLit (List.headD (raw_ints% [6816860719312144041074025]) 0) 60 false) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [79698700076612939220178406939123025]) 0) 24 true) .empty .empty)))

#time def treeG_J012_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [302850651584367716806592346662039745]) 0) 20 true) (.node 33 (sourceLit (List.headD (raw_ints% [285302316712647099081680789084483295]) 0) 21 true) (.node 32 (sourceLit (List.headD (raw_ints% [51096571466451484793085]) 0) 67 false) (.node 31 (sourceLit (List.headD (raw_ints% [111173191469092558336795834708592025]) 0) 23 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [12615859307681623557675]) 0) 69 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [599193844236790540114264262414338845]) 0) 17 true) (.node 36 (sourceLit (List.headD (raw_ints% [6233241033107314872525]) 0) 70 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [192579774559805047041]) 0) 75 false) .empty .empty)))

#time def treeG_J012_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [414156814146764197441065]) 0) 64 false) treeG_J012_part003 treeG_J012_part004)

#time def treeG_J012_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [458380723923192298686111225]) 0) 54 false) treeG_J012_part002 treeG_J012_part005)

#time def treeG_J012_part007 : IntSourceTree :=
  (.node 47 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 45 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 40 false) (.node 44 (sourceLit (List.headD (raw_ints% [10406497287226355785106167749075]) 0) 41 false) (.node 43 (sourceLit (List.headD (raw_ints% [11871874581330315826470131760825]) 0) 39 false) .empty .empty) .empty) (.node 46 (sourceLit (List.headD (raw_ints% [2438674624313238394064804919525]) 0) 43 false) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [139753972818880455160846846125]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 44 true) (.node 48 (sourceLit (List.headD (raw_ints% [1162212070732496172273106997775]) 0) 44 false) .empty .empty) .empty) (.node 51 (sourceLit (List.headD (raw_ints% [188442453671909775023335424775]) 0) 46 true) .empty .empty)))

#time def treeG_J012_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [3814624568257282895209219125]) 0) 52 false) (.node 55 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 50 false) (.node 54 (sourceLit (List.headD (raw_ints% [69025304895041329823223257089275]) 0) 40 true) (.node 53 (sourceLit (List.headD (raw_ints% [323688233819213441308025921025]) 0) 47 true) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [53045495794559912022201364609275]) 0) 39 true) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [934277033295099233158193775]) 0) 54 false) (.node 58 (sourceLit (List.headD (raw_ints% [129307510396114422838029894531825]) 0) 37 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [178080075616971488129486123142375]) 0) 36 true) .empty .empty)))

#time def treeG_J012_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 48 false) treeG_J012_part007 treeG_J012_part008)

#time def treeG_J012_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [4600393246616255153658899313932925]) 0) 30 true) (.node 64 (sourceLit (List.headD (raw_ints% [1536589106694132122808243436803525]) 0) 32 true) (.node 63 (sourceLit (List.headD (raw_ints% [28149682860660474208277325]) 0) 59 false) (.node 62 (sourceLit (List.headD (raw_ints% [1033786650125764869913724982188625]) 0) 33 true) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [27691210676709753658480125]) 0) 59 false) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [3359207212647079442034015]) 0) 62 false) (.node 68 (sourceLit (List.headD (raw_ints% [6842302648610062214328001201007775]) 0) 29 true) (.node 67 (sourceLit (List.headD (raw_ints% [6816860719312144041074025]) 0) 61 false) .empty .empty) .empty) (.node 70 (sourceLit (List.headD (raw_ints% [79698700076612939220178406939123025]) 0) 25 true) .empty .empty)))

#time def treeG_J012_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [302850651584367716806592346662039745]) 0) 21 true) (.node 74 (sourceLit (List.headD (raw_ints% [285302316712647099081680789084483295]) 0) 22 true) (.node 73 (sourceLit (List.headD (raw_ints% [51096571466451484793085]) 0) 68 false) (.node 72 (sourceLit (List.headD (raw_ints% [111173191469092558336795834708592025]) 0) 24 true) .empty .empty) .empty) (.node 75 (sourceLit (List.headD (raw_ints% [12615859307681623557675]) 0) 70 false) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [599193844236790540114264262414338845]) 0) 18 true) (.node 77 (sourceLit (List.headD (raw_ints% [6233241033107314872525]) 0) 71 false) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [192579774559805047041]) 0) 76 false) .empty .empty)))

#time def treeG_J012_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [414156814146764197441065]) 0) 65 false) treeG_J012_part010 treeG_J012_part011)

#time def treeG_J012_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [458380723923192298686111225]) 0) 55 false) treeG_J012_part009 treeG_J012_part012)

#time def treeG_J012_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [1942047668929799334433365777193553175]) 0) 16 false) treeG_J012_part006 treeG_J012_part013)

#time def treeG_J012_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [882704125094735261951413305525]) 0) 45 false) (.node 87 (sourceLit (List.headD (raw_ints% [3715137177893980615856502841275]) 0) 43 false) (.node 86 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 41 false) (.node 85 (sourceLit (List.headD (raw_ints% [3983911331456558695520681414775]) 0) 43 false) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 43 false) .empty .empty)) (.node 92 (sourceLit (List.headD (raw_ints% [53196673524606108738644928525]) 0) 46 true) (.node 91 (sourceLit (List.headD (raw_ints% [211885055564109077179348444125]) 0) 47 false) (.node 90 (sourceLit (List.headD (raw_ints% [9918023877468935527543969725]) 0) 48 true) .empty .empty) .empty) (.node 93 (sourceLit (List.headD (raw_ints% [138271144330460806960984791169275]) 0) 39 false) .empty .empty)))

#time def treeG_J012_part016 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [856380007551943894574753033112225]) 0) 35 true) (.node 97 (sourceLit (List.headD (raw_ints% [719420422316844169517191939216575]) 0) 36 true) (.node 96 (sourceLit (List.headD (raw_ints% [5895328878215800838050611375]) 0) 52 false) (.node 95 (sourceLit (List.headD (raw_ints% [499156943365770726563584692104925]) 0) 38 true) .empty .empty) .empty) (.node 98 (sourceLit (List.headD (raw_ints% [1440173767481091831025512675]) 0) 54 false) .empty .empty)) (.node 101 (sourceLit (List.headD (raw_ints% [4664775769617322750229830958367375]) 0) 32 true) (.node 100 (sourceLit (List.headD (raw_ints% [1410173342667006167630276325]) 0) 54 false) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [345781992480550401853001925]) 0) 56 false) .empty .empty)))

#time def treeG_J012_part017 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [354898798468591210450646804775]) 0) 48 true) treeG_J012_part015 treeG_J012_part016)

#time def treeG_J012_part018 : IntSourceTree :=
  (.node 108 (sourceLit (List.headD (raw_ints% [10274514225977208640114035]) 0) 61 false) (.node 106 (sourceLit (List.headD (raw_ints% [5218587489349402404351525]) 0) 62 false) (.node 105 (sourceLit (List.headD (raw_ints% [19985032460489858811272995674923475]) 0) 29 true) (.node 104 (sourceLit (List.headD (raw_ints% [84907520765932143174629175]) 0) 58 false) .empty .empty) .empty) (.node 107 (sourceLit (List.headD (raw_ints% [29960843324319979014943193310455625]) 0) 28 true) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [526416409143810955424631420804392175]) 0) 23 true) (.node 110 (sourceLit (List.headD (raw_ints% [2530893584353551047151885]) 0) 63 false) (.node 109 (sourceLit (List.headD (raw_ints% [358208669434431042496813669925374575]) 0) 24 true) .empty .empty) .empty) (.node 112 (sourceLit (List.headD (raw_ints% [311963671213861227854895]) 0) 66 false) .empty .empty)))

#time def treeG_J012_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [4692602836628874496197]) 0) 72 false) (.node 116 (sourceLit (List.headD (raw_ints% [18998477582255932242825]) 0) 70 false) (.node 115 (sourceLit (List.headD (raw_ints% [1979567882116809075846853966013826615]) 0) 20 true) (.node 114 (sourceLit (List.headD (raw_ints% [19240356079384930617705]) 0) 70 false) .empty .empty) .empty) (.node 117 (sourceLit (List.headD (raw_ints% [9092027006462976397696690830770932995]) 0) 17 true) .empty .empty)) (.node 125 (sourceLit (List.headD (raw_ints% [4373848529963800567646890648725]) 0) 42 false) (.node 119 (sourceLit (List.headD (raw_ints% [6735598422824123655347479876508263935]) 0) 16 true) .empty .empty) (.node 126 (sourceLit (List.headD (raw_ints% [5529148038599878996976557910025]) 0) 43 false) .empty .empty)))

#time def treeG_J012_part020 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [1493468746792833834307052566252989105]) 0) 21 true) treeG_J012_part018 treeG_J012_part019)

#time def treeG_J012_part021 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [6733704094311986836501556420705475]) 0) 31 true) treeG_J012_part017 treeG_J012_part020)

#time def treeG_J012_part022 : IntSourceTree :=
  (.node 132 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 53 false) (.node 130 (sourceLit (List.headD (raw_ints% [603196179456974351629719613275]) 0) 46 false) (.node 129 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 45 false) (.node 128 (sourceLit (List.headD (raw_ints% [638231276790371110895848960875]) 0) 46 false) .empty .empty) .empty) (.node 131 (sourceLit (List.headD (raw_ints% [109098262652158290802983666975]) 0) 46 false) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [386109363117968979593267688525]) 0) 49 true) (.node 134 (sourceLit (List.headD (raw_ints% [103648224612751068392104024129275]) 0) 41 false) (.node 133 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 49 false) .empty .empty) .empty) (.node 136 (sourceLit (List.headD (raw_ints% [223055723785605407270691663747825]) 0) 40 true) .empty .empty)))

#time def treeG_J012_part023 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [1815494559745778940158052988089375]) 0) 34 true) (.node 140 (sourceLit (List.headD (raw_ints% [339149965967486203222633454984925]) 0) 37 true) (.node 139 (sourceLit (List.headD (raw_ints% [1946070501667084428892831575]) 0) 54 false) (.node 138 (sourceLit (List.headD (raw_ints% [295056455960364873339581022342375]) 0) 38 true) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [237948154685953467236041275]) 0) 57 false) .empty .empty)) (.node 144 (sourceLit (List.headD (raw_ints% [2598557493808927356846656491950975]) 0) 33 true) (.node 143 (sourceLit (List.headD (raw_ints% [233183261037908505019892625]) 0) 57 false) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [28608155044611194758074525]) 0) 60 false) .empty .empty)))

#time def treeG_J012_part024 : IntSourceTree :=
  (.node 137 (sourceLit (List.headD (raw_ints% [7976033188174318780892003625]) 0) 52 false) treeG_J012_part022 treeG_J012_part023)

#time def treeG_J012_part025 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [1702579956060022652269755]) 0) 64 false) (.node 149 (sourceLit (List.headD (raw_ints% [1728826753332532299520005]) 0) 64 false) (.node 148 (sourceLit (List.headD (raw_ints% [11559270337854958400307596054723925]) 0) 30 true) (.node 147 (sourceLit (List.headD (raw_ints% [14057489238085465576332075]) 0) 61 false) .empty .empty) .empty) (.node 150 (sourceLit (List.headD (raw_ints% [139254984678909051638317631493125775]) 0) 26 true) .empty .empty)) (.node 153 (sourceLit (List.headD (raw_ints% [209770528280958258268725]) 0) 67 false) (.node 152 (sourceLit (List.headD (raw_ints% [207621608837359198543917793047900075]) 0) 25 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [604083215040093367612685888584252905]) 0) 23 true) .empty .empty)))

#time def treeG_J012_part026 : IntSourceTree :=
  (.node 166 (sourceLit (List.headD (raw_ints% [14371216598452487579411212131525]) 0) 41 false) (.node 158 (sourceLit (List.headD (raw_ints% [4246416581113092928791213284178297075]) 0) 19 true) (.node 157 (sourceLit (List.headD (raw_ints% [3191309137287154342575]) 0) 73 false) (.node 156 (sourceLit (List.headD (raw_ints% [838358615266220679520130809675893435]) 0) 22 true) .empty .empty) .empty) (.node 159 (sourceLit (List.headD (raw_ints% [3151964640150434119869]) 0) 73 false) .empty .empty)) (.node 168 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 48 false) (.node 167 (sourceLit (List.headD (raw_ints% [7343158899305777378096612978775]) 0) 43 false) .empty .empty) (.node 169 (sourceLit (List.headD (raw_ints% [1670220982066749181631982537975]) 0) 45 false) .empty .empty)))

#time def treeG_J012_part027 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [25864852851088237677735]) 0) 70 false) treeG_J012_part025 treeG_J012_part026)

#time def treeG_J012_part028 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [7692319606936801828807048180495275]) 0) 31 true) treeG_J012_part024 treeG_J012_part027)

#time def treeG_J012_part029 : IntSourceTree :=
  (.node 127 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 42 false) treeG_J012_part021 treeG_J012_part028)

#time def treeG_J012_part030 : IntSourceTree :=
  (.node 84 (sourceLit (List.headD (raw_ints% [20619571641257916961763913058275]) 0) 39 false) treeG_J012_part014 treeG_J012_part029)

#time def treeG_J012_part031 : IntSourceTree :=
  (.node 175 (sourceLit (List.headD (raw_ints% [2157528537169787820837249078173325]) 0) 38 false) (.node 173 (sourceLit (List.headD (raw_ints% [9453313131767410932906481534725]) 0) 39 false) (.node 172 (sourceLit (List.headD (raw_ints% [271393198828922690344612262475]) 0) 46 false) (.node 171 (sourceLit (List.headD (raw_ints% [195655561946432637225185584575]) 0) 48 false) .empty .empty) .empty) (.node 174 (sourceLit (List.headD (raw_ints% [625390358763198543020027797275]) 0) 48 false) .empty .empty)) (.node 178 (sourceLit (List.headD (raw_ints% [5095685653212135118840978275]) 0) 53 false) (.node 177 (sourceLit (List.headD (raw_ints% [6418362738822528863144941300713825]) 0) 36 true) (.node 176 (sourceLit (List.headD (raw_ints% [409690678630832182945470134025]) 0) 50 true) .empty .empty) .empty) (.node 179 (sourceLit (List.headD (raw_ints% [3864523287813894078858543324365775]) 0) 35 true) .empty .empty)))

#time def treeG_J012_part032 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [63168807341395816607820012067507725]) 0) 29 true) (.node 183 (sourceLit (List.headD (raw_ints% [22314208861620476206027291388724525]) 0) 31 true) (.node 182 (sourceLit (List.headD (raw_ints% [606010626263263467091163175]) 0) 56 false) (.node 181 (sourceLit (List.headD (raw_ints% [17040822052301794256018710160667825]) 0) 32 true) .empty .empty) .empty) (.node 184 (sourceLit (List.headD (raw_ints% [74137870135988180922631725]) 0) 59 false) .empty .empty)) (.node 187 (sourceLit (List.headD (raw_ints% [93116270386668850245969577577468775]) 0) 28 true) (.node 186 (sourceLit (List.headD (raw_ints% [18170980065912389949371475]) 0) 61 false) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [17840464250193722512550115]) 0) 61 false) .empty .empty)))

#time def treeG_J012_part033 : IntSourceTree :=
  (.node 180 (sourceLit (List.headD (raw_ints% [2481967660667162690155386825]) 0) 54 false) treeG_J012_part031 treeG_J012_part032)

#time def treeG_J012_part034 : IntSourceTree :=
  (.node 194 (sourceLit (List.headD (raw_ints% [132809103963418535797905]) 0) 68 false) (.node 192 (sourceLit (List.headD (raw_ints% [1078652613632300196559965]) 0) 65 false) (.node 191 (sourceLit (List.headD (raw_ints% [1701663345718733870788450683085620225]) 0) 23 true) (.node 190 (sourceLit (List.headD (raw_ints% [4384413428976578150928135]) 0) 63 false) .empty .empty) .empty) (.node 193 (sourceLit (List.headD (raw_ints% [5150422736002660519098316811279813295]) 0) 21 true) .empty .empty)) (.node 197 (sourceLit (List.headD (raw_ints% [44562924370575147091591680988486246845]) 0) 17 true) (.node 196 (sourceLit (List.headD (raw_ints% [32731228119920543112645]) 0) 70 false) (.node 195 (sourceLit (List.headD (raw_ints% [7685763558524684805956120251334219865]) 0) 20 true) .empty .empty) .empty) (.node 198 (sourceLit (List.headD (raw_ints% [8072633712519742874103]) 0) 72 false) .empty .empty)))

#time def treeG_J012_part035 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [505819217750915711904742455975]) 0) 46 false) (.node 209 (sourceLit (List.headD (raw_ints% [1160408793663865456722644457825]) 0) 45 false) (.node 208 (sourceLit (List.headD (raw_ints% [4790233792144292934513217135275]) 0) 44 false) (.node 207 (sourceLit (List.headD (raw_ints% [5623519538524886444117430834075]) 0) 43 false) .empty .empty) .empty) (.node 210 (sourceLit (List.headD (raw_ints% [266756200652443707500565731175]) 0) 48 false) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [901638534315357775231269975]) 0) 47 false) (.node 212 (sourceLit (List.headD (raw_ints% [123524479201204015206683986575]) 0) 49 false) .empty .empty) (.node 214 (sourceLit (List.headD (raw_ints% [197843136093734725851301566723825]) 0) 40 true) .empty .empty)))

#time def treeG_J012_part036 : IntSourceTree :=
  (.node 199 (sourceLit (List.headD (raw_ints% [61207066874985363205311932670344489265]) 0) 16 true) treeG_J012_part034 treeG_J012_part035)

#time def treeG_J012_part037 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [1121377933811003632742558625079287825]) 0) 24 true) treeG_J012_part033 treeG_J012_part036)

#time def treeG_J012_part038 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [3186223355878921672413276414395925]) 0) 36 true) (.node 218 (sourceLit (List.headD (raw_ints% [5828249826901799116465779256029075]) 0) 37 true) (.node 217 (sourceLit (List.headD (raw_ints% [425642745007180820507254141275]) 0) 51 true) (.node 216 (sourceLit (List.headD (raw_ints% [2603639984740998635378632405668975]) 0) 39 false) .empty .empty) .empty) (.node 219 (sourceLit (List.headD (raw_ints% [787403787886262672487036675]) 0) 56 false) .empty .empty)) (.node 223 (sourceLit (List.headD (raw_ints% [186413682612677481035635275]) 0) 58 false) (.node 222 (sourceLit (List.headD (raw_ints% [13409832932810236375702604184489075]) 0) 33 true) (.node 221 (sourceLit (List.headD (raw_ints% [1530175041923348821211221725]) 0) 55 false) .empty .empty) .empty) (.node 224 (sourceLit (List.headD (raw_ints% [17117093874002621492333978404822575]) 0) 32 true) .empty .empty)))

#time def treeG_J012_part039 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [842867964453185529465923362093036275]) 0) 25 true) (.node 228 (sourceLit (List.headD (raw_ints% [69997729710958933445354385468020925]) 0) 29 true) (.node 227 (sourceLit (List.headD (raw_ints% [22284470893739314322410875]) 0) 61 false) (.node 226 (sourceLit (List.headD (raw_ints% [47784168127522212950205915706517175]) 0) 30 true) .empty .empty) .empty) (.node 229 (sourceLit (List.headD (raw_ints% [10925157236863593314470095]) 0) 62 false) .empty .empty)) (.node 232 (sourceLit (List.headD (raw_ints% [1286420128044015473700615096989820075]) 0) 24 true) (.node 231 (sourceLit (List.headD (raw_ints% [670458368229138874664595]) 0) 66 false) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [659111557070383680022515]) 0) 66 false) .empty .empty)))

#time def treeG_J012_part040 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [2845607193211061635284825]) 0) 64 false) treeG_J012_part038 treeG_J012_part039)

#time def treeG_J012_part041 : IntSourceTree :=
  (.node 239 (sourceLit (List.headD (raw_ints% [2460334536184654377117]) 0) 74 false) (.node 237 (sourceLit (List.headD (raw_ints% [19965991570771925742345]) 0) 71 false) (.node 236 (sourceLit (List.headD (raw_ints% [6009046327992243446915858631982432995]) 0) 21 true) (.node 235 (sourceLit (List.headD (raw_ints% [81079398261242060442435]) 0) 69 false) .empty .empty) .empty) (.node 238 (sourceLit (List.headD (raw_ints% [36070091208348961234009254420129652695]) 0) 18 true) .empty .empty)) (.node 250 (sourceLit (List.headD (raw_ints% [426475026731164227684390698175]) 0) 47 false) (.node 249 (sourceLit (List.headD (raw_ints% [780003202519385938220308649325]) 0) 47 false) (.node 248 (sourceLit (List.headD (raw_ints% [4195324100169359728151099193675]) 0) 44 false) .empty .empty) .empty) (.node 251 (sourceLit (List.headD (raw_ints% [337856839358454777775945877775]) 0) 48 false) .empty .empty)))

#time def treeG_J012_part042 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [48076602494678507029203059791417425]) 0) 36 false) (.node 255 (sourceLit (List.headD (raw_ints% [3740273625919665627647661611963925]) 0) 38 true) (.node 254 (sourceLit (List.headD (raw_ints% [156122180057220796311199131825]) 0) 50 true) (.node 253 (sourceLit (List.headD (raw_ints% [243524820272298412210382322970875]) 0) 39 false) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [1421190400511999705558765619825]) 0) 50 false) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [42761475327400498852867690723866825]) 0) 35 true) (.node 258 (sourceLit (List.headD (raw_ints% [435834116313605090744936097825]) 0) 52 true) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [3817262642422938689740906575]) 0) 54 false) .empty .empty)))

#time def treeG_J012_part043 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [740245236672908733464872649475]) 0) 46 false) treeG_J012_part041 treeG_J012_part042)

#time def treeG_J012_part044 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [3942256305922473783872945034111307485]) 0) 22 true) treeG_J012_part040 treeG_J012_part043)

#time def treeG_J012_part045 : IntSourceTree :=
  (.node 215 (sourceLit (List.headD (raw_ints% [126437465235145940326661935725]) 0) 52 false) treeG_J012_part037 treeG_J012_part044)

#time def treeG_J012_part046 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [27358735025464596215185725]) 0) 61 false) (.node 264 (sourceLit (List.headD (raw_ints% [56137906238344650056501775]) 0) 60 false) (.node 263 (sourceLit (List.headD (raw_ints% [84964454600861414799593542087188075]) 0) 31 true) (.node 262 (sourceLit (List.headD (raw_ints% [462082207830042677060029275]) 0) 57 false) .empty .empty) .empty) (.node 265 (sourceLit (List.headD (raw_ints% [210704694642646127269523642409653475]) 0) 29 true) .empty .empty)) (.node 269 (sourceLit (List.headD (raw_ints% [3358476767690368107760122044874051375]) 0) 24 true) (.node 268 (sourceLit (List.headD (raw_ints% [26728477537284906132271635]) 0) 61 false) (.node 267 (sourceLit (List.headD (raw_ints% [289157074633508853355677748074668625]) 0) 28 true) .empty .empty) .empty) (.node 270 (sourceLit (List.headD (raw_ints% [817592975985876895442745]) 0) 66 false) .empty .empty)))

#time def treeG_J012_part047 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [24174085070660758664895]) 0) 71 false) (.node 274 (sourceLit (List.headD (raw_ints% [393493349143546608426705]) 0) 67 false) (.node 273 (sourceLit (List.headD (raw_ints% [15432299312701587060111524740557307905]) 0) 21 true) (.node 272 (sourceLit (List.headD (raw_ints% [1603180859284255302098415]) 0) 65 false) .empty .empty) .empty) (.node 275 (sourceLit (List.headD (raw_ints% [23852286888855105465027440021556240015]) 0) 20 true) .empty .empty)) (.node 278 (sourceLit (List.headD (raw_ints% [5946678929126091434121]) 0) 73 false) (.node 277 (sourceLit (List.headD (raw_ints% [147726558125176643209715795234951608995]) 0) 17 true) .empty .empty) (.node 279 (sourceLit (List.headD (raw_ints% [227353662791806326666762102690692732295]) 0) 16 true) .empty .empty)))

#time def treeG_J012_part048 : IntSourceTree :=
  (.node 271 (sourceLit (List.headD (raw_ints% [5041280369906750364938936213658669975]) 0) 23 true) treeG_J012_part046 treeG_J012_part047)

#time def treeG_J012_part049 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [110341989091508284515420972423675]) 0) 42 false) (.node 292 (sourceLit (List.headD (raw_ints% [1674471563728521582572358525]) 0) 56 false) (.node 291 (sourceLit (List.headD (raw_ints% [1200080889173741198832820336725]) 0) 46 false) (.node 290 (sourceLit (List.headD (raw_ints% [256623500933471115359871459075]) 0) 49 false) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [184835899534648343922410344875]) 0) 49 false) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [461708286379795131516504940275]) 0) 53 false) (.node 296 (sourceLit (List.headD (raw_ints% [1585978402665166065756573504408225]) 0) 41 true) (.node 295 (sourceLit (List.headD (raw_ints% [408997110527512676964523003275]) 0) 51 true) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [13476213080395076536417209761861625]) 0) 39 false) .empty .empty)))

#time def treeG_J012_part050 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [16961840181714698326814890920591375]) 0) 34 true) (.node 302 (sourceLit (List.headD (raw_ints% [17877123100753365721375882728878175]) 0) 35 true) (.node 301 (sourceLit (List.headD (raw_ints% [1143543800249794934264842425]) 0) 56 false) (.node 300 (sourceLit (List.headD (raw_ints% [9893812992880394295113603577367725]) 0) 38 true) .empty .empty) .empty) (.node 303 (sourceLit (List.headD (raw_ints% [17229282826085324751524625]) 0) 62 false) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [40730131628780978579829431675784075]) 0) 32 true) (.node 305 (sourceLit (List.headD (raw_ints% [33373048692656156974223175]) 0) 61 false) .empty .empty) (.node 307 (sourceLit (List.headD (raw_ints% [32432999157189878107960575]) 0) 61 false) .empty .empty)))

#time def treeG_J012_part051 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [442133346616695192124832391225]) 0) 53 true) treeG_J012_part049 treeG_J012_part050)

#time def treeG_J012_part052 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [1517457653252747135714227367925]) 0) 46 false) treeG_J012_part048 treeG_J012_part051)

#time def treeG_J012_part053 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [236017325553467905518975]) 0) 68 false) (.node 311 (sourceLit (List.headD (raw_ints% [964727583742614916220895]) 0) 66 false) (.node 310 (sourceLit (List.headD (raw_ints% [628902200809295644573549670695253775]) 0) 27 true) (.node 309 (sourceLit (List.headD (raw_ints% [3950830075105328204450385]) 0) 64 false) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [938715060465683722809580279167212475]) 0) 26 true) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [4460810140215715504527895347393451755]) 0) 23 true) (.node 315 (sourceLit (List.headD (raw_ints% [231334552621062487541835]) 0) 68 false) (.node 314 (sourceLit (List.headD (raw_ints% [2872510751694778319059644926611500105]) 0) 24 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [28382178570549591587445]) 0) 71 false) .empty .empty)))

#time def treeG_J012_part054 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [195427853329751149531466030206725]) 0) 39 false) (.node 331 (sourceLit (List.headD (raw_ints% [688637164375429683663539958525]) 0) 48 false) (.node 330 (sourceLit (List.headD (raw_ints% [545491313260791454014918334875]) 0) 48 false) (.node 319 (sourceLit (List.headD (raw_ints% [871586098235359264251]) 0) 76 false) .empty .empty) .empty) (.node 332 (sourceLit (List.headD (raw_ints% [1659916541674573664200768023975]) 0) 46 false) .empty .empty)) (.node 335 (sourceLit (List.headD (raw_ints% [7271217276847930732141132729521525]) 0) 38 false) (.node 334 (sourceLit (List.headD (raw_ints% [85239519897967285058402369175]) 0) 52 false) .empty .empty) (.node 336 (sourceLit (List.headD (raw_ints% [3057178842622050413416857632925]) 0) 50 true) .empty .empty)))

#time def treeG_J012_part055 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [27914116729206920493926635203705489075]) 0) 20 true) treeG_J012_part053 treeG_J012_part054)

#time def treeG_J012_part056 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [340730796209876128602406575]) 0) 58 false) (.node 340 (sourceLit (List.headD (raw_ints% [55743826157389766351821662225]) 0) 57 true) (.node 339 (sourceLit (List.headD (raw_ints% [474000293900042948018218403103438825]) 0) 35 false) (.node 338 (sourceLit (List.headD (raw_ints% [2282667261832785616810955858925]) 0) 52 false) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [1181489737752866770513335122803067025]) 0) 32 true) .empty .empty)) (.node 344 (sourceLit (List.headD (raw_ints% [81696356370337947955695225]) 0) 60 false) (.node 343 (sourceLit (List.headD (raw_ints% [487103484623246288284434705236913525]) 0) 31 true) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [874853076987094565646629376508194525]) 0) 29 true) .empty .empty)))

#time def treeG_J012_part057 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [15083590055990710261414653248589450825]) 0) 23 true) (.node 349 (sourceLit (List.headD (raw_ints% [10667721307352826766500573161951401425]) 0) 24 true) (.node 348 (sourceLit (List.headD (raw_ints% [38137520777094850083649515]) 0) 61 false) (.node 347 (sourceLit (List.headD (raw_ints% [1014207137487482461198864065550421775]) 0) 28 true) .empty .empty) .empty) (.node 350 (sourceLit (List.headD (raw_ints% [2315644123133574413564895]) 0) 65 false) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [44645464557102171199701613126144290495]) 0) 21 true) (.node 352 (sourceLit (List.headD (raw_ints% [2255729475686204362785165]) 0) 65 false) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [550575953070325013649195]) 0) 67 false) .empty .empty)))

#time def treeG_J012_part058 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [39387362359847717733260625]) 0) 61 false) treeG_J012_part056 treeG_J012_part057)

#time def treeG_J012_part059 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [149579220265249135237623764073543825]) 0) 36 true) treeG_J012_part055 treeG_J012_part058)

#time def treeG_J012_part060 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [54789836230637479977580840651661925]) 0) 31 true) treeG_J012_part052 treeG_J012_part059)

#time def treeG_J012_part061 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [84918325335823699261206135100001775]) 0) 32 true) treeG_J012_part045 treeG_J012_part060)

#time def treeG_J012_part062 : IntSourceTree :=
  (.node 170 (sourceLit (List.headD (raw_ints% [307458740201537001353863061475]) 0) 46 false) treeG_J012_part030 treeG_J012_part061)

#time def treeG_J012_part063 : IntSourceTree :=
  (.node 371 (sourceLit (List.headD (raw_ints% [3163849616912590433286526342275]) 0) 46 false) (.node 358 (sourceLit (List.headD (raw_ints% [16488820712297408719203]) 0) 72 false) (.node 357 (sourceLit (List.headD (raw_ints% [423257139822434941369854809231410215645]) 0) 17 true) (.node 356 (sourceLit (List.headD (raw_ints% [134638212338419452882255]) 0) 69 false) .empty .empty) .empty) (.node 359 (sourceLit (List.headD (raw_ints% [665898072542815129138890223827882918105]) 0) 16 true) .empty .empty)) (.node 374 (sourceLit (List.headD (raw_ints% [245940103036281988530217859487975]) 0) 40 true) (.node 373 (sourceLit (List.headD (raw_ints% [920572943535980288511126644475]) 0) 47 false) (.node 372 (sourceLit (List.headD (raw_ints% [474304804218178921094278067325]) 0) 49 false) .empty .empty) .empty) (.node 375 (sourceLit (List.headD (raw_ints% [749955190119381817198132479975]) 0) 51 false) .empty .empty)))

#time def treeG_J012_part064 : IntSourceTree :=
  (.node 381 (sourceLit (List.headD (raw_ints% [224118848429808860341551491325]) 0) 56 true) (.node 379 (sourceLit (List.headD (raw_ints% [1362400304224740404467894125075]) 0) 54 false) (.node 378 (sourceLit (List.headD (raw_ints% [203484072586829441383292603120990325]) 0) 37 true) (.node 377 (sourceLit (List.headD (raw_ints% [4904011988141230939482877394025]) 0) 51 true) .empty .empty) .empty) (.node 380 (sourceLit (List.headD (raw_ints% [513575545871564525198672817412909725]) 0) 36 false) .empty .empty)) (.node 383 (sourceLit (List.headD (raw_ints% [202896533601193530590209575]) 0) 59 false) (.node 382 (sourceLit (List.headD (raw_ints% [1109981245349853307627831591887554325]) 0) 33 true) .empty .empty) (.node 384 (sourceLit (List.headD (raw_ints% [419256123896387494977175141554548025]) 0) 32 true) .empty .empty)))

#time def treeG_J012_part065 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [13615130887508594995167426747154425]) 0) 39 false) treeG_J012_part063 treeG_J012_part064)

#time def treeG_J012_part066 : IntSourceTree :=
  (.node 390 (sourceLit (List.headD (raw_ints% [8152112504115644188206374479170386325]) 0) 25 true) (.node 388 (sourceLit (List.headD (raw_ints% [795047792564932541288540702943774075]) 0) 29 true) (.node 387 (sourceLit (List.headD (raw_ints% [46341725562505557358560675]) 0) 61 false) (.node 386 (sourceLit (List.headD (raw_ints% [711932550471970651327311649805058225]) 0) 30 true) .empty .empty) .empty) (.node 389 (sourceLit (List.headD (raw_ints% [22334200476673537265847975]) 0) 62 false) .empty .empty)) (.node 393 (sourceLit (List.headD (raw_ints% [1311660173472332740709265]) 0) 66 false) (.node 392 (sourceLit (List.headD (raw_ints% [11328729814127975370176332131920600925]) 0) 24 true) (.node 391 (sourceLit (List.headD (raw_ints% [1319254432998983884125]) 0) 76 false) .empty .empty) .empty) (.node 394 (sourceLit (List.headD (raw_ints% [33155421550323057923463033419698290075]) 0) 22 true) .empty .empty)))

#time def treeG_J012_part067 : IntSourceTree :=
  (.node 412 (sourceLit (List.headD (raw_ints% [4667782692150607202372284660575]) 0) 46 false) (.node 398 (sourceLit (List.headD (raw_ints% [311600672905607259394148268416588259345]) 0) 18 true) (.node 397 (sourceLit (List.headD (raw_ints% [77873855197320269707365]) 0) 70 false) (.node 396 (sourceLit (List.headD (raw_ints% [50224816604514938726769616240437956325]) 0) 21 true) .empty .empty) .empty) (.node 399 (sourceLit (List.headD (raw_ints% [9516131926414534605195]) 0) 73 false) .empty .empty)) (.node 414 (sourceLit (List.headD (raw_ints% [443259374831496272423311262325]) 0) 48 true) (.node 413 (sourceLit (List.headD (raw_ints% [775948385709079280869615451674875]) 0) 39 false) .empty .empty) (.node 415 (sourceLit (List.headD (raw_ints% [9238738101138186640382875605425325]) 0) 38 true) .empty .empty)))

#time def treeG_J012_part068 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [9976293764039453940855]) 0) 73 false) treeG_J012_part066 treeG_J012_part067)

#time def treeG_J012_part069 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [24161653838840895490736025]) 0) 62 false) treeG_J012_part065 treeG_J012_part068)

#time def treeG_J012_part070 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [17615907205642931576870865280016178225]) 0) 32 false) (.node 419 (sourceLit (List.headD (raw_ints% [2101872874594678479084559228071361425]) 0) 35 true) (.node 418 (sourceLit (List.headD (raw_ints% [3593339624987008278146916626475]) 0) 53 true) (.node 417 (sourceLit (List.headD (raw_ints% [367421314465386655160302592028014625]) 0) 36 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [1585375608854299469875180773975]) 0) 55 false) .empty .empty)) (.node 424 (sourceLit (List.headD (raw_ints% [60600088615427791317257175]) 0) 61 false) (.node 423 (sourceLit (List.headD (raw_ints% [8392746478175580172738218029863521075]) 0) 31 true) (.node 422 (sourceLit (List.headD (raw_ints% [224800310022228612598756304475]) 0) 57 true) .empty .empty) .empty) (.node 425 (sourceLit (List.headD (raw_ints% [5833244905355105353988172888364573875]) 0) 29 true) .empty .empty)))

#time def treeG_J012_part071 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [50133309976934443244236342584773639775]) 0) 23 true) (.node 429 (sourceLit (List.headD (raw_ints% [40215337416802855875966031826450139375]) 0) 24 true) (.node 428 (sourceLit (List.headD (raw_ints% [54545930347916264633471835]) 0) 61 false) (.node 427 (sourceLit (List.headD (raw_ints% [4681253266288282749419629132890044025]) 0) 28 true) .empty .empty) .empty) (.node 430 (sourceLit (List.headD (raw_ints% [13071623984139239611588395]) 0) 63 false) .empty .empty)) (.node 433 (sourceLit (List.headD (raw_ints% [136614212468945434723119700984585324305]) 0) 21 true) (.node 432 (sourceLit (List.headD (raw_ints% [3147936681877633626590835]) 0) 65 false) .empty .empty) (.node 434 (sourceLit (List.headD (raw_ints% [380542110201003863530035]) 0) 68 false) .empty .empty)))

#time def treeG_J012_part072 : IntSourceTree :=
  (.node 426 (sourceLit (List.headD (raw_ints% [57259252995515864229683475]) 0) 61 false) treeG_J012_part070 treeG_J012_part071)

#time def treeG_J012_part073 : IntSourceTree :=
  (.node 454 (sourceLit (List.headD (raw_ints% [510944244372680634699916655581425]) 0) 41 false) (.node 438 (sourceLit (List.headD (raw_ints% [44896213772725452268959]) 0) 71 false) (.node 437 (sourceLit (List.headD (raw_ints% [1183936991522043097886772910462604386755]) 0) 17 true) (.node 436 (sourceLit (List.headD (raw_ints% [184603188110843073225105]) 0) 69 false) .empty .empty) .empty) (.node 439 (sourceLit (List.headD (raw_ints% [1826907310702042946014295923504823156655]) 0) 16 true) .empty .empty)) (.node 457 (sourceLit (List.headD (raw_ints% [5480505795620404310846132473425]) 0) 52 false) (.node 456 (sourceLit (List.headD (raw_ints% [11426934494323390817775151176289875]) 0) 40 true) (.node 455 (sourceLit (List.headD (raw_ints% [3443080135309023541215841182225]) 0) 49 true) .empty .empty) .empty) (.node 458 (sourceLit (List.headD (raw_ints% [285452693526108048271797597574502475]) 0) 38 false) .empty .empty)))

#time def treeG_J012_part074 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [3986745177139596338880521444154486525]) 0) 33 true) (.node 462 (sourceLit (List.headD (raw_ints% [9362944225496392442249348435951866275]) 0) 34 false) (.node 461 (sourceLit (List.headD (raw_ints% [452373614321027082554183066325]) 0) 58 false) (.node 460 (sourceLit (List.headD (raw_ints% [1307724210233121502141616022742135575]) 0) 37 true) .empty .empty) .empty) (.node 463 (sourceLit (List.headD (raw_ints% [225206103089430999659936723625]) 0) 58 true) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [2560656177441567351330430619279757825]) 0) 31 true) (.node 465 (sourceLit (List.headD (raw_ints% [18219217388293447913260575]) 0) 63 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [68176780428526171100806275]) 0) 61 false) .empty .empty)))

#time def treeG_J012_part075 : IntSourceTree :=
  (.node 459 (sourceLit (List.headD (raw_ints% [2477869964605874341307405375775]) 0) 55 true) treeG_J012_part073 treeG_J012_part074)

#time def treeG_J012_part076 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [197175315237206662642823069727574557255]) 0) 20 true) treeG_J012_part072 treeG_J012_part075)

#time def treeG_J012_part077 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [6056999603099577682209387552825]) 0) 50 false) treeG_J012_part069 treeG_J012_part076)

#time def treeG_J012_part078 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [918138254202650442940785]) 0) 67 false) (.node 471 (sourceLit (List.headD (raw_ints% [7667957826575401622212395]) 0) 64 false) (.node 470 (sourceLit (List.headD (raw_ints% [16031612456343605843879828673639876525]) 0) 26 true) (.node 469 (sourceLit (List.headD (raw_ints% [8052932467810681841905965]) 0) 64 false) .empty .empty) .empty) (.node 472 (sourceLit (List.headD (raw_ints% [19402290081403233937030005226426519425]) 0) 25 true) .empty .empty)) (.node 476 (sourceLit (List.headD (raw_ints% [73475249316345861958026726743568300465]) 0) 22 true) (.node 475 (sourceLit (List.headD (raw_ints% [220921409976372600476355]) 0) 69 false) (.node 474 (sourceLit (List.headD (raw_ints% [51729395459311188399828333782443517115]) 0) 23 true) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [26682333228380700879435]) 0) 72 false) .empty .empty)))

#time def treeG_J012_part079 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [2268461355151853147248262274975]) 0) 55 false) (.node 496 (sourceLit (List.headD (raw_ints% [4750039869204300611712614367525]) 0) 51 true) (.node 495 (sourceLit (List.headD (raw_ints% [17413846011101076795581542094728125]) 0) 38 false) (.node 479 (sourceLit (List.headD (raw_ints% [25863949919896383058569]) 0) 72 false) .empty .empty) .empty) (.node 497 (sourceLit (List.headD (raw_ints% [733083218283735161329107429669290625]) 0) 36 true) .empty .empty)) (.node 500 (sourceLit (List.headD (raw_ints% [6541115538066048152489991525525]) 0) 55 true) (.node 499 (sourceLit (List.headD (raw_ints% [6669115971012407251433320789263401025]) 0) 35 false) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [101310256660562707713934290735512855025]) 0) 32 true) .empty .empty)))

#time def treeG_J012_part080 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [436168159308217919246312321023008063705]) 0) 19 true) treeG_J012_part078 treeG_J012_part079)

#time def treeG_J012_part081 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [36289245572776794871867260775586081175]) 0) 28 true) (.node 505 (sourceLit (List.headD (raw_ints% [121742600763111977490188513324578994925]) 0) 29 true) (.node 504 (sourceLit (List.headD (raw_ints% [225448503443892710825205752325]) 0) 59 true) (.node 503 (sourceLit (List.headD (raw_ints% [158199854086117859248727793005093381475]) 0) 31 false) .empty .empty) .empty) (.node 506 (sourceLit (List.headD (raw_ints% [88494486110831719076401125]) 0) 61 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [19140105887103487756035465]) 0) 63 false) (.node 509 (sourceLit (List.headD (raw_ints% [208501812901491557444423627690111137425]) 0) 24 true) (.node 508 (sourceLit (List.headD (raw_ints% [81807630509136077568140715]) 0) 61 false) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [206372489324563250257840916193464384625]) 0) 23 true) .empty .empty)))

#time def treeG_J012_part082 : IntSourceTree :=
  (.node 517 (sourceLit (List.headD (raw_ints% [3518478964724092067426937601125766843005]) 0) 17 true) (.node 515 (sourceLit (List.headD (raw_ints% [630495012111772351754430270791521716585]) 0) 20 true) (.node 514 (sourceLit (List.headD (raw_ints% [268798072000823289705375]) 0) 69 false) (.node 513 (sourceLit (List.headD (raw_ints% [484259070135958051261840466261063297295]) 0) 21 true) .empty .empty) .empty) (.node 516 (sourceLit (List.headD (raw_ints% [257239631841902127727605]) 0) 69 false) .empty .empty)) (.node 519 (sourceLit (List.headD (raw_ints% [5151783238229443761926701212863305862625]) 0) 16 true) (.node 518 (sourceLit (List.headD (raw_ints% [61833119140797351248781]) 0) 71 false) .empty .empty) (.node 537 (sourceLit (List.headD (raw_ints% [5115272832412352461279373420475]) 0) 53 true) .empty .empty)))

#time def treeG_J012_part083 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [565002643087220999452695]) 0) 68 false) treeG_J012_part081 treeG_J012_part082)

#time def treeG_J012_part084 : IntSourceTree :=
  (.node 502 (sourceLit (List.headD (raw_ints% [2034294767306336942815488569775]) 0) 57 false) treeG_J012_part080 treeG_J012_part083)

#time def treeG_J012_part085 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [282437608799470992809428161675]) 0) 61 false) (.node 541 (sourceLit (List.headD (raw_ints% [8350609995350156482706723790825]) 0) 56 true) (.node 540 (sourceLit (List.headD (raw_ints% [9284564391478650255716552834747672175]) 0) 36 false) (.node 539 (sourceLit (List.headD (raw_ints% [7014792674909580635803929925725]) 0) 55 false) .empty .empty) .empty) (.node 542 (sourceLit (List.headD (raw_ints% [120036145111555492598432987607416587575]) 0) 33 true) .empty .empty)) (.node 546 (sourceLit (List.headD (raw_ints% [116621288408228842787527652086019479275]) 0) 30 true) (.node 545 (sourceLit (List.headD (raw_ints% [225594257182999058408511836925]) 0) 60 true) (.node 544 (sourceLit (List.headD (raw_ints% [166173344440397051926488835893402354525]) 0) 32 false) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [108812191793137267051995975]) 0) 61 false) .empty .empty)))

#time def treeG_J012_part086 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [1341872318146233554869995]) 0) 67 false) (.node 551 (sourceLit (List.headD (raw_ints% [5736074030264043066911535]) 0) 65 false) (.node 550 (sourceLit (List.headD (raw_ints% [176438587988804345756663970342831384375]) 0) 25 true) (.node 549 (sourceLit (List.headD (raw_ints% [49595900637893350200516855]) 0) 62 false) .empty .empty) .empty) (.node 552 (sourceLit (List.headD (raw_ints% [167567909161756782383780905740611345775]) 0) 24 true) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [316674734025273978934395]) 0) 69 false) (.node 554 (sourceLit (List.headD (raw_ints% [380800279217335674462183798696176263065]) 0) 22 true) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [483544513479080627838376817304385115655]) 0) 21 true) .empty .empty)))

#time def treeG_J012_part087 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [32403040099053444663736172345639811225]) 0) 29 true) treeG_J012_part085 treeG_J012_part086)

#time def treeG_J012_part088 : IntSourceTree :=
  (.node 582 (sourceLit (List.headD (raw_ints% [1298113095332061678190276545075]) 0) 60 true) (.node 580 (sourceLit (List.headD (raw_ints% [20570700887885209424097851376975]) 0) 55 false) (.node 559 (sourceLit (List.headD (raw_ints% [8992292305225242047553]) 0) 74 false) (.node 558 (sourceLit (List.headD (raw_ints% [2646142646107656228934312959079750715595]) 0) 18 true) .empty .empty) .empty) (.node 581 (sourceLit (List.headD (raw_ints% [398416317187879515896863981447438364625]) 0) 32 false) .empty .empty)) (.node 584 (sourceLit (List.headD (raw_ints% [2484949373839660653300631045725]) 0) 59 false) (.node 583 (sourceLit (List.headD (raw_ints% [1118489014978561800036191693864426082075]) 0) 31 true) .empty .empty) (.node 585 (sourceLit (List.headD (raw_ints% [2780516111809464808314009887619016667325]) 0) 29 false) .empty .empty)))

#time def treeG_J012_part089 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [1205136214585871515795470846549186690375]) 0) 23 true) (.node 589 (sourceLit (List.headD (raw_ints% [1865292753437928901034691402430836780975]) 0) 24 true) (.node 588 (sourceLit (List.headD (raw_ints% [135816753077138456535851235]) 0) 61 false) (.node 587 (sourceLit (List.headD (raw_ints% [896681061693053947428353955912569753025]) 0) 28 true) .empty .empty) .empty) (.node 590 (sourceLit (List.headD (raw_ints% [15227897375394931222240695]) 0) 64 false) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [2196827476452150466878654025588718235105]) 0) 21 true) (.node 592 (sourceLit (List.headD (raw_ints% [3476063457915159069100755]) 0) 66 false) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [804276174144586975459245]) 0) 68 false) .empty .empty)))

#time def treeG_J012_part090 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [112841375834554945063794119025]) 0) 62 true) treeG_J012_part088 treeG_J012_part089)

#time def treeG_J012_part091 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [150510298928379324209865]) 0) 70 false) treeG_J012_part087 treeG_J012_part090)

#time def treeG_J012_part092 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [1303988605335951257872702624818295575]) 0) 37 true) treeG_J012_part084 treeG_J012_part091)

#time def treeG_J012_part093 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [1943102736861675104065544214973134975]) 0) 30 true) treeG_J012_part077 treeG_J012_part092)

#time def treeG_J012_part094 : IntSourceTree :=
  (.node 621 (sourceLit (List.headD (raw_ints% [3615163860404420738350571895975]) 0) 59 false) (.node 598 (sourceLit (List.headD (raw_ints% [22169294946895493240271]) 0) 73 false) (.node 597 (sourceLit (List.headD (raw_ints% [11954945466606488023401120552614556857955]) 0) 17 true) (.node 596 (sourceLit (List.headD (raw_ints% [376109836208645830141185]) 0) 69 false) .empty .empty) .empty) (.node 599 (sourceLit (List.headD (raw_ints% [16017357930631806069547802459774699862135]) 0) 16 true) .empty .empty)) (.node 624 (sourceLit (List.headD (raw_ints% [160582794927369856495335066219728554575]) 0) 35 true) (.node 623 (sourceLit (List.headD (raw_ints% [790275352065766335499852353375]) 0) 62 true) (.node 622 (sourceLit (List.headD (raw_ints% [64806557787429376061912121131856869025]) 0) 36 false) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [1355271815511329855854571441325]) 0) 61 false) .empty .empty)))

#time def treeG_J012_part095 : IntSourceTree :=
  (.node 631 (sourceLit (List.headD (raw_ints% [1186477918141361019416145]) 0) 68 false) (.node 629 (sourceLit (List.headD (raw_ints% [21555213109811276583833595]) 0) 64 false) (.node 628 (sourceLit (List.headD (raw_ints% [108034752699250062845577222945866242725]) 0) 32 true) (.node 627 (sourceLit (List.headD (raw_ints% [451474315530012917522228472075]) 0) 61 true) .empty .empty) .empty) (.node 630 (sourceLit (List.headD (raw_ints% [211106770681140569409753429011000674575]) 0) 28 true) .empty .empty)) (.node 633 (sourceLit (List.headD (raw_ints% [266773892471115689278845]) 0) 70 false) (.node 632 (sourceLit (List.headD (raw_ints% [129696038178014341676461242601071918075]) 0) 27 true) .empty .empty) (.node 634 (sourceLit (List.headD (raw_ints% [227003399654351849052058778361567746505]) 0) 25 true) .empty .empty)))

#time def treeG_J012_part096 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [362142175027211706387692192463129518325]) 0) 33 false) treeG_J012_part094 treeG_J012_part095)

#time def treeG_J012_part097 : IntSourceTree :=
  (.node 663 (sourceLit (List.headD (raw_ints% [5266108713374041867998567446303265699675]) 0) 31 false) (.node 638 (sourceLit (List.headD (raw_ints% [1163600352562353974308350949191850767795]) 0) 21 true) (.node 637 (sourceLit (List.headD (raw_ints% [28199942160033313241415]) 0) 73 false) (.node 636 (sourceLit (List.headD (raw_ints% [241545338518479052013082912684187909035]) 0) 24 true) .empty .empty) .empty) (.node 639 (sourceLit (List.headD (raw_ints% [6588501320835125596359]) 0) 75 false) .empty .empty)) (.node 666 (sourceLit (List.headD (raw_ints% [734056595672942400459182780175]) 0) 63 false) (.node 665 (sourceLit (List.headD (raw_ints% [23335113862512806439716898363744271652925]) 0) 29 true) (.node 664 (sourceLit (List.headD (raw_ints% [15129355006891922021298268699725]) 0) 59 true) .empty .empty) .empty) (.node 667 (sourceLit (List.headD (raw_ints% [24073780263434603156240654273552858925825]) 0) 28 false) .empty .empty)))

#time def treeG_J012_part098 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [14404265410333685267708385027348487278495]) 0) 21 true) (.node 671 (sourceLit (List.headD (raw_ints% [12305697109007124926428748610154856482425]) 0) 23 true) (.node 670 (sourceLit (List.headD (raw_ints% [27882528844227621945426495]) 0) 64 false) (.node 669 (sourceLit (List.headD (raw_ints% [53448500628578103275900846745852679494225]) 0) 24 true) .empty .empty) .empty) (.node 672 (sourceLit (List.headD (raw_ints% [6015759887215729086228405]) 0) 66 false) .empty .empty)) (.node 675 (sourceLit (List.headD (raw_ints% [12112310356251605295388721696362447388385]) 0) 20 true) (.node 674 (sourceLit (List.headD (raw_ints% [1329914965624338538771515]) 0) 68 false) .empty .empty) (.node 676 (sourceLit (List.headD (raw_ints% [599093044029980162908515]) 0) 69 false) .empty .empty)))

#time def treeG_J012_part099 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [903084447813102973500992795385]) 0) 61 true) treeG_J012_part097 treeG_J012_part098)

#time def treeG_J012_part100 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [243800720059656498262425]) 0) 70 false) treeG_J012_part096 treeG_J012_part099)

#time def treeG_J012_part101 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [26232251262730500090818435903449307799525]) 0) 30 true) (.node 704 (sourceLit (List.headD (raw_ints% [6550771072793000719961247976061094136275]) 0) 32 false) (.node 679 (sourceLit (List.headD (raw_ints% [58453064633358848286186658288503749276745]) 0) 16 true) (.node 678 (sourceLit (List.headD (raw_ints% [34230589373171133242559]) 0) 73 false) .empty .empty) .empty) (.node 705 (sourceLit (List.headD (raw_ints% [17839898637914581733007411582375]) 0) 60 true) .empty .empty)) (.node 709 (sourceLit (List.headD (raw_ints% [903170668665542218607328129765]) 0) 62 true) (.node 708 (sourceLit (List.headD (raw_ints% [24938058285028603659005272057119788867625]) 0) 29 false) (.node 707 (sourceLit (List.headD (raw_ints% [6323927080913552121195690713475]) 0) 61 false) .empty .empty) .empty) (.node 710 (sourceLit (List.headD (raw_ints% [51759646463128978720622819313764674097625]) 0) 25 true) .empty .empty)))

#time def treeG_J012_part102 : IntSourceTree :=
  (.node 716 (sourceLit (List.headD (raw_ints% [10179947648103772879284058394888944116105]) 0) 21 true) (.node 714 (sourceLit (List.headD (raw_ints% [12588238213098870475291914800455945306455]) 0) 22 true) (.node 713 (sourceLit (List.headD (raw_ints% [3881568747446803571997645]) 0) 67 false) (.node 712 (sourceLit (List.headD (raw_ints% [11268128803583010193017058669346281137825]) 0) 24 true) .empty .empty) .empty) (.node 715 (sourceLit (List.headD (raw_ints% [842313525505025542246665]) 0) 69 false) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [40571858373625317497481297501002741712645]) 0) 18 true) (.node 717 (sourceLit (List.headD (raw_ints% [373493506749713656977195]) 0) 70 false) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [21053586731500882049841]) 0) 74 false) .empty .empty)))

#time def treeG_J012_part103 : IntSourceTree :=
  (.node 711 (sourceLit (List.headD (raw_ints% [18390705499096733790097335]) 0) 65 false) treeG_J012_part101 treeG_J012_part102)

#time def treeG_J012_part104 : IntSourceTree :=
  (.node 750 (sourceLit (List.headD (raw_ints% [903226433723230673851218982755]) 0) 63 true) (.node 748 (sourceLit (List.headD (raw_ints% [13550938609640207215892374222335]) 0) 61 false) (.node 747 (sourceLit (List.headD (raw_ints% [233931790365278603882788141501147321322025]) 0) 28 true) (.node 746 (sourceLit (List.headD (raw_ints% [20776125020606351334844142703075]) 0) 61 true) .empty .empty) .empty) (.node 749 (sourceLit (List.headD (raw_ints% [1649484230870408737452238258401519167022225]) 0) 24 false) .empty .empty)) (.node 752 (sourceLit (List.headD (raw_ints% [6187472805940502351934465]) 0) 67 false) (.node 751 (sourceLit (List.headD (raw_ints% [401771474596024704838553805899962536298575]) 0) 23 true) .empty .empty) (.node 753 (sourceLit (List.headD (raw_ints% [165885795446994477820564553682192010926705]) 0) 21 true) .empty .empty)))

#time def treeG_J012_part105 : IntSourceTree :=
  (.node 759 (sourceLit (List.headD (raw_ints% [266121802355643691693663721719518184424415]) 0) 16 true) (.node 757 (sourceLit (List.headD (raw_ints% [275877663545196582845141763541908663860355]) 0) 17 true) (.node 756 (sourceLit (List.headD (raw_ints% [1085534006980070921584815]) 0) 69 false) (.node 755 (sourceLit (List.headD (raw_ints% [88593595348539358506946596707285115063255]) 0) 20 true) .empty .empty) .empty) (.node 758 (sourceLit (List.headD (raw_ints% [236571149257029124006959]) 0) 71 false) .empty .empty)) (.node 787 (sourceLit (List.headD (raw_ints% [47876177122126254790883976119625]) 0) 61 true) (.node 786 (sourceLit (List.headD (raw_ints% [77189851144965659024957650942085542816425]) 0) 31 false) .empty .empty) (.node 788 (sourceLit (List.headD (raw_ints% [129434924325153603770896706779133555094825]) 0) 30 true) .empty .empty)))

#time def treeG_J012_part106 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [1275826890911232516613065]) 0) 69 false) treeG_J012_part104 treeG_J012_part105)

#time def treeG_J012_part107 : IntSourceTree :=
  (.node 745 (sourceLit (List.headD (raw_ints% [128147451027200817959096865980721777833325]) 0) 29 false) treeG_J012_part103 treeG_J012_part106)

#time def treeG_J012_part108 : IntSourceTree :=
  (.node 677 (sourceLit (List.headD (raw_ints% [49880661194124149291948105094537547855005]) 0) 17 true) treeG_J012_part100 treeG_J012_part107)

#time def treeG_J012_part109 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [76648778616947803672636319440868032810125]) 0) 23 true) (.node 792 (sourceLit (List.headD (raw_ints% [195251672896220847322768373615308127580375]) 0) 25 true) (.node 791 (sourceLit (List.headD (raw_ints% [903263215134228867318799177425]) 0) 64 true) (.node 790 (sourceLit (List.headD (raw_ints% [850621938666768858086430538857641920559925]) 0) 26 false) .empty .empty) .empty) (.node 793 (sourceLit (List.headD (raw_ints% [8493376864434201131871285]) 0) 67 false) .empty .empty)) (.node 797 (sourceLit (List.headD (raw_ints% [178010125057589316151905]) 0) 72 false) (.node 796 (sourceLit (List.headD (raw_ints% [39206823850217792813831269156198085473575]) 0) 22 true) (.node 795 (sourceLit (List.headD (raw_ints% [1709340256317439490979465]) 0) 69 false) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [117652902585785632673830233020452961073855]) 0) 19 true) .empty .empty)))

#time def treeG_J012_part110 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [14011722493264326434221442427622233265257375]) 0) 23 false) (.node 829 (sourceLit (List.headD (raw_ints% [18217154544490070020127016726130614219159825]) 0) 24 true) (.node 828 (sourceLit (List.headD (raw_ints% [109303292853892716797660326461585]) 0) 61 true) (.node 827 (sourceLit (List.headD (raw_ints% [1468969408684729148282110556574516006384825]) 0) 28 false) .empty .empty) .empty) (.node 830 (sourceLit (List.headD (raw_ints% [15357335712028980108350921334855]) 0) 63 false) .empty .empty)) (.node 833 (sourceLit (List.headD (raw_ints% [6082167737232072636508023402007668071645295]) 0) 21 true) (.node 832 (sourceLit (List.headD (raw_ints% [903287965025452629328206915285]) 0) 65 true) .empty .empty) (.node 834 (sourceLit (List.headD (raw_ints% [5941723082611736098645155]) 0) 68 false) .empty .empty)))

#time def treeG_J012_part111 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [152356802331025595807595]) 0) 72 false) treeG_J012_part109 treeG_J012_part110)

#time def treeG_J012_part112 : IntSourceTree :=
  (.node 868 (sourceLit (List.headD (raw_ints% [1727839257335036355823903970132783116574475]) 0) 29 false) (.node 838 (sourceLit (List.headD (raw_ints% [475469350973328140600661]) 0) 71 false) (.node 837 (sourceLit (List.headD (raw_ints% [2233359062868742157240059462454768806448445]) 0) 17 true) (.node 836 (sourceLit (List.headD (raw_ints% [2333146505654808060374115]) 0) 69 false) .empty .empty) .empty) (.node 839 (sourceLit (List.headD (raw_ints% [1616324639016926431087620006607729192757265]) 0) 16 true) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [2032574865895401121958715064035]) 0) 67 false) (.node 870 (sourceLit (List.headD (raw_ints% [19918398421823607736299877803845898060279675]) 0) 25 true) (.node 869 (sourceLit (List.headD (raw_ints% [123757402132198466232160028813685]) 0) 62 true) .empty .empty) .empty) (.node 872 (sourceLit (List.headD (raw_ints% [14402225839056768128866979174852849520418125]) 0) 24 false) .empty .empty)))

#time def treeG_J012_part113 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [1998053257697170891892398996413862884300735]) 0) 18 true) (.node 876 (sourceLit (List.headD (raw_ints% [1059373214822189914627571976034207238951595]) 0) 21 true) (.node 875 (sourceLit (List.headD (raw_ints% [2116191413147148303832845]) 0) 70 false) (.node 874 (sourceLit (List.headD (raw_ints% [5928870179998177029162750763125932006025045]) 0) 22 true) .empty .empty) .empty) (.node 877 (sourceLit (List.headD (raw_ints% [1621106005424450795766495]) 0) 70 false) .empty .empty)) (.node 909 (sourceLit (List.headD (raw_ints% [128798867013932396792856870814628733679926225]) 0) 24 false) (.node 879 (sourceLit (List.headD (raw_ints% [161556274321151272396533]) 0) 73 false) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [34778684461056861585127737537135]) 0) 65 true) .empty .empty)))

#time def treeG_J012_part114 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [903304951779181497730470657855]) 0) 66 true) treeG_J012_part112 treeG_J012_part113)

#time def treeG_J012_part115 : IntSourceTree :=
  (.node 835 (sourceLit (List.headD (raw_ints% [1137786862522625500255234514346603409898745]) 0) 20 true) treeG_J012_part111 treeG_J012_part114)

#time def treeG_J012_part116 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [6131619146933785154957265]) 0) 69 false) (.node 914 (sourceLit (List.headD (raw_ints% [903316835225346721202667948165]) 0) 67 true) (.node 913 (sourceLit (List.headD (raw_ints% [236517781162140362698379690199653260398335295]) 0) 21 false) (.node 912 (sourceLit (List.headD (raw_ints% [17163886892188661604997927427565]) 0) 65 false) .empty .empty) .empty) (.node 915 (sourceLit (List.headD (raw_ints% [46293174577462790733046771590660852638301615]) 0) 20 true) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [14368101422560440704051571964703173881648615]) 0) 16 true) (.node 918 (sourceLit (List.headD (raw_ints% [572818327225561327582917]) 0) 72 false) (.node 917 (sourceLit (List.headD (raw_ints% [31666583811441335110842243770639862840002595]) 0) 17 true) .empty .empty) .empty) (.node 950 (sourceLit (List.headD (raw_ints% [37179316358939001132289187154618657935051475]) 0) 27 false) .empty .empty)))

#time def treeG_J012_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [11308450340660150204604799903656661349837505]) 0) 23 true) (.node 954 (sourceLit (List.headD (raw_ints% [60611662835534634931885610240694798101090085]) 0) 24 false) (.node 953 (sourceLit (List.headD (raw_ints% [4516797960991960775682099521355]) 0) 68 false) (.node 952 (sourceLit (List.headD (raw_ints% [46940283926727489113371861008310566816978225]) 0) 26 true) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [903325299990999309795883279545]) 0) 68 true) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [7417132638436041054737461193556499988925465]) 0) 20 true) (.node 957 (sourceLit (List.headD (raw_ints% [2255256570754667179595385]) 0) 71 false) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [25703878306525628449149]) 0) 77 false) .empty .empty)))

#time def treeG_J012_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [38843834192847663829045167665205]) 0) 66 true) treeG_J012_part116 treeG_J012_part117)

#time def treeG_J012_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [420609560882276463003117]) 0) 74 false) (.node 996 (sourceLit (List.headD (raw_ints% [451665715805073121790519118405]) 0) 70 true) (.node 995 (sourceLit (List.headD (raw_ints% [1985866385314571108553386299292894391873184335]) 0) 20 false) (.node 994 (sourceLit (List.headD (raw_ints% [18970508679193189823931066033585]) 0) 67 false) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [1415815059793057891078572143897412789939198045]) 0) 17 true) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [3483142603814838205681721235694308729089302035]) 0) 22 true) (.node 999 (sourceLit (List.headD (raw_ints% [222980143007392873047547186229104825763966265]) 0) 16 true) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [9936916989592094566863474656565]) 0) 69 false) .empty .empty)))

#time def treeG_J012_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [5194291352698583844326996887485]) 0) 71 false) (.node 1039 (sourceLit (List.headD (raw_ints% [317794047656173949206521]) 0) 75 false) (.node 1038 (sourceLit (List.headD (raw_ints% [1386146529239313726859622299123186789983496185]) 0) 18 true) (.node 1037 (sourceLit (List.headD (raw_ints% [225833985530821938228849356895]) 0) 72 true) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [29851007215833276754007156184847364224587600615]) 0) 20 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [225834826749943702781775363129]) 0) 73 true) (.node 1077 (sourceLit (List.headD (raw_ints% [66411021033463832590976348108938085982660297405]) 0) 17 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [10866192090907116941829431206756389494104003215]) 0) 16 true) .empty .empty)))

#time def treeG_J012_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [2031100186677211709371805498907521037272534355]) 0) 21 false) treeG_J012_part119 treeG_J012_part120)

#time def treeG_J012_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [3240695952472699665954178794731529536684941695]) 0) 21 true) treeG_J012_part118 treeG_J012_part121)

#time def treeG_J012_part123 : IntSourceTree :=
  (.node 911 (sourceLit (List.headD (raw_ints% [173358909867853188324620464858389417747494775]) 0) 23 true) treeG_J012_part115 treeG_J012_part122)

#time def treeG_J012_part124 : IntSourceTree :=
  (.node 789 (sourceLit (List.headD (raw_ints% [3613527319576437358624925588025]) 0) 64 false) treeG_J012_part108 treeG_J012_part123)

#time def treeG_J012_part125 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [2415907221626913043943040118777888387935]) 0) 20 true) treeG_J012_part093 treeG_J012_part124)

#time def treeG_J012_part126 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [68068057165377800744881197630011763345]) 0) 20 true) treeG_J012_part062 treeG_J012_part125)

#time def treeG_J012 : IntSourceTree := treeG_J012_part126

#time def treeG_J013_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 5 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 39 false) (.node 4 (sourceLit (List.headD (raw_ints% [2301222637056327918278815931175]) 0) 42 false) (.node 3 (sourceLit (List.headD (raw_ints% [11871874581330315826470131760825]) 0) 38 false) .empty .empty) .empty) (.node 6 (sourceLit (List.headD (raw_ints% [1099176638256514785833312057325]) 0) 43 false) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [64155049557054303237609594375]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 43 true) (.node 8 (sourceLit (List.headD (raw_ints% [132402150923693691762807260175]) 0) 46 false) .empty .empty) .empty) (.node 11 (sourceLit (List.headD (raw_ints% [188442453671909775023335424775]) 0) 45 true) .empty .empty)))

#time def treeG_J013_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [3814624568257282895209219125]) 0) 51 false) (.node 15 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 49 false) (.node 14 (sourceLit (List.headD (raw_ints% [70254520979693746577148018049275]) 0) 39 true) (.node 13 (sourceLit (List.headD (raw_ints% [323688233819213441308025921025]) 0) 46 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [55340032485911089962860918401275]) 0) 38 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [934277033295099233158193775]) 0) 53 false) (.node 18 (sourceLit (List.headD (raw_ints% [137945766175318857438159979395825]) 0) 36 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [194447297093358837898153652358375]) 0) 35 true) .empty .empty)))

#time def treeG_J013_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 49 false) treeG_J013_part000 treeG_J013_part001)

#time def treeG_J013_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [5516469682442476807295028750400125]) 0) 29 true) (.node 24 (sourceLit (List.headD (raw_ints% [1775150678523877345109318810883525]) 0) 31 true) (.node 23 (sourceLit (List.headD (raw_ints% [28149682860660474208277325]) 0) 58 false) (.node 22 (sourceLit (List.headD (raw_ints% [1158489289945858963389287109548625]) 0) 32 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [27691210676709753658480125]) 0) 58 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [8606598006497600213923509745314975]) 0) 28 true) (.node 27 (sourceLit (List.headD (raw_ints% [6816860719312144041074025]) 0) 60 false) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [3359207212647079442034015]) 0) 61 false) .empty .empty)))

#time def treeG_J013_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [12615859307681623557675]) 0) 69 false) (.node 33 (sourceLit (List.headD (raw_ints% [51096571466451484793085]) 0) 67 false) (.node 32 (sourceLit (List.headD (raw_ints% [163925426419055874720697135788656025]) 0) 23 true) (.node 31 (sourceLit (List.headD (raw_ints% [414156814146764197441065]) 0) 64 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [489917046215535114146510078122307295]) 0) 21 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [6233241033107314872525]) 0) 70 false) (.node 36 (sourceLit (List.headD (raw_ints% [700387840332835860361117822506954945]) 0) 20 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [3693537367468110143998138236558543645]) 0) 17 true) .empty .empty)))

#time def treeG_J013_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [106954021467427319351860745830489425]) 0) 24 true) treeG_J013_part003 treeG_J013_part004)

#time def treeG_J013_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [458380723923192298686111225]) 0) 54 false) treeG_J013_part002 treeG_J013_part005)

#time def treeG_J013_part007 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 46 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 40 false) (.node 45 (sourceLit (List.headD (raw_ints% [2301222637056327918278815931175]) 0) 43 false) (.node 44 (sourceLit (List.headD (raw_ints% [11871874581330315826470131760825]) 0) 39 false) .empty .empty) .empty) (.node 47 (sourceLit (List.headD (raw_ints% [1099176638256514785833312057325]) 0) 44 false) .empty .empty)) (.node 51 (sourceLit (List.headD (raw_ints% [64155049557054303237609594375]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 44 true) (.node 49 (sourceLit (List.headD (raw_ints% [132402150923693691762807260175]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [188442453671909775023335424775]) 0) 46 true) .empty .empty)))

#time def treeG_J013_part008 : IntSourceTree :=
  (.node 58 (sourceLit (List.headD (raw_ints% [3814624568257282895209219125]) 0) 52 false) (.node 56 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 50 false) (.node 55 (sourceLit (List.headD (raw_ints% [70254520979693746577148018049275]) 0) 40 true) (.node 54 (sourceLit (List.headD (raw_ints% [323688233819213441308025921025]) 0) 47 true) .empty .empty) .empty) (.node 57 (sourceLit (List.headD (raw_ints% [55340032485911089962860918401275]) 0) 39 true) .empty .empty)) (.node 60 (sourceLit (List.headD (raw_ints% [934277033295099233158193775]) 0) 54 false) (.node 59 (sourceLit (List.headD (raw_ints% [137945766175318857438159979395825]) 0) 37 true) .empty .empty) (.node 61 (sourceLit (List.headD (raw_ints% [194447297093358837898153652358375]) 0) 36 true) .empty .empty)))

#time def treeG_J013_part009 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 50 false) treeG_J013_part007 treeG_J013_part008)

#time def treeG_J013_part010 : IntSourceTree :=
  (.node 67 (sourceLit (List.headD (raw_ints% [5516469682442476807295028750400125]) 0) 30 true) (.node 65 (sourceLit (List.headD (raw_ints% [1775150678523877345109318810883525]) 0) 32 true) (.node 64 (sourceLit (List.headD (raw_ints% [28149682860660474208277325]) 0) 59 false) (.node 63 (sourceLit (List.headD (raw_ints% [1158489289945858963389287109548625]) 0) 33 true) .empty .empty) .empty) (.node 66 (sourceLit (List.headD (raw_ints% [27691210676709753658480125]) 0) 59 false) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [8606598006497600213923509745314975]) 0) 29 true) (.node 68 (sourceLit (List.headD (raw_ints% [6816860719312144041074025]) 0) 61 false) .empty .empty) (.node 70 (sourceLit (List.headD (raw_ints% [3359207212647079442034015]) 0) 62 false) .empty .empty)))

#time def treeG_J013_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [12615859307681623557675]) 0) 70 false) (.node 74 (sourceLit (List.headD (raw_ints% [51096571466451484793085]) 0) 68 false) (.node 73 (sourceLit (List.headD (raw_ints% [163925426419055874720697135788656025]) 0) 24 true) (.node 72 (sourceLit (List.headD (raw_ints% [414156814146764197441065]) 0) 65 false) .empty .empty) .empty) (.node 75 (sourceLit (List.headD (raw_ints% [489917046215535114146510078122307295]) 0) 22 true) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [6233241033107314872525]) 0) 71 false) (.node 77 (sourceLit (List.headD (raw_ints% [700387840332835860361117822506954945]) 0) 21 true) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [3693537367468110143998138236558543645]) 0) 18 true) .empty .empty)))

#time def treeG_J013_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [106954021467427319351860745830489425]) 0) 25 true) treeG_J013_part010 treeG_J013_part011)

#time def treeG_J013_part013 : IntSourceTree :=
  (.node 62 (sourceLit (List.headD (raw_ints% [458380723923192298686111225]) 0) 55 false) treeG_J013_part009 treeG_J013_part012)

#time def treeG_J013_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [192579774559805047041]) 0) 75 false) treeG_J013_part006 treeG_J013_part013)

#time def treeG_J013_part015 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [200649252290333080288004925975]) 0) 47 false) (.node 88 (sourceLit (List.headD (raw_ints% [834372336409127402307697536975]) 0) 45 false) (.node 87 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 41 false) (.node 86 (sourceLit (List.headD (raw_ints% [3503268635856141050724319805025]) 0) 43 false) .empty .empty) .empty) (.node 89 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 43 false) .empty .empty)) (.node 93 (sourceLit (List.headD (raw_ints% [53196673524606108738644928525]) 0) 46 true) (.node 92 (sourceLit (List.headD (raw_ints% [12137441808091354666574788125]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [9918023877468935527543969725]) 0) 48 true) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [134173757381619417781235587969275]) 0) 39 false) .empty .empty)))

#time def treeG_J013_part016 : IntSourceTree :=
  (.node 100 (sourceLit (List.headD (raw_ints% [909118832309192021607126182808225]) 0) 35 true) (.node 98 (sourceLit (List.headD (raw_ints% [747494753599258581967614715024575]) 0) 36 true) (.node 97 (sourceLit (List.headD (raw_ints% [5895328878215800838050611375]) 0) 52 false) (.node 96 (sourceLit (List.headD (raw_ints% [506696135351638882654323225992925]) 0) 38 true) .empty .empty) .empty) (.node 99 (sourceLit (List.headD (raw_ints% [1440173767481091831025512675]) 0) 54 false) .empty .empty)) (.node 102 (sourceLit (List.headD (raw_ints% [5063824217041623849351629765919375]) 0) 32 true) (.node 101 (sourceLit (List.headD (raw_ints% [1410173342667006167630276325]) 0) 54 false) .empty .empty) (.node 103 (sourceLit (List.headD (raw_ints% [345781992480550401853001925]) 0) 56 false) .empty .empty)))

#time def treeG_J013_part017 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [354898798468591210450646804775]) 0) 48 true) treeG_J013_part015 treeG_J013_part016)

#time def treeG_J013_part018 : IntSourceTree :=
  (.node 109 (sourceLit (List.headD (raw_ints% [10274514225977208640114035]) 0) 61 false) (.node 107 (sourceLit (List.headD (raw_ints% [5218587489349402404351525]) 0) 62 false) (.node 106 (sourceLit (List.headD (raw_ints% [22885941173939560714454072223736275]) 0) 29 true) (.node 105 (sourceLit (List.headD (raw_ints% [84907520765932143174629175]) 0) 58 false) .empty .empty) .empty) (.node 108 (sourceLit (List.headD (raw_ints% [35525159453042214244436720257886025]) 0) 28 true) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [2530893584353551047151885]) 0) 63 false) (.node 110 (sourceLit (List.headD (raw_ints% [443868250948419094339243877869668975]) 0) 24 true) .empty .empty) (.node 112 (sourceLit (List.headD (raw_ints% [691706745320362680094188830855259375]) 0) 23 true) .empty .empty)))

#time def treeG_J013_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [18718873523182637387557632083664014595]) 0) 17 true) (.node 116 (sourceLit (List.headD (raw_ints% [3218948529391445052810962802471503415]) 0) 20 true) (.node 115 (sourceLit (List.headD (raw_ints% [19240356079384930617705]) 0) 70 false) (.node 114 (sourceLit (List.headD (raw_ints% [2132889776489358881384644094496189105]) 0) 21 true) .empty .empty) .empty) (.node 117 (sourceLit (List.headD (raw_ints% [18998477582255932242825]) 0) 70 false) .empty .empty)) (.node 126 (sourceLit (List.headD (raw_ints% [4373848529963800567646890648725]) 0) 42 false) (.node 119 (sourceLit (List.headD (raw_ints% [4692602836628874496197]) 0) 72 false) .empty .empty) (.node 127 (sourceLit (List.headD (raw_ints% [601022999399906566222751936925]) 0) 46 false) .empty .empty)))

#time def treeG_J013_part020 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [311963671213861227854895]) 0) 66 false) treeG_J013_part018 treeG_J013_part019)

#time def treeG_J013_part021 : IntSourceTree :=
  (.node 104 (sourceLit (List.headD (raw_ints% [7492763641042994362004978065505475]) 0) 31 true) treeG_J013_part017 treeG_J013_part020)

#time def treeG_J013_part022 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [32944484907676534094988710625]) 0) 50 false) (.node 131 (sourceLit (List.headD (raw_ints% [8530887670829923565649708225]) 0) 52 false) (.node 130 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 45 false) (.node 129 (sourceLit (List.headD (raw_ints% [569568034561740018782083016625]) 0) 46 false) .empty .empty) .empty) (.node 132 (sourceLit (List.headD (raw_ints% [109098262652158290802983666975]) 0) 46 false) .empty .empty)) (.node 136 (sourceLit (List.headD (raw_ints% [386109363117968979593267688525]) 0) 49 true) (.node 135 (sourceLit (List.headD (raw_ints% [102214139180656582179191803009275]) 0) 41 false) (.node 134 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 49 false) .empty .empty) .empty) (.node 137 (sourceLit (List.headD (raw_ints% [225678051432863896345731153795825]) 0) 40 true) .empty .empty)))

#time def treeG_J013_part023 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [1952667463547882442981171328185375]) 0) 34 true) (.node 141 (sourceLit (List.headD (raw_ints% [357335767607916591854486265224925]) 0) 37 true) (.node 140 (sourceLit (List.headD (raw_ints% [1946070501667084428892831575]) 0) 54 false) (.node 139 (sourceLit (List.headD (raw_ints% [304774493711969862264727367814375]) 0) 38 true) .empty .empty) .empty) (.node 142 (sourceLit (List.headD (raw_ints% [237948154685953467236041275]) 0) 57 false) .empty .empty)) (.node 145 (sourceLit (List.headD (raw_ints% [2858806481259558508447829627310975]) 0) 33 true) (.node 144 (sourceLit (List.headD (raw_ints% [233183261037908505019892625]) 0) 57 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [28608155044611194758074525]) 0) 60 false) .empty .empty)))

#time def treeG_J013_part024 : IntSourceTree :=
  (.node 138 (sourceLit (List.headD (raw_ints% [7976033188174318780892003625]) 0) 52 false) treeG_J013_part022 treeG_J013_part023)

#time def treeG_J013_part025 : IntSourceTree :=
  (.node 152 (sourceLit (List.headD (raw_ints% [1702579956060022652269755]) 0) 64 false) (.node 150 (sourceLit (List.headD (raw_ints% [1728826753332532299520005]) 0) 64 false) (.node 149 (sourceLit (List.headD (raw_ints% [13459280723272307015256605256285525]) 0) 30 true) (.node 148 (sourceLit (List.headD (raw_ints% [14057489238085465576332075]) 0) 61 false) .empty .empty) .empty) (.node 151 (sourceLit (List.headD (raw_ints% [168457114740495887493691566019589775]) 0) 26 true) .empty .empty)) (.node 154 (sourceLit (List.headD (raw_ints% [209770528280958258268725]) 0) 67 false) (.node 153 (sourceLit (List.headD (raw_ints% [263890659450653402686745847533301675]) 0) 25 true) .empty .empty) (.node 155 (sourceLit (List.headD (raw_ints% [821486365136911883619067008186940905]) 0) 23 true) .empty .empty)))

#time def treeG_J013_part026 : IntSourceTree :=
  (.node 168 (sourceLit (List.headD (raw_ints% [1569719661190498862583310210725]) 0) 45 false) (.node 159 (sourceLit (List.headD (raw_ints% [7512668077857263621779746923552735475]) 0) 19 true) (.node 158 (sourceLit (List.headD (raw_ints% [3191309137287154342575]) 0) 73 false) (.node 157 (sourceLit (List.headD (raw_ints% [1259280344529304596224922489982274235]) 0) 22 true) .empty .empty) .empty) (.node 167 (sourceLit (List.headD (raw_ints% [14371216598452487579411212131525]) 0) 41 false) .empty .empty)) (.node 170 (sourceLit (List.headD (raw_ints% [184459391135703469247039045325]) 0) 48 false) (.node 169 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 48 false) .empty .empty) (.node 171 (sourceLit (List.headD (raw_ints% [307458740201537001353863061475]) 0) 46 false) .empty .empty)))

#time def treeG_J013_part027 : IntSourceTree :=
  (.node 156 (sourceLit (List.headD (raw_ints% [25864852851088237677735]) 0) 70 false) treeG_J013_part025 treeG_J013_part026)

#time def treeG_J013_part028 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [8684735745748541953579521736668075]) 0) 31 true) treeG_J013_part024 treeG_J013_part027)

#time def treeG_J013_part029 : IntSourceTree :=
  (.node 128 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 42 false) treeG_J013_part021 treeG_J013_part028)

#time def treeG_J013_part030 : IntSourceTree :=
  (.node 85 (sourceLit (List.headD (raw_ints% [20619571641257916961763913058275]) 0) 39 false) treeG_J013_part014 treeG_J013_part029)

#time def treeG_J013_part031 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [409690678630832182945470134025]) 0) 50 true) (.node 175 (sourceLit (List.headD (raw_ints% [625390358763198543020027797275]) 0) 48 false) (.node 174 (sourceLit (List.headD (raw_ints% [766852800223665871838170750725]) 0) 39 false) (.node 173 (sourceLit (List.headD (raw_ints% [271393198828922690344612262475]) 0) 46 false) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [2142122362242144197521392074141325]) 0) 38 false) .empty .empty)) (.node 180 (sourceLit (List.headD (raw_ints% [3967273067082325774628511702221775]) 0) 35 true) (.node 179 (sourceLit (List.headD (raw_ints% [5095685653212135118840978275]) 0) 53 false) (.node 178 (sourceLit (List.headD (raw_ints% [6474202892252386101095782206441825]) 0) 36 true) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [2481967660667162690155386825]) 0) 54 false) .empty .empty)))

#time def treeG_J013_part032 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [18170980065912389949371475]) 0) 61 false) (.node 185 (sourceLit (List.headD (raw_ints% [74137870135988180922631725]) 0) 59 false) (.node 184 (sourceLit (List.headD (raw_ints% [23749915775723124725693763185460525]) 0) 31 true) (.node 183 (sourceLit (List.headD (raw_ints% [606010626263263467091163175]) 0) 56 false) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [68595866226366311555876475850214925]) 0) 29 true) .empty .empty)) (.node 189 (sourceLit (List.headD (raw_ints% [17840464250193722512550115]) 0) 61 false) (.node 188 (sourceLit (List.headD (raw_ints% [103430612478934457012835627528803175]) 0) 28 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [1278919681630436203613601594934878225]) 0) 24 true) .empty .empty)))

#time def treeG_J013_part033 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [17805664909865038029335491208475825]) 0) 32 true) treeG_J013_part031 treeG_J013_part032)

#time def treeG_J013_part034 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [9924833312799145085094109328519551065]) 0) 20 true) (.node 194 (sourceLit (List.headD (raw_ints% [6311611325931550004591223026569464495]) 0) 21 true) (.node 193 (sourceLit (List.headD (raw_ints% [1078652613632300196559965]) 0) 65 false) (.node 192 (sourceLit (List.headD (raw_ints% [2003607090527571519804876225458177025]) 0) 23 true) .empty .empty) .empty) (.node 195 (sourceLit (List.headD (raw_ints% [132809103963418535797905]) 0) 68 false) .empty .empty)) (.node 198 (sourceLit (List.headD (raw_ints% [61875068526692856770837407275201536445]) 0) 17 true) (.node 197 (sourceLit (List.headD (raw_ints% [32731228119920543112645]) 0) 70 false) .empty .empty) (.node 199 (sourceLit (List.headD (raw_ints% [8072633712519742874103]) 0) 72 false) .empty .empty)))

#time def treeG_J013_part035 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [54999950593236824289107468475]) 0) 50 false) (.node 211 (sourceLit (List.headD (raw_ints% [116212289769064080721841379525]) 0) 49 false) (.node 210 (sourceLit (List.headD (raw_ints% [1160408793663865456722644457825]) 0) 45 false) (.node 209 (sourceLit (List.headD (raw_ints% [250037906657189710950306798525]) 0) 48 false) .empty .empty) .empty) (.node 212 (sourceLit (List.headD (raw_ints% [505819217750915711904742455975]) 0) 46 false) .empty .empty)) (.node 215 (sourceLit (List.headD (raw_ints% [203661425561089498486545435267825]) 0) 40 true) (.node 214 (sourceLit (List.headD (raw_ints% [901638534315357775231269975]) 0) 47 false) .empty .empty) (.node 216 (sourceLit (List.headD (raw_ints% [126437465235145940326661935725]) 0) 52 false) .empty .empty)))

#time def treeG_J013_part036 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [5623519538524886444117430834075]) 0) 43 false) treeG_J013_part034 treeG_J013_part035)

#time def treeG_J013_part037 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [4384413428976578150928135]) 0) 63 false) treeG_J013_part033 treeG_J013_part036)

#time def treeG_J013_part038 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [1530175041923348821211221725]) 0) 55 false) (.node 220 (sourceLit (List.headD (raw_ints% [787403787886262672487036675]) 0) 56 false) (.node 219 (sourceLit (List.headD (raw_ints% [5864653904828446376566327470813075]) 0) 37 true) (.node 218 (sourceLit (List.headD (raw_ints% [425642745007180820507254141275]) 0) 51 true) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [3252601531866492590919539171771925]) 0) 36 true) .empty .empty)) (.node 225 (sourceLit (List.headD (raw_ints% [18032302813204007708798103930838575]) 0) 32 true) (.node 224 (sourceLit (List.headD (raw_ints% [186413682612677481035635275]) 0) 58 false) (.node 223 (sourceLit (List.headD (raw_ints% [13900329982769273143373148552105075]) 0) 33 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [2845607193211061635284825]) 0) 64 false) .empty .empty)))

#time def treeG_J013_part039 : IntSourceTree :=
  (.node 232 (sourceLit (List.headD (raw_ints% [670458368229138874664595]) 0) 66 false) (.node 230 (sourceLit (List.headD (raw_ints% [10925157236863593314470095]) 0) 62 false) (.node 229 (sourceLit (List.headD (raw_ints% [76512051032389842982322417016232125]) 0) 29 true) (.node 228 (sourceLit (List.headD (raw_ints% [22284470893739314322410875]) 0) 61 false) .empty .empty) .empty) (.node 231 (sourceLit (List.headD (raw_ints% [942005452149444428626218462895698675]) 0) 25 true) .empty .empty)) (.node 234 (sourceLit (List.headD (raw_ints% [659111557070383680022515]) 0) 66 false) (.node 233 (sourceLit (List.headD (raw_ints% [1475825771626264714431384530391573675]) 0) 24 true) .empty .empty) (.node 235 (sourceLit (List.headD (raw_ints% [4668638595657726237353089010195582685]) 0) 22 true) .empty .empty)))

#time def treeG_J013_part040 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [51226394734869227648717432376878775]) 0) 30 true) treeG_J013_part038 treeG_J013_part039)

#time def treeG_J013_part041 : IntSourceTree :=
  (.node 250 (sourceLit (List.headD (raw_ints% [315616422178675952653574551725]) 0) 48 false) (.node 239 (sourceLit (List.headD (raw_ints% [46849732370978329527277913428096065495]) 0) 18 true) (.node 238 (sourceLit (List.headD (raw_ints% [19965991570771925742345]) 0) 71 false) (.node 237 (sourceLit (List.headD (raw_ints% [7406272623740535892644264348555002595]) 0) 21 true) .empty .empty) .empty) (.node 249 (sourceLit (List.headD (raw_ints% [4195324100169359728151099193675]) 0) 44 false) .empty .empty)) (.node 252 (sourceLit (List.headD (raw_ints% [72240072018607401529793289975]) 0) 50 false) (.node 251 (sourceLit (List.headD (raw_ints% [426475026731164227684390698175]) 0) 47 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [740245236672908733464872649475]) 0) 46 false) .empty .empty)))

#time def treeG_J013_part042 : IntSourceTree :=
  (.node 259 (sourceLit (List.headD (raw_ints% [435834116313605090744936097825]) 0) 52 true) (.node 257 (sourceLit (List.headD (raw_ints% [1421190400511999705558765619825]) 0) 50 false) (.node 256 (sourceLit (List.headD (raw_ints% [3771413766730860185413755556283925]) 0) 38 true) (.node 255 (sourceLit (List.headD (raw_ints% [156122180057220796311199131825]) 0) 50 true) .empty .empty) .empty) (.node 258 (sourceLit (List.headD (raw_ints% [47969858333978337944501452314169425]) 0) 36 false) .empty .empty)) (.node 261 (sourceLit (List.headD (raw_ints% [3817262642422938689740906575]) 0) 54 false) (.node 260 (sourceLit (List.headD (raw_ints% [42949958171545245237902108064282825]) 0) 35 true) .empty .empty) (.node 262 (sourceLit (List.headD (raw_ints% [86277584109862724880089762288225775]) 0) 32 true) .empty .empty)))

#time def treeG_J013_part043 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [224512944829674366416346020122875]) 0) 39 false) treeG_J013_part041 treeG_J013_part042)

#time def treeG_J013_part044 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [81079398261242060442435]) 0) 69 false) treeG_J013_part040 treeG_J013_part043)

#time def treeG_J013_part045 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [2593478465107871990212854381732975]) 0) 39 false) treeG_J013_part037 treeG_J013_part044)

#time def treeG_J013_part046 : IntSourceTree :=
  (.node 268 (sourceLit (List.headD (raw_ints% [306380545400019364176903831486227025]) 0) 28 true) (.node 266 (sourceLit (List.headD (raw_ints% [219920978784897811784893187043202275]) 0) 29 true) (.node 265 (sourceLit (List.headD (raw_ints% [56137906238344650056501775]) 0) 60 false) (.node 264 (sourceLit (List.headD (raw_ints% [87452724086431060421291425231380075]) 0) 31 true) .empty .empty) .empty) (.node 267 (sourceLit (List.headD (raw_ints% [27358735025464596215185725]) 0) 61 false) .empty .empty)) (.node 271 (sourceLit (List.headD (raw_ints% [817592975985876895442745]) 0) 66 false) (.node 270 (sourceLit (List.headD (raw_ints% [3617851584442513747255033094103977775]) 0) 24 true) (.node 269 (sourceLit (List.headD (raw_ints% [26728477537284906132271635]) 0) 61 false) .empty .empty) .empty) (.node 272 (sourceLit (List.headD (raw_ints% [5532436526667983909204871477707412375]) 0) 23 true) .empty .empty)))

#time def treeG_J013_part047 : IntSourceTree :=
  (.node 278 (sourceLit (List.headD (raw_ints% [175125655433004291793779051878558546595]) 0) 17 true) (.node 276 (sourceLit (List.headD (raw_ints% [27424275452462664813730602753045110415]) 0) 20 true) (.node 275 (sourceLit (List.headD (raw_ints% [393493349143546608426705]) 0) 67 false) (.node 274 (sourceLit (List.headD (raw_ints% [17301601020088685426310929459695714305]) 0) 21 true) .empty .empty) .empty) (.node 277 (sourceLit (List.headD (raw_ints% [24174085070660758664895]) 0) 71 false) .empty .empty)) (.node 290 (sourceLit (List.headD (raw_ints% [1517457653252747135714227367925]) 0) 46 false) (.node 279 (sourceLit (List.headD (raw_ints% [5946678929126091434121]) 0) 73 false) .empty .empty) (.node 291 (sourceLit (List.headD (raw_ints% [24925516551201483991466646525]) 0) 52 false) .empty .empty)))

#time def treeG_J013_part048 : IntSourceTree :=
  (.node 273 (sourceLit (List.headD (raw_ints% [1603180859284255302098415]) 0) 65 false) treeG_J013_part046 treeG_J013_part047)

#time def treeG_J013_part049 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [1591223057959683043906652484504225]) 0) 41 true) (.node 295 (sourceLit (List.headD (raw_ints% [107043592597690966225722863847675]) 0) 42 false) (.node 294 (sourceLit (List.headD (raw_ints% [184835899534648343922410344875]) 0) 49 false) (.node 293 (sourceLit (List.headD (raw_ints% [89480193443977978770479111475]) 0) 50 false) .empty .empty) .empty) (.node 296 (sourceLit (List.headD (raw_ints% [408997110527512676964523003275]) 0) 51 true) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [13458628059701696080266944946245625]) 0) 39 false) (.node 298 (sourceLit (List.headD (raw_ints% [461708286379795131516504940275]) 0) 53 false) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [442133346616695192124832391225]) 0) 53 true) .empty .empty)))

#time def treeG_J013_part050 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [33373048692656156974223175]) 0) 61 false) (.node 304 (sourceLit (List.headD (raw_ints% [17229282826085324751524625]) 0) 62 false) (.node 303 (sourceLit (List.headD (raw_ints% [18094313531773362934179153434030175]) 0) 35 true) (.node 302 (sourceLit (List.headD (raw_ints% [1143543800249794934264842425]) 0) 56 false) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [17355105318306763178123330325135375]) 0) 34 true) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [32432999157189878107960575]) 0) 61 false) (.node 307 (sourceLit (List.headD (raw_ints% [42173646012507146034043938666580875]) 0) 32 true) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [57467123591907380298645353617498725]) 0) 31 true) .empty .empty)))

#time def treeG_J013_part051 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [9924339159919688161745642223127725]) 0) 38 true) treeG_J013_part049 treeG_J013_part050)

#time def treeG_J013_part052 : IntSourceTree :=
  (.node 292 (sourceLit (List.headD (raw_ints% [1200080889173741198832820336725]) 0) 46 false) treeG_J013_part048 treeG_J013_part051)

#time def treeG_J013_part053 : IntSourceTree :=
  (.node 315 (sourceLit (List.headD (raw_ints% [3158240606107739797239460112375032905]) 0) 24 true) (.node 313 (sourceLit (List.headD (raw_ints% [1014152688760429798693371736828959675]) 0) 26 true) (.node 312 (sourceLit (List.headD (raw_ints% [964727583742614916220895]) 0) 66 false) (.node 311 (sourceLit (List.headD (raw_ints% [668961533073267329657203657802069775]) 0) 27 true) .empty .empty) .empty) (.node 314 (sourceLit (List.headD (raw_ints% [236017325553467905518975]) 0) 68 false) .empty .empty)) (.node 318 (sourceLit (List.headD (raw_ints% [28382178570549591587445]) 0) 71 false) (.node 317 (sourceLit (List.headD (raw_ints% [5004500707180532230271584601122526955]) 0) 23 true) (.node 316 (sourceLit (List.headD (raw_ints% [231334552621062487541835]) 0) 68 false) .empty .empty) .empty) (.node 319 (sourceLit (List.headD (raw_ints% [32068980765506490566625284612615620275]) 0) 20 true) .empty .empty)))

#time def treeG_J013_part054 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [7196808729856971104636887199409525]) 0) 38 false) (.node 334 (sourceLit (List.headD (raw_ints% [141997927516859434627536420478725]) 0) 39 false) (.node 333 (sourceLit (List.headD (raw_ints% [1659916541674573664200768023975]) 0) 46 false) (.node 332 (sourceLit (List.headD (raw_ints% [127164060391004470401939882225]) 0) 50 false) .empty .empty) .empty) (.node 335 (sourceLit (List.headD (raw_ints% [85239519897967285058402369175]) 0) 52 false) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [149808134043398052754527211322439825]) 0) 36 true) (.node 337 (sourceLit (List.headD (raw_ints% [3057178842622050413416857632925]) 0) 50 true) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [2282667261832785616810955858925]) 0) 52 false) .empty .empty)))

#time def treeG_J013_part055 : IntSourceTree :=
  (.node 331 (sourceLit (List.headD (raw_ints% [545491313260791454014918334875]) 0) 48 false) treeG_J013_part053 treeG_J013_part054)

#time def treeG_J013_part056 : IntSourceTree :=
  (.node 345 (sourceLit (List.headD (raw_ints% [81696356370337947955695225]) 0) 60 false) (.node 343 (sourceLit (List.headD (raw_ints% [340730796209876128602406575]) 0) 58 false) (.node 342 (sourceLit (List.headD (raw_ints% [1184037828359857359823352442272123025]) 0) 32 true) (.node 341 (sourceLit (List.headD (raw_ints% [55743826157389766351821662225]) 0) 57 true) .empty .empty) .empty) (.node 344 (sourceLit (List.headD (raw_ints% [491565308930316553472441484657585525]) 0) 31 true) .empty .empty)) (.node 347 (sourceLit (List.headD (raw_ints% [39387362359847717733260625]) 0) 61 false) (.node 346 (sourceLit (List.headD (raw_ints% [890805761586735031614999953765461725]) 0) 29 true) .empty .empty) (.node 348 (sourceLit (List.headD (raw_ints% [1043176127000209308912502205844360975]) 0) 28 true) .empty .empty)))

#time def treeG_J013_part057 : IntSourceTree :=
  (.node 354 (sourceLit (List.headD (raw_ints% [47604171060578821690064861697357704895]) 0) 21 true) (.node 352 (sourceLit (List.headD (raw_ints% [15874332531676570639825645571958820425]) 0) 23 true) (.node 351 (sourceLit (List.headD (raw_ints% [2315644123133574413564895]) 0) 65 false) (.node 350 (sourceLit (List.headD (raw_ints% [11093732055085775609198177431975695825]) 0) 24 true) .empty .empty) .empty) (.node 353 (sourceLit (List.headD (raw_ints% [2255729475686204362785165]) 0) 65 false) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [73639423942985008697932120842955942545]) 0) 20 true) (.node 355 (sourceLit (List.headD (raw_ints% [550575953070325013649195]) 0) 67 false) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [134638212338419452882255]) 0) 69 false) .empty .empty)))

#time def treeG_J013_part058 : IntSourceTree :=
  (.node 349 (sourceLit (List.headD (raw_ints% [38137520777094850083649515]) 0) 61 false) treeG_J013_part056 treeG_J013_part057)

#time def treeG_J013_part059 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [473626056081999519806444346344142825]) 0) 35 false) treeG_J013_part055 treeG_J013_part058)

#time def treeG_J013_part060 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [3950830075105328204450385]) 0) 64 false) treeG_J013_part052 treeG_J013_part059)

#time def treeG_J013_part061 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [462082207830042677060029275]) 0) 57 false) treeG_J013_part045 treeG_J013_part060)

#time def treeG_J013_part062 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [21986108875228339596024044775]) 0) 51 false) treeG_J013_part030 treeG_J013_part061)

#time def treeG_J013_part063 : IntSourceTree :=
  (.node 375 (sourceLit (List.headD (raw_ints% [286176442873904430275355034911975]) 0) 40 true) (.node 373 (sourceLit (List.headD (raw_ints% [164847927338030962033400652975]) 0) 50 false) (.node 372 (sourceLit (List.headD (raw_ints% [3163849616912590433286526342275]) 0) 46 false) (.node 359 (sourceLit (List.headD (raw_ints% [16488820712297408719203]) 0) 72 false) .empty .empty) .empty) (.node 374 (sourceLit (List.headD (raw_ints% [920572943535980288511126644475]) 0) 47 false) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [4904011988141230939482877394025]) 0) 51 true) (.node 377 (sourceLit (List.headD (raw_ints% [13561700961695703280263497137426425]) 0) 39 false) (.node 376 (sourceLit (List.headD (raw_ints% [749955190119381817198132479975]) 0) 51 false) .empty .empty) .empty) (.node 379 (sourceLit (List.headD (raw_ints% [203642646282204837075594991107422325]) 0) 37 true) .empty .empty)))

#time def treeG_J013_part064 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [422144887657089500759948163357044025]) 0) 32 true) (.node 383 (sourceLit (List.headD (raw_ints% [1111660574232763908086635828536002325]) 0) 33 true) (.node 382 (sourceLit (List.headD (raw_ints% [224118848429808860341551491325]) 0) 56 true) (.node 381 (sourceLit (List.headD (raw_ints% [513323412721678272453426915236653725]) 0) 36 false) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [202896533601193530590209575]) 0) 59 false) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [722111177536706447478824199099138225]) 0) 30 true) (.node 386 (sourceLit (List.headD (raw_ints% [24161653838840895490736025]) 0) 62 false) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [46341725562505557358560675]) 0) 61 false) .empty .empty)))

#time def treeG_J013_part065 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [1362400304224740404467894125075]) 0) 54 false) treeG_J013_part063 treeG_J013_part064)

#time def treeG_J013_part066 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [1311660173472332740709265]) 0) 66 false) (.node 392 (sourceLit (List.headD (raw_ints% [1319254432998983884125]) 0) 76 false) (.node 391 (sourceLit (List.headD (raw_ints% [8417885922792706290569362800767416725]) 0) 25 true) (.node 390 (sourceLit (List.headD (raw_ints% [22334200476673537265847975]) 0) 62 false) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [11817721776634851445052158624642981725]) 0) 24 true) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [9976293764039453940855]) 0) 73 false) (.node 395 (sourceLit (List.headD (raw_ints% [34971208636147862501107021247857573275]) 0) 22 true) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [53621421114262879776845782438465834725]) 0) 21 true) .empty .empty)))

#time def treeG_J013_part067 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [9486220272848206546839727478705325]) 0) 38 true) (.node 414 (sourceLit (List.headD (raw_ints% [533219182859715385861272654106875]) 0) 39 false) (.node 413 (sourceLit (List.headD (raw_ints% [4667782692150607202372284660575]) 0) 46 false) (.node 399 (sourceLit (List.headD (raw_ints% [337174512024077871414482638614662422545]) 0) 18 true) .empty .empty) .empty) (.node 415 (sourceLit (List.headD (raw_ints% [443259374831496272423311262325]) 0) 48 true) .empty .empty)) (.node 418 (sourceLit (List.headD (raw_ints% [366795349430529305238743165521262625]) 0) 36 false) (.node 417 (sourceLit (List.headD (raw_ints% [6056999603099577682209387552825]) 0) 50 false) .empty .empty) (.node 419 (sourceLit (List.headD (raw_ints% [3593339624987008278146916626475]) 0) 53 true) .empty .empty)))

#time def treeG_J013_part068 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [77873855197320269707365]) 0) 70 false) treeG_J013_part066 treeG_J013_part067)

#time def treeG_J013_part069 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [813307632632579787717920791374366075]) 0) 29 true) treeG_J013_part065 treeG_J013_part068)

#time def treeG_J013_part070 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [60600088615427791317257175]) 0) 61 false) (.node 423 (sourceLit (List.headD (raw_ints% [224800310022228612598756304475]) 0) 57 true) (.node 422 (sourceLit (List.headD (raw_ints% [17610387035453562078333013729845042225]) 0) 32 false) (.node 421 (sourceLit (List.headD (raw_ints% [1585375608854299469875180773975]) 0) 55 false) .empty .empty) .empty) (.node 424 (sourceLit (List.headD (raw_ints% [8401719284931794711220645143630433075]) 0) 31 true) .empty .empty)) (.node 428 (sourceLit (List.headD (raw_ints% [4733713293293442270918091386948744825]) 0) 28 true) (.node 427 (sourceLit (List.headD (raw_ints% [57259252995515864229683475]) 0) 61 false) (.node 426 (sourceLit (List.headD (raw_ints% [5863512440926696980544170659947242675]) 0) 29 true) .empty .empty) .empty) (.node 429 (sourceLit (List.headD (raw_ints% [54545930347916264633471835]) 0) 61 false) .empty .empty)))

#time def treeG_J013_part071 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [380542110201003863530035]) 0) 68 false) (.node 433 (sourceLit (List.headD (raw_ints% [3147936681877633626590835]) 0) 65 false) (.node 432 (sourceLit (List.headD (raw_ints% [51468754850665079684729256834180513375]) 0) 23 true) (.node 431 (sourceLit (List.headD (raw_ints% [13071623984139239611588395]) 0) 63 false) .empty .empty) .empty) (.node 434 (sourceLit (List.headD (raw_ints% [141479377365578801430769676296930002705]) 0) 21 true) .empty .empty)) (.node 437 (sourceLit (List.headD (raw_ints% [184603188110843073225105]) 0) 69 false) (.node 436 (sourceLit (List.headD (raw_ints% [206130245146197891310924049139904643655]) 0) 20 true) .empty .empty) (.node 438 (sourceLit (List.headD (raw_ints% [1250435040570308319178081260965781807555]) 0) 17 true) .empty .empty)))

#time def treeG_J013_part072 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [40957956433399330804748753215983732975]) 0) 24 true) treeG_J013_part070 treeG_J013_part071)

#time def treeG_J013_part073 : IntSourceTree :=
  (.node 458 (sourceLit (List.headD (raw_ints% [5480505795620404310846132473425]) 0) 52 false) (.node 456 (sourceLit (List.headD (raw_ints% [3443080135309023541215841182225]) 0) 49 true) (.node 455 (sourceLit (List.headD (raw_ints% [409697812866809908068313844509425]) 0) 41 false) (.node 454 (sourceLit (List.headD (raw_ints% [936802437153656728465289504025]) 0) 49 false) .empty .empty) .empty) (.node 457 (sourceLit (List.headD (raw_ints% [11523960617271954913551612308065875]) 0) 40 true) .empty .empty)) (.node 460 (sourceLit (List.headD (raw_ints% [2477869964605874341307405375775]) 0) 55 true) (.node 459 (sourceLit (List.headD (raw_ints% [285218997856367071157169078314342475]) 0) 38 false) .empty .empty) (.node 461 (sourceLit (List.headD (raw_ints% [1308045319530658244432315595220087575]) 0) 37 true) .empty .empty)))

#time def treeG_J013_part074 : IntSourceTree :=
  (.node 467 (sourceLit (List.headD (raw_ints% [2570700631694995266532673230424052225]) 0) 31 true) (.node 465 (sourceLit (List.headD (raw_ints% [3989787198637352605230348490136694525]) 0) 33 true) (.node 464 (sourceLit (List.headD (raw_ints% [225206103089430999659936723625]) 0) 58 true) (.node 463 (sourceLit (List.headD (raw_ints% [9361023804843162993209824779190522275]) 0) 34 false) .empty .empty) .empty) (.node 466 (sourceLit (List.headD (raw_ints% [18219217388293447913260575]) 0) 63 false) .empty .empty)) (.node 469 (sourceLit (List.headD (raw_ints% [1960202830330431241600085297787189375]) 0) 30 true) (.node 468 (sourceLit (List.headD (raw_ints% [68176780428526171100806275]) 0) 61 false) .empty .empty) (.node 470 (sourceLit (List.headD (raw_ints% [8052932467810681841905965]) 0) 64 false) .empty .empty)))

#time def treeG_J013_part075 : IntSourceTree :=
  (.node 462 (sourceLit (List.headD (raw_ints% [452373614321027082554183066325]) 0) 58 false) treeG_J013_part073 treeG_J013_part074)

#time def treeG_J013_part076 : IntSourceTree :=
  (.node 439 (sourceLit (List.headD (raw_ints% [44896213772725452268959]) 0) 71 false) treeG_J013_part072 treeG_J013_part075)

#time def treeG_J013_part077 : IntSourceTree :=
  (.node 420 (sourceLit (List.headD (raw_ints% [2102767226339638216411204275203521425]) 0) 35 true) treeG_J013_part069 treeG_J013_part076)

#time def treeG_J013_part078 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [220921409976372600476355]) 0) 69 false) (.node 474 (sourceLit (List.headD (raw_ints% [918138254202650442940785]) 0) 67 false) (.node 473 (sourceLit (List.headD (raw_ints% [19825516537015114119838549104768765825]) 0) 25 true) (.node 472 (sourceLit (List.headD (raw_ints% [7667957826575401622212395]) 0) 64 false) .empty .empty) .empty) (.node 475 (sourceLit (List.headD (raw_ints% [53254084364715469464831327524536214715]) 0) 23 true) .empty .empty)) (.node 479 (sourceLit (List.headD (raw_ints% [456630264273115223881799311175559692505]) 0) 19 true) (.node 478 (sourceLit (List.headD (raw_ints% [26682333228380700879435]) 0) 72 false) (.node 477 (sourceLit (List.headD (raw_ints% [76254412015967505767039133350719404465]) 0) 22 true) .empty .empty) .empty) (.node 495 (sourceLit (List.headD (raw_ints% [4190469123446123186284469278425]) 0) 48 false) .empty .empty)))

#time def treeG_J013_part079 : IntSourceTree :=
  (.node 501 (sourceLit (List.headD (raw_ints% [6541115538066048152489991525525]) 0) 55 true) (.node 499 (sourceLit (List.headD (raw_ints% [2268461355151853147248262274975]) 0) 55 false) (.node 498 (sourceLit (List.headD (raw_ints% [735562089183231862472394759379370625]) 0) 36 true) (.node 497 (sourceLit (List.headD (raw_ints% [4750039869204300611712614367525]) 0) 51 true) .empty .empty) .empty) (.node 500 (sourceLit (List.headD (raw_ints% [6666271192041511354925909528233001025]) 0) 35 false) .empty .empty)) (.node 503 (sourceLit (List.headD (raw_ints% [2034294767306336942815488569775]) 0) 57 false) (.node 502 (sourceLit (List.headD (raw_ints% [101325287485415689722001211823930647025]) 0) 32 true) .empty .empty) (.node 504 (sourceLit (List.headD (raw_ints% [158178100162422402602577841610678789475]) 0) 31 false) .empty .empty)))

#time def treeG_J013_part080 : IntSourceTree :=
  (.node 496 (sourceLit (List.headD (raw_ints% [16041385278717165075932748990856125]) 0) 38 false) treeG_J013_part078 treeG_J013_part079)

#time def treeG_J013_part081 : IntSourceTree :=
  (.node 510 (sourceLit (List.headD (raw_ints% [209948005848895868120062164900776507025]) 0) 24 true) (.node 508 (sourceLit (List.headD (raw_ints% [36397496813826481993604680299836090775]) 0) 28 true) (.node 507 (sourceLit (List.headD (raw_ints% [88494486110831719076401125]) 0) 61 false) (.node 506 (sourceLit (List.headD (raw_ints% [121809677915468586386826981024426982125]) 0) 29 true) .empty .empty) .empty) (.node 509 (sourceLit (List.headD (raw_ints% [81807630509136077568140715]) 0) 61 false) .empty .empty)) (.node 512 (sourceLit (List.headD (raw_ints% [208851809234187916428705866487550016625]) 0) 23 true) (.node 511 (sourceLit (List.headD (raw_ints% [19140105887103487756035465]) 0) 63 false) .empty .empty) (.node 513 (sourceLit (List.headD (raw_ints% [565002643087220999452695]) 0) 68 false) .empty .empty)))

#time def treeG_J013_part082 : IntSourceTree :=
  (.node 519 (sourceLit (List.headD (raw_ints% [61833119140797351248781]) 0) 71 false) (.node 517 (sourceLit (List.headD (raw_ints% [257239631841902127727605]) 0) 69 false) (.node 516 (sourceLit (List.headD (raw_ints% [645935104689249620126377191252674791785]) 0) 20 true) (.node 515 (sourceLit (List.headD (raw_ints% [268798072000823289705375]) 0) 69 false) .empty .empty) .empty) (.node 518 (sourceLit (List.headD (raw_ints% [3629847328451612049912423273480260078205]) 0) 17 true) .empty .empty)) (.node 538 (sourceLit (List.headD (raw_ints% [5115272832412352461279373420475]) 0) 53 true) (.node 537 (sourceLit (List.headD (raw_ints% [39089306513261074903035973606987875]) 0) 39 false) .empty .empty) (.node 539 (sourceLit (List.headD (raw_ints% [1306000084895966004786732916008055575]) 0) 37 true) .empty .empty)))

#time def treeG_J013_part083 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [492937151818904850404063895055670503695]) 0) 21 true) treeG_J013_part081 treeG_J013_part082)

#time def treeG_J013_part084 : IntSourceTree :=
  (.node 505 (sourceLit (List.headD (raw_ints% [225448503443892710825205752325]) 0) 59 true) treeG_J013_part080 treeG_J013_part083)

#time def treeG_J013_part085 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [166157674559697107813038538590952178525]) 0) 32 false) (.node 543 (sourceLit (List.headD (raw_ints% [120047335095102015708420861382311691575]) 0) 33 true) (.node 542 (sourceLit (List.headD (raw_ints% [8350609995350156482706723790825]) 0) 56 true) (.node 541 (sourceLit (List.headD (raw_ints% [9282361831102827843790540718673176175]) 0) 36 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [282437608799470992809428161675]) 0) 61 false) .empty .empty)) (.node 548 (sourceLit (List.headD (raw_ints% [108812191793137267051995975]) 0) 61 false) (.node 547 (sourceLit (List.headD (raw_ints% [116668276652078595853761634563578877675]) 0) 30 true) (.node 546 (sourceLit (List.headD (raw_ints% [225594257182999058408511836925]) 0) 60 true) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [32477091153165619510404509704261712025]) 0) 29 true) .empty .empty)))

#time def treeG_J013_part086 : IntSourceTree :=
  (.node 555 (sourceLit (List.headD (raw_ints% [386428983089473911474401240006598074265]) 0) 22 true) (.node 553 (sourceLit (List.headD (raw_ints% [169200776160157688189028768278012484975]) 0) 24 true) (.node 552 (sourceLit (List.headD (raw_ints% [5736074030264043066911535]) 0) 65 false) (.node 551 (sourceLit (List.headD (raw_ints% [177407935338289243605882774485560190775]) 0) 25 true) .empty .empty) .empty) (.node 554 (sourceLit (List.headD (raw_ints% [1341872318146233554869995]) 0) 67 false) .empty .empty)) (.node 557 (sourceLit (List.headD (raw_ints% [493426280657314608592298924551235982855]) 0) 21 true) (.node 556 (sourceLit (List.headD (raw_ints% [316674734025273978934395]) 0) 69 false) .empty .empty) (.node 558 (sourceLit (List.headD (raw_ints% [150510298928379324209865]) 0) 70 false) .empty .empty)))

#time def treeG_J013_part087 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [49595900637893350200516855]) 0) 62 false) treeG_J013_part085 treeG_J013_part086)

#time def treeG_J013_part088 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [1118556780923238528269944732669172322075]) 0) 31 true) (.node 582 (sourceLit (List.headD (raw_ints% [398360866080706180723298514821472284625]) 0) 32 false) (.node 581 (sourceLit (List.headD (raw_ints% [20570700887885209424097851376975]) 0) 55 false) (.node 580 (sourceLit (List.headD (raw_ints% [17114271871209239393219772856297445625]) 0) 35 true) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [1298113095332061678190276545075]) 0) 60 true) .empty .empty)) (.node 586 (sourceLit (List.headD (raw_ints% [2780332470870622311395443598479661838525]) 0) 29 false) (.node 585 (sourceLit (List.headD (raw_ints% [2484949373839660653300631045725]) 0) 59 false) .empty .empty) (.node 587 (sourceLit (List.headD (raw_ints% [112841375834554945063794119025]) 0) 62 true) .empty .empty)))

#time def treeG_J013_part089 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [3476063457915159069100755]) 0) 66 false) (.node 591 (sourceLit (List.headD (raw_ints% [15227897375394931222240695]) 0) 64 false) (.node 590 (sourceLit (List.headD (raw_ints% [1868585827953703780545826456171973062575]) 0) 24 true) (.node 589 (sourceLit (List.headD (raw_ints% [135816753077138456535851235]) 0) 61 false) .empty .empty) .empty) (.node 592 (sourceLit (List.headD (raw_ints% [1210411673472126032418356329396931509575]) 0) 23 true) .empty .empty)) (.node 595 (sourceLit (List.headD (raw_ints% [804276174144586975459245]) 0) 68 false) (.node 594 (sourceLit (List.headD (raw_ints% [2214275266743618160620396397392529255905]) 0) 21 true) .empty .empty) (.node 596 (sourceLit (List.headD (raw_ints% [2445496760026541671668832728800109802335]) 0) 20 true) .empty .empty)))

#time def treeG_J013_part090 : IntSourceTree :=
  (.node 588 (sourceLit (List.headD (raw_ints% [896948716402802284836488396208794930625]) 0) 28 true) treeG_J013_part088 treeG_J013_part089)

#time def treeG_J013_part091 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [2716586799905381602148824651129140693195]) 0) 18 true) treeG_J013_part087 treeG_J013_part090)

#time def treeG_J013_part092 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [7014792674909580635803929925725]) 0) 55 false) treeG_J013_part084 treeG_J013_part091)

#time def treeG_J013_part093 : IntSourceTree :=
  (.node 471 (sourceLit (List.headD (raw_ints% [16270035255303312257089695207608158125]) 0) 26 true) treeG_J013_part077 treeG_J013_part092)

#time def treeG_J013_part094 : IntSourceTree :=
  (.node 623 (sourceLit (List.headD (raw_ints% [64801025146976024553964922025472997025]) 0) 36 false) (.node 621 (sourceLit (List.headD (raw_ints% [3299579212789008404626289196871327725]) 0) 39 true) (.node 599 (sourceLit (List.headD (raw_ints% [22169294946895493240271]) 0) 73 false) (.node 598 (sourceLit (List.headD (raw_ints% [12159793652582455425041142312159291373155]) 0) 17 true) .empty .empty) .empty) (.node 622 (sourceLit (List.headD (raw_ints% [3615163860404420738350571895975]) 0) 59 false) .empty .empty)) (.node 626 (sourceLit (List.headD (raw_ints% [1355271815511329855854571441325]) 0) 61 false) (.node 625 (sourceLit (List.headD (raw_ints% [160589306935366954510372908907515562575]) 0) 35 true) (.node 624 (sourceLit (List.headD (raw_ints% [790275352065766335499852353375]) 0) 62 true) .empty .empty) .empty) (.node 627 (sourceLit (List.headD (raw_ints% [362125093440337613406150654130405089525]) 0) 33 false) .empty .empty)))

#time def treeG_J013_part095 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [130151362163996043028665945139864878075]) 0) 27 true) (.node 631 (sourceLit (List.headD (raw_ints% [211397236576926817117492960210801608975]) 0) 28 true) (.node 630 (sourceLit (List.headD (raw_ints% [21555213109811276583833595]) 0) 64 false) (.node 629 (sourceLit (List.headD (raw_ints% [108058953156204583165760485813066652325]) 0) 32 true) .empty .empty) .empty) (.node 632 (sourceLit (List.headD (raw_ints% [1186477918141361019416145]) 0) 68 false) .empty .empty)) (.node 635 (sourceLit (List.headD (raw_ints% [228480785456768031143249394673241397705]) 0) 25 true) (.node 634 (sourceLit (List.headD (raw_ints% [266773892471115689278845]) 0) 70 false) .empty .empty) (.node 636 (sourceLit (List.headD (raw_ints% [243800720059656498262425]) 0) 70 false) .empty .empty)))

#time def treeG_J013_part096 : IntSourceTree :=
  (.node 628 (sourceLit (List.headD (raw_ints% [451474315530012917522228472075]) 0) 61 true) treeG_J013_part094 treeG_J013_part095)

#time def treeG_J013_part097 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [15129355006891922021298268699725]) 0) 59 true) (.node 663 (sourceLit (List.headD (raw_ints% [2456638477868241208270424220525]) 0) 61 false) (.node 639 (sourceLit (List.headD (raw_ints% [1180400856584634227861539707628768834995]) 0) 21 true) (.node 638 (sourceLit (List.headD (raw_ints% [28199942160033313241415]) 0) 73 false) .empty .empty) .empty) (.node 664 (sourceLit (List.headD (raw_ints% [5265822390329704099723699742299444131675]) 0) 31 false) .empty .empty)) (.node 667 (sourceLit (List.headD (raw_ints% [734056595672942400459182780175]) 0) 63 false) (.node 666 (sourceLit (List.headD (raw_ints% [23335763758597592488723175938641653848125]) 0) 29 true) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [24072954696584409542830130260554720660225]) 0) 28 false) .empty .empty)))

#time def treeG_J013_part098 : IntSourceTree :=
  (.node 674 (sourceLit (List.headD (raw_ints% [14445099090247875347048844580510175137695]) 0) 21 true) (.node 672 (sourceLit (List.headD (raw_ints% [12319011467451190263101193124094371464825]) 0) 23 true) (.node 671 (sourceLit (List.headD (raw_ints% [27882528844227621945426495]) 0) 64 false) (.node 670 (sourceLit (List.headD (raw_ints% [53457598188023042800323542280118152927825]) 0) 24 true) .empty .empty) .empty) (.node 673 (sourceLit (List.headD (raw_ints% [6015759887215729086228405]) 0) 66 false) .empty .empty)) (.node 676 (sourceLit (List.headD (raw_ints% [12177273509206612321499128530287339650785]) 0) 20 true) (.node 675 (sourceLit (List.headD (raw_ints% [1329914965624338538771515]) 0) 68 false) .empty .empty) (.node 677 (sourceLit (List.headD (raw_ints% [599093044029980162908515]) 0) 69 false) .empty .empty)))

#time def treeG_J013_part099 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [903084447813102973500992795385]) 0) 61 true) treeG_J013_part097 treeG_J013_part098)

#time def treeG_J013_part100 : IntSourceTree :=
  (.node 637 (sourceLit (List.headD (raw_ints% [244008809921153382884566725531109227435]) 0) 24 true) treeG_J013_part096 treeG_J013_part099)

#time def treeG_J013_part101 : IntSourceTree :=
  (.node 707 (sourceLit (List.headD (raw_ints% [26232764506120293395972381171684894564325]) 0) 30 true) (.node 705 (sourceLit (List.headD (raw_ints% [6550536845812639735806683013559568632275]) 0) 32 false) (.node 704 (sourceLit (List.headD (raw_ints% [811728457483501885942569143475]) 0) 64 false) (.node 679 (sourceLit (List.headD (raw_ints% [34230589373171133242559]) 0) 73 false) .empty .empty) .empty) (.node 706 (sourceLit (List.headD (raw_ints% [17839898637914581733007411582375]) 0) 60 true) .empty .empty)) (.node 710 (sourceLit (List.headD (raw_ints% [903170668665542218607328129765]) 0) 62 true) (.node 709 (sourceLit (List.headD (raw_ints% [24937426321834046208156214147059253878825]) 0) 29 false) (.node 708 (sourceLit (List.headD (raw_ints% [6323927080913552121195690713475]) 0) 61 false) .empty .empty) .empty) (.node 711 (sourceLit (List.headD (raw_ints% [51766420295407628263383598598431740056025]) 0) 25 true) .empty .empty)))

#time def treeG_J013_part102 : IntSourceTree :=
  (.node 717 (sourceLit (List.headD (raw_ints% [10225203029837385258422594726038465831305]) 0) 21 true) (.node 715 (sourceLit (List.headD (raw_ints% [12617252806593731097902849423124243956055]) 0) 22 true) (.node 714 (sourceLit (List.headD (raw_ints% [3881568747446803571997645]) 0) 67 false) (.node 713 (sourceLit (List.headD (raw_ints% [11277800570139221918871865562975452440225]) 0) 24 true) .empty .empty) .empty) (.node 716 (sourceLit (List.headD (raw_ints% [842313525505025542246665]) 0) 69 false) .empty .empty)) (.node 719 (sourceLit (List.headD (raw_ints% [40863254834555736770515621762774520170245]) 0) 18 true) (.node 718 (sourceLit (List.headD (raw_ints% [373493506749713656977195]) 0) 70 false) .empty .empty) (.node 745 (sourceLit (List.headD (raw_ints% [67079976285836042721622693882125]) 0) 59 false) .empty .empty)))

#time def treeG_J013_part103 : IntSourceTree :=
  (.node 712 (sourceLit (List.headD (raw_ints% [18390705499096733790097335]) 0) 65 false) treeG_J013_part101 treeG_J013_part102)

#time def treeG_J013_part104 : IntSourceTree :=
  (.node 751 (sourceLit (List.headD (raw_ints% [903226433723230673851218982755]) 0) 63 true) (.node 749 (sourceLit (List.headD (raw_ints% [13550938609640207215892374222335]) 0) 61 false) (.node 748 (sourceLit (List.headD (raw_ints% [233935070745546756710609179634033877174825]) 0) 28 true) (.node 747 (sourceLit (List.headD (raw_ints% [20776125020606351334844142703075]) 0) 61 true) .empty .empty) .empty) (.node 750 (sourceLit (List.headD (raw_ints% [1649452882785402000122321247691910401172625]) 0) 24 false) .empty .empty)) (.node 753 (sourceLit (List.headD (raw_ints% [6187472805940502351934465]) 0) 67 false) (.node 752 (sourceLit (List.headD (raw_ints% [401812350895809835843967595663359548983375]) 0) 23 true) .empty .empty) (.node 754 (sourceLit (List.headD (raw_ints% [165999710031979675354901004427097063905905]) 0) 21 true) .empty .empty)))

#time def treeG_J013_part105 : IntSourceTree :=
  (.node 786 (sourceLit (List.headD (raw_ints% [21229968730937656113657526366125]) 0) 62 false) (.node 758 (sourceLit (List.headD (raw_ints% [276900035267563517676115091809426235751555]) 0) 17 true) (.node 757 (sourceLit (List.headD (raw_ints% [1085534006980070921584815]) 0) 69 false) (.node 756 (sourceLit (List.headD (raw_ints% [88760748943543236461723666854706611997655]) 0) 20 true) .empty .empty) .empty) (.node 759 (sourceLit (List.headD (raw_ints% [236571149257029124006959]) 0) 71 false) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [47876177122126254790883976119625]) 0) 61 true) (.node 787 (sourceLit (List.headD (raw_ints% [77188558898860060828801242663639823264425]) 0) 31 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [129436248533690401459382696890546565526825]) 0) 30 true) .empty .empty)))

#time def treeG_J013_part106 : IntSourceTree :=
  (.node 755 (sourceLit (List.headD (raw_ints% [1275826890911232516613065]) 0) 69 false) treeG_J013_part104 treeG_J013_part105)

#time def treeG_J013_part107 : IntSourceTree :=
  (.node 746 (sourceLit (List.headD (raw_ints% [128144353291599828261630104155594751964525]) 0) 29 false) treeG_J013_part103 treeG_J013_part106)

#time def treeG_J013_part108 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [50306461687232810593407939423804670850205]) 0) 17 true) treeG_J013_part100 treeG_J013_part107)

#time def treeG_J013_part109 : IntSourceTree :=
  (.node 795 (sourceLit (List.headD (raw_ints% [76691228612692972128499077501986409974925]) 0) 23 true) (.node 793 (sourceLit (List.headD (raw_ints% [195267275162835306962547865050192048271575]) 0) 25 true) (.node 792 (sourceLit (List.headD (raw_ints% [903263215134228867318799177425]) 0) 64 true) (.node 791 (sourceLit (List.headD (raw_ints% [850609651540404814192852423145171070614325]) 0) 26 false) .empty .empty) .empty) (.node 794 (sourceLit (List.headD (raw_ints% [8493376864434201131871285]) 0) 67 false) .empty .empty)) (.node 798 (sourceLit (List.headD (raw_ints% [178010125057589316151905]) 0) 72 false) (.node 797 (sourceLit (List.headD (raw_ints% [39267772956852925601650536064334073083175]) 0) 22 true) (.node 796 (sourceLit (List.headD (raw_ints% [1709340256317439490979465]) 0) 69 false) .empty .empty) .empty) (.node 799 (sourceLit (List.headD (raw_ints% [118018390216503890452799735023325857790655]) 0) 19 true) .empty .empty)))

#time def treeG_J013_part110 : IntSourceTree :=
  (.node 832 (sourceLit (List.headD (raw_ints% [14011566775542286862929606365986096678812575]) 0) 23 false) (.node 830 (sourceLit (List.headD (raw_ints% [18217292695097773386923306449681870788606225]) 0) 24 true) (.node 829 (sourceLit (List.headD (raw_ints% [109303292853892716797660326461585]) 0) 61 true) (.node 828 (sourceLit (List.headD (raw_ints% [1468952013127307729971429062252271049405625]) 0) 28 false) .empty .empty) .empty) (.node 831 (sourceLit (List.headD (raw_ints% [15357335712028980108350921334855]) 0) 63 false) .empty .empty)) (.node 834 (sourceLit (List.headD (raw_ints% [6082553095178750147446630677179048480784495]) 0) 21 true) (.node 833 (sourceLit (List.headD (raw_ints% [903287965025452629328206915285]) 0) 65 true) .empty .empty) (.node 835 (sourceLit (List.headD (raw_ints% [5941723082611736098645155]) 0) 68 false) .empty .empty)))

#time def treeG_J013_part111 : IntSourceTree :=
  (.node 827 (sourceLit (List.headD (raw_ints% [105695999944356975789474248167575]) 0) 61 false) treeG_J013_part109 treeG_J013_part110)

#time def treeG_J013_part112 : IntSourceTree :=
  (.node 869 (sourceLit (List.headD (raw_ints% [1727824510194688532890194456033364180459275]) 0) 29 false) (.node 839 (sourceLit (List.headD (raw_ints% [475469350973328140600661]) 0) 71 false) (.node 838 (sourceLit (List.headD (raw_ints% [2236237433971023720829519216307954441571645]) 0) 17 true) (.node 837 (sourceLit (List.headD (raw_ints% [2333146505654808060374115]) 0) 69 false) .empty .empty) .empty) (.node 868 (sourceLit (List.headD (raw_ints% [259268177010840206369832472454775]) 0) 61 false) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [19918511998178583015309011295972212929834875]) 0) 25 true) (.node 870 (sourceLit (List.headD (raw_ints% [123757402132198466232160028813685]) 0) 62 true) .empty .empty) (.node 872 (sourceLit (List.headD (raw_ints% [2032574865895401121958715064035]) 0) 67 false) .empty .empty)))

#time def treeG_J013_part113 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [1621106005424450795766495]) 0) 70 false) (.node 876 (sourceLit (List.headD (raw_ints% [2116191413147148303832845]) 0) 70 false) (.node 875 (sourceLit (List.headD (raw_ints% [5929170637953364203189632522175075660834645]) 0) 22 true) (.node 874 (sourceLit (List.headD (raw_ints% [903304951779181497730470657855]) 0) 66 true) .empty .empty) .empty) (.node 877 (sourceLit (List.headD (raw_ints% [1059763362945838466390960501048407801434795]) 0) 21 true) .empty .empty)) (.node 909 (sourceLit (List.headD (raw_ints% [627839646875573129537325271371135]) 0) 61 false) (.node 879 (sourceLit (List.headD (raw_ints% [2000200653538015939923919746261302725990335]) 0) 18 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [128798061347557839491895751635817178337999825]) 0) 24 false) .empty .empty)))

#time def treeG_J013_part114 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [14402101325867957476854702096086480775355725]) 0) 24 false) treeG_J013_part112 treeG_J013_part113)

#time def treeG_J013_part115 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [1138298908859544317594261573177075947601145]) 0) 20 true) treeG_J013_part111 treeG_J013_part114)

#time def treeG_J013_part116 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [46295066194767369307922798604223529339076015]) 0) 20 true) (.node 914 (sourceLit (List.headD (raw_ints% [236516174309066069777121864214562740886476095]) 0) 21 false) (.node 913 (sourceLit (List.headD (raw_ints% [17163886892188661604997927427565]) 0) 65 false) (.node 912 (sourceLit (List.headD (raw_ints% [173359662760970950985401696733763800117491575]) 0) 23 true) .empty .empty) .empty) (.node 915 (sourceLit (List.headD (raw_ints% [903316835225346721202667948165]) 0) 67 true) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [572818327225561327582917]) 0) 72 false) (.node 918 (sourceLit (List.headD (raw_ints% [31676190180295807203681216817241095204341795]) 0) 17 true) (.node 917 (sourceLit (List.headD (raw_ints% [6131619146933785154957265]) 0) 69 false) .empty .empty) .empty) (.node 950 (sourceLit (List.headD (raw_ints% [187899262251942898942371325046205]) 0) 64 false) .empty .empty)))

#time def treeG_J013_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [903325299990999309795883279545]) 0) 68 true) (.node 954 (sourceLit (List.headD (raw_ints% [4516797960991960775682099521355]) 0) 68 false) (.node 953 (sourceLit (List.headD (raw_ints% [46940441021709727115564099707462570223211825]) 0) 26 true) (.node 952 (sourceLit (List.headD (raw_ints% [38843834192847663829045167665205]) 0) 66 true) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [60611336236754858495077874184184454136827685]) 0) 24 false) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [2255256570754667179595385]) 0) 71 false) (.node 957 (sourceLit (List.headD (raw_ints% [11308825707955382710382959525793780384410305]) 0) 23 true) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [7418997381689447815939324267744948119587865]) 0) 20 true) .empty .empty)))

#time def treeG_J013_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [37179143336434105626801190732947347816958675]) 0) 27 false) treeG_J013_part116 treeG_J013_part117)

#time def treeG_J013_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [1415853500437993179725337602484362794000177245]) 0) 17 true) (.node 996 (sourceLit (List.headD (raw_ints% [1985857825770922841150414772498126061717561935]) 0) 20 false) (.node 995 (sourceLit (List.headD (raw_ints% [18970508679193189823931066033585]) 0) 67 false) (.node 994 (sourceLit (List.headD (raw_ints% [3240704399698488605173224245492167235172032895]) 0) 21 true) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [451665715805073121790519118405]) 0) 70 true) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [190606415507547160023906996173805]) 0) 66 true) (.node 999 (sourceLit (List.headD (raw_ints% [420609560882276463003117]) 0) 74 false) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [3483149744645508039153535742228905051719343635]) 0) 22 true) .empty .empty)))

#time def treeG_J013_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [29851055782934987154378700710329366475472311015]) 0) 20 true) (.node 1039 (sourceLit (List.headD (raw_ints% [1386177510911235388461580305413383001521825785]) 0) 18 true) (.node 1038 (sourceLit (List.headD (raw_ints% [225833985530821938228849356895]) 0) 72 true) (.node 1037 (sourceLit (List.headD (raw_ints% [2031093128602744371991946610601301183255203155]) 0) 21 false) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [104788462093370174923919031103695]) 0) 68 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [66410833615725813083467629141726000658166678205]) 0) 17 false) (.node 1077 (sourceLit (List.headD (raw_ints% [5194291352698583844326996887485]) 0) 71 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [225834826749943702781775363129]) 0) 73 true) .empty .empty)))

#time def treeG_J013_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [9936916989592094566863474656565]) 0) 69 false) treeG_J013_part119 treeG_J013_part120)

#time def treeG_J013_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [172539223663579316921178598088385]) 0) 65 true) treeG_J013_part118 treeG_J013_part121)

#time def treeG_J013_part123 : IntSourceTree :=
  (.node 911 (sourceLit (List.headD (raw_ints% [34778684461056861585127737537135]) 0) 65 true) treeG_J013_part115 treeG_J013_part122)

#time def treeG_J013_part124 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [3613527319576437358624925588025]) 0) 64 false) treeG_J013_part108 treeG_J013_part123)

#time def treeG_J013_part125 : IntSourceTree :=
  (.node 597 (sourceLit (List.headD (raw_ints% [376109836208645830141185]) 0) 69 false) treeG_J013_part093 treeG_J013_part124)

#time def treeG_J013_part126 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [465450435086103833680983777065124903645]) 0) 17 true) treeG_J013_part062 treeG_J013_part125)

#time def treeG_J013 : IntSourceTree := treeG_J013_part126

#time def treeG_J014_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [1099176638256514785833312057325]) 0) 43 false) (.node 5 (sourceLit (List.headD (raw_ints% [2301222637056327918278815931175]) 0) 42 false) (.node 4 (sourceLit (List.headD (raw_ints% [7408763836469294839075345384575]) 0) 38 false) (.node 3 (sourceLit (List.headD (raw_ints% [9788163008115153653366762687625]) 0) 40 false) .empty .empty) .empty) (.node 6 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 39 false) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [352798277927109278051206923075]) 0) 43 true) (.node 9 (sourceLit (List.headD (raw_ints% [132402150923693691762807260175]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [191276174779758042316919416125]) 0) 42 true) .empty .empty) .empty) (.node 11 (sourceLit (List.headD (raw_ints% [64155049557054303237609594375]) 0) 47 false) .empty .empty)))

#time def treeG_J014_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [55340032485911089962860918401275]) 0) 38 true) (.node 15 (sourceLit (List.headD (raw_ints% [70254520979693746577148018049275]) 0) 39 true) (.node 14 (sourceLit (List.headD (raw_ints% [332605538004749946777346173525]) 0) 46 true) (.node 13 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 49 false) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 50 false) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [137945766175318857438159979395825]) 0) 36 true) (.node 18 (sourceLit (List.headD (raw_ints% [3569835825909221960757290625]) 0) 51 false) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [876300752212663748682737025]) 0) 53 false) .empty .empty)))

#time def treeG_J014_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [207763279407238870206862638525]) 0) 45 true) treeG_J014_part000 treeG_J014_part001)

#time def treeG_J014_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [26106765727873007498902425]) 0) 58 false) (.node 24 (sourceLit (List.headD (raw_ints% [52998438744577727250767775]) 0) 57 false) (.node 23 (sourceLit (List.headD (raw_ints% [1158489289945858963389287109548625]) 0) 32 true) (.node 22 (sourceLit (List.headD (raw_ints% [430772971026794448935893725]) 0) 54 false) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [1775150678523877345109318810883525]) 0) 31 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [6435420268666260706360875]) 0) 60 false) (.node 27 (sourceLit (List.headD (raw_ints% [5516469682442476807295028750400125]) 0) 29 true) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [8606598006497600213923509745314975]) 0) 28 true) .empty .empty)))

#time def treeG_J014_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [489917046215535114146510078122307295]) 0) 21 true) (.node 33 (sourceLit (List.headD (raw_ints% [163925426419055874720697135788656025]) 0) 23 true) (.node 32 (sourceLit (List.headD (raw_ints% [97970342674925511242235]) 0) 66 false) (.node 31 (sourceLit (List.headD (raw_ints% [106954021467427319351860745830489425]) 0) 24 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [48396517715292436008585]) 0) 67 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [700387840332835860361117822506954945]) 0) 20 true) (.node 36 (sourceLit (List.headD (raw_ints% [11960131968114425995725]) 0) 69 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [5914238543588137680225]) 0) 70 false) .empty .empty)))

#time def treeG_J014_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [3175063546818032314931115]) 0) 61 false) treeG_J014_part003 treeG_J014_part004)

#time def treeG_J014_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [194447297093358837898153652358375]) 0) 35 true) treeG_J014_part002 treeG_J014_part005)

#time def treeG_J014_part007 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [1099176638256514785833312057325]) 0) 44 false) (.node 46 (sourceLit (List.headD (raw_ints% [2301222637056327918278815931175]) 0) 43 false) (.node 45 (sourceLit (List.headD (raw_ints% [7408763836469294839075345384575]) 0) 39 false) (.node 44 (sourceLit (List.headD (raw_ints% [9788163008115153653366762687625]) 0) 41 false) .empty .empty) .empty) (.node 47 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 40 false) .empty .empty)) (.node 51 (sourceLit (List.headD (raw_ints% [352798277927109278051206923075]) 0) 44 true) (.node 50 (sourceLit (List.headD (raw_ints% [132402150923693691762807260175]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [191276174779758042316919416125]) 0) 43 true) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [64155049557054303237609594375]) 0) 48 false) .empty .empty)))

#time def treeG_J014_part008 : IntSourceTree :=
  (.node 58 (sourceLit (List.headD (raw_ints% [55340032485911089962860918401275]) 0) 39 true) (.node 56 (sourceLit (List.headD (raw_ints% [70254520979693746577148018049275]) 0) 40 true) (.node 55 (sourceLit (List.headD (raw_ints% [332605538004749946777346173525]) 0) 47 true) (.node 54 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 50 false) .empty .empty) .empty) (.node 57 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 51 false) .empty .empty)) (.node 60 (sourceLit (List.headD (raw_ints% [137945766175318857438159979395825]) 0) 37 true) (.node 59 (sourceLit (List.headD (raw_ints% [3569835825909221960757290625]) 0) 52 false) .empty .empty) (.node 61 (sourceLit (List.headD (raw_ints% [876300752212663748682737025]) 0) 54 false) .empty .empty)))

#time def treeG_J014_part009 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [207763279407238870206862638525]) 0) 46 true) treeG_J014_part007 treeG_J014_part008)

#time def treeG_J014_part010 : IntSourceTree :=
  (.node 67 (sourceLit (List.headD (raw_ints% [26106765727873007498902425]) 0) 59 false) (.node 65 (sourceLit (List.headD (raw_ints% [52998438744577727250767775]) 0) 58 false) (.node 64 (sourceLit (List.headD (raw_ints% [1158489289945858963389287109548625]) 0) 33 true) (.node 63 (sourceLit (List.headD (raw_ints% [430772971026794448935893725]) 0) 55 false) .empty .empty) .empty) (.node 66 (sourceLit (List.headD (raw_ints% [1775150678523877345109318810883525]) 0) 32 true) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [6435420268666260706360875]) 0) 61 false) (.node 68 (sourceLit (List.headD (raw_ints% [5516469682442476807295028750400125]) 0) 30 true) .empty .empty) (.node 70 (sourceLit (List.headD (raw_ints% [8606598006497600213923509745314975]) 0) 29 true) .empty .empty)))

#time def treeG_J014_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [489917046215535114146510078122307295]) 0) 22 true) (.node 74 (sourceLit (List.headD (raw_ints% [163925426419055874720697135788656025]) 0) 24 true) (.node 73 (sourceLit (List.headD (raw_ints% [97970342674925511242235]) 0) 67 false) (.node 72 (sourceLit (List.headD (raw_ints% [106954021467427319351860745830489425]) 0) 25 true) .empty .empty) .empty) (.node 75 (sourceLit (List.headD (raw_ints% [48396517715292436008585]) 0) 68 false) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [700387840332835860361117822506954945]) 0) 21 true) (.node 77 (sourceLit (List.headD (raw_ints% [11960131968114425995725]) 0) 70 false) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [5914238543588137680225]) 0) 71 false) .empty .empty)))

#time def treeG_J014_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [3175063546818032314931115]) 0) 62 false) treeG_J014_part010 treeG_J014_part011)

#time def treeG_J014_part013 : IntSourceTree :=
  (.node 62 (sourceLit (List.headD (raw_ints% [194447297093358837898153652358375]) 0) 36 true) treeG_J014_part009 treeG_J014_part012)

#time def treeG_J014_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [3693537367468110143998138236558543645]) 0) 17 true) treeG_J014_part006 treeG_J014_part013)

#time def treeG_J014_part015 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 43 true) (.node 88 (sourceLit (List.headD (raw_ints% [1721485573017822380852274745125]) 0) 41 false) (.node 87 (sourceLit (List.headD (raw_ints% [3503268635856141050724319805025]) 0) 43 false) (.node 86 (sourceLit (List.headD (raw_ints% [13478594449480283381932254856275]) 0) 39 false) .empty .empty) .empty) (.node 89 (sourceLit (List.headD (raw_ints% [834372336409127402307697536975]) 0) 45 false) .empty .empty)) (.node 93 (sourceLit (List.headD (raw_ints% [12137441808091354666574788125]) 0) 51 false) (.node 92 (sourceLit (List.headD (raw_ints% [72517499259935203922172142275]) 0) 46 true) (.node 91 (sourceLit (List.headD (raw_ints% [200649252290333080288004925975]) 0) 47 false) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [82921020809727793636379103525]) 0) 46 true) .empty .empty)))

#time def treeG_J014_part016 : IntSourceTree :=
  (.node 100 (sourceLit (List.headD (raw_ints% [10521621381627180515916225]) 0) 61 false) (.node 98 (sourceLit (List.headD (raw_ints% [10995094343800403639132455125]) 0) 51 false) (.node 97 (sourceLit (List.headD (raw_ints% [506696135351638882654323225992925]) 0) 38 true) (.node 96 (sourceLit (List.headD (raw_ints% [361735398344169197977125665025]) 0) 48 true) .empty .empty) .empty) (.node 99 (sourceLit (List.headD (raw_ints% [747494753599258581967614715024575]) 0) 36 true) .empty .empty)) (.node 102 (sourceLit (List.headD (raw_ints% [1321828533398533048429580325]) 0) 54 false) (.node 101 (sourceLit (List.headD (raw_ints% [909118832309192021607126182808225]) 0) 35 true) .empty .empty) (.node 103 (sourceLit (List.headD (raw_ints% [5063824217041623849351629765919375]) 0) 32 true) .empty .empty)))

#time def treeG_J014_part017 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [134173757381619417781235587969275]) 0) 39 false) treeG_J014_part015 treeG_J014_part016)

#time def treeG_J014_part018 : IntSourceTree :=
  (.node 109 (sourceLit (List.headD (raw_ints% [35525159453042214244436720257886025]) 0) 28 true) (.node 107 (sourceLit (List.headD (raw_ints% [22885941173939560714454072223736275]) 0) 29 true) (.node 106 (sourceLit (List.headD (raw_ints% [79890111761282447002633125]) 0) 58 false) (.node 105 (sourceLit (List.headD (raw_ints% [7492763641042994362004978065505475]) 0) 31 true) .empty .empty) .empty) (.node 108 (sourceLit (List.headD (raw_ints% [9835672729603373396270775]) 0) 61 false) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [443868250948419094339243877869668975]) 0) 24 true) (.node 110 (sourceLit (List.headD (raw_ints% [9695776990514489097790635]) 0) 61 false) .empty .empty) (.node 112 (sourceLit (List.headD (raw_ints% [2391300805418628224993235]) 0) 63 false) .empty .empty)))

#time def treeG_J014_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [18006025392640714311225]) 0) 70 false) (.node 116 (sourceLit (List.headD (raw_ints% [9109096436794502503215]) 0) 71 false) (.node 115 (sourceLit (List.headD (raw_ints% [2132889776489358881384644094496189105]) 0) 21 true) (.node 114 (sourceLit (List.headD (raw_ints% [147544167634558586475885]) 0) 67 false) .empty .empty) .empty) (.node 117 (sourceLit (List.headD (raw_ints% [3218948529391445052810962802471503415]) 0) 20 true) .empty .empty)) (.node 126 (sourceLit (List.headD (raw_ints% [5185717734002497816809130825275]) 0) 43 false) (.node 119 (sourceLit (List.headD (raw_ints% [18718873523182637387557632083664014595]) 0) 17 true) .empty .empty) (.node 127 (sourceLit (List.headD (raw_ints% [1517457653252747135714227367925]) 0) 43 false) .empty .empty)))

#time def treeG_J014_part020 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [691706745320362680094188830855259375]) 0) 23 true) treeG_J014_part018 treeG_J014_part019)

#time def treeG_J014_part021 : IntSourceTree :=
  (.node 104 (sourceLit (List.headD (raw_ints% [324776093537638994434358175]) 0) 56 false) treeG_J014_part017 treeG_J014_part020)

#time def treeG_J014_part022 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [62728280887368462362518353975]) 0) 46 false) (.node 131 (sourceLit (List.headD (raw_ints% [80761051573675617867143753475]) 0) 46 false) (.node 130 (sourceLit (List.headD (raw_ints% [569568034561740018782083016625]) 0) 46 false) (.node 129 (sourceLit (List.headD (raw_ints% [2104037922577338465486113577375]) 0) 42 false) .empty .empty) .empty) (.node 132 (sourceLit (List.headD (raw_ints% [8530887670829923565649708225]) 0) 52 false) .empty .empty)) (.node 136 (sourceLit (List.headD (raw_ints% [102214139180656582179191803009275]) 0) 41 false) (.node 135 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 51 false) (.node 134 (sourceLit (List.headD (raw_ints% [32944484907676534094988710625]) 0) 50 false) .empty .empty) .empty) (.node 137 (sourceLit (List.headD (raw_ints% [390865258683588449176905156525]) 0) 49 true) .empty .empty)))

#time def treeG_J014_part023 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [111381945296467324936710825]) 0) 58 false) (.node 141 (sourceLit (List.headD (raw_ints% [1817234321483894463391816575]) 0) 54 false) (.node 140 (sourceLit (List.headD (raw_ints% [304774493711969862264727367814375]) 0) 38 true) (.node 139 (sourceLit (List.headD (raw_ints% [1856314629472795419593791125]) 0) 54 false) .empty .empty) .empty) (.node 142 (sourceLit (List.headD (raw_ints% [357335767607916591854486265224925]) 0) 37 true) .empty .empty)) (.node 145 (sourceLit (List.headD (raw_ints% [218779216048483539932822625]) 0) 57 false) (.node 144 (sourceLit (List.headD (raw_ints% [1952667463547882442981171328185375]) 0) 34 true) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [2858806481259558508447829627310975]) 0) 33 true) .empty .empty)))

#time def treeG_J014_part024 : IntSourceTree :=
  (.node 138 (sourceLit (List.headD (raw_ints% [225678051432863896345731153795825]) 0) 40 true) treeG_J014_part022 treeG_J014_part023)

#time def treeG_J014_part025 : IntSourceTree :=
  (.node 152 (sourceLit (List.headD (raw_ints% [168457114740495887493691566019589775]) 0) 26 true) (.node 150 (sourceLit (List.headD (raw_ints% [13459280723272307015256605256285525]) 0) 30 true) (.node 149 (sourceLit (List.headD (raw_ints% [13235925190540486086180675]) 0) 61 false) (.node 148 (sourceLit (List.headD (raw_ints% [8684735745748541953579521736668075]) 0) 31 true) .empty .empty) .empty) (.node 151 (sourceLit (List.headD (raw_ints% [25471536889439284308045]) 0) 70 false) .empty .empty)) (.node 154 (sourceLit (List.headD (raw_ints% [263890659450653402686745847533301675]) 0) 25 true) (.node 153 (sourceLit (List.headD (raw_ints% [1607538064019224135055355]) 0) 64 false) .empty .empty) (.node 155 (sourceLit (List.headD (raw_ints% [24786912479816537616825]) 0) 70 false) .empty .empty)))

#time def treeG_J014_part026 : IntSourceTree :=
  (.node 168 (sourceLit (List.headD (raw_ints% [10418175653004154704861544198275]) 0) 41 false) (.node 159 (sourceLit (List.headD (raw_ints% [1511473356131572078875]) 0) 74 false) (.node 158 (sourceLit (List.headD (raw_ints% [1259280344529304596224922489982274235]) 0) 22 true) (.node 157 (sourceLit (List.headD (raw_ints% [24476253779063584017135]) 0) 70 false) .empty .empty) .empty) (.node 167 (sourceLit (List.headD (raw_ints% [6868166832148854582893941845525]) 0) 43 false) .empty .empty)) (.node 170 (sourceLit (List.headD (raw_ints% [1066895997104872636034372743275]) 0) 44 false) (.node 169 (sourceLit (List.headD (raw_ints% [1569719661190498862583310210725]) 0) 45 false) .empty .empty) (.node 171 (sourceLit (List.headD (raw_ints% [184459391135703469247039045325]) 0) 48 false) .empty .empty)))

#time def treeG_J014_part027 : IntSourceTree :=
  (.node 156 (sourceLit (List.headD (raw_ints% [821486365136911883619067008186940905]) 0) 23 true) treeG_J014_part025 treeG_J014_part026)

#time def treeG_J014_part028 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [13445836508352359875932675]) 0) 61 false) treeG_J014_part024 treeG_J014_part027)

#time def treeG_J014_part029 : IntSourceTree :=
  (.node 128 (sourceLit (List.headD (raw_ints% [601022999399906566222751936925]) 0) 46 false) treeG_J014_part021 treeG_J014_part028)

#time def treeG_J014_part030 : IntSourceTree :=
  (.node 85 (sourceLit (List.headD (raw_ints% [3743470185529412867543973378225]) 0) 43 false) treeG_J014_part014 treeG_J014_part029)

#time def treeG_J014_part031 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [2142122362242144197521392074141325]) 0) 38 false) (.node 175 (sourceLit (List.headD (raw_ints% [766852800223665871838170750725]) 0) 39 false) (.node 174 (sourceLit (List.headD (raw_ints% [208377582584464718361415811475]) 0) 46 false) (.node 173 (sourceLit (List.headD (raw_ints% [21986108875228339596024044775]) 0) 51 false) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [611419915539191351118092735025]) 0) 48 false) .empty .empty)) (.node 180 (sourceLit (List.headD (raw_ints% [1182930861048655866575152725]) 0) 55 false) (.node 179 (sourceLit (List.headD (raw_ints% [6474202892252386101095782206441825]) 0) 36 true) (.node 178 (sourceLit (List.headD (raw_ints% [412855447371189256455170066775]) 0) 50 true) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [3967273067082325774628511702221775]) 0) 35 true) .empty .empty)))

#time def treeG_J014_part032 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [68595866226366311555876475850214925]) 0) 29 true) (.node 185 (sourceLit (List.headD (raw_ints% [23749915775723124725693763185460525]) 0) 31 true) (.node 184 (sourceLit (List.headD (raw_ints% [566279468834099605059328425]) 0) 56 false) (.node 183 (sourceLit (List.headD (raw_ints% [17805664909865038029335491208475825]) 0) 32 true) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [34722276071800273232547375]) 0) 60 false) .empty .empty)) (.node 189 (sourceLit (List.headD (raw_ints% [103430612478934457012835627528803175]) 0) 28 true) (.node 188 (sourceLit (List.headD (raw_ints% [17056000287101346355594575]) 0) 61 false) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [16776073390566483074570715]) 0) 61 false) .empty .empty)))

#time def treeG_J014_part033 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [2312640109569255878354052825]) 0) 54 false) treeG_J014_part031 treeG_J014_part032)

#time def treeG_J014_part034 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [7838908021511017556805]) 0) 72 false) (.node 194 (sourceLit (List.headD (raw_ints% [1017361393480989789151815]) 0) 65 false) (.node 193 (sourceLit (List.headD (raw_ints% [2003607090527571519804876225458177025]) 0) 23 true) (.node 192 (sourceLit (List.headD (raw_ints% [4129412638277828557866285]) 0) 63 false) .empty .empty) .empty) (.node 195 (sourceLit (List.headD (raw_ints% [6311611325931550004591223026569464495]) 0) 21 true) .empty .empty)) (.node 198 (sourceLit (List.headD (raw_ints% [30946482165486453723045]) 0) 70 false) (.node 197 (sourceLit (List.headD (raw_ints% [9924833312799145085094109328519551065]) 0) 20 true) .empty .empty) (.node 199 (sourceLit (List.headD (raw_ints% [61875068526692856770837407275201536445]) 0) 17 true) .empty .empty)))

#time def treeG_J014_part035 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [405350923927204416950400944475]) 0) 46 false) (.node 211 (sourceLit (List.headD (raw_ints% [905373893957521400300085236325]) 0) 45 false) (.node 210 (sourceLit (List.headD (raw_ints% [250037906657189710950306798525]) 0) 48 false) (.node 209 (sourceLit (List.headD (raw_ints% [2078534432606704059843857655225]) 0) 44 false) .empty .empty) .empty) (.node 212 (sourceLit (List.headD (raw_ints% [116212289769064080721841379525]) 0) 49 false) .empty .empty)) (.node 215 (sourceLit (List.headD (raw_ints% [41306934610557434779551258525]) 0) 47 true) (.node 214 (sourceLit (List.headD (raw_ints% [54999950593236824289107468475]) 0) 50 false) .empty .empty) (.node 216 (sourceLit (List.headD (raw_ints% [203661425561089498486545435267825]) 0) 40 true) .empty .empty)))

#time def treeG_J014_part036 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [4464074834549228318002934097825]) 0) 44 false) treeG_J014_part034 treeG_J014_part035)

#time def treeG_J014_part037 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [1278919681630436203613601594934878225]) 0) 24 true) treeG_J014_part033 treeG_J014_part036)

#time def treeG_J014_part038 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [3252601531866492590919539171771925]) 0) 36 true) (.node 220 (sourceLit (List.headD (raw_ints% [5864653904828446376566327470813075]) 0) 37 true) (.node 219 (sourceLit (List.headD (raw_ints% [427705964406971619811920395775]) 0) 51 true) (.node 218 (sourceLit (List.headD (raw_ints% [2593478465107871990212854381732975]) 0) 39 false) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [2914489122710729002908794325]) 0) 54 false) .empty .empty)) (.node 225 (sourceLit (List.headD (raw_ints% [43437531598202008140813225]) 0) 60 false) (.node 224 (sourceLit (List.headD (raw_ints% [13900329982769273143373148552105075]) 0) 33 true) (.node 223 (sourceLit (List.headD (raw_ints% [1421584547197517278860366225]) 0) 55 false) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [18032302813204007708798103930838575]) 0) 32 true) .empty .empty)))

#time def treeG_J014_part039 : IntSourceTree :=
  (.node 232 (sourceLit (List.headD (raw_ints% [942005452149444428626218462895698675]) 0) 25 true) (.node 230 (sourceLit (List.headD (raw_ints% [76512051032389842982322417016232125]) 0) 29 true) (.node 229 (sourceLit (List.headD (raw_ints% [20876075383662206625008475]) 0) 61 false) (.node 228 (sourceLit (List.headD (raw_ints% [51226394734869227648717432376878775]) 0) 30 true) .empty .empty) .empty) (.node 231 (sourceLit (List.headD (raw_ints% [10255359946870026291711195]) 0) 62 false) .empty .empty)) (.node 234 (sourceLit (List.headD (raw_ints% [1475825771626264714431384530391573675]) 0) 24 true) (.node 233 (sourceLit (List.headD (raw_ints% [1260937287129302211405465]) 0) 65 false) .empty .empty) (.node 235 (sourceLit (List.headD (raw_ints% [620770793803925187282615]) 0) 66 false) .empty .empty)))

#time def treeG_J014_part040 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [5319109890861978339153675]) 0) 63 false) treeG_J014_part038 treeG_J014_part039)

#time def treeG_J014_part041 : IntSourceTree :=
  (.node 250 (sourceLit (List.headD (raw_ints% [3090172868108535483653342567175]) 0) 44 false) (.node 239 (sourceLit (List.headD (raw_ints% [18854695316433877092045]) 0) 71 false) (.node 238 (sourceLit (List.headD (raw_ints% [7406272623740535892644264348555002595]) 0) 21 true) (.node 237 (sourceLit (List.headD (raw_ints% [38235010393024556437305]) 0) 70 false) .empty .empty) .empty) (.node 249 (sourceLit (List.headD (raw_ints% [723588793339682363854905971775]) 0) 47 false) .empty .empty)) (.node 252 (sourceLit (List.headD (raw_ints% [167833572887558740160906396775]) 0) 48 false) (.node 251 (sourceLit (List.headD (raw_ints% [315616422178675952653574551725]) 0) 48 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [72240072018607401529793289975]) 0) 50 false) .empty .empty)))

#time def treeG_J014_part042 : IntSourceTree :=
  (.node 259 (sourceLit (List.headD (raw_ints% [47969858333978337944501452314169425]) 0) 36 false) (.node 257 (sourceLit (List.headD (raw_ints% [3771413766730860185413755556283925]) 0) 38 true) (.node 256 (sourceLit (List.headD (raw_ints% [326363425074874392948821996775]) 0) 49 true) (.node 255 (sourceLit (List.headD (raw_ints% [224512944829674366416346020122875]) 0) 39 false) .empty .empty) .empty) (.node 258 (sourceLit (List.headD (raw_ints% [1415140621593969056750167958325]) 0) 50 false) .empty .empty)) (.node 261 (sourceLit (List.headD (raw_ints% [42949958171545245237902108064282825]) 0) 35 true) (.node 260 (sourceLit (List.headD (raw_ints% [437169411295360866744521617575]) 0) 52 true) .empty .empty) (.node 262 (sourceLit (List.headD (raw_ints% [3516338135852202127463535825]) 0) 54 false) .empty .empty)))

#time def treeG_J014_part043 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [602324265269944115539386077475]) 0) 46 false) treeG_J014_part041 treeG_J014_part042)

#time def treeG_J014_part044 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [4668638595657726237353089010195582685]) 0) 22 true) treeG_J014_part040 treeG_J014_part043)

#time def treeG_J014_part045 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [501142587111389900147498945775]) 0) 50 false) treeG_J014_part037 treeG_J014_part044)

#time def treeG_J014_part046 : IntSourceTree :=
  (.node 268 (sourceLit (List.headD (raw_ints% [25496878839794480357634825]) 0) 61 false) (.node 266 (sourceLit (List.headD (raw_ints% [52152787124603743049079075]) 0) 60 false) (.node 265 (sourceLit (List.headD (raw_ints% [87452724086431060421291425231380075]) 0) 31 true) (.node 264 (sourceLit (List.headD (raw_ints% [106913134795427209225129725]) 0) 59 false) .empty .empty) .empty) (.node 267 (sourceLit (List.headD (raw_ints% [219920978784897811784893187043202275]) 0) 29 true) .empty .empty)) (.node 271 (sourceLit (List.headD (raw_ints% [3617851584442513747255033094103977775]) 0) 24 true) (.node 270 (sourceLit (List.headD (raw_ints% [24976077376757930175446235]) 0) 61 false) (.node 269 (sourceLit (List.headD (raw_ints% [306380545400019364176903831486227025]) 0) 28 true) .empty .empty) .empty) (.node 272 (sourceLit (List.headD (raw_ints% [3062973654296098866922455]) 0) 64 false) .empty .empty)))

#time def treeG_J014_part047 : IntSourceTree :=
  (.node 278 (sourceLit (List.headD (raw_ints% [45523538620562659151565]) 0) 70 false) (.node 276 (sourceLit (List.headD (raw_ints% [369925737115572625464855]) 0) 67 false) (.node 275 (sourceLit (List.headD (raw_ints% [17301601020088685426310929459695714305]) 0) 21 true) (.node 274 (sourceLit (List.headD (raw_ints% [1504513180777614633659115]) 0) 65 false) .empty .empty) .empty) (.node 277 (sourceLit (List.headD (raw_ints% [27424275452462664813730602753045110415]) 0) 20 true) .empty .empty)) (.node 290 (sourceLit (List.headD (raw_ints% [236775443341246326452299586625]) 0) 49 false) (.node 279 (sourceLit (List.headD (raw_ints% [175125655433004291793779051878558546595]) 0) 17 true) .empty .empty) (.node 291 (sourceLit (List.headD (raw_ints% [1092399487075507041676628665425]) 0) 46 false) .empty .empty)))

#time def treeG_J014_part048 : IntSourceTree :=
  (.node 273 (sourceLit (List.headD (raw_ints% [5532436526667983909204871477707412375]) 0) 23 true) treeG_J014_part046 treeG_J014_part047)

#time def treeG_J014_part049 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [413753006093132146548160471275]) 0) 51 true) (.node 295 (sourceLit (List.headD (raw_ints% [10056737498132836723733395875]) 0) 53 false) (.node 294 (sourceLit (List.headD (raw_ints% [89480193443977978770479111475]) 0) 50 false) (.node 293 (sourceLit (List.headD (raw_ints% [937317659173265504336850229725]) 0) 46 false) .empty .empty) .empty) (.node 296 (sourceLit (List.headD (raw_ints% [107043592597690966225722863847675]) 0) 42 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [460711646500235169140522088525]) 0) 53 false) (.node 298 (sourceLit (List.headD (raw_ints% [1591223057959683043906652484504225]) 0) 41 true) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [13458628059701696080266944946245625]) 0) 39 false) .empty .empty)))

#time def treeG_J014_part050 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [17355105318306763178123330325135375]) 0) 34 true) (.node 304 (sourceLit (List.headD (raw_ints% [18094313531773362934179153434030175]) 0) 35 true) (.node 303 (sourceLit (List.headD (raw_ints% [32730524822729450759424525]) 0) 61 false) (.node 302 (sourceLit (List.headD (raw_ints% [9924339159919688161745642223127725]) 0) 38 true) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [15868900799306300271079125]) 0) 62 false) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [42173646012507146034043938666580875]) 0) 32 true) (.node 307 (sourceLit (List.headD (raw_ints% [30876347561155829692464375]) 0) 61 false) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [30117682295926754090261175]) 0) 61 false) .empty .empty)))

#time def treeG_J014_part051 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [442998389540782324750339206225]) 0) 53 true) treeG_J014_part049 treeG_J014_part050)

#time def treeG_J014_part052 : IntSourceTree :=
  (.node 292 (sourceLit (List.headD (raw_ints% [24925516551201483991466646525]) 0) 52 false) treeG_J014_part048 treeG_J014_part051)

#time def treeG_J014_part053 : IntSourceTree :=
  (.node 315 (sourceLit (List.headD (raw_ints% [220935596743422361594125]) 0) 68 false) (.node 313 (sourceLit (List.headD (raw_ints% [901018183583398327758495]) 0) 66 false) (.node 312 (sourceLit (List.headD (raw_ints% [668961533073267329657203657802069775]) 0) 27 true) (.node 311 (sourceLit (List.headD (raw_ints% [3593925153781226534115]) 0) 74 false) .empty .empty) .empty) (.node 314 (sourceLit (List.headD (raw_ints% [1014152688760429798693371736828959675]) 0) 26 true) .empty .empty)) (.node 318 (sourceLit (List.headD (raw_ints% [5004500707180532230271584601122526955]) 0) 23 true) (.node 317 (sourceLit (List.headD (raw_ints% [216985695543474399715635]) 0) 68 false) (.node 316 (sourceLit (List.headD (raw_ints% [3158240606107739797239460112375032905]) 0) 24 true) .empty .empty) .empty) (.node 319 (sourceLit (List.headD (raw_ints% [13021896144594131865]) 0) 82 false) .empty .empty)))

#time def treeG_J014_part054 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [648179025015125168108290664775]) 0) 49 false) (.node 334 (sourceLit (List.headD (raw_ints% [1272311053076586893134314381975]) 0) 46 false) (.node 333 (sourceLit (List.headD (raw_ints% [127164060391004470401939882225]) 0) 50 false) (.node 332 (sourceLit (List.headD (raw_ints% [756732341300389561354815871875]) 0) 47 false) .empty .empty) .empty) (.node 335 (sourceLit (List.headD (raw_ints% [141997927516859434627536420478725]) 0) 39 false) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [3070152645966497642942809843425]) 0) 50 true) (.node 337 (sourceLit (List.headD (raw_ints% [7196808729856971104636887199409525]) 0) 38 false) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [149808134043398052754527211322439825]) 0) 36 true) .empty .empty)))

#time def treeG_J014_part055 : IntSourceTree :=
  (.node 331 (sourceLit (List.headD (raw_ints% [631485351186309353155623794775]) 0) 48 false) treeG_J014_part053 treeG_J014_part054)

#time def treeG_J014_part056 : IntSourceTree :=
  (.node 345 (sourceLit (List.headD (raw_ints% [491565308930316553472441484657585525]) 0) 31 true) (.node 343 (sourceLit (List.headD (raw_ints% [1184037828359857359823352442272123025]) 0) 32 true) (.node 342 (sourceLit (List.headD (raw_ints% [223257363838317263438901371025]) 0) 55 true) (.node 341 (sourceLit (List.headD (raw_ints% [473626056081999519806444346344142825]) 0) 35 false) .empty .empty) .empty) (.node 344 (sourceLit (List.headD (raw_ints% [154931063786408396850266475]) 0) 59 false) .empty .empty)) (.node 347 (sourceLit (List.headD (raw_ints% [890805761586735031614999953765461725]) 0) 29 true) (.node 346 (sourceLit (List.headD (raw_ints% [74798419269846659119553925]) 0) 60 false) .empty .empty) (.node 348 (sourceLit (List.headD (raw_ints% [36255816282517179027293925]) 0) 61 false) .empty .empty)))

#time def treeG_J014_part057 : IntSourceTree :=
  (.node 354 (sourceLit (List.headD (raw_ints% [2099559553555978677374865]) 0) 65 false) (.node 352 (sourceLit (List.headD (raw_ints% [4297385060647853074945065]) 0) 64 false) (.node 351 (sourceLit (List.headD (raw_ints% [11093732055085775609198177431975695825]) 0) 24 true) (.node 350 (sourceLit (List.headD (raw_ints% [35259287215095578005076115]) 0) 61 false) .empty .empty) .empty) (.node 353 (sourceLit (List.headD (raw_ints% [15874332531676570639825645571958820425]) 0) 23 true) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [513816649858116820911645]) 0) 67 false) (.node 355 (sourceLit (List.headD (raw_ints% [47604171060578821690064861697357704895]) 0) 21 true) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [73639423942985008697932120842955942545]) 0) 20 true) .empty .empty)))

#time def treeG_J014_part058 : IntSourceTree :=
  (.node 349 (sourceLit (List.headD (raw_ints% [1043176127000209308912502205844360975]) 0) 28 true) treeG_J014_part056 treeG_J014_part057)

#time def treeG_J014_part059 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [2280015997296301543306609971675]) 0) 52 false) treeG_J014_part055 treeG_J014_part058)

#time def treeG_J014_part060 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [57467123591907380298645353617498725]) 0) 31 true) treeG_J014_part052 treeG_J014_part059)

#time def treeG_J014_part061 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [86277584109862724880089762288225775]) 0) 32 true) treeG_J014_part045 treeG_J014_part060)

#time def treeG_J014_part062 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [234039602407286439656459649225]) 0) 46 false) treeG_J014_part030 treeG_J014_part061)

#time def treeG_J014_part063 : IntSourceTree :=
  (.node 375 (sourceLit (List.headD (raw_ints% [628679853196085342815377045975]) 0) 47 false) (.node 373 (sourceLit (List.headD (raw_ints% [2089611706028292741082413257775]) 0) 46 false) (.node 372 (sourceLit (List.headD (raw_ints% [432081218776697481223890622575]) 0) 49 false) (.node 359 (sourceLit (List.headD (raw_ints% [465450435086103833680983777065124903645]) 0) 17 true) .empty .empty) .empty) (.node 374 (sourceLit (List.headD (raw_ints% [164847927338030962033400652975]) 0) 50 false) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [13561700961695703280263497137426425]) 0) 39 false) (.node 377 (sourceLit (List.headD (raw_ints% [1475685037201389461204611607325]) 0) 50 false) (.node 376 (sourceLit (List.headD (raw_ints% [286176442873904430275355034911975]) 0) 40 true) .empty .empty) .empty) (.node 379 (sourceLit (List.headD (raw_ints% [4912999231967438319504898197525]) 0) 51 true) .empty .empty)))

#time def treeG_J014_part064 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [91455460589183195765949975]) 0) 60 false) (.node 383 (sourceLit (List.headD (raw_ints% [224304740632644605863202955825]) 0) 56 true) (.node 382 (sourceLit (List.headD (raw_ints% [513323412721678272453426915236653725]) 0) 36 false) (.node 381 (sourceLit (List.headD (raw_ints% [680753596709270967014237294475]) 0) 55 false) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [1111660574232763908086635828536002325]) 0) 33 true) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [21961035854345414713544775]) 0) 62 false) (.node 386 (sourceLit (List.headD (raw_ints% [422144887657089500759948163357044025]) 0) 32 true) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [722111177536706447478824199099138225]) 0) 30 true) .empty .empty)))

#time def treeG_J014_part065 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [203642646282204837075594991107422325]) 0) 37 true) treeG_J014_part063 treeG_J014_part064)

#time def treeG_J014_part066 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [11817721776634851445052158624642981725]) 0) 24 true) (.node 392 (sourceLit (List.headD (raw_ints% [8417885922792706290569362800767416725]) 0) 25 true) (.node 391 (sourceLit (List.headD (raw_ints% [20538569785207674121341075]) 0) 62 false) (.node 390 (sourceLit (List.headD (raw_ints% [813307632632579787717920791374366075]) 0) 29 true) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [2495348693481056419428075]) 0) 65 false) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [34971208636147862501107021247857573275]) 0) 22 true) (.node 395 (sourceLit (List.headD (raw_ints% [1215817166582289230998365]) 0) 66 false) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [148415477157321210598005]) 0) 69 false) .empty .empty)))

#time def treeG_J014_part067 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [667678196834164993401204283575]) 0) 48 true) (.node 414 (sourceLit (List.headD (raw_ints% [2906912358979998589030512133575]) 0) 46 false) (.node 413 (sourceLit (List.headD (raw_ints% [152458579192846505410975370175]) 0) 51 false) (.node 399 (sourceLit (List.headD (raw_ints% [72600931694091517293465]) 0) 70 false) .empty .empty) .empty) (.node 415 (sourceLit (List.headD (raw_ints% [533219182859715385861272654106875]) 0) 39 false) .empty .empty)) (.node 418 (sourceLit (List.headD (raw_ints% [6021522720369276565352033058075]) 0) 50 false) (.node 417 (sourceLit (List.headD (raw_ints% [9486220272848206546839727478705325]) 0) 38 true) .empty .empty) (.node 419 (sourceLit (List.headD (raw_ints% [366795349430529305238743165521262625]) 0) 36 false) .empty .empty)))

#time def treeG_J014_part068 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [53621421114262879776845782438465834725]) 0) 21 true) treeG_J014_part066 treeG_J014_part067)

#time def treeG_J014_part069 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [42393950269107603964326675]) 0) 61 false) treeG_J014_part065 treeG_J014_part068)

#time def treeG_J014_part070 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [8401719284931794711220645143630433075]) 0) 31 true) (.node 423 (sourceLit (List.headD (raw_ints% [17610387035453562078333013729845042225]) 0) 32 false) (.node 422 (sourceLit (List.headD (raw_ints% [1584764557256859197467375959975]) 0) 55 false) (.node 421 (sourceLit (List.headD (raw_ints% [2102767226339638216411204275203521425]) 0) 35 true) .empty .empty) .empty) (.node 424 (sourceLit (List.headD (raw_ints% [224924464887790239450604021725]) 0) 57 true) .empty .empty)) (.node 428 (sourceLit (List.headD (raw_ints% [51588327134864479826885175]) 0) 61 false) (.node 427 (sourceLit (List.headD (raw_ints% [5863512440926696980544170659947242675]) 0) 29 true) (.node 426 (sourceLit (List.headD (raw_ints% [108112501908519732412346025]) 0) 60 false) .empty .empty) .empty) (.node 429 (sourceLit (List.headD (raw_ints% [4733713293293442270918091386948744825]) 0) 28 true) .empty .empty)))

#time def treeG_J014_part071 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [141479377365578801430769676296930002705]) 0) 21 true) (.node 433 (sourceLit (List.headD (raw_ints% [51468754850665079684729256834180513375]) 0) 23 true) (.node 432 (sourceLit (List.headD (raw_ints% [11943799663911967971450945]) 0) 63 false) (.node 431 (sourceLit (List.headD (raw_ints% [40957956433399330804748753215983732975]) 0) 24 true) .empty .empty) .empty) (.node 434 (sourceLit (List.headD (raw_ints% [2891137833406134161481285]) 0) 65 false) .empty .empty)) (.node 437 (sourceLit (List.headD (raw_ints% [206130245146197891310924049139904643655]) 0) 20 true) (.node 436 (sourceLit (List.headD (raw_ints% [10968758073815193907605]) 0) 73 false) .empty .empty) (.node 438 (sourceLit (List.headD (raw_ints% [170892336012293339783505]) 0) 69 false) .empty .empty)))

#time def treeG_J014_part072 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [49528613323119629923577235]) 0) 61 false) treeG_J014_part070 treeG_J014_part071)

#time def treeG_J014_part073 : IntSourceTree :=
  (.node 458 (sourceLit (List.headD (raw_ints% [11523960617271954913551612308065875]) 0) 40 true) (.node 456 (sourceLit (List.headD (raw_ints% [409697812866809908068313844509425]) 0) 41 false) (.node 455 (sourceLit (List.headD (raw_ints% [142389531611494577888445942975]) 0) 51 false) (.node 454 (sourceLit (List.headD (raw_ints% [444986389433355059610500827725]) 0) 50 false) .empty .empty) .empty) (.node 457 (sourceLit (List.headD (raw_ints% [3619048271236943915810427498225]) 0) 49 true) .empty .empty)) (.node 460 (sourceLit (List.headD (raw_ints% [285218997856367071157169078314342475]) 0) 38 false) (.node 459 (sourceLit (List.headD (raw_ints% [683407622021044680303558203475]) 0) 55 false) .empty .empty) (.node 461 (sourceLit (List.headD (raw_ints% [2479007404025205932717114336775]) 0) 55 true) .empty .empty)))

#time def treeG_J014_part074 : IntSourceTree :=
  (.node 467 (sourceLit (List.headD (raw_ints% [64190430199828902985256475]) 0) 61 false) (.node 465 (sourceLit (List.headD (raw_ints% [225290286730146972233667821625]) 0) 58 true) (.node 464 (sourceLit (List.headD (raw_ints% [9361023804843162993209824779190522275]) 0) 34 false) (.node 463 (sourceLit (List.headD (raw_ints% [226133662236187975416322364475]) 0) 59 false) .empty .empty) .empty) (.node 466 (sourceLit (List.headD (raw_ints% [3989787198637352605230348490136694525]) 0) 33 true) .empty .empty)) (.node 469 (sourceLit (List.headD (raw_ints% [60782704000621355689443675]) 0) 61 false) (.node 468 (sourceLit (List.headD (raw_ints% [2570700631694995266532673230424052225]) 0) 31 true) .empty .empty) (.node 470 (sourceLit (List.headD (raw_ints% [1960202830330431241600085297787189375]) 0) 30 true) .empty .empty)))

#time def treeG_J014_part075 : IntSourceTree :=
  (.node 462 (sourceLit (List.headD (raw_ints% [1308045319530658244432315595220087575]) 0) 37 true) treeG_J014_part073 treeG_J014_part074)

#time def treeG_J014_part076 : IntSourceTree :=
  (.node 439 (sourceLit (List.headD (raw_ints% [1250435040570308319178081260965781807555]) 0) 17 true) treeG_J014_part072 treeG_J014_part075)

#time def treeG_J014_part077 : IntSourceTree :=
  (.node 420 (sourceLit (List.headD (raw_ints% [449563451828983741425719260575]) 0) 56 true) treeG_J014_part069 treeG_J014_part076)

#time def treeG_J014_part078 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [53254084364715469464831327524536214715]) 0) 23 true) (.node 474 (sourceLit (List.headD (raw_ints% [19825516537015114119838549104768765825]) 0) 25 true) (.node 473 (sourceLit (List.headD (raw_ints% [6953102276949855132594795]) 0) 64 false) (.node 472 (sourceLit (List.headD (raw_ints% [16270035255303312257089695207608158125]) 0) 26 true) .empty .empty) .empty) (.node 475 (sourceLit (List.headD (raw_ints% [209415083352980616310365]) 0) 69 false) .empty .empty)) (.node 479 (sourceLit (List.headD (raw_ints% [12286425539775227811255]) 0) 73 false) (.node 478 (sourceLit (List.headD (raw_ints% [76254412015967505767039133350719404465]) 0) 22 true) (.node 477 (sourceLit (List.headD (raw_ints% [202584781204764994445355]) 0) 69 false) .empty .empty) .empty) (.node 495 (sourceLit (List.headD (raw_ints% [1289445068259306938303338736254725]) 0) 39 false) .empty .empty)))

#time def treeG_J014_part079 : IntSourceTree :=
  (.node 501 (sourceLit (List.headD (raw_ints% [6666271192041511354925909528233001025]) 0) 35 false) (.node 499 (sourceLit (List.headD (raw_ints% [735562089183231862472394759379370625]) 0) 36 true) (.node 498 (sourceLit (List.headD (raw_ints% [2410142747901555120290615139075]) 0) 52 true) (.node 497 (sourceLit (List.headD (raw_ints% [16041385278717165075932748990856125]) 0) 38 false) .empty .empty) .empty) (.node 500 (sourceLit (List.headD (raw_ints% [566485536925014210864638732025]) 0) 57 false) .empty .empty)) (.node 503 (sourceLit (List.headD (raw_ints% [101325287485415689722001211823930647025]) 0) 32 true) (.node 502 (sourceLit (List.headD (raw_ints% [6542779365307271062901604633525]) 0) 55 true) .empty .empty) (.node 504 (sourceLit (List.headD (raw_ints% [2033993762777294042781182937525]) 0) 57 false) .empty .empty)))

#time def treeG_J014_part080 : IntSourceTree :=
  (.node 496 (sourceLit (List.headD (raw_ints% [2945910702618078239616339371175]) 0) 48 false) treeG_J014_part078 treeG_J014_part079)

#time def treeG_J014_part081 : IntSourceTree :=
  (.node 510 (sourceLit (List.headD (raw_ints% [72036794678123081455310115]) 0) 61 false) (.node 508 (sourceLit (List.headD (raw_ints% [76792533264793326143627775]) 0) 61 false) (.node 507 (sourceLit (List.headD (raw_ints% [121809677915468586386826981024426982125]) 0) 29 true) (.node 506 (sourceLit (List.headD (raw_ints% [225506511733964011698492513675]) 0) 59 true) .empty .empty) .empty) (.node 509 (sourceLit (List.headD (raw_ints% [36397496813826481993604680299836090775]) 0) 28 true) .empty .empty)) (.node 512 (sourceLit (List.headD (raw_ints% [17046243873999987830785215]) 0) 63 false) (.node 511 (sourceLit (List.headD (raw_ints% [209948005848895868120062164900776507025]) 0) 24 true) .empty .empty) (.node 513 (sourceLit (List.headD (raw_ints% [208851809234187916428705866487550016625]) 0) 23 true) .empty .empty)))

#time def treeG_J014_part082 : IntSourceTree :=
  (.node 519 (sourceLit (List.headD (raw_ints% [3629847328451612049912423273480260078205]) 0) 17 true) (.node 517 (sourceLit (List.headD (raw_ints% [645935104689249620126377191252674791785]) 0) 20 true) (.node 516 (sourceLit (List.headD (raw_ints% [121665018762459065049525]) 0) 70 false) (.node 515 (sourceLit (List.headD (raw_ints% [492937151818904850404063895055670503695]) 0) 21 true) .empty .empty) .empty) (.node 518 (sourceLit (List.headD (raw_ints% [234277226397236649107205]) 0) 69 false) .empty .empty)) (.node 538 (sourceLit (List.headD (raw_ints% [39089306513261074903035973606987875]) 0) 39 false) (.node 537 (sourceLit (List.headD (raw_ints% [820619871731877769428345858675]) 0) 52 false) .empty .empty) (.node 539 (sourceLit (List.headD (raw_ints% [5143773235985733841504847952975]) 0) 53 true) .empty .empty)))

#time def treeG_J014_part083 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [2030982221771860485556755]) 0) 66 false) treeG_J014_part081 treeG_J014_part082)

#time def treeG_J014_part084 : IntSourceTree :=
  (.node 505 (sourceLit (List.headD (raw_ints% [158178100162422402602577841610678789475]) 0) 31 false) treeG_J014_part080 treeG_J014_part083)

#time def treeG_J014_part085 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [1129642024753720507507425379575]) 0) 59 false) (.node 543 (sourceLit (List.headD (raw_ints% [8351848663196774866232183549325]) 0) 56 true) (.node 542 (sourceLit (List.headD (raw_ints% [9282361831102827843790540718673176175]) 0) 36 false) (.node 541 (sourceLit (List.headD (raw_ints% [7010891699425319619634224192975]) 0) 55 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [120047335095102015708420861382311691575]) 0) 33 true) .empty .empty)) (.node 548 (sourceLit (List.headD (raw_ints% [116668276652078595853761634563578877675]) 0) 30 true) (.node 547 (sourceLit (List.headD (raw_ints% [225634892594363669504463026625]) 0) 60 true) (.node 546 (sourceLit (List.headD (raw_ints% [166157674559697107813038538590952178525]) 0) 32 false) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [92802362528965296597811875]) 0) 61 false) .empty .empty)))

#time def treeG_J014_part086 : IntSourceTree :=
  (.node 555 (sourceLit (List.headD (raw_ints% [1193321888359938020315295]) 0) 67 false) (.node 553 (sourceLit (List.headD (raw_ints% [2523285399262533174547605]) 0) 66 false) (.node 552 (sourceLit (List.headD (raw_ints% [177407935338289243605882774485560190775]) 0) 25 true) (.node 551 (sourceLit (List.headD (raw_ints% [43046751140211125653073955]) 0) 62 false) .empty .empty) .empty) (.node 554 (sourceLit (List.headD (raw_ints% [169200776160157688189028768278012484975]) 0) 24 true) .empty .empty)) (.node 557 (sourceLit (List.headD (raw_ints% [284075293845071265752745]) 0) 69 false) (.node 556 (sourceLit (List.headD (raw_ints% [386428983089473911474401240006598074265]) 0) 22 true) .empty .empty) (.node 558 (sourceLit (List.headD (raw_ints% [493426280657314608592298924551235982855]) 0) 21 true) .empty .empty)))

#time def treeG_J014_part087 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [32477091153165619510404509704261712025]) 0) 29 true) treeG_J014_part085 treeG_J014_part086)

#time def treeG_J014_part088 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [5192921212987034454506683243425]) 0) 58 true) (.node 582 (sourceLit (List.headD (raw_ints% [20564562764157910302170053019475]) 0) 55 false) (.node 581 (sourceLit (List.headD (raw_ints% [17114271871209239393219772856297445625]) 0) 35 true) (.node 580 (sourceLit (List.headD (raw_ints% [9675657531385847528421957809175]) 0) 54 true) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [398360866080706180723298514821472284625]) 0) 32 false) .empty .empty)) (.node 586 (sourceLit (List.headD (raw_ints% [2484790561241405026713343272825]) 0) 59 false) (.node 585 (sourceLit (List.headD (raw_ints% [1118556780923238528269944732669172322075]) 0) 31 true) .empty .empty) (.node 587 (sourceLit (List.headD (raw_ints% [2780332470870622311395443598479661838525]) 0) 29 false) .empty .empty)))

#time def treeG_J014_part089 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [1210411673472126032418356329396931509575]) 0) 23 true) (.node 591 (sourceLit (List.headD (raw_ints% [1868585827953703780545826456171973062575]) 0) 24 true) (.node 590 (sourceLit (List.headD (raw_ints% [113567930379807511740313635]) 0) 61 false) (.node 589 (sourceLit (List.headD (raw_ints% [896948716402802284836488396208794930625]) 0) 28 true) .empty .empty) .empty) (.node 592 (sourceLit (List.headD (raw_ints% [6500126816552784455572185]) 0) 65 false) .empty .empty)) (.node 595 (sourceLit (List.headD (raw_ints% [2214275266743618160620396397392529255905]) 0) 21 true) (.node 594 (sourceLit (List.headD (raw_ints% [3015588576753205863538455]) 0) 66 false) .empty .empty) (.node 596 (sourceLit (List.headD (raw_ints% [706661813310101760117195]) 0) 68 false) .empty .empty)))

#time def treeG_J014_part090 : IntSourceTree :=
  (.node 588 (sourceLit (List.headD (raw_ints% [3526745080119194731728228975]) 0) 67 true) treeG_J014_part088 treeG_J014_part089)

#time def treeG_J014_part091 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [135985822079034826617165]) 0) 70 false) treeG_J014_part087 treeG_J014_part090)

#time def treeG_J014_part092 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [1306000084895966004786732916008055575]) 0) 37 true) treeG_J014_part084 treeG_J014_part091)

#time def treeG_J014_part093 : IntSourceTree :=
  (.node 471 (sourceLit (List.headD (raw_ints% [113242357569968577352485]) 0) 70 false) treeG_J014_part077 treeG_J014_part092)

#time def treeG_J014_part094 : IntSourceTree :=
  (.node 623 (sourceLit (List.headD (raw_ints% [903637857104833911512569892775]) 0) 61 false) (.node 621 (sourceLit (List.headD (raw_ints% [8343274615405583574028091001075]) 0) 56 true) (.node 599 (sourceLit (List.headD (raw_ints% [12159793652582455425041142312159291373155]) 0) 17 true) (.node 598 (sourceLit (List.headD (raw_ints% [333873361292905882398285]) 0) 69 false) .empty .empty) .empty) (.node 622 (sourceLit (List.headD (raw_ints% [3299579212789008404626289196871327725]) 0) 39 true) .empty .empty)) (.node 626 (sourceLit (List.headD (raw_ints% [160589306935366954510372908907515562575]) 0) 35 true) (.node 625 (sourceLit (List.headD (raw_ints% [790320404717594370251763577875]) 0) 62 true) (.node 624 (sourceLit (List.headD (raw_ints% [64801025146976024553964922025472997025]) 0) 36 false) .empty .empty) .empty) (.node 627 (sourceLit (List.headD (raw_ints% [1355212726917884348108903149725]) 0) 61 false) .empty .empty)))

#time def treeG_J014_part095 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [994210354322562820256145]) 0) 68 false) (.node 631 (sourceLit (List.headD (raw_ints% [2152135596911510805885]) 0) 77 false) (.node 630 (sourceLit (List.headD (raw_ints% [108058953156204583165760485813066652325]) 0) 32 true) (.node 629 (sourceLit (List.headD (raw_ints% [451516172617785890957811120675]) 0) 61 true) .empty .empty) .empty) (.node 632 (sourceLit (List.headD (raw_ints% [211397236576926817117492960210801608975]) 0) 28 true) .empty .empty)) (.node 635 (sourceLit (List.headD (raw_ints% [227783336049158480402895]) 0) 70 false) (.node 634 (sourceLit (List.headD (raw_ints% [130151362163996043028665945139864878075]) 0) 27 true) .empty .empty) (.node 636 (sourceLit (List.headD (raw_ints% [228480785456768031143249394673241397705]) 0) 25 true) .empty .empty)))

#time def treeG_J014_part096 : IntSourceTree :=
  (.node 628 (sourceLit (List.headD (raw_ints% [362125093440337613406150654130405089525]) 0) 33 false) treeG_J014_part094 treeG_J014_part095)

#time def treeG_J014_part097 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [5265822390329704099723699742299444131675]) 0) 31 false) (.node 663 (sourceLit (List.headD (raw_ints% [1243053144554692332307628549220532182225]) 0) 32 true) (.node 639 (sourceLit (List.headD (raw_ints% [772998200054183811645]) 0) 78 false) (.node 638 (sourceLit (List.headD (raw_ints% [244008809921153382884566725531109227435]) 0) 24 true) .empty .empty) .empty) (.node 664 (sourceLit (List.headD (raw_ints% [19651126926664377038707801527825]) 0) 58 false) .empty .empty)) (.node 667 (sourceLit (List.headD (raw_ints% [23335763758597592488723175938641653848125]) 0) 29 true) (.node 666 (sourceLit (List.headD (raw_ints% [15129917036722914950741560518825]) 0) 59 true) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [1468068569481698579524206476925]) 0) 62 false) .empty .empty)))

#time def treeG_J014_part098 : IntSourceTree :=
  (.node 674 (sourceLit (List.headD (raw_ints% [4938094257827296698510705]) 0) 66 false) (.node 672 (sourceLit (List.headD (raw_ints% [11130167993346312066237735]) 0) 65 false) (.node 671 (sourceLit (List.headD (raw_ints% [53457598188023042800323542280118152927825]) 0) 24 true) (.node 670 (sourceLit (List.headD (raw_ints% [903145913165951589427362554985]) 0) 61 true) .empty .empty) .empty) (.node 673 (sourceLit (List.headD (raw_ints% [12319011467451190263101193124094371464825]) 0) 23 true) .empty .empty)) (.node 676 (sourceLit (List.headD (raw_ints% [1115604875083166083105965]) 0) 68 false) (.node 675 (sourceLit (List.headD (raw_ints% [14445099090247875347048844580510175137695]) 0) 21 true) .empty .empty) (.node 677 (sourceLit (List.headD (raw_ints% [12177273509206612321499128530287339650785]) 0) 20 true) .empty .empty)))

#time def treeG_J014_part099 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [24072954696584409542830130260554720660225]) 0) 28 false) treeG_J014_part097 treeG_J014_part098)

#time def treeG_J014_part100 : IntSourceTree :=
  (.node 637 (sourceLit (List.headD (raw_ints% [211293259732515247182225]) 0) 70 false) treeG_J014_part096 treeG_J014_part099)

#time def treeG_J014_part101 : IntSourceTree :=
  (.node 707 (sourceLit (List.headD (raw_ints% [17840342490558683646959366818275]) 0) 60 true) (.node 705 (sourceLit (List.headD (raw_ints% [25973690164405132000721910150825]) 0) 59 false) (.node 704 (sourceLit (List.headD (raw_ints% [1761461345730500528739347925424316158425]) 0) 33 true) (.node 679 (sourceLit (List.headD (raw_ints% [50306461687232810593407939423804670850205]) 0) 17 true) .empty .empty) .empty) (.node 706 (sourceLit (List.headD (raw_ints% [6550536845812639735806683013559568632275]) 0) 32 false) .empty .empty)) (.node 710 (sourceLit (List.headD (raw_ints% [24937426321834046208156214147059253878825]) 0) 29 false) (.node 709 (sourceLit (List.headD (raw_ints% [6323790450544580209054637028375]) 0) 61 false) (.node 708 (sourceLit (List.headD (raw_ints% [26232764506120293395972381171684894564325]) 0) 30 true) .empty .empty) .empty) (.node 711 (sourceLit (List.headD (raw_ints% [903216434345191185813449794665]) 0) 62 true) .empty .empty)))

#time def treeG_J014_part102 : IntSourceTree :=
  (.node 717 (sourceLit (List.headD (raw_ints% [693018355618135588741515]) 0) 69 false) (.node 715 (sourceLit (List.headD (raw_ints% [3115827569434028855287545]) 0) 67 false) (.node 714 (sourceLit (List.headD (raw_ints% [11277800570139221918871865562975452440225]) 0) 24 true) (.node 713 (sourceLit (List.headD (raw_ints% [7153326576056060785213155]) 0) 66 false) .empty .empty) .empty) (.node 716 (sourceLit (List.headD (raw_ints% [12617252806593731097902849423124243956055]) 0) 22 true) .empty .empty)) (.node 719 (sourceLit (List.headD (raw_ints% [313412138423284050549495]) 0) 70 false) (.node 718 (sourceLit (List.headD (raw_ints% [10225203029837385258422594726038465831305]) 0) 21 true) .empty .empty) (.node 745 (sourceLit (List.headD (raw_ints% [19357513156173708329638483145693973399075]) 0) 31 true) .empty .empty)))

#time def treeG_J014_part103 : IntSourceTree :=
  (.node 712 (sourceLit (List.headD (raw_ints% [51766420295407628263383598598431740056025]) 0) 25 true) treeG_J014_part101 treeG_J014_part102)

#time def treeG_J014_part104 : IntSourceTree :=
  (.node 751 (sourceLit (List.headD (raw_ints% [1649452882785402000122321247691910401172625]) 0) 24 false) (.node 749 (sourceLit (List.headD (raw_ints% [233935070745546756710609179634033877174825]) 0) 28 true) (.node 748 (sourceLit (List.headD (raw_ints% [20776479629522080806007779772125]) 0) 61 true) (.node 747 (sourceLit (List.headD (raw_ints% [128144353291599828261630104155594751964525]) 0) 29 false) .empty .empty) .empty) (.node 750 (sourceLit (List.headD (raw_ints% [13550726814255112007536636611735]) 0) 61 false) .empty .empty)) (.node 753 (sourceLit (List.headD (raw_ints% [401812350895809835843967595663359548983375]) 0) 23 true) (.node 752 (sourceLit (List.headD (raw_ints% [903260955017164571061714745605]) 0) 63 true) .empty .empty) (.node 754 (sourceLit (List.headD (raw_ints% [9368558894284824871915605]) 0) 66 false) .empty .empty)))

#time def treeG_J014_part105 : IntSourceTree :=
  (.node 786 (sourceLit (List.headD (raw_ints% [12954025000993174032722583079626771015675]) 0) 33 true) (.node 758 (sourceLit (List.headD (raw_ints% [874737033599116071152415]) 0) 69 false) (.node 757 (sourceLit (List.headD (raw_ints% [88760748943543236461723666854706611997655]) 0) 20 true) (.node 756 (sourceLit (List.headD (raw_ints% [500055673587715693045395]) 0) 70 false) .empty .empty) .empty) (.node 759 (sourceLit (List.headD (raw_ints% [276900035267563517676115091809426235751555]) 0) 17 true) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [77188558898860060828801242663639823264425]) 0) 31 false) (.node 787 (sourceLit (List.headD (raw_ints% [42458819928045931299572373819375]) 0) 61 false) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [47876749709588741821070196572625]) 0) 61 true) .empty .empty)))

#time def treeG_J014_part106 : IntSourceTree :=
  (.node 755 (sourceLit (List.headD (raw_ints% [165999710031979675354901004427097063905905]) 0) 21 true) treeG_J014_part104 treeG_J014_part105)

#time def treeG_J014_part107 : IntSourceTree :=
  (.node 746 (sourceLit (List.headD (raw_ints% [67077297365533178952185380820475]) 0) 59 false) treeG_J014_part103 treeG_J014_part106)

#time def treeG_J014_part108 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [511299677637155106330615]) 0) 69 false) treeG_J014_part100 treeG_J014_part107)

#time def treeG_J014_part109 : IntSourceTree :=
  (.node 795 (sourceLit (List.headD (raw_ints% [1563182831212699004157015]) 0) 69 false) (.node 793 (sourceLit (List.headD (raw_ints% [903289568323468795304855598225]) 0) 64 true) (.node 792 (sourceLit (List.headD (raw_ints% [850609651540404814192852423145171070614325]) 0) 26 false) (.node 791 (sourceLit (List.headD (raw_ints% [56460715814844934349023775025]) 0) 70 false) .empty .empty) .empty) (.node 794 (sourceLit (List.headD (raw_ints% [195267275162835306962547865050192048271575]) 0) 25 true) .empty .empty)) (.node 798 (sourceLit (List.headD (raw_ints% [39267772956852925601650536064334073083175]) 0) 22 true) (.node 797 (sourceLit (List.headD (raw_ints% [1307204338732727183440065]) 0) 69 false) (.node 796 (sourceLit (List.headD (raw_ints% [76691228612692972128499077501986409974925]) 0) 23 true) .empty .empty) .empty) (.node 799 (sourceLit (List.headD (raw_ints% [70165611896979002575365]) 0) 73 false) .empty .empty)))

#time def treeG_J014_part110 : IntSourceTree :=
  (.node 832 (sourceLit (List.headD (raw_ints% [15357204203617467764411801152005]) 0) 63 false) (.node 830 (sourceLit (List.headD (raw_ints% [109304226233432595649677029756985]) 0) 61 true) (.node 829 (sourceLit (List.headD (raw_ints% [1468952013127307729971429062252271049405625]) 0) 28 false) (.node 828 (sourceLit (List.headD (raw_ints% [105694119485613943405152527410875]) 0) 61 false) .empty .empty) .empty) (.node 831 (sourceLit (List.headD (raw_ints% [18217292695097773386923306449681870788606225]) 0) 24 true) .empty .empty)) (.node 834 (sourceLit (List.headD (raw_ints% [903308305441257364954599429435]) 0) 65 true) (.node 833 (sourceLit (List.headD (raw_ints% [14011566775542286862929606365986096678812575]) 0) 23 false) .empty .empty) (.node 835 (sourceLit (List.headD (raw_ints% [6082553095178750147446630677179048480784495]) 0) 21 true) .empty .empty)))

#time def treeG_J014_part111 : IntSourceTree :=
  (.node 827 (sourceLit (List.headD (raw_ints% [542673153323381397308752762703651424466125]) 0) 29 true) treeG_J014_part109 treeG_J014_part110)

#time def treeG_J014_part112 : IntSourceTree :=
  (.node 869 (sourceLit (List.headD (raw_ints% [259264988680816628631375251394375]) 0) 61 false) (.node 839 (sourceLit (List.headD (raw_ints% [2236237433971023720829519216307954441571645]) 0) 17 true) (.node 838 (sourceLit (List.headD (raw_ints% [1739671643866338295727715]) 0) 69 false) (.node 837 (sourceLit (List.headD (raw_ints% [1138298908859544317594261573177075947601145]) 0) 20 true) .empty .empty) .empty) (.node 868 (sourceLit (List.headD (raw_ints% [697050271121101518966355248030931070994975]) 0) 30 true) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [123758169482032898843027116163385]) 0) 62 true) (.node 870 (sourceLit (List.headD (raw_ints% [1727824510194688532890194456033364180459275]) 0) 29 false) .empty .empty) (.node 872 (sourceLit (List.headD (raw_ints% [19918511998178583015309011295972212929834875]) 0) 25 true) .empty .empty)))

#time def treeG_J014_part113 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [1059763362945838466390960501048407801434795]) 0) 21 true) (.node 876 (sourceLit (List.headD (raw_ints% [5929170637953364203189632522175075660834645]) 0) 22 true) (.node 875 (sourceLit (List.headD (raw_ints% [903320810903907066546632685555]) 0) 66 true) (.node 874 (sourceLit (List.headD (raw_ints% [14402101325867957476854702096086480775355725]) 0) 24 false) .empty .empty) .empty) (.node 877 (sourceLit (List.headD (raw_ints% [2945304291767206061006415]) 0) 69 false) .empty .empty)) (.node 909 (sourceLit (List.headD (raw_ints% [7045354182096119881702271046499719617365425]) 0) 28 true) (.node 879 (sourceLit (List.headD (raw_ints% [1178346748690506275124795]) 0) 70 false) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [627834203595065852912427532545735]) 0) 61 false) .empty .empty)))

#time def treeG_J014_part114 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [8130246885970468279858328375115]) 0) 65 false) treeG_J014_part112 treeG_J014_part113)

#time def treeG_J014_part115 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [265781789406245827777905]) 0) 72 false) treeG_J014_part111 treeG_J014_part114)

#time def treeG_J014_part116 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [903329315921168066413121578515]) 0) 67 true) (.node 914 (sourceLit (List.headD (raw_ints% [17163802077382193924671256179665]) 0) 65 false) (.node 913 (sourceLit (List.headD (raw_ints% [173359662760970950985401696733763800117491575]) 0) 23 true) (.node 912 (sourceLit (List.headD (raw_ints% [69557686842825183303719458657695]) 0) 64 true) .empty .empty) .empty) (.node 915 (sourceLit (List.headD (raw_ints% [236516174309066069777121864214562740886476095]) 0) 21 false) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [31676190180295807203681216817241095204341795]) 0) 17 true) (.node 918 (sourceLit (List.headD (raw_ints% [4150936939668073826285115]) 0) 69 false) (.node 917 (sourceLit (List.headD (raw_ints% [46295066194767369307922798604223529339076015]) 0) 20 true) .empty .empty) .empty) (.node 950 (sourceLit (List.headD (raw_ints% [2193294673072702103648116375633270949456175]) 0) 31 true) .empty .empty)))

#time def treeG_J014_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [60611336236754858495077874184184454136827685]) 0) 24 false) (.node 954 (sourceLit (List.headD (raw_ints% [46940441021709727115564099707462570223211825]) 0) 26 true) (.node 953 (sourceLit (List.headD (raw_ints% [38843966864397825791788893516405]) 0) 66 true) (.node 952 (sourceLit (List.headD (raw_ints% [37179143336434105626801190732947347816958675]) 0) 27 false) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [4516780722071525247804472216305]) 0) 68 false) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [11308825707955382710382959525793780384410305]) 0) 23 true) (.node 957 (sourceLit (List.headD (raw_ints% [903335206529751600825243591345]) 0) 68 true) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [90716253386766587865]) 0) 85 false) .empty .empty)))

#time def treeG_J014_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [183494231708276062440296545095]) 0) 74 false) treeG_J014_part116 treeG_J014_part117)

#time def treeG_J014_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [225834839366672817224767469115]) 0) 71 true) (.node 996 (sourceLit (List.headD (raw_ints% [18970452204207269057631010443735]) 0) 67 false) (.node 995 (sourceLit (List.headD (raw_ints% [3240704399698488605173224245492167235172032895]) 0) 21 true) (.node 994 (sourceLit (List.headD (raw_ints% [172539669534973497091826830245285]) 0) 65 true) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [1985857825770922841150414772498126061717561935]) 0) 20 false) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [1550854013613701239505296199017929211153016475]) 0) 24 false) (.node 999 (sourceLit (List.headD (raw_ints% [1415853500437993179725337602484362794000177245]) 0) 17 true) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [190606792423259598083044719110505]) 0) 66 true) .empty .empty)))

#time def treeG_J014_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [3274644447304169799073058274285]) 0) 73 true) (.node 1039 (sourceLit (List.headD (raw_ints% [225835582514220561616655259195]) 0) 72 true) (.node 1038 (sourceLit (List.headD (raw_ints% [2031093128602744371991946610601301183255203155]) 0) 21 false) (.node 1037 (sourceLit (List.headD (raw_ints% [2484223426342127582307031754385]) 0) 71 false) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [28054368617517708437257963429779034613620296495]) 0) 21 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [5194281692050927981838830977885]) 0) 71 false) (.node 1077 (sourceLit (List.headD (raw_ints% [29851055782934987154378700710329366475472311015]) 0) 20 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [66410833615725813083467629141726000658166678205]) 0) 17 false) .empty .empty)))

#time def treeG_J014_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [3483149744645508039153535742228905051719343635]) 0) 22 true) treeG_J014_part119 treeG_J014_part120)

#time def treeG_J014_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [1363092249526862331043039800188078930260169175]) 0) 23 false) treeG_J014_part118 treeG_J014_part121)

#time def treeG_J014_part123 : IntSourceTree :=
  (.node 911 (sourceLit (List.headD (raw_ints% [128798061347557839491895751635817178337999825]) 0) 24 false) treeG_J014_part115 treeG_J014_part122)

#time def treeG_J014_part124 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [129436248533690401459382696890546565526825]) 0) 30 true) treeG_J014_part108 treeG_J014_part123)

#time def treeG_J014_part125 : IntSourceTree :=
  (.node 597 (sourceLit (List.headD (raw_ints% [2445496760026541671668832728800109802335]) 0) 20 true) treeG_J014_part093 treeG_J014_part124)

#time def treeG_J014_part126 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [125938618302349081412505]) 0) 69 false) treeG_J014_part062 treeG_J014_part125)

#time def treeG_J014 : IntSourceTree := treeG_J014_part126

#time def treeG_J015_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 39 false) (.node 5 (sourceLit (List.headD (raw_ints% [7408763836469294839075345384575]) 0) 38 false) (.node 4 (sourceLit (List.headD (raw_ints% [2186692625245228855743661466625]) 0) 42 false) (.node 3 (sourceLit (List.headD (raw_ints% [47993317543072179017785269499275]) 0) 36 false) .empty .empty) .empty) (.node 6 (sourceLit (List.headD (raw_ints% [1046472067814740136100196283475]) 0) 43 false) .empty .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [61242063523112378117631645225]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [191276174779758042316919416125]) 0) 42 true) (.node 8 (sourceLit (List.headD (raw_ints% [126239302919911795760677041225]) 0) 46 false) .empty .empty) .empty) (.node 11 (sourceLit (List.headD (raw_ints% [352798277927109278051206923075]) 0) 43 true) .empty .empty)))

#time def treeG_J015_part001 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 50 false) (.node 15 (sourceLit (List.headD (raw_ints% [332605538004749946777346173525]) 0) 46 true) (.node 14 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 50 false) (.node 13 (sourceLit (List.headD (raw_ints% [207763279407238870206862638525]) 0) 45 true) .empty .empty) .empty) (.node 16 (sourceLit (List.headD (raw_ints% [71248820212612590351433824692475]) 0) 39 true) .empty .empty)) (.node 19 (sourceLit (List.headD (raw_ints% [3569835825909221960757290625]) 0) 51 false) (.node 18 (sourceLit (List.headD (raw_ints% [57211654571405384126222436788475]) 0) 38 true) .empty .empty) (.node 20 (sourceLit (List.headD (raw_ints% [145038228815086709004582575389425]) 0) 36 true) .empty .empty)))

#time def treeG_J015_part002 : IntSourceTree :=
  (.node 12 (sourceLit (List.headD (raw_ints% [14911714221369378590363311125]) 0) 49 false) treeG_J015_part000 treeG_J015_part001)

#time def treeG_J015_part003 : IntSourceTree :=
  (.node 26 (sourceLit (List.headD (raw_ints% [1973633906286225370063813522118085]) 0) 31 true) (.node 24 (sourceLit (List.headD (raw_ints% [1261865971072081893053086438316625]) 0) 32 true) (.node 23 (sourceLit (List.headD (raw_ints% [430772971026794448935893725]) 0) 54 false) (.node 22 (sourceLit (List.headD (raw_ints% [207956749740535698024672882822375]) 0) 35 true) .empty .empty) .empty) (.node 25 (sourceLit (List.headD (raw_ints% [52998438744577727250767775]) 0) 57 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [6280997670860409940453082452933245]) 0) 29 true) (.node 27 (sourceLit (List.headD (raw_ints% [26106765727873007498902425]) 0) 58 false) .empty .empty) (.node 29 (sourceLit (List.headD (raw_ints% [6435420268666260706360875]) 0) 60 false) .empty .empty)))

#time def treeG_J015_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [48396517715292436008585]) 0) 67 false) (.node 33 (sourceLit (List.headD (raw_ints% [97970342674925511242235]) 0) 66 false) (.node 32 (sourceLit (List.headD (raw_ints% [129813323279078089784884642965183825]) 0) 24 true) (.node 31 (sourceLit (List.headD (raw_ints% [3175063546818032314931115]) 0) 61 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [208258617811348277984743481746851225]) 0) 23 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [11960131968114425995725]) 0) 69 false) (.node 36 (sourceLit (List.headD (raw_ints% [662183161339871309686804450988437215]) 0) 21 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [1035608388682895484115204169705910465]) 0) 20 true) .empty .empty)))

#time def treeG_J015_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [10082927915166712471056303101930655]) 0) 28 true) treeG_J015_part003 treeG_J015_part004)

#time def treeG_J015_part006 : IntSourceTree :=
  (.node 21 (sourceLit (List.headD (raw_ints% [876300752212663748682737025]) 0) 53 false) treeG_J015_part002 treeG_J015_part005)

#time def treeG_J015_part007 : IntSourceTree :=
  (.node 48 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 40 false) (.node 46 (sourceLit (List.headD (raw_ints% [7408763836469294839075345384575]) 0) 39 false) (.node 45 (sourceLit (List.headD (raw_ints% [2186692625245228855743661466625]) 0) 43 false) (.node 44 (sourceLit (List.headD (raw_ints% [47993317543072179017785269499275]) 0) 37 false) .empty .empty) .empty) (.node 47 (sourceLit (List.headD (raw_ints% [1046472067814740136100196283475]) 0) 44 false) .empty .empty)) (.node 51 (sourceLit (List.headD (raw_ints% [61242063523112378117631645225]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [191276174779758042316919416125]) 0) 43 true) (.node 49 (sourceLit (List.headD (raw_ints% [126239302919911795760677041225]) 0) 47 false) .empty .empty) .empty) (.node 52 (sourceLit (List.headD (raw_ints% [352798277927109278051206923075]) 0) 44 true) .empty .empty)))

#time def treeG_J015_part008 : IntSourceTree :=
  (.node 58 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 51 false) (.node 56 (sourceLit (List.headD (raw_ints% [332605538004749946777346173525]) 0) 47 true) (.node 55 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 51 false) (.node 54 (sourceLit (List.headD (raw_ints% [207763279407238870206862638525]) 0) 46 true) .empty .empty) .empty) (.node 57 (sourceLit (List.headD (raw_ints% [71248820212612590351433824692475]) 0) 40 true) .empty .empty)) (.node 60 (sourceLit (List.headD (raw_ints% [3569835825909221960757290625]) 0) 52 false) (.node 59 (sourceLit (List.headD (raw_ints% [57211654571405384126222436788475]) 0) 39 true) .empty .empty) (.node 61 (sourceLit (List.headD (raw_ints% [145038228815086709004582575389425]) 0) 37 true) .empty .empty)))

#time def treeG_J015_part009 : IntSourceTree :=
  (.node 53 (sourceLit (List.headD (raw_ints% [14911714221369378590363311125]) 0) 50 false) treeG_J015_part007 treeG_J015_part008)

#time def treeG_J015_part010 : IntSourceTree :=
  (.node 67 (sourceLit (List.headD (raw_ints% [1973633906286225370063813522118085]) 0) 32 true) (.node 65 (sourceLit (List.headD (raw_ints% [1261865971072081893053086438316625]) 0) 33 true) (.node 64 (sourceLit (List.headD (raw_ints% [430772971026794448935893725]) 0) 55 false) (.node 63 (sourceLit (List.headD (raw_ints% [207956749740535698024672882822375]) 0) 36 true) .empty .empty) .empty) (.node 66 (sourceLit (List.headD (raw_ints% [52998438744577727250767775]) 0) 58 false) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [6280997670860409940453082452933245]) 0) 30 true) (.node 68 (sourceLit (List.headD (raw_ints% [26106765727873007498902425]) 0) 59 false) .empty .empty) (.node 70 (sourceLit (List.headD (raw_ints% [6435420268666260706360875]) 0) 61 false) .empty .empty)))

#time def treeG_J015_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [48396517715292436008585]) 0) 68 false) (.node 74 (sourceLit (List.headD (raw_ints% [97970342674925511242235]) 0) 67 false) (.node 73 (sourceLit (List.headD (raw_ints% [129813323279078089784884642965183825]) 0) 25 true) (.node 72 (sourceLit (List.headD (raw_ints% [3175063546818032314931115]) 0) 62 false) .empty .empty) .empty) (.node 75 (sourceLit (List.headD (raw_ints% [208258617811348277984743481746851225]) 0) 24 true) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [11960131968114425995725]) 0) 70 false) (.node 77 (sourceLit (List.headD (raw_ints% [662183161339871309686804450988437215]) 0) 22 true) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [1035608388682895484115204169705910465]) 0) 21 true) .empty .empty)))

#time def treeG_J015_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [10082927915166712471056303101930655]) 0) 29 true) treeG_J015_part010 treeG_J015_part011)

#time def treeG_J015_part013 : IntSourceTree :=
  (.node 62 (sourceLit (List.headD (raw_ints% [876300752212663748682737025]) 0) 54 false) treeG_J015_part009 treeG_J015_part012)

#time def treeG_J015_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [5914238543588137680225]) 0) 70 false) treeG_J015_part006 treeG_J015_part013)

#time def treeG_J015_part015 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [191236542316711213403722437225]) 0) 47 false) (.node 88 (sourceLit (List.headD (raw_ints% [793993461974916544578842201025]) 0) 45 false) (.node 87 (sourceLit (List.headD (raw_ints% [13478594449480283381932254856275]) 0) 39 false) (.node 86 (sourceLit (List.headD (raw_ints% [3326913182675717575387126649775]) 0) 43 false) .empty .empty) .empty) (.node 89 (sourceLit (List.headD (raw_ints% [1721485573017822380852274745125]) 0) 41 false) .empty .empty)) (.node 93 (sourceLit (List.headD (raw_ints% [72517499259935203922172142275]) 0) 46 true) (.node 92 (sourceLit (List.headD (raw_ints% [11582587325435749881817083525]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 43 true) .empty .empty) .empty) (.node 94 (sourceLit (List.headD (raw_ints% [22540963357883944380781749375]) 0) 50 false) .empty .empty)))

#time def treeG_J015_part016 : IntSourceTree :=
  (.node 100 (sourceLit (List.headD (raw_ints% [770348244327399437014976413226175]) 0) 36 true) (.node 98 (sourceLit (List.headD (raw_ints% [512778907129495338685248160751325]) 0) 38 true) (.node 97 (sourceLit (List.headD (raw_ints% [361735398344169197977125665025]) 0) 48 true) (.node 96 (sourceLit (List.headD (raw_ints% [130906774187743216808582223284475]) 0) 39 false) .empty .empty) .empty) (.node 99 (sourceLit (List.headD (raw_ints% [10995094343800403639132455125]) 0) 51 false) .empty .empty)) (.node 102 (sourceLit (List.headD (raw_ints% [952349080780157974011987720293025]) 0) 35 true) (.node 101 (sourceLit (List.headD (raw_ints% [10521621381627180515916225]) 0) 61 false) .empty .empty) (.node 103 (sourceLit (List.headD (raw_ints% [1321828533398533048429580325]) 0) 54 false) .empty .empty)))

#time def treeG_J015_part017 : IntSourceTree :=
  (.node 95 (sourceLit (List.headD (raw_ints% [82921020809727793636379103525]) 0) 46 true) treeG_J015_part015 treeG_J015_part016)

#time def treeG_J015_part018 : IntSourceTree :=
  (.node 109 (sourceLit (List.headD (raw_ints% [9835672729603373396270775]) 0) 61 false) (.node 107 (sourceLit (List.headD (raw_ints% [79890111761282447002633125]) 0) 58 false) (.node 106 (sourceLit (List.headD (raw_ints% [8121293862290429774360877984414915]) 0) 31 true) (.node 105 (sourceLit (List.headD (raw_ints% [324776093537638994434358175]) 0) 56 false) .empty .empty) .empty) (.node 108 (sourceLit (List.headD (raw_ints% [25297144829719195980567933900956115]) 0) 29 true) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [9695776990514489097790635]) 0) 61 false) (.node 110 (sourceLit (List.headD (raw_ints% [40165053451716567052568356521535305]) 0) 28 true) .empty .empty) (.node 112 (sourceLit (List.headD (raw_ints% [515494063291591508362718755558378095]) 0) 24 true) .empty .empty)))

#time def treeG_J015_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [4261856902036074993379231438201587255]) 0) 20 true) (.node 116 (sourceLit (List.headD (raw_ints% [2669954723641701138069091256961182385]) 0) 21 true) (.node 115 (sourceLit (List.headD (raw_ints% [147544167634558586475885]) 0) 67 false) (.node 114 (sourceLit (List.headD (raw_ints% [830247968421276440294333661974619375]) 0) 23 true) .empty .empty) .empty) (.node 117 (sourceLit (List.headD (raw_ints% [9109096436794502503215]) 0) 71 false) .empty .empty)) (.node 126 (sourceLit (List.headD (raw_ints% [33175789870133589339634578730125]) 0) 39 false) (.node 119 (sourceLit (List.headD (raw_ints% [18006025392640714311225]) 0) 70 false) .empty .empty) (.node 127 (sourceLit (List.headD (raw_ints% [570110278715244359821732591575]) 0) 46 false) .empty .empty)))

#time def treeG_J015_part020 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [2391300805418628224993235]) 0) 63 false) treeG_J015_part018 treeG_J015_part019)

#time def treeG_J015_part021 : IntSourceTree :=
  (.node 104 (sourceLit (List.headD (raw_ints% [5392750020625060443736445811999375]) 0) 32 true) treeG_J015_part017 treeG_J015_part020)

#time def treeG_J015_part022 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [31418635080373620936905022975]) 0) 50 false) (.node 131 (sourceLit (List.headD (raw_ints% [2031163731149981801345168625]) 0) 54 false) (.node 130 (sourceLit (List.headD (raw_ints% [2104037922577338465486113577375]) 0) 42 false) (.node 129 (sourceLit (List.headD (raw_ints% [541514856135092953057488118575]) 0) 46 false) .empty .empty) .empty) (.node 132 (sourceLit (List.headD (raw_ints% [80761051573675617867143753475]) 0) 46 false) .empty .empty)) (.node 136 (sourceLit (List.headD (raw_ints% [15605282324688884571310441875]) 0) 51 false) (.node 135 (sourceLit (List.headD (raw_ints% [3814624568257282895209219125]) 0) 53 false) (.node 134 (sourceLit (List.headD (raw_ints% [62728280887368462362518353975]) 0) 46 false) .empty .empty) .empty) (.node 137 (sourceLit (List.headD (raw_ints% [101077797200177903580008023988475]) 0) 41 false) .empty .empty)))

#time def treeG_J015_part023 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [372196165519811137993657418735325]) 0) 37 true) (.node 141 (sourceLit (List.headD (raw_ints% [312655007756156364005196918918375]) 0) 38 true) (.node 140 (sourceLit (List.headD (raw_ints% [1856314629472795419593791125]) 0) 54 false) (.node 139 (sourceLit (List.headD (raw_ints% [227783626279044977279512861981425]) 0) 40 true) .empty .empty) .empty) (.node 142 (sourceLit (List.headD (raw_ints% [1817234321483894463391816575]) 0) 54 false) .empty .empty)) (.node 145 (sourceLit (List.headD (raw_ints% [2065442024776489275341679686841375]) 0) 34 true) (.node 144 (sourceLit (List.headD (raw_ints% [111381945296467324936710825]) 0) 58 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [218779216048483539932822625]) 0) 57 false) .empty .empty)))

#time def treeG_J015_part024 : IntSourceTree :=
  (.node 138 (sourceLit (List.headD (raw_ints% [390865258683588449176905156525]) 0) 49 true) treeG_J015_part022 treeG_J015_part023)

#time def treeG_J015_part025 : IntSourceTree :=
  (.node 152 (sourceLit (List.headD (raw_ints% [25471536889439284308045]) 0) 70 false) (.node 150 (sourceLit (List.headD (raw_ints% [13235925190540486086180675]) 0) 61 false) (.node 149 (sourceLit (List.headD (raw_ints% [9508073579429393020057425724011435]) 0) 31 true) (.node 148 (sourceLit (List.headD (raw_ints% [13445836508352359875932675]) 0) 61 false) .empty .empty) .empty) (.node 151 (sourceLit (List.headD (raw_ints% [15041062768274927290756026709802325]) 0) 30 true) .empty .empty)) (.node 154 (sourceLit (List.headD (raw_ints% [1607538064019224135055355]) 0) 64 false) (.node 153 (sourceLit (List.headD (raw_ints% [192840370006256709288917056296597135]) 0) 26 true) .empty .empty) (.node 155 (sourceLit (List.headD (raw_ints% [310994675304964081154795090113884075]) 0) 25 true) .empty .empty)))

#time def treeG_J015_part026 : IntSourceTree :=
  (.node 168 (sourceLit (List.headD (raw_ints% [1486447652886060894708088165275]) 0) 45 false) (.node 159 (sourceLit (List.headD (raw_ints% [1613124256676589754632013634247838395]) 0) 22 true) (.node 158 (sourceLit (List.headD (raw_ints% [24476253779063584017135]) 0) 70 false) (.node 157 (sourceLit (List.headD (raw_ints% [1003885781150914914191143402986372585]) 0) 23 true) .empty .empty) .empty) (.node 167 (sourceLit (List.headD (raw_ints% [52872985290786895297336902603975]) 0) 39 false) .empty .empty)) (.node 170 (sourceLit (List.headD (raw_ints% [175139156909190869826882840675]) 0) 48 false) (.node 169 (sourceLit (List.headD (raw_ints% [10418175653004154704861544198275]) 0) 41 false) .empty .empty) (.node 171 (sourceLit (List.headD (raw_ints% [1066895997104872636034372743275]) 0) 44 false) .empty .empty)))

#time def treeG_J015_part027 : IntSourceTree :=
  (.node 156 (sourceLit (List.headD (raw_ints% [24786912479816537616825]) 0) 70 false) treeG_J015_part025 treeG_J015_part026)

#time def treeG_J015_part028 : IntSourceTree :=
  (.node 147 (sourceLit (List.headD (raw_ints% [3073829978002102202148532231148415]) 0) 33 true) treeG_J015_part024 treeG_J015_part027)

#time def treeG_J015_part029 : IntSourceTree :=
  (.node 128 (sourceLit (List.headD (raw_ints% [1517457653252747135714227367925]) 0) 43 false) treeG_J015_part021 treeG_J015_part028)

#time def treeG_J015_part030 : IntSourceTree :=
  (.node 85 (sourceLit (List.headD (raw_ints% [10146138426650721044677481028675]) 0) 40 false) treeG_J015_part014 treeG_J015_part029)

#time def treeG_J015_part031 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [611419915539191351118092735025]) 0) 48 false) (.node 175 (sourceLit (List.headD (raw_ints% [208377582584464718361415811475]) 0) 46 false) (.node 174 (sourceLit (List.headD (raw_ints% [40296306802863297493028296575]) 0) 50 false) (.node 173 (sourceLit (List.headD (raw_ints% [234039602407286439656459649225]) 0) 46 false) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [5909156335088570898366530996475]) 0) 39 true) .empty .empty)) (.node 180 (sourceLit (List.headD (raw_ints% [6518727796602039835929435170179425]) 0) 36 true) (.node 179 (sourceLit (List.headD (raw_ints% [412855447371189256455170066775]) 0) 50 true) (.node 178 (sourceLit (List.headD (raw_ints% [2130023662332341795965376544566925]) 0) 38 false) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [1182930861048655866575152725]) 0) 55 false) .empty .empty)))

#time def treeG_J015_part032 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [34722276071800273232547375]) 0) 60 false) (.node 185 (sourceLit (List.headD (raw_ints% [566279468834099605059328425]) 0) 56 false) (.node 184 (sourceLit (List.headD (raw_ints% [18427804572642852387857628987061425]) 0) 32 true) (.node 183 (sourceLit (List.headD (raw_ints% [2312640109569255878354052825]) 0) 54 false) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [24925778534133398631105997005047085]) 0) 31 true) .empty .empty)) (.node 189 (sourceLit (List.headD (raw_ints% [17056000287101346355594575]) 0) 61 false) (.node 188 (sourceLit (List.headD (raw_ints% [73065414466348074488185097495793165]) 0) 29 true) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [111964123819153721268350455062647655]) 0) 28 true) .empty .empty)))

#time def treeG_J015_part033 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [4050131043318343850071162982400975]) 0) 35 true) treeG_J015_part031 treeG_J015_part032)

#time def treeG_J015_part034 : IntSourceTree :=
  (.node 196 (sourceLit (List.headD (raw_ints% [7281874886117149458884351626683108015]) 0) 21 true) (.node 194 (sourceLit (List.headD (raw_ints% [2255197951678830908328339238770934785]) 0) 23 true) (.node 193 (sourceLit (List.headD (raw_ints% [4129412638277828557866285]) 0) 63 false) (.node 192 (sourceLit (List.headD (raw_ints% [1409761971047599184854052663296319505]) 0) 24 true) .empty .empty) .empty) (.node 195 (sourceLit (List.headD (raw_ints% [1017361393480989789151815]) 0) 65 false) .empty .empty)) (.node 198 (sourceLit (List.headD (raw_ints% [11800315596378563633679063009580374105]) 0) 20 true) (.node 197 (sourceLit (List.headD (raw_ints% [7838908021511017556805]) 0) 72 false) .empty .empty) (.node 199 (sourceLit (List.headD (raw_ints% [30946482165486453723045]) 0) 70 false) .empty .empty)))

#time def treeG_J015_part035 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [52245494411482214821917434925]) 0) 50 false) (.node 211 (sourceLit (List.headD (raw_ints% [110141917512391452183837444675]) 0) 49 false) (.node 210 (sourceLit (List.headD (raw_ints% [2078534432606704059843857655225]) 0) 44 false) (.node 209 (sourceLit (List.headD (raw_ints% [236233199187741985412650011675]) 0) 48 false) .empty .empty) .empty) (.node 212 (sourceLit (List.headD (raw_ints% [905373893957521400300085236325]) 0) 45 false) .empty .empty)) (.node 215 (sourceLit (List.headD (raw_ints% [25037808529834165912191420075]) 0) 51 false) (.node 214 (sourceLit (List.headD (raw_ints% [405350923927204416950400944475]) 0) 46 false) .empty .empty) (.node 216 (sourceLit (List.headD (raw_ints% [41306934610557434779551258525]) 0) 47 true) .empty .empty)))

#time def treeG_J015_part036 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [40733324064764918211623083660575]) 0) 40 false) treeG_J015_part034 treeG_J015_part035)

#time def treeG_J015_part037 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [16776073390566483074570715]) 0) 61 false) treeG_J015_part033 treeG_J015_part036)

#time def treeG_J015_part038 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [2914489122710729002908794325]) 0) 54 false) (.node 220 (sourceLit (List.headD (raw_ints% [427705964406971619811920395775]) 0) 51 true) (.node 219 (sourceLit (List.headD (raw_ints% [2585590914890431750524402268529775]) 0) 39 false) (.node 218 (sourceLit (List.headD (raw_ints% [501142587111389900147498945775]) 0) 50 false) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [5893417781089727107919041332342675]) 0) 37 true) .empty .empty)) (.node 225 (sourceLit (List.headD (raw_ints% [14296920523089873837174269613378675]) 0) 33 true) (.node 224 (sourceLit (List.headD (raw_ints% [1421584547197517278860366225]) 0) 55 false) (.node 223 (sourceLit (List.headD (raw_ints% [3305738712278721574083848144930325]) 0) 36 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [43437531598202008140813225]) 0) 60 false) .empty .empty)))

#time def treeG_J015_part039 : IntSourceTree :=
  (.node 232 (sourceLit (List.headD (raw_ints% [10255359946870026291711195]) 0) 62 false) (.node 230 (sourceLit (List.headD (raw_ints% [20876075383662206625008475]) 0) 61 false) (.node 229 (sourceLit (List.headD (raw_ints% [54049267307489288448070246047770295]) 0) 30 true) (.node 228 (sourceLit (List.headD (raw_ints% [5319109890861978339153675]) 0) 63 false) .empty .empty) .empty) (.node 231 (sourceLit (List.headD (raw_ints% [81881998282603866686838401643043005]) 0) 29 true) .empty .empty)) (.node 234 (sourceLit (List.headD (raw_ints% [1260937287129302211405465]) 0) 65 false) (.node 233 (sourceLit (List.headD (raw_ints% [1024081231035085766276218550703125235]) 0) 25 true) .empty .empty) (.node 235 (sourceLit (List.headD (raw_ints% [1633208601068902746018749058543166635]) 0) 24 true) .empty .empty)))

#time def treeG_J015_part040 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [18778118578129194226808932542750255]) 0) 32 true) treeG_J015_part038 treeG_J015_part039)

#time def treeG_J015_part041 : IntSourceTree :=
  (.node 250 (sourceLit (List.headD (raw_ints% [297327241466293100998417182675]) 0) 48 false) (.node 239 (sourceLit (List.headD (raw_ints% [8574067083025384124415035741084697315]) 0) 21 true) (.node 238 (sourceLit (List.headD (raw_ints% [38235010393024556437305]) 0) 70 false) (.node 237 (sourceLit (List.headD (raw_ints% [5274103323815319630502064820710362845]) 0) 22 true) .empty .empty) .empty) (.node 249 (sourceLit (List.headD (raw_ints% [7578787102940190876690384865575]) 0) 43 false) .empty .empty)) (.node 252 (sourceLit (List.headD (raw_ints% [68309852766463534304426215725]) 0) 50 false) (.node 251 (sourceLit (List.headD (raw_ints% [3090172868108535483653342567175]) 0) 44 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [167833572887558740160906396775]) 0) 48 false) .empty .empty)))

#time def treeG_J015_part042 : IntSourceTree :=
  (.node 259 (sourceLit (List.headD (raw_ints% [1415140621593969056750167958325]) 0) 50 false) (.node 257 (sourceLit (List.headD (raw_ints% [326363425074874392948821996775]) 0) 49 true) (.node 256 (sourceLit (List.headD (raw_ints% [211018883811490058051038644250875]) 0) 39 false) (.node 255 (sourceLit (List.headD (raw_ints% [602324265269944115539386077475]) 0) 46 false) .empty .empty) .empty) (.node 258 (sourceLit (List.headD (raw_ints% [3794541668215896820432437176354325]) 0) 38 true) .empty .empty)) (.node 261 (sourceLit (List.headD (raw_ints% [437169411295360866744521617575]) 0) 52 true) (.node 260 (sourceLit (List.headD (raw_ints% [47888182434848947844319871466655825]) 0) 36 false) .empty .empty) (.node 262 (sourceLit (List.headD (raw_ints% [43097211205399473013281167676340425]) 0) 35 true) .empty .empty)))

#time def treeG_J015_part043 : IntSourceTree :=
  (.node 254 (sourceLit (List.headD (raw_ints% [64194682020101132150806573275]) 0) 50 false) treeG_J015_part041 treeG_J015_part042)

#time def treeG_J015_part044 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [620770793803925187282615]) 0) 66 false) treeG_J015_part040 treeG_J015_part043)

#time def treeG_J015_part045 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [208064750735444378058382578973425]) 0) 40 true) treeG_J015_part037 treeG_J015_part044)

#time def treeG_J015_part046 : IntSourceTree :=
  (.node 268 (sourceLit (List.headD (raw_ints% [227384482783719033140757823188210915]) 0) 29 true) (.node 266 (sourceLit (List.headD (raw_ints% [89449585650585592066288159901982315]) 0) 31 true) (.node 265 (sourceLit (List.headD (raw_ints% [106913134795427209225129725]) 0) 59 false) (.node 264 (sourceLit (List.headD (raw_ints% [87355834220276237982825511650708975]) 0) 32 true) .empty .empty) .empty) (.node 267 (sourceLit (List.headD (raw_ints% [52152787124603743049079075]) 0) 60 false) .empty .empty)) (.node 271 (sourceLit (List.headD (raw_ints% [24976077376757930175446235]) 0) 61 false) (.node 270 (sourceLit (List.headD (raw_ints% [320430014640760586316211513319514705]) 0) 28 true) (.node 269 (sourceLit (List.headD (raw_ints% [25496878839794480357634825]) 0) 61 false) .empty .empty) .empty) (.node 272 (sourceLit (List.headD (raw_ints% [3830685919039048283103605041858432815]) 0) 24 true) .empty .empty)))

#time def treeG_J015_part047 : IntSourceTree :=
  (.node 278 (sourceLit (List.headD (raw_ints% [30392510994143993410337455556102528655]) 0) 20 true) (.node 276 (sourceLit (List.headD (raw_ints% [18849462730985294477415633310007558145]) 0) 21 true) (.node 275 (sourceLit (List.headD (raw_ints% [1504513180777614633659115]) 0) 65 false) (.node 274 (sourceLit (List.headD (raw_ints% [5937451896601855221881409166854067095]) 0) 23 true) .empty .empty) .empty) (.node 277 (sourceLit (List.headD (raw_ints% [369925737115572625464855]) 0) 67 false) .empty .empty)) (.node 290 (sourceLit (List.headD (raw_ints% [2750126335166743408423263605175]) 0) 45 false) (.node 279 (sourceLit (List.headD (raw_ints% [45523538620562659151565]) 0) 70 false) .empty .empty) (.node 291 (sourceLit (List.headD (raw_ints% [11699082747118853050911233625]) 0) 53 false) .empty .empty)))

#time def treeG_J015_part048 : IntSourceTree :=
  (.node 273 (sourceLit (List.headD (raw_ints% [3062973654296098866922455]) 0) 64 false) treeG_J015_part046 treeG_J015_part047)

#time def treeG_J015_part049 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [104770908636733609027355305806075]) 0) 42 false) (.node 295 (sourceLit (List.headD (raw_ints% [2447304593141685389913447075]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [937317659173265504336850229725]) 0) 46 false) (.node 293 (sourceLit (List.headD (raw_ints% [84374211121444853786934996525]) 0) 50 false) .empty .empty) .empty) (.node 296 (sourceLit (List.headD (raw_ints% [10056737498132836723733395875]) 0) 53 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [1595033145776582142739209861221025]) 0) 41 true) (.node 298 (sourceLit (List.headD (raw_ints% [413753006093132146548160471275]) 0) 51 true) .empty .empty) (.node 300 (sourceLit (List.headD (raw_ints% [460711646500235169140522088525]) 0) 53 false) .empty .empty)))

#time def treeG_J015_part050 : IntSourceTree :=
  (.node 306 (sourceLit (List.headD (raw_ints% [15868900799306300271079125]) 0) 62 false) (.node 304 (sourceLit (List.headD (raw_ints% [32730524822729450759424525]) 0) 61 false) (.node 303 (sourceLit (List.headD (raw_ints% [9947868123280187859799329882852525]) 0) 38 true) (.node 302 (sourceLit (List.headD (raw_ints% [442998389540782324750339206225]) 0) 53 true) .empty .empty) .empty) (.node 305 (sourceLit (List.headD (raw_ints% [18264728424296591036412810509332575]) 0) 35 true) .empty .empty)) (.node 308 (sourceLit (List.headD (raw_ints% [30876347561155829692464375]) 0) 61 false) (.node 307 (sourceLit (List.headD (raw_ints% [17667866768114099459869806839808015]) 0) 34 true) .empty .empty) (.node 309 (sourceLit (List.headD (raw_ints% [43333803869057436173171894285110155]) 0) 32 true) .empty .empty)))

#time def treeG_J015_part051 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [13445400053984668738059728199749625]) 0) 39 false) treeG_J015_part049 treeG_J015_part050)

#time def treeG_J015_part052 : IntSourceTree :=
  (.node 292 (sourceLit (List.headD (raw_ints% [1092399487075507041676628665425]) 0) 46 false) treeG_J015_part048 treeG_J015_part051)

#time def treeG_J015_part053 : IntSourceTree :=
  (.node 315 (sourceLit (List.headD (raw_ints% [1076060823883238118965665027077725115]) 0) 26 true) (.node 313 (sourceLit (List.headD (raw_ints% [701651172000990629206846622788826895]) 0) 27 true) (.node 312 (sourceLit (List.headD (raw_ints% [3593925153781226534115]) 0) 74 false) (.node 311 (sourceLit (List.headD (raw_ints% [59637004089539179907343277919117925]) 0) 31 true) .empty .empty) .empty) (.node 314 (sourceLit (List.headD (raw_ints% [901018183583398327758495]) 0) 66 false) .empty .empty)) (.node 318 (sourceLit (List.headD (raw_ints% [216985695543474399715635]) 0) 68 false) (.node 317 (sourceLit (List.headD (raw_ints% [3393839851792493711728392122324298825]) 0) 24 true) (.node 316 (sourceLit (List.headD (raw_ints% [220935596743422361594125]) 0) 68 false) .empty .empty) .empty) (.node 319 (sourceLit (List.headD (raw_ints% [5454610977779652321480604953754457835]) 0) 23 true) .empty .empty)))

#time def treeG_J015_part054 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [109754223820776929375696690763525]) 0) 39 false) (.node 334 (sourceLit (List.headD (raw_ints% [104553740222788575423063419775]) 0) 50 false) (.node 333 (sourceLit (List.headD (raw_ints% [756732341300389561354815871875]) 0) 47 false) (.node 332 (sourceLit (List.headD (raw_ints% [118875471187438114510153522275]) 0) 50 false) .empty .empty) .empty) (.node 335 (sourceLit (List.headD (raw_ints% [1272311053076586893134314381975]) 0) 46 false) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [7147210744591372309307806962148725]) 0) 38 false) (.node 337 (sourceLit (List.headD (raw_ints% [648179025015125168108290664775]) 0) 49 false) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [3070152645966497642942809843425]) 0) 50 true) .empty .empty)))

#time def treeG_J015_part055 : IntSourceTree :=
  (.node 331 (sourceLit (List.headD (raw_ints% [7910332472558438150039711853525]) 0) 44 false) treeG_J015_part053 treeG_J015_part054)

#time def treeG_J015_part056 : IntSourceTree :=
  (.node 345 (sourceLit (List.headD (raw_ints% [154931063786408396850266475]) 0) 59 false) (.node 343 (sourceLit (List.headD (raw_ints% [223257363838317263438901371025]) 0) 55 true) (.node 342 (sourceLit (List.headD (raw_ints% [473350012932908872631192470068328425]) 0) 35 false) (.node 341 (sourceLit (List.headD (raw_ints% [2280015997296301543306609971675]) 0) 52 false) .empty .empty) .empty) (.node 344 (sourceLit (List.headD (raw_ints% [1185971285559587808071488713354414225]) 0) 32 true) .empty .empty)) (.node 347 (sourceLit (List.headD (raw_ints% [74798419269846659119553925]) 0) 60 false) (.node 346 (sourceLit (List.headD (raw_ints% [495021723926905321098921776396660085]) 0) 31 true) .empty .empty) (.node 348 (sourceLit (List.headD (raw_ints% [903358990375583332290909814559502045]) 0) 29 true) .empty .empty)))

#time def treeG_J015_part057 : IntSourceTree :=
  (.node 354 (sourceLit (List.headD (raw_ints% [16515385607429844912737682762388393545]) 0) 23 true) (.node 352 (sourceLit (List.headD (raw_ints% [11436387127882981773176274105435755985]) 0) 24 true) (.node 351 (sourceLit (List.headD (raw_ints% [35259287215095578005076115]) 0) 61 false) (.node 350 (sourceLit (List.headD (raw_ints% [1066251709169077371225289103804010255]) 0) 28 true) .empty .empty) .empty) (.node 353 (sourceLit (List.headD (raw_ints% [4297385060647853074945065]) 0) 64 false) .empty .empty)) (.node 356 (sourceLit (List.headD (raw_ints% [50018429997541945136386928422966849215]) 0) 21 true) (.node 355 (sourceLit (List.headD (raw_ints% [2099559553555978677374865]) 0) 65 false) .empty .empty) (.node 357 (sourceLit (List.headD (raw_ints% [513816649858116820911645]) 0) 67 false) .empty .empty)))

#time def treeG_J015_part058 : IntSourceTree :=
  (.node 349 (sourceLit (List.headD (raw_ints% [36255816282517179027293925]) 0) 61 false) treeG_J015_part056 treeG_J015_part057)

#time def treeG_J015_part059 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [149970303764550204979629302584801425]) 0) 36 true) treeG_J015_part055 treeG_J015_part058)

#time def treeG_J015_part060 : IntSourceTree :=
  (.node 310 (sourceLit (List.headD (raw_ints% [30117682295926754090261175]) 0) 61 false) treeG_J015_part052 treeG_J015_part059)

#time def treeG_J015_part061 : IntSourceTree :=
  (.node 263 (sourceLit (List.headD (raw_ints% [3516338135852202127463535825]) 0) 54 false) treeG_J015_part045 treeG_J015_part060)

#time def treeG_J015_part062 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [20916032372963958939705614475]) 0) 51 false) treeG_J015_part030 treeG_J015_part061)

#time def treeG_J015_part063 : IntSourceTree :=
  (.node 375 (sourceLit (List.headD (raw_ints% [65396866732521609184448266575]) 0) 51 false) (.node 373 (sourceLit (List.headD (raw_ints% [153376731253431375233372048025]) 0) 50 false) (.node 372 (sourceLit (List.headD (raw_ints% [5725533498407424066686454522675]) 0) 45 false) (.node 359 (sourceLit (List.headD (raw_ints% [125938618302349081412505]) 0) 69 false) .empty .empty) .empty) (.node 374 (sourceLit (List.headD (raw_ints% [2089611706028292741082413257775]) 0) 46 false) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [1475685037201389461204611607325]) 0) 50 false) (.node 377 (sourceLit (List.headD (raw_ints% [309329410726157506733724532460775]) 0) 40 true) (.node 376 (sourceLit (List.headD (raw_ints% [628679853196085342815377045975]) 0) 47 false) .empty .empty) .empty) (.node 379 (sourceLit (List.headD (raw_ints% [13527343327697700880264646407032825]) 0) 39 false) .empty .empty)))

#time def treeG_J015_part064 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [1112912371862401443925837471317083925]) 0) 33 true) (.node 383 (sourceLit (List.headD (raw_ints% [513141485426029624070389789599738525]) 0) 36 false) (.node 382 (sourceLit (List.headD (raw_ints% [680753596709270967014237294475]) 0) 55 false) (.node 381 (sourceLit (List.headD (raw_ints% [203751903980488879931868215383799925]) 0) 37 true) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [224304740632644605863202955825]) 0) 56 true) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [424350256854448923259442549037428025]) 0) 32 true) (.node 386 (sourceLit (List.headD (raw_ints% [91455460589183195765949975]) 0) 60 false) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [21961035854345414713544775]) 0) 62 false) .empty .empty)))

#time def treeG_J015_part065 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [4912999231967438319504898197525]) 0) 51 true) treeG_J015_part063 treeG_J015_part064)

#time def treeG_J015_part066 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [2495348693481056419428075]) 0) 65 false) (.node 392 (sourceLit (List.headD (raw_ints% [20538569785207674121341075]) 0) 62 false) (.node 391 (sourceLit (List.headD (raw_ints% [827703692810920651595915992127538555]) 0) 29 true) (.node 390 (sourceLit (List.headD (raw_ints% [42393950269107603964326675]) 0) 61 false) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [8629782439879019256348887614280448405]) 0) 25 true) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [1215817166582289230998365]) 0) 66 false) (.node 395 (sourceLit (List.headD (raw_ints% [12211142311896892436875022654077493085]) 0) 24 true) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [36443070590371970289473359933669653915]) 0) 22 true) .empty .empty)))

#time def treeG_J015_part067 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [425976908452040093063303509018875]) 0) 39 false) (.node 414 (sourceLit (List.headD (raw_ints% [202199722284074175043680676275]) 0) 50 false) (.node 413 (sourceLit (List.headD (raw_ints% [4212068815806644943976822778925]) 0) 46 false) (.node 399 (sourceLit (List.headD (raw_ints% [56391920352097196079048672543257202405]) 0) 21 true) .empty .empty) .empty) (.node 415 (sourceLit (List.headD (raw_ints% [2906912358979998589030512133575]) 0) 46 false) .empty .empty)) (.node 418 (sourceLit (List.headD (raw_ints% [9621846030400632363177603221834925]) 0) 38 true) (.node 417 (sourceLit (List.headD (raw_ints% [667678196834164993401204283575]) 0) 48 true) .empty .empty) (.node 419 (sourceLit (List.headD (raw_ints% [6021522720369276565352033058075]) 0) 50 false) .empty .empty)))

#time def treeG_J015_part068 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [148415477157321210598005]) 0) 69 false) treeG_J015_part066 treeG_J015_part067)

#time def treeG_J015_part069 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [730023774899353587598222237419061425]) 0) 30 true) treeG_J015_part065 treeG_J015_part068)

#time def treeG_J015_part070 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [224924464887790239450604021725]) 0) 57 true) (.node 423 (sourceLit (List.headD (raw_ints% [1584764557256859197467375959975]) 0) 55 false) (.node 422 (sourceLit (List.headD (raw_ints% [2103365244776819912086138193138727825]) 0) 35 true) (.node 421 (sourceLit (List.headD (raw_ints% [449563451828983741425719260575]) 0) 56 true) .empty .empty) .empty) (.node 424 (sourceLit (List.headD (raw_ints% [17606498819192535778323961980546047025]) 0) 32 false) .empty .empty)) (.node 428 (sourceLit (List.headD (raw_ints% [5886245119295599439860170970039346355]) 0) 29 true) (.node 427 (sourceLit (List.headD (raw_ints% [108112501908519732412346025]) 0) 60 false) (.node 426 (sourceLit (List.headD (raw_ints% [8408277250972306230307777994140011315]) 0) 31 true) .empty .empty) .empty) (.node 429 (sourceLit (List.headD (raw_ints% [51588327134864479826885175]) 0) 61 false) .empty .empty)))

#time def treeG_J015_part071 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [2891137833406134161481285]) 0) 65 false) (.node 433 (sourceLit (List.headD (raw_ints% [11943799663911967971450945]) 0) 63 false) (.node 432 (sourceLit (List.headD (raw_ints% [41536649212015939928962349390726711535]) 0) 24 true) (.node 431 (sourceLit (List.headD (raw_ints% [49528613323119629923577235]) 0) 61 false) .empty .empty) .empty) (.node 434 (sourceLit (List.headD (raw_ints% [52522873911602309138053418151855193695]) 0) 23 true) .empty .empty)) (.node 437 (sourceLit (List.headD (raw_ints% [10968758073815193907605]) 0) 73 false) (.node 436 (sourceLit (List.headD (raw_ints% [145359846992808333853613434042273040145]) 0) 21 true) .empty .empty) (.node 438 (sourceLit (List.headD (raw_ints% [213334200459759956950815787111082197575]) 0) 20 true) .empty .empty)))

#time def treeG_J015_part072 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [4773938490025751329560488795548481145]) 0) 28 true) treeG_J015_part070 treeG_J015_part071)

#time def treeG_J015_part073 : IntSourceTree :=
  (.node 458 (sourceLit (List.headD (raw_ints% [3619048271236943915810427498225]) 0) 49 true) (.node 456 (sourceLit (List.headD (raw_ints% [142389531611494577888445942975]) 0) 51 false) (.node 455 (sourceLit (List.headD (raw_ints% [34200713887888141464808102425]) 0) 53 false) (.node 454 (sourceLit (List.headD (raw_ints% [6334525925584997146871232300075]) 0) 46 false) .empty .empty) .empty) (.node 457 (sourceLit (List.headD (raw_ints% [367653159589098799898514020739825]) 0) 41 false) .empty .empty)) (.node 460 (sourceLit (List.headD (raw_ints% [683407622021044680303558203475]) 0) 55 false) (.node 459 (sourceLit (List.headD (raw_ints% [11574594679049166621721124814433875]) 0) 40 true) .empty .empty) (.node 461 (sourceLit (List.headD (raw_ints% [285079850494101149497865930240563275]) 0) 38 false) .empty .empty)))

#time def treeG_J015_part074 : IntSourceTree :=
  (.node 467 (sourceLit (List.headD (raw_ints% [3991963497058928653524167722551291645]) 0) 33 true) (.node 465 (sourceLit (List.headD (raw_ints% [9359705595527468611124899725931565475]) 0) 34 false) (.node 464 (sourceLit (List.headD (raw_ints% [226133662236187975416322364475]) 0) 59 false) (.node 463 (sourceLit (List.headD (raw_ints% [1308253365101424768078263991369233175]) 0) 37 true) .empty .empty) .empty) (.node 466 (sourceLit (List.headD (raw_ints% [225290286730146972233667821625]) 0) 58 true) .empty .empty)) (.node 469 (sourceLit (List.headD (raw_ints% [2578110672198122926130974366310142465]) 0) 31 true) (.node 468 (sourceLit (List.headD (raw_ints% [64190430199828902985256475]) 0) 61 false) .empty .empty) (.node 470 (sourceLit (List.headD (raw_ints% [60782704000621355689443675]) 0) 61 false) .empty .empty)))

#time def treeG_J015_part075 : IntSourceTree :=
  (.node 462 (sourceLit (List.headD (raw_ints% [2479007404025205932717114336775]) 0) 55 true) treeG_J015_part073 treeG_J015_part074)

#time def treeG_J015_part076 : IntSourceTree :=
  (.node 439 (sourceLit (List.headD (raw_ints% [170892336012293339783505]) 0) 69 false) treeG_J015_part072 treeG_J015_part075)

#time def treeG_J015_part077 : IntSourceTree :=
  (.node 420 (sourceLit (List.headD (raw_ints% [366407797007713419063863645097326625]) 0) 36 false) treeG_J015_part069 treeG_J015_part076)

#time def treeG_J015_part078 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [209415083352980616310365]) 0) 69 false) (.node 474 (sourceLit (List.headD (raw_ints% [6953102276949855132594795]) 0) 64 false) (.node 473 (sourceLit (List.headD (raw_ints% [16453433386068460336306730888223131565]) 0) 26 true) (.node 472 (sourceLit (List.headD (raw_ints% [113242357569968577352485]) 0) 70 false) .empty .empty) .empty) (.node 475 (sourceLit (List.headD (raw_ints% [20155865799852708350589197748888850305]) 0) 25 true) .empty .empty)) (.node 479 (sourceLit (List.headD (raw_ints% [78471140053831380435883557283912497585]) 0) 22 true) (.node 478 (sourceLit (List.headD (raw_ints% [202584781204764994445355]) 0) 69 false) (.node 477 (sourceLit (List.headD (raw_ints% [54458388201218181782070037054301693115]) 0) 23 true) .empty .empty) .empty) (.node 495 (sourceLit (List.headD (raw_ints% [9762139492189995704711952466575]) 0) 46 false) .empty .empty)))

#time def treeG_J015_part079 : IntSourceTree :=
  (.node 501 (sourceLit (List.headD (raw_ints% [566485536925014210864638732025]) 0) 57 false) (.node 499 (sourceLit (List.headD (raw_ints% [2410142747901555120290615139075]) 0) 52 true) (.node 498 (sourceLit (List.headD (raw_ints% [15504296583826213161553827553672125]) 0) 38 false) (.node 497 (sourceLit (List.headD (raw_ints% [2945910702618078239616339371175]) 0) 48 false) .empty .empty) .empty) (.node 500 (sourceLit (List.headD (raw_ints% [736794826737286750958939639159210625]) 0) 36 true) .empty .empty)) (.node 503 (sourceLit (List.headD (raw_ints% [6542779365307271062901604633525]) 0) 55 true) (.node 502 (sourceLit (List.headD (raw_ints% [6664642852682438304051993076987740225]) 0) 35 false) .empty .empty) (.node 504 (sourceLit (List.headD (raw_ints% [101334714185683720935332857428176970225]) 0) 32 true) .empty .empty)))

#time def treeG_J015_part080 : IntSourceTree :=
  (.node 496 (sourceLit (List.headD (raw_ints% [694712084226278526455528391243525]) 0) 39 false) treeG_J015_part078 treeG_J015_part079)

#time def treeG_J015_part081 : IntSourceTree :=
  (.node 510 (sourceLit (List.headD (raw_ints% [36475832265144215488535101065413798295]) 0) 28 true) (.node 508 (sourceLit (List.headD (raw_ints% [121856586786590117472913196151601986285]) 0) 29 true) (.node 507 (sourceLit (List.headD (raw_ints% [225506511733964011698492513675]) 0) 59 true) (.node 506 (sourceLit (List.headD (raw_ints% [158163566779411804008306173609045058915]) 0) 31 false) .empty .empty) .empty) (.node 509 (sourceLit (List.headD (raw_ints% [76792533264793326143627775]) 0) 61 false) .empty .empty)) (.node 512 (sourceLit (List.headD (raw_ints% [211022377809733223460770310028213614225]) 0) 24 true) (.node 511 (sourceLit (List.headD (raw_ints% [72036794678123081455310115]) 0) 61 false) .empty .empty) (.node 513 (sourceLit (List.headD (raw_ints% [17046243873999987830785215]) 0) 63 false) .empty .empty)))

#time def treeG_J015_part082 : IntSourceTree :=
  (.node 519 (sourceLit (List.headD (raw_ints% [234277226397236649107205]) 0) 69 false) (.node 517 (sourceLit (List.headD (raw_ints% [121665018762459065049525]) 0) 70 false) (.node 516 (sourceLit (List.headD (raw_ints% [499627858602478333365240893922170169615]) 0) 21 true) (.node 515 (sourceLit (List.headD (raw_ints% [2030982221771860485556755]) 0) 66 false) .empty .empty) .empty) (.node 518 (sourceLit (List.headD (raw_ints% [658000010759730951562304805757744892265]) 0) 20 true) .empty .empty)) (.node 538 (sourceLit (List.headD (raw_ints% [820619871731877769428345858675]) 0) 52 false) (.node 537 (sourceLit (List.headD (raw_ints% [40594234951919073341499650236125]) 0) 40 true) .empty .empty) (.node 539 (sourceLit (List.headD (raw_ints% [38653485941924546404996077182539875]) 0) 39 false) .empty .empty)))

#time def treeG_J015_part083 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [210732060265493056242854276059714911345]) 0) 23 true) treeG_J015_part081 treeG_J015_part082)

#time def treeG_J015_part084 : IntSourceTree :=
  (.node 505 (sourceLit (List.headD (raw_ints% [2033993762777294042781182937525]) 0) 57 false) treeG_J015_part080 treeG_J015_part083)

#time def treeG_J015_part085 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [120054125376738658157582656880040101175]) 0) 33 true) (.node 543 (sourceLit (List.headD (raw_ints% [9281149582885287840208521059726206575]) 0) 36 false) (.node 542 (sourceLit (List.headD (raw_ints% [7010891699425319619634224192975]) 0) 55 false) (.node 541 (sourceLit (List.headD (raw_ints% [1306954527725489049954671499640337175]) 0) 37 true) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [8351848663196774866232183549325]) 0) 56 true) .empty .empty)) (.node 548 (sourceLit (List.headD (raw_ints% [225634892594363669504463026625]) 0) 60 true) (.node 547 (sourceLit (List.headD (raw_ints% [166147493773529661315354509054147642205]) 0) 32 false) (.node 546 (sourceLit (List.headD (raw_ints% [1129642024753720507507425379575]) 0) 59 false) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [116700365442193871620651247418981701355]) 0) 30 true) .empty .empty)))

#time def treeG_J015_part086 : IntSourceTree :=
  (.node 555 (sourceLit (List.headD (raw_ints% [170420328665787639541675880561937210735]) 0) 24 true) (.node 553 (sourceLit (List.headD (raw_ints% [178115511037596302788156848251767351095]) 0) 25 true) (.node 552 (sourceLit (List.headD (raw_ints% [43046751140211125653073955]) 0) 62 false) (.node 551 (sourceLit (List.headD (raw_ints% [32529597467929384810570528261992855705]) 0) 29 true) .empty .empty) .empty) (.node 554 (sourceLit (List.headD (raw_ints% [2523285399262533174547605]) 0) 66 false) .empty .empty)) (.node 557 (sourceLit (List.headD (raw_ints% [390711082200041969801100819813566783385]) 0) 22 true) (.node 556 (sourceLit (List.headD (raw_ints% [1193321888359938020315295]) 0) 67 false) .empty .empty) (.node 558 (sourceLit (List.headD (raw_ints% [284075293845071265752745]) 0) 69 false) .empty .empty)))

#time def treeG_J015_part087 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [92802362528965296597811875]) 0) 61 false) treeG_J015_part085 treeG_J015_part086)

#time def treeG_J015_part088 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [398331500838012931822005531339415580625]) 0) 32 false) (.node 582 (sourceLit (List.headD (raw_ints% [17120279074486350703689365074110437625]) 0) 35 true) (.node 581 (sourceLit (List.headD (raw_ints% [9675657531385847528421957809175]) 0) 54 true) (.node 580 (sourceLit (List.headD (raw_ints% [1355250601808079493438876874079848625]) 0) 36 false) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [20564562764157910302170053019475]) 0) 55 false) .empty .empty)) (.node 586 (sourceLit (List.headD (raw_ints% [1118596569793321069268967428649365868315]) 0) 31 true) (.node 585 (sourceLit (List.headD (raw_ints% [5192921212987034454506683243425]) 0) 58 true) .empty .empty) (.node 587 (sourceLit (List.headD (raw_ints% [2484790561241405026713343272825]) 0) 59 false) .empty .empty)))

#time def treeG_J015_part089 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [6500126816552784455572185]) 0) 65 false) (.node 591 (sourceLit (List.headD (raw_ints% [113567930379807511740313635]) 0) 61 false) (.node 590 (sourceLit (List.headD (raw_ints% [897127091272406757476674878286439812545]) 0) 28 true) (.node 589 (sourceLit (List.headD (raw_ints% [3526745080119194731728228975]) 0) 67 true) .empty .empty) .empty) (.node 592 (sourceLit (List.headD (raw_ints% [1870871860137747404415743498739329150895]) 0) 24 true) .empty .empty)) (.node 595 (sourceLit (List.headD (raw_ints% [3015588576753205863538455]) 0) 66 false) (.node 594 (sourceLit (List.headD (raw_ints% [1214192028035277366062400509954423897415]) 0) 23 true) .empty .empty) (.node 596 (sourceLit (List.headD (raw_ints% [2227097400050123899301573195068825202145]) 0) 21 true) .empty .empty)))

#time def treeG_J015_part090 : IntSourceTree :=
  (.node 588 (sourceLit (List.headD (raw_ints% [2780216487163064698518585341017964261565]) 0) 29 false) treeG_J015_part088 treeG_J015_part089)

#time def treeG_J015_part091 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [501057730652068190690537691189919897095]) 0) 21 true) treeG_J015_part087 treeG_J015_part090)

#time def treeG_J015_part092 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [5143773235985733841504847952975]) 0) 53 true) treeG_J015_part084 treeG_J015_part091)

#time def treeG_J015_part093 : IntSourceTree :=
  (.node 471 (sourceLit (List.headD (raw_ints% [1973117398607415338982286401710471295]) 0) 30 true) treeG_J015_part077 treeG_J015_part092)

#time def treeG_J015_part094 : IntSourceTree :=
  (.node 623 (sourceLit (List.headD (raw_ints% [3300178582171454817987235766729580525]) 0) 39 true) (.node 621 (sourceLit (List.headD (raw_ints% [332775641191696067924193546715023225]) 0) 40 false) (.node 599 (sourceLit (List.headD (raw_ints% [333873361292905882398285]) 0) 69 false) (.node 598 (sourceLit (List.headD (raw_ints% [2467688646840604806846501752750789374815]) 0) 20 true) .empty .empty) .empty) (.node 622 (sourceLit (List.headD (raw_ints% [8343274615405583574028091001075]) 0) 56 true) .empty .empty)) (.node 626 (sourceLit (List.headD (raw_ints% [790320404717594370251763577875]) 0) 62 true) (.node 625 (sourceLit (List.headD (raw_ints% [64798203276843948747448523527431960225]) 0) 36 false) (.node 624 (sourceLit (List.headD (raw_ints% [903637857104833911512569892775]) 0) 61 false) .empty .empty) .empty) (.node 627 (sourceLit (List.headD (raw_ints% [160593007945856341323040242212939188815]) 0) 35 true) .empty .empty)))

#time def treeG_J015_part095 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [211594543637518887703448331310945224975]) 0) 28 true) (.node 631 (sourceLit (List.headD (raw_ints% [108074686725559671583263043753055869605]) 0) 32 true) (.node 630 (sourceLit (List.headD (raw_ints% [451516172617785890957811120675]) 0) 61 true) (.node 629 (sourceLit (List.headD (raw_ints% [362114606575657321267404573554618245365]) 0) 33 false) .empty .empty) .empty) (.node 632 (sourceLit (List.headD (raw_ints% [2152135596911510805885]) 0) 77 false) .empty .empty)) (.node 635 (sourceLit (List.headD (raw_ints% [130471462421186215815090578674060835835]) 0) 27 true) (.node 634 (sourceLit (List.headD (raw_ints% [994210354322562820256145]) 0) 68 false) .empty .empty) (.node 636 (sourceLit (List.headD (raw_ints% [227783336049158480402895]) 0) 70 false) .empty .empty)))

#time def treeG_J015_part096 : IntSourceTree :=
  (.node 628 (sourceLit (List.headD (raw_ints% [1355212726917884348108903149725]) 0) 61 false) treeG_J015_part094 treeG_J015_part095)

#time def treeG_J015_part097 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [19651126926664377038707801527825]) 0) 58 false) (.node 663 (sourceLit (List.headD (raw_ints% [53937661225780244598282417023775]) 0) 55 true) (.node 639 (sourceLit (List.headD (raw_ints% [245828864523567077019495507695108684715]) 0) 24 true) (.node 638 (sourceLit (List.headD (raw_ints% [211293259732515247182225]) 0) 70 false) .empty .empty) .empty) (.node 664 (sourceLit (List.headD (raw_ints% [1243177217873905365226737887622188195025]) 0) 32 true) .empty .empty)) (.node 667 (sourceLit (List.headD (raw_ints% [15129917036722914950741560518825]) 0) 59 true) (.node 666 (sourceLit (List.headD (raw_ints% [5265681579511333789105672934405011322715]) 0) 31 false) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [23336121504232676387867736344274180429885]) 0) 29 true) .empty .empty)))

#time def treeG_J015_part098 : IntSourceTree :=
  (.node 674 (sourceLit (List.headD (raw_ints% [12327858764765931446958292693946070500985]) 0) 23 true) (.node 672 (sourceLit (List.headD (raw_ints% [53463367743348804446214934902825276086865]) 0) 24 true) (.node 671 (sourceLit (List.headD (raw_ints% [903145913165951589427362554985]) 0) 61 true) (.node 670 (sourceLit (List.headD (raw_ints% [24072461912114475318590567585782007515905]) 0) 28 false) .empty .empty) .empty) (.node 673 (sourceLit (List.headD (raw_ints% [11130167993346312066237735]) 0) 65 false) .empty .empty)) (.node 676 (sourceLit (List.headD (raw_ints% [14473249789861711725030020875210961784735]) 0) 21 true) (.node 675 (sourceLit (List.headD (raw_ints% [4938094257827296698510705]) 0) 66 false) .empty .empty) (.node 677 (sourceLit (List.headD (raw_ints% [1115604875083166083105965]) 0) 68 false) .empty .empty)))

#time def treeG_J015_part099 : IntSourceTree :=
  (.node 669 (sourceLit (List.headD (raw_ints% [1468068569481698579524206476925]) 0) 62 false) treeG_J015_part097 treeG_J015_part098)

#time def treeG_J015_part100 : IntSourceTree :=
  (.node 637 (sourceLit (List.headD (raw_ints% [229548289731260241187559046906907302345]) 0) 25 true) treeG_J015_part096 treeG_J015_part099)

#time def treeG_J015_part101 : IntSourceTree :=
  (.node 707 (sourceLit (List.headD (raw_ints% [6550425643078184519689994872108524833235]) 0) 32 false) (.node 705 (sourceLit (List.headD (raw_ints% [1761562844088656955206326075841643876825]) 0) 33 true) (.node 704 (sourceLit (List.headD (raw_ints% [82854072653134929766684653592575]) 0) 56 true) (.node 679 (sourceLit (List.headD (raw_ints% [511299677637155106330615]) 0) 69 false) .empty .empty) .empty) (.node 706 (sourceLit (List.headD (raw_ints% [25973690164405132000721910150825]) 0) 59 false) .empty .empty)) (.node 710 (sourceLit (List.headD (raw_ints% [6323790450544580209054637028375]) 0) 61 false) (.node 709 (sourceLit (List.headD (raw_ints% [26233038356837934958006972932711126392805]) 0) 30 true) (.node 708 (sourceLit (List.headD (raw_ints% [17840342490558683646959366818275]) 0) 60 true) .empty .empty) .empty) (.node 711 (sourceLit (List.headD (raw_ints% [24937059405918952691256671935806454472745]) 0) 29 false) .empty .empty)))

#time def treeG_J015_part102 : IntSourceTree :=
  (.node 717 (sourceLit (List.headD (raw_ints% [12636863472011629795529548499955703365975]) 0) 22 true) (.node 715 (sourceLit (List.headD (raw_ints% [11284087065396441720437568064553583814305]) 0) 24 true) (.node 714 (sourceLit (List.headD (raw_ints% [7153326576056060785213155]) 0) 66 false) (.node 713 (sourceLit (List.headD (raw_ints% [51770611394248653344587348252337714287065]) 0) 25 true) .empty .empty) .empty) (.node 716 (sourceLit (List.headD (raw_ints% [3115827569434028855287545]) 0) 67 false) .empty .empty)) (.node 719 (sourceLit (List.headD (raw_ints% [10256770979771514013001313187730408497545]) 0) 21 true) (.node 718 (sourceLit (List.headD (raw_ints% [693018355618135588741515]) 0) 69 false) .empty .empty) (.node 745 (sourceLit (List.headD (raw_ints% [122156326506463683844100256648225]) 0) 57 true) .empty .empty)))

#time def treeG_J015_part103 : IntSourceTree :=
  (.node 712 (sourceLit (List.headD (raw_ints% [903216434345191185813449794665]) 0) 62 true) treeG_J015_part101 treeG_J015_part102)

#time def treeG_J015_part104 : IntSourceTree :=
  (.node 751 (sourceLit (List.headD (raw_ints% [13550726814255112007536636611735]) 0) 61 false) (.node 749 (sourceLit (List.headD (raw_ints% [20776479629522080806007779772125]) 0) 61 true) (.node 748 (sourceLit (List.headD (raw_ints% [128142931793483628702907654298010577761645]) 0) 29 false) (.node 747 (sourceLit (List.headD (raw_ints% [67077297365533178952185380820475]) 0) 59 false) .empty .empty) .empty) (.node 750 (sourceLit (List.headD (raw_ints% [233936768766817954982646351047471018658345]) 0) 28 true) .empty .empty)) (.node 753 (sourceLit (List.headD (raw_ints% [903260955017164571061714745605]) 0) 63 true) (.node 752 (sourceLit (List.headD (raw_ints% [1649435169722161776686641938794438362342545]) 0) 24 false) .empty .empty) (.node 754 (sourceLit (List.headD (raw_ints% [401837032389223295309740493324755643795535]) 0) 23 true) .empty .empty)))

#time def treeG_J015_part105 : IntSourceTree :=
  (.node 786 (sourceLit (List.headD (raw_ints% [174103706835273947845544076949875]) 0) 58 true) (.node 758 (sourceLit (List.headD (raw_ints% [88871505880132987735079110750354348952535]) 0) 20 true) (.node 757 (sourceLit (List.headD (raw_ints% [500055673587715693045395]) 0) 70 false) (.node 756 (sourceLit (List.headD (raw_ints% [166072143256481355801971068157646379244145]) 0) 21 true) .empty .empty) .empty) (.node 759 (sourceLit (List.headD (raw_ints% [874737033599116071152415]) 0) 69 false) .empty .empty)) (.node 788 (sourceLit (List.headD (raw_ints% [42458819928045931299572373819375]) 0) 61 false) (.node 787 (sourceLit (List.headD (raw_ints% [12954304987649386975223138206623343585275]) 0) 33 true) .empty .empty) (.node 789 (sourceLit (List.headD (raw_ints% [77187985075160781830457313615360852077225]) 0) 31 false) .empty .empty)))

#time def treeG_J015_part106 : IntSourceTree :=
  (.node 755 (sourceLit (List.headD (raw_ints% [9368558894284824871915605]) 0) 66 false) treeG_J015_part104 treeG_J015_part105)

#time def treeG_J015_part107 : IntSourceTree :=
  (.node 746 (sourceLit (List.headD (raw_ints% [19358184332220589430756281541138162337315]) 0) 31 true) treeG_J015_part103 treeG_J015_part106)

#time def treeG_J015_part108 : IntSourceTree :=
  (.node 678 (sourceLit (List.headD (raw_ints% [12223401895960050629157277249291277975265]) 0) 20 true) treeG_J015_part100 treeG_J015_part107)

#time def treeG_J015_part109 : IntSourceTree :=
  (.node 795 (sourceLit (List.headD (raw_ints% [195276472661913426794651462630101029990615]) 0) 25 true) (.node 793 (sourceLit (List.headD (raw_ints% [850602890558205215015614643523388038314805]) 0) 26 false) (.node 792 (sourceLit (List.headD (raw_ints% [56460715814844934349023775025]) 0) 70 false) (.node 791 (sourceLit (List.headD (raw_ints% [129436914086368453836951511491638736565545]) 0) 30 true) .empty .empty) .empty) (.node 794 (sourceLit (List.headD (raw_ints% [903289568323468795304855598225]) 0) 64 true) .empty .empty)) (.node 798 (sourceLit (List.headD (raw_ints% [1307204338732727183440065]) 0) 69 false) (.node 797 (sourceLit (List.headD (raw_ints% [76717639892234863003220759828845337939085]) 0) 23 true) (.node 796 (sourceLit (List.headD (raw_ints% [1563182831212699004157015]) 0) 69 false) .empty .empty) .empty) (.node 799 (sourceLit (List.headD (raw_ints% [39307367450180736861038898781311970227495]) 0) 22 true) .empty .empty)))

#time def treeG_J015_part110 : IntSourceTree :=
  (.node 832 (sourceLit (List.headD (raw_ints% [18217360172777323867816435409724196642732305]) 0) 24 true) (.node 830 (sourceLit (List.headD (raw_ints% [1468944529969390464269963368893244651893945]) 0) 28 false) (.node 829 (sourceLit (List.headD (raw_ints% [105694119485613943405152527410875]) 0) 61 false) (.node 828 (sourceLit (List.headD (raw_ints% [542680691398264011910048076909957572490445]) 0) 29 true) .empty .empty) .empty) (.node 831 (sourceLit (List.headD (raw_ints% [109304226233432595649677029756985]) 0) 61 true) .empty .empty)) (.node 834 (sourceLit (List.headD (raw_ints% [14011483281320506735559574789698964256832415]) 0) 23 false) (.node 833 (sourceLit (List.headD (raw_ints% [15357204203617467764411801152005]) 0) 63 false) .empty .empty) (.node 835 (sourceLit (List.headD (raw_ints% [903308305441257364954599429435]) 0) 65 true) .empty .empty)))

#time def treeG_J015_part111 : IntSourceTree :=
  (.node 827 (sourceLit (List.headD (raw_ints% [120590502100403563398864728885175]) 0) 60 true) treeG_J015_part109 treeG_J015_part110)

#time def treeG_J015_part112 : IntSourceTree :=
  (.node 869 (sourceLit (List.headD (raw_ints% [697056661548585575570962704140679276644895]) 0) 30 true) (.node 839 (sourceLit (List.headD (raw_ints% [1739671643866338295727715]) 0) 69 false) (.node 838 (sourceLit (List.headD (raw_ints% [1138610732395624820316453046511171058072825]) 0) 20 true) (.node 837 (sourceLit (List.headD (raw_ints% [265781789406245827777905]) 0) 72 false) .empty .empty) .empty) (.node 868 (sourceLit (List.headD (raw_ints% [81524661014224747349218551352275]) 0) 62 true) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [1727818358142127371943866391876522125025035]) 0) 29 false) (.node 870 (sourceLit (List.headD (raw_ints% [259264988680816628631375251394375]) 0) 61 false) .empty .empty) (.node 872 (sourceLit (List.headD (raw_ints% [123758169482032898843027116163385]) 0) 62 true) .empty .empty)))

#time def treeG_J015_part113 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [2945304291767206061006415]) 0) 69 false) (.node 876 (sourceLit (List.headD (raw_ints% [903320810903907066546632685555]) 0) 66 true) (.node 875 (sourceLit (List.headD (raw_ints% [14402036226644333589148877714959166316813645]) 0) 24 false) (.node 874 (sourceLit (List.headD (raw_ints% [8130246885970468279858328375115]) 0) 65 false) .empty .empty) .empty) (.node 877 (sourceLit (List.headD (raw_ints% [5929339702140278575620434216347895904577365]) 0) 22 true) .empty .empty)) (.node 909 (sourceLit (List.headD (raw_ints% [431792763542512932802026732819975]) 0) 61 true) (.node 879 (sourceLit (List.headD (raw_ints% [1059995997495263346594375248948547117617835]) 0) 21 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [7045397822358075068837665002018678865053105]) 0) 28 true) .empty .empty)))

#time def treeG_J015_part114 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [19918565953893734297847664696770972719361915]) 0) 25 true) treeG_J015_part112 treeG_J015_part113)

#time def treeG_J015_part115 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [6082774981924748301626875736005586580455535]) 0) 21 true) treeG_J015_part111 treeG_J015_part114)

#time def treeG_J015_part116 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [236515354608234085728008919175352247649473855]) 0) 21 false) (.node 914 (sourceLit (List.headD (raw_ints% [173360010912470381118340892363866746011727735]) 0) 23 true) (.node 913 (sourceLit (List.headD (raw_ints% [69557686842825183303719458657695]) 0) 64 true) (.node 912 (sourceLit (List.headD (raw_ints% [128797735093873475672223884489821612644334545]) 0) 24 false) .empty .empty) .empty) (.node 915 (sourceLit (List.headD (raw_ints% [17163802077382193924671256179665]) 0) 65 false) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [4150936939668073826285115]) 0) 69 false) (.node 918 (sourceLit (List.headD (raw_ints% [46296106884726603784647020684271996178546095]) 0) 20 true) (.node 917 (sourceLit (List.headD (raw_ints% [903329315921168066413121578515]) 0) 67 true) .empty .empty) .empty) (.node 950 (sourceLit (List.headD (raw_ints% [1122850515765842494235428717034325]) 0) 61 true) .empty .empty)))

#time def treeG_J015_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [4516780722071525247804472216305]) 0) 68 false) (.node 954 (sourceLit (List.headD (raw_ints% [38843966864397825791788893516405]) 0) 66 true) (.node 953 (sourceLit (List.headD (raw_ints% [37179075261941802492517887296648146340924115]) 0) 27 false) (.node 952 (sourceLit (List.headD (raw_ints% [183494231708276062440296545095]) 0) 74 false) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [46940511784778678676872442519706478082135345]) 0) 26 true) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [903335206529751600825243591345]) 0) 68 true) (.node 957 (sourceLit (List.headD (raw_ints% [60611173577593591075907338347925035888512805]) 0) 24 false) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [11309027721807835109513161358830862265232065]) 0) 23 true) .empty .empty)))

#time def treeG_J015_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [2193304045125050610195382848473800247519535]) 0) 31 true) treeG_J015_part116 treeG_J015_part117)

#time def treeG_J015_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [1985853661367721518213681847817873144610955855]) 0) 20 false) (.node 996 (sourceLit (List.headD (raw_ints% [3240708108834069521047845240436566844906135935]) 0) 21 true) (.node 995 (sourceLit (List.headD (raw_ints% [172539669534973497091826830245285]) 0) 65 true) (.node 994 (sourceLit (List.headD (raw_ints% [1363090419294608060878913285856607428921299415]) 0) 23 false) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [18970452204207269057631010443735]) 0) 67 false) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [523041807110170210765024570045065]) 0) 65 false) (.node 999 (sourceLit (List.headD (raw_ints% [225834839366672817224767469115]) 0) 71 true) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [1550852466433722775586403055935433341249840795]) 0) 24 false) .empty .empty)))

#time def treeG_J015_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [28054347571773633930430294135403500304903588655]) 0) 21 false) (.node 1039 (sourceLit (List.headD (raw_ints% [2031089772254952858651734493253196593671884115]) 0) 21 false) (.node 1038 (sourceLit (List.headD (raw_ints% [2484223426342127582307031754385]) 0) 71 false) (.node 1037 (sourceLit (List.headD (raw_ints% [3483152803144443885351474593828266988460187155]) 0) 22 true) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [1218623283755313918621875970335415]) 0) 65 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [29851076086523272601025478598444009052292453095]) 0) 20 true) (.node 1077 (sourceLit (List.headD (raw_ints% [3274644447304169799073058274285]) 0) 73 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [5194281692050927981838830977885]) 0) 71 false) .empty .empty)))

#time def treeG_J015_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [190606792423259598083044719110505]) 0) 66 true) treeG_J015_part119 treeG_J015_part120)

#time def treeG_J015_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [445353873381374559181446783012255]) 0) 64 false) treeG_J015_part118 treeG_J015_part121)

#time def treeG_J015_part123 : IntSourceTree :=
  (.node 911 (sourceLit (List.headD (raw_ints% [627834203595065852912427532545735]) 0) 61 false) treeG_J015_part115 treeG_J015_part122)

#time def treeG_J015_part124 : IntSourceTree :=
  (.node 790 (sourceLit (List.headD (raw_ints% [47876749709588741821070196572625]) 0) 61 true) treeG_J015_part108 treeG_J015_part123)

#time def treeG_J015_part125 : IntSourceTree :=
  (.node 597 (sourceLit (List.headD (raw_ints% [706661813310101760117195]) 0) 68 false) treeG_J015_part093 treeG_J015_part124)

#time def treeG_J015_part126 : IntSourceTree :=
  (.node 358 (sourceLit (List.headD (raw_ints% [78210364263215805364971092358275033745]) 0) 20 true) treeG_J015_part062 treeG_J015_part125)

#time def treeG_J015 : IntSourceTree := treeG_J015_part126

#time def treeG_J016_part000 : IntSourceTree :=
  (.node 8 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 6 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 42 false) (.node 5 (sourceLit (List.headD (raw_ints% [2186692625245228855743661466625]) 0) 42 false) (.node 4 (sourceLit (List.headD (raw_ints% [505819217750915711904742455975]) 0) 42 false) .empty .empty) .empty) (.node 7 (sourceLit (List.headD (raw_ints% [1046472067814740136100196283475]) 0) 43 false) .empty .empty)) (.node 11 (sourceLit (List.headD (raw_ints% [61242063523112378117631645225]) 0) 47 false) (.node 10 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 46 true) (.node 9 (sourceLit (List.headD (raw_ints% [126239302919911795760677041225]) 0) 46 false) .empty .empty) .empty) (.node 12 (sourceLit (List.headD (raw_ints% [6569080750011892362399252675]) 0) 49 true) .empty .empty)))

#time def treeG_J016_part001 : IntSourceTree :=
  (.node 18 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [663843756034384296049396575]) 0) 55 true) (.node 15 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 50 false) (.node 14 (sourceLit (List.headD (raw_ints% [13960535108245484673635817525]) 0) 49 true) .empty .empty) .empty) (.node 17 (sourceLit (List.headD (raw_ints% [71248820212612590351433824692475]) 0) 39 true) .empty .empty)) (.node 20 (sourceLit (List.headD (raw_ints% [52608106908135902579581125]) 0) 57 false) (.node 19 (sourceLit (List.headD (raw_ints% [57211654571405384126222436788475]) 0) 38 true) .empty .empty) (.node 21 (sourceLit (List.headD (raw_ints% [145038228815086709004582575389425]) 0) 36 true) .empty .empty)))

#time def treeG_J016_part002 : IntSourceTree :=
  (.node 13 (sourceLit (List.headD (raw_ints% [14911714221369378590363311125]) 0) 49 false) treeG_J016_part000 treeG_J016_part001)

#time def treeG_J016_part003 : IntSourceTree :=
  (.node 27 (sourceLit (List.headD (raw_ints% [1973633906286225370063813522118085]) 0) 31 true) (.node 25 (sourceLit (List.headD (raw_ints% [1261865971072081893053086438316625]) 0) 32 true) (.node 24 (sourceLit (List.headD (raw_ints% [796223598026546681201925]) 0) 63 false) (.node 23 (sourceLit (List.headD (raw_ints% [207956749740535698024672882822375]) 0) 35 true) .empty .empty) .empty) (.node 26 (sourceLit (List.headD (raw_ints% [3139103755257088841969175]) 0) 61 false) .empty .empty)) (.node 29 (sourceLit (List.headD (raw_ints% [6280997670860409940453082452933245]) 0) 29 true) (.node 28 (sourceLit (List.headD (raw_ints% [387058189853318997303225]) 0) 64 false) .empty .empty) (.node 30 (sourceLit (List.headD (raw_ints% [382073053341589264620675]) 0) 64 false) .empty .empty)))

#time def treeG_J016_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [720335500418863195965]) 0) 73 false) (.node 34 (sourceLit (List.headD (raw_ints% [5827828038149823491835]) 0) 70 false) (.node 33 (sourceLit (List.headD (raw_ints% [129813323279078089784884642965183825]) 0) 24 true) (.node 32 (sourceLit (List.headD (raw_ints% [2948374455750583249635]) 0) 71 false) .empty .empty) .empty) (.node 35 (sourceLit (List.headD (raw_ints% [208258617811348277984743481746851225]) 0) 23 true) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [712617350715991619325]) 0) 73 false) (.node 37 (sourceLit (List.headD (raw_ints% [662183161339871309686804450988437215]) 0) 21 true) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [1035608388682895484115204169705910465]) 0) 20 true) .empty .empty)))

#time def treeG_J016_part005 : IntSourceTree :=
  (.node 31 (sourceLit (List.headD (raw_ints% [10082927915166712471056303101930655]) 0) 28 true) treeG_J016_part003 treeG_J016_part004)

#time def treeG_J016_part006 : IntSourceTree :=
  (.node 22 (sourceLit (List.headD (raw_ints% [51749199040247969476241025]) 0) 57 false) treeG_J016_part002 treeG_J016_part005)

#time def treeG_J016_part007 : IntSourceTree :=
  (.node 50 (sourceLit (List.headD (raw_ints% [126239302919911795760677041225]) 0) 47 false) (.node 48 (sourceLit (List.headD (raw_ints% [1046472067814740136100196283475]) 0) 44 false) (.node 47 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 43 false) (.node 46 (sourceLit (List.headD (raw_ints% [2186692625245228855743661466625]) 0) 43 false) .empty .empty) .empty) (.node 49 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)) (.node 52 (sourceLit (List.headD (raw_ints% [61242063523112378117631645225]) 0) 48 false) (.node 51 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 47 true) .empty .empty) (.node 53 (sourceLit (List.headD (raw_ints% [6569080750011892362399252675]) 0) 50 true) .empty .empty)))

#time def treeG_J016_part008 : IntSourceTree :=
  (.node 59 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 55 false) (.node 57 (sourceLit (List.headD (raw_ints% [663843756034384296049396575]) 0) 56 true) (.node 56 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 51 false) (.node 55 (sourceLit (List.headD (raw_ints% [13960535108245484673635817525]) 0) 50 true) .empty .empty) .empty) (.node 58 (sourceLit (List.headD (raw_ints% [71248820212612590351433824692475]) 0) 40 true) .empty .empty)) (.node 61 (sourceLit (List.headD (raw_ints% [52608106908135902579581125]) 0) 58 false) (.node 60 (sourceLit (List.headD (raw_ints% [57211654571405384126222436788475]) 0) 39 true) .empty .empty) (.node 62 (sourceLit (List.headD (raw_ints% [145038228815086709004582575389425]) 0) 37 true) .empty .empty)))

#time def treeG_J016_part009 : IntSourceTree :=
  (.node 54 (sourceLit (List.headD (raw_ints% [14911714221369378590363311125]) 0) 50 false) treeG_J016_part007 treeG_J016_part008)

#time def treeG_J016_part010 : IntSourceTree :=
  (.node 68 (sourceLit (List.headD (raw_ints% [1973633906286225370063813522118085]) 0) 32 true) (.node 66 (sourceLit (List.headD (raw_ints% [1261865971072081893053086438316625]) 0) 33 true) (.node 65 (sourceLit (List.headD (raw_ints% [796223598026546681201925]) 0) 64 false) (.node 64 (sourceLit (List.headD (raw_ints% [207956749740535698024672882822375]) 0) 36 true) .empty .empty) .empty) (.node 67 (sourceLit (List.headD (raw_ints% [3139103755257088841969175]) 0) 62 false) .empty .empty)) (.node 70 (sourceLit (List.headD (raw_ints% [6280997670860409940453082452933245]) 0) 30 true) (.node 69 (sourceLit (List.headD (raw_ints% [387058189853318997303225]) 0) 65 false) .empty .empty) (.node 71 (sourceLit (List.headD (raw_ints% [382073053341589264620675]) 0) 65 false) .empty .empty)))

#time def treeG_J016_part011 : IntSourceTree :=
  (.node 77 (sourceLit (List.headD (raw_ints% [720335500418863195965]) 0) 74 false) (.node 75 (sourceLit (List.headD (raw_ints% [5827828038149823491835]) 0) 71 false) (.node 74 (sourceLit (List.headD (raw_ints% [129813323279078089784884642965183825]) 0) 25 true) (.node 73 (sourceLit (List.headD (raw_ints% [2948374455750583249635]) 0) 72 false) .empty .empty) .empty) (.node 76 (sourceLit (List.headD (raw_ints% [208258617811348277984743481746851225]) 0) 24 true) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [712617350715991619325]) 0) 74 false) (.node 78 (sourceLit (List.headD (raw_ints% [662183161339871309686804450988437215]) 0) 22 true) .empty .empty) (.node 86 (sourceLit (List.headD (raw_ints% [1755490226312001588375282641325]) 0) 42 false) .empty .empty)))

#time def treeG_J016_part012 : IntSourceTree :=
  (.node 72 (sourceLit (List.headD (raw_ints% [10082927915166712471056303101930655]) 0) 29 true) treeG_J016_part010 treeG_J016_part011)

#time def treeG_J016_part013 : IntSourceTree :=
  (.node 63 (sourceLit (List.headD (raw_ints% [51749199040247969476241025]) 0) 58 false) treeG_J016_part009 treeG_J016_part012)

#time def treeG_J016_part014 : IntSourceTree :=
  (.node 45 (sourceLit (List.headD (raw_ints% [505819217750915711904742455975]) 0) 43 false) treeG_J016_part006 treeG_J016_part013)

#time def treeG_J016_part015 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [8114746808838219977081429775]) 0) 48 true) (.node 90 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 46 false) (.node 89 (sourceLit (List.headD (raw_ints% [793993461974916544578842201025]) 0) 45 false) (.node 88 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 44 false) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [191236542316711213403722437225]) 0) 47 false) .empty .empty)) (.node 94 (sourceLit (List.headD (raw_ints% [12315787891802084775961193175]) 0) 49 true) (.node 93 (sourceLit (List.headD (raw_ints% [11582587325435749881817083525]) 0) 51 false) .empty .empty) (.node 95 (sourceLit (List.headD (raw_ints% [22540963357883944380781749375]) 0) 50 false) .empty .empty)))

#time def treeG_J016_part016 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [770348244327399437014976413226175]) 0) 36 true) (.node 99 (sourceLit (List.headD (raw_ints% [512778907129495338685248160751325]) 0) 38 true) (.node 98 (sourceLit (List.headD (raw_ints% [5739130347384181003686047475]) 0) 54 true) (.node 97 (sourceLit (List.headD (raw_ints% [130906774187743216808582223284475]) 0) 39 false) .empty .empty) .empty) (.node 100 (sourceLit (List.headD (raw_ints% [323164085292834830131712625]) 0) 56 false) .empty .empty)) (.node 103 (sourceLit (List.headD (raw_ints% [952349080780157974011987720293025]) 0) 35 true) (.node 102 (sourceLit (List.headD (raw_ints% [158683228592295640842083475]) 0) 57 false) .empty .empty) (.node 104 (sourceLit (List.headD (raw_ints% [39009621471823222577010225]) 0) 59 false) .empty .empty)))

#time def treeG_J016_part017 : IntSourceTree :=
  (.node 96 (sourceLit (List.headD (raw_ints% [3339035011695335936845472325]) 0) 51 true) treeG_J016_part015 treeG_J016_part016)

#time def treeG_J016_part018 : IntSourceTree :=
  (.node 110 (sourceLit (List.headD (raw_ints% [1166159706071686724592225]) 0) 64 false) (.node 108 (sourceLit (List.headD (raw_ints% [2364987375550450847362725]) 0) 63 false) (.node 107 (sourceLit (List.headD (raw_ints% [8121293862290429774360877984414915]) 0) 31 true) (.node 106 (sourceLit (List.headD (raw_ints% [9600473813167658057261625]) 0) 61 false) .empty .empty) .empty) (.node 109 (sourceLit (List.headD (raw_ints% [25297144829719195980567933900956115]) 0) 29 true) .empty .empty)) (.node 112 (sourceLit (List.headD (raw_ints% [287725070757570600632355]) 0) 66 false) (.node 111 (sourceLit (List.headD (raw_ints% [40165053451716567052568356521535305]) 0) 28 true) .empty .empty) (.node 113 (sourceLit (List.headD (raw_ints% [515494063291591508362718755558378095]) 0) 24 true) .empty .empty)))

#time def treeG_J016_part019 : IntSourceTree :=
  (.node 119 (sourceLit (List.headD (raw_ints% [4261856902036074993379231438201587255]) 0) 20 true) (.node 117 (sourceLit (List.headD (raw_ints% [2669954723641701138069091256961182385]) 0) 21 true) (.node 116 (sourceLit (List.headD (raw_ints% [4387157037312097099905]) 0) 72 false) (.node 115 (sourceLit (List.headD (raw_ints% [830247968421276440294333661974619375]) 0) 23 true) .empty .empty) .empty) (.node 118 (sourceLit (List.headD (raw_ints% [2168724650959461164535]) 0) 73 false) .empty .empty)) (.node 128 (sourceLit (List.headD (raw_ints% [570110278715244359821732591575]) 0) 46 false) (.node 127 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 44 false) .empty .empty) (.node 129 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 45 false) .empty .empty)))

#time def treeG_J016_part020 : IntSourceTree :=
  (.node 114 (sourceLit (List.headD (raw_ints% [17759167607854842505245]) 0) 70 false) treeG_J016_part018 treeG_J016_part019)

#time def treeG_J016_part021 : IntSourceTree :=
  (.node 105 (sourceLit (List.headD (raw_ints% [5392750020625060443736445811999375]) 0) 32 true) treeG_J016_part017 treeG_J016_part020)

#time def treeG_J016_part022 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [822373608221699948837312175]) 0) 51 false) (.node 133 (sourceLit (List.headD (raw_ints% [5023414691185564747717075575]) 0) 49 false) (.node 132 (sourceLit (List.headD (raw_ints% [2031163731149981801345168625]) 0) 54 false) (.node 131 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 48 false) .empty .empty) .empty) (.node 134 (sourceLit (List.headD (raw_ints% [31418635080373620936905022975]) 0) 50 false) .empty .empty)) (.node 137 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 52 false) (.node 136 (sourceLit (List.headD (raw_ints% [3814624568257282895209219125]) 0) 53 false) .empty .empty) (.node 138 (sourceLit (List.headD (raw_ints% [101077797200177903580008023988475]) 0) 41 false) .empty .empty)))

#time def treeG_J016_part023 : IntSourceTree :=
  (.node 144 (sourceLit (List.headD (raw_ints% [372196165519811137993657418735325]) 0) 37 true) (.node 142 (sourceLit (List.headD (raw_ints% [312655007756156364005196918918375]) 0) 38 true) (.node 141 (sourceLit (List.headD (raw_ints% [217947871476563024972550375]) 0) 57 false) (.node 140 (sourceLit (List.headD (raw_ints% [227783626279044977279512861981425]) 0) 40 true) .empty .empty) .empty) (.node 143 (sourceLit (List.headD (raw_ints% [53467014776023835682921225]) 0) 59 false) .empty .empty)) (.node 146 (sourceLit (List.headD (raw_ints% [2065442024776489275341679686841375]) 0) 34 true) (.node 145 (sourceLit (List.headD (raw_ints% [26270043903398475677779425]) 0) 60 false) .empty .empty) (.node 147 (sourceLit (List.headD (raw_ints% [3230685028955284607646225]) 0) 63 false) .empty .empty)))

#time def treeG_J016_part024 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [3083755323246643819488461175]) 0) 56 true) treeG_J016_part022 treeG_J016_part023)

#time def treeG_J016_part025 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [193377088173551936644035]) 0) 67 false) (.node 151 (sourceLit (List.headD (raw_ints% [392043326365048729985775]) 0) 66 false) (.node 150 (sourceLit (List.headD (raw_ints% [9508073579429393020057425724011435]) 0) 31 true) (.node 149 (sourceLit (List.headD (raw_ints% [1590870995843812852756275]) 0) 64 false) .empty .empty) .empty) (.node 152 (sourceLit (List.headD (raw_ints% [15041062768274927290756026709802325]) 0) 30 true) .empty .empty)) (.node 155 (sourceLit (List.headD (raw_ints% [5965669784852509506705]) 0) 72 false) (.node 154 (sourceLit (List.headD (raw_ints% [192840370006256709288917056296597135]) 0) 26 true) .empty .empty) (.node 156 (sourceLit (List.headD (raw_ints% [310994675304964081154795090113884075]) 0) 25 true) .empty .empty)))

#time def treeG_J016_part026 : IntSourceTree :=
  (.node 170 (sourceLit (List.headD (raw_ints% [123266868191399627270903623725]) 0) 47 false) (.node 168 (sourceLit (List.headD (raw_ints% [1219916936928679069887908276175]) 0) 44 false) (.node 159 (sourceLit (List.headD (raw_ints% [728053650121734772605]) 0) 75 false) (.node 158 (sourceLit (List.headD (raw_ints% [1003885781150914914191143402986372585]) 0) 23 true) .empty .empty) .empty) (.node 169 (sourceLit (List.headD (raw_ints% [1486447652886060894708088165275]) 0) 45 false) .empty .empty)) (.node 172 (sourceLit (List.headD (raw_ints% [50620563426562229380841300025]) 0) 48 false) (.node 171 (sourceLit (List.headD (raw_ints% [175139156909190869826882840675]) 0) 48 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [20916032372963958939705614475]) 0) 51 false) .empty .empty)))

#time def treeG_J016_part027 : IntSourceTree :=
  (.node 157 (sourceLit (List.headD (raw_ints% [2946486036474370707975]) 0) 73 false) treeG_J016_part025 treeG_J016_part026)

#time def treeG_J016_part028 : IntSourceTree :=
  (.node 148 (sourceLit (List.headD (raw_ints% [3073829978002102202148532231148415]) 0) 33 true) treeG_J016_part024 treeG_J016_part027)

#time def treeG_J016_part029 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [541514856135092953057488118575]) 0) 46 false) treeG_J016_part021 treeG_J016_part028)

#time def treeG_J016_part030 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [3326913182675717575387126649775]) 0) 43 false) treeG_J016_part014 treeG_J016_part029)

#time def treeG_J016_part031 : IntSourceTree :=
  (.node 179 (sourceLit (List.headD (raw_ints% [2130023662332341795965376544566925]) 0) 38 false) (.node 177 (sourceLit (List.headD (raw_ints% [5909156335088570898366530996475]) 0) 39 true) (.node 176 (sourceLit (List.headD (raw_ints% [4983782228138735834520096675]) 0) 51 false) (.node 175 (sourceLit (List.headD (raw_ints% [40296306802863297493028296575]) 0) 50 false) .empty .empty) .empty) (.node 178 (sourceLit (List.headD (raw_ints% [18760725779623174807316967825]) 0) 53 false) .empty .empty)) (.node 182 (sourceLit (List.headD (raw_ints% [277212514360830409103017275]) 0) 57 false) (.node 181 (sourceLit (List.headD (raw_ints% [6518727796602039835929435170179425]) 0) 36 true) (.node 180 (sourceLit (List.headD (raw_ints% [6490674731786122469108634975]) 0) 56 true) .empty .empty) .empty) (.node 183 (sourceLit (List.headD (raw_ints% [4050131043318343850071162982400975]) 0) 35 true) .empty .empty)))

#time def treeG_J016_part032 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [73065414466348074488185097495793165]) 0) 29 true) (.node 187 (sourceLit (List.headD (raw_ints% [24925778534133398631105997005047085]) 0) 31 true) (.node 186 (sourceLit (List.headD (raw_ints% [2083696261278852202564725]) 0) 64 false) (.node 185 (sourceLit (List.headD (raw_ints% [18427804572642852387857628987061425]) 0) 32 true) .empty .empty) .empty) (.node 188 (sourceLit (List.headD (raw_ints% [4096382682360118367929725]) 0) 63 false) .empty .empty)) (.node 191 (sourceLit (List.headD (raw_ints% [111964123819153721268350455062647655]) 0) 28 true) (.node 190 (sourceLit (List.headD (raw_ints% [2015582285615938980920325]) 0) 64 false) .empty .empty) (.node 192 (sourceLit (List.headD (raw_ints% [496361581972526859339195]) 0) 66 false) .empty .empty)))

#time def treeG_J016_part033 : IntSourceTree :=
  (.node 184 (sourceLit (List.headD (raw_ints% [67924408080224448788832225]) 0) 59 false) treeG_J016_part031 treeG_J016_part032)

#time def treeG_J016_part034 : IntSourceTree :=
  (.node 198 (sourceLit (List.headD (raw_ints% [3724247421989280251415]) 0) 73 false) (.node 196 (sourceLit (List.headD (raw_ints% [7544182532392921913505]) 0) 72 false) (.node 195 (sourceLit (List.headD (raw_ints% [2255197951678830908328339238770934785]) 0) 23 true) (.node 194 (sourceLit (List.headD (raw_ints% [122340417742132566623055]) 0) 68 false) .empty .empty) .empty) (.node 197 (sourceLit (List.headD (raw_ints% [7281874886117149458884351626683108015]) 0) 21 true) .empty .empty)) (.node 209 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 50 false) (.node 199 (sourceLit (List.headD (raw_ints% [11800315596378563633679063009580374105]) 0) 20 true) .empty .empty) (.node 210 (sourceLit (List.headD (raw_ints% [236233199187741985412650011675]) 0) 48 false) .empty .empty)))

#time def treeG_J016_part035 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [25037808529834165912191420075]) 0) 51 false) (.node 214 (sourceLit (List.headD (raw_ints% [52245494411482214821917434925]) 0) 50 false) (.node 213 (sourceLit (List.headD (raw_ints% [22798574367688332316562112225]) 0) 50 false) (.node 212 (sourceLit (List.headD (raw_ints% [110141917512391452183837444675]) 0) 49 false) .empty .empty) .empty) (.node 215 (sourceLit (List.headD (raw_ints% [20717870057729814373720719975]) 0) 50 false) .empty .empty)) (.node 218 (sourceLit (List.headD (raw_ints% [208064750735444378058382578973425]) 0) 40 true) (.node 217 (sourceLit (List.headD (raw_ints% [287335357089509620678097025]) 0) 55 true) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [31095747072609750085270812525]) 0) 54 false) .empty .empty)))

#time def treeG_J016_part036 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [12751744985317202821127961075]) 0) 51 false) treeG_J016_part034 treeG_J016_part035)

#time def treeG_J016_part037 : IntSourceTree :=
  (.node 193 (sourceLit (List.headD (raw_ints% [1409761971047599184854052663296319505]) 0) 24 true) treeG_J016_part033 treeG_J016_part036)

#time def treeG_J016_part038 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [81356180032863228732525]) 0) 69 false) (.node 223 (sourceLit (List.headD (raw_ints% [170278484808782737737174825]) 0) 58 false) (.node 222 (sourceLit (List.headD (raw_ints% [5893417781089727107919041332342675]) 0) 37 true) (.node 221 (sourceLit (List.headD (raw_ints% [3354311301631342747040592675]) 0) 58 true) .empty .empty) .empty) (.node 224 (sourceLit (List.headD (raw_ints% [3305738712278721574083848144930325]) 0) 36 true) .empty .empty)) (.node 227 (sourceLit (List.headD (raw_ints% [5104100016160124202612675]) 0) 63 false) (.node 226 (sourceLit (List.headD (raw_ints% [14296920523089873837174269613378675]) 0) 33 true) .empty .empty) (.node 228 (sourceLit (List.headD (raw_ints% [18778118578129194226808932542750255]) 0) 32 true) .empty .empty)))

#time def treeG_J016_part039 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [1024081231035085766276218550703125235]) 0) 25 true) (.node 232 (sourceLit (List.headD (raw_ints% [81881998282603866686838401643043005]) 0) 29 true) (.node 231 (sourceLit (List.headD (raw_ints% [1231495632885841520948775]) 0) 65 false) (.node 230 (sourceLit (List.headD (raw_ints% [54049267307489288448070246047770295]) 0) 30 true) .empty .empty) .empty) (.node 233 (sourceLit (List.headD (raw_ints% [37873061724871865336895]) 0) 70 false) .empty .empty)) (.node 236 (sourceLit (List.headD (raw_ints% [1633208601068902746018749058543166635]) 0) 24 true) (.node 235 (sourceLit (List.headD (raw_ints% [74615059463312490569415]) 0) 69 false) .empty .empty) (.node 237 (sourceLit (List.headD (raw_ints% [2298848247959275602765]) 0) 74 false) .empty .empty)))

#time def treeG_J016_part040 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [1252755843258152757586725]) 0) 65 false) treeG_J016_part038 treeG_J016_part039)

#time def treeG_J016_part041 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [68309852766463534304426215725]) 0) 50 false) (.node 251 (sourceLit (List.headD (raw_ints% [297327241466293100998417182675]) 0) 48 false) (.node 250 (sourceLit (List.headD (raw_ints% [352798277927109278051206923075]) 0) 47 false) (.node 239 (sourceLit (List.headD (raw_ints% [2268140121745810706205]) 0) 74 false) .empty .empty) .empty) (.node 252 (sourceLit (List.headD (raw_ints% [153407356338513015757206077175]) 0) 48 false) .empty .empty)) (.node 255 (sourceLit (List.headD (raw_ints% [64194682020101132150806573275]) 0) 50 false) (.node 254 (sourceLit (List.headD (raw_ints% [68831680196580114994853104575]) 0) 49 false) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [3933521957397769634800155825]) 0) 53 false) .empty .empty)))

#time def treeG_J016_part042 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [13694457720886201397265387975]) 0) 57 true) (.node 260 (sourceLit (List.headD (raw_ints% [44077096536181995023488082475]) 0) 55 false) (.node 259 (sourceLit (List.headD (raw_ints% [3794541668215896820432437176354325]) 0) 38 true) (.node 258 (sourceLit (List.headD (raw_ints% [21059408636339251772741744025]) 0) 53 true) .empty .empty) .empty) (.node 261 (sourceLit (List.headD (raw_ints% [47888182434848947844319871466655825]) 0) 36 false) .empty .empty)) (.node 264 (sourceLit (List.headD (raw_ints% [12794259591069786118542825]) 0) 62 false) (.node 263 (sourceLit (List.headD (raw_ints% [43097211205399473013281167676340425]) 0) 35 true) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [87355834220276237982825511650708975]) 0) 32 true) .empty .empty)))

#time def treeG_J016_part043 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [211018883811490058051038644250875]) 0) 39 false) treeG_J016_part041 treeG_J016_part042)

#time def treeG_J016_part044 : IntSourceTree :=
  (.node 238 (sourceLit (List.headD (raw_ints% [5274103323815319630502064820710362845]) 0) 22 true) treeG_J016_part040 treeG_J016_part043)

#time def treeG_J016_part045 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [2585590914890431750524402268529775]) 0) 39 false) treeG_J016_part037 treeG_J016_part044)

#time def treeG_J016_part046 : IntSourceTree :=
  (.node 271 (sourceLit (List.headD (raw_ints% [320430014640760586316211513319514705]) 0) 28 true) (.node 269 (sourceLit (List.headD (raw_ints% [227384482783719033140757823188210915]) 0) 29 true) (.node 268 (sourceLit (List.headD (raw_ints% [6111817349960130037295625]) 0) 63 false) (.node 267 (sourceLit (List.headD (raw_ints% [89449585650585592066288159901982315]) 0) 31 true) .empty .empty) .empty) (.node 270 (sourceLit (List.headD (raw_ints% [2995441087416672049426575]) 0) 64 false) .empty .empty)) (.node 273 (sourceLit (List.headD (raw_ints% [3830685919039048283103605041858432815]) 0) 24 true) (.node 272 (sourceLit (List.headD (raw_ints% [183783512728328665402395]) 0) 68 false) .empty .empty) (.node 274 (sourceLit (List.headD (raw_ints% [180644076056842356072105]) 0) 68 false) .empty .empty)))

#time def treeG_J016_part047 : IntSourceTree :=
  (.node 291 (sourceLit (List.headD (raw_ints% [250784318044571655482183234475]) 0) 48 false) (.node 278 (sourceLit (List.headD (raw_ints% [5471145569847822159645]) 0) 73 false) (.node 277 (sourceLit (List.headD (raw_ints% [18849462730985294477415633310007558145]) 0) 21 true) (.node 276 (sourceLit (List.headD (raw_ints% [44438329333740802915395]) 0) 70 false) .empty .empty) .empty) (.node 279 (sourceLit (List.headD (raw_ints% [30392510994143993410337455556102528655]) 0) 20 true) .empty .empty)) (.node 293 (sourceLit (List.headD (raw_ints% [107810207603136351124081852725]) 0) 49 false) (.node 292 (sourceLit (List.headD (raw_ints% [11699082747118853050911233625]) 0) 53 false) .empty .empty) (.node 294 (sourceLit (List.headD (raw_ints% [84374211121444853786934996525]) 0) 50 false) .empty .empty)))

#time def treeG_J016_part048 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [5937451896601855221881409166854067095]) 0) 23 true) treeG_J016_part046 treeG_J016_part047)

#time def treeG_J016_part049 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [1595033145776582142739209861221025]) 0) 41 true) (.node 298 (sourceLit (List.headD (raw_ints% [104770908636733609027355305806075]) 0) 42 false) (.node 297 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 54 false) (.node 296 (sourceLit (List.headD (raw_ints% [2447304593141685389913447075]) 0) 55 false) .empty .empty) .empty) (.node 299 (sourceLit (List.headD (raw_ints% [26077577854474500929006278275]) 0) 55 true) .empty .empty)) (.node 302 (sourceLit (List.headD (raw_ints% [13445400053984668738059728199749625]) 0) 39 false) (.node 301 (sourceLit (List.headD (raw_ints% [57494341742707366011650453175]) 0) 56 false) .empty .empty) (.node 303 (sourceLit (List.headD (raw_ints% [866546012855936508437660175]) 0) 62 true) .empty .empty)))

#time def treeG_J016_part050 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [3606305663443824522122175]) 0) 64 false) (.node 307 (sourceLit (List.headD (raw_ints% [7388297027137453542654825]) 0) 63 false) (.node 306 (sourceLit (List.headD (raw_ints% [18264728424296591036412810509332575]) 0) 35 true) (.node 305 (sourceLit (List.headD (raw_ints% [7587464068966539479661225]) 0) 63 false) .empty .empty) .empty) (.node 308 (sourceLit (List.headD (raw_ints% [17667866768114099459869806839808015]) 0) 34 true) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [220493181816353816059725]) 0) 68 false) (.node 310 (sourceLit (List.headD (raw_ints% [43333803869057436173171894285110155]) 0) 32 true) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [59637004089539179907343277919117925]) 0) 31 true) .empty .empty)))

#time def treeG_J016_part051 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [9947868123280187859799329882852525]) 0) 38 true) treeG_J016_part049 treeG_J016_part050)

#time def treeG_J016_part052 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [6014226267356287577641548075]) 0) 53 false) treeG_J016_part048 treeG_J016_part051)

#time def treeG_J016_part053 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [3393839851792493711728392122324298825]) 0) 24 true) (.node 316 (sourceLit (List.headD (raw_ints% [1076060823883238118965665027077725115]) 0) 26 true) (.node 315 (sourceLit (List.headD (raw_ints% [53014508296764932751345]) 0) 70 false) (.node 314 (sourceLit (List.headD (raw_ints% [701651172000990629206846622788826895]) 0) 27 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [26047543350066598093275]) 0) 71 false) .empty .empty)) (.node 332 (sourceLit (List.headD (raw_ints% [348161279750630295207160391775]) 0) 48 false) (.node 319 (sourceLit (List.headD (raw_ints% [195495937994507535]) 0) 88 false) .empty .empty) (.node 333 (sourceLit (List.headD (raw_ints% [118875471187438114510153522275]) 0) 50 false) .empty .empty)))

#time def treeG_J016_part054 : IntSourceTree :=
  (.node 339 (sourceLit (List.headD (raw_ints% [7147210744591372309307806962148725]) 0) 38 false) (.node 337 (sourceLit (List.headD (raw_ints% [109754223820776929375696690763525]) 0) 39 false) (.node 336 (sourceLit (List.headD (raw_ints% [8094930577314805520482940325]) 0) 53 false) (.node 335 (sourceLit (List.headD (raw_ints% [104553740222788575423063419775]) 0) 50 false) .empty .empty) .empty) (.node 338 (sourceLit (List.headD (raw_ints% [39092179322646407277367143525]) 0) 53 false) .empty .empty)) (.node 341 (sourceLit (List.headD (raw_ints% [149970303764550204979629302584801425]) 0) 36 true) (.node 340 (sourceLit (List.headD (raw_ints% [96232252245130996881500639025]) 0) 55 true) .empty .empty) (.node 342 (sourceLit (List.headD (raw_ints% [35594399731796783704457920575]) 0) 58 false) .empty .empty)))

#time def treeG_J016_part055 : IntSourceTree :=
  (.node 334 (sourceLit (List.headD (raw_ints% [146788735009692587253310600875]) 0) 49 false) treeG_J016_part053 treeG_J016_part054)

#time def treeG_J016_part056 : IntSourceTree :=
  (.node 348 (sourceLit (List.headD (raw_ints% [8664776704314777048014025]) 0) 63 false) (.node 346 (sourceLit (List.headD (raw_ints% [2232182404071072521672175]) 0) 65 false) (.node 345 (sourceLit (List.headD (raw_ints% [1185971285559587808071488713354414225]) 0) 32 true) (.node 344 (sourceLit (List.headD (raw_ints% [1745886285302942802993863175]) 0) 62 true) .empty .empty) .empty) (.node 347 (sourceLit (List.headD (raw_ints% [495021723926905321098921776396660085]) 0) 31 true) .empty .empty)) (.node 350 (sourceLit (List.headD (raw_ints% [4217170239470976994817775]) 0) 64 false) (.node 349 (sourceLit (List.headD (raw_ints% [903358990375583332290909814559502045]) 0) 29 true) .empty .empty) (.node 351 (sourceLit (List.headD (raw_ints% [1066251709169077371225289103804010255]) 0) 28 true) .empty .empty)))

#time def treeG_J016_part057 : IntSourceTree :=
  (.node 357 (sourceLit (List.headD (raw_ints% [50018429997541945136386928422966849215]) 0) 21 true) (.node 355 (sourceLit (List.headD (raw_ints% [16515385607429844912737682762388393545]) 0) 23 true) (.node 354 (sourceLit (List.headD (raw_ints% [251505481057497382842315]) 0) 68 false) (.node 353 (sourceLit (List.headD (raw_ints% [11436387127882981773176274105435755985]) 0) 24 true) .empty .empty) .empty) (.node 356 (sourceLit (List.headD (raw_ints% [61590687259789062587295]) 0) 70 false) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [78210364263215805364971092358275033745]) 0) 20 true) (.node 358 (sourceLit (List.headD (raw_ints% [15105252210370953773985]) 0) 72 false) .empty .empty) (.node 373 (sourceLit (List.headD (raw_ints% [120175536073746972041539269525]) 0) 50 false) .empty .empty)))

#time def treeG_J016_part058 : IntSourceTree :=
  (.node 352 (sourceLit (List.headD (raw_ints% [257202850904378966717055]) 0) 68 false) treeG_J016_part056 treeG_J016_part057)

#time def treeG_J016_part059 : IntSourceTree :=
  (.node 343 (sourceLit (List.headD (raw_ints% [473350012932908872631192470068328425]) 0) 35 false) treeG_J016_part055 treeG_J016_part058)

#time def treeG_J016_part060 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [108037389278584934728605]) 0) 69 false) treeG_J016_part052 treeG_J016_part059)

#time def treeG_J016_part061 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [3123099260824394436316875]) 0) 64 false) treeG_J016_part045 treeG_J016_part060)

#time def treeG_J016_part062 : IntSourceTree :=
  (.node 174 (sourceLit (List.headD (raw_ints% [22362617274173214271395344325]) 0) 49 false) treeG_J016_part030 treeG_J016_part061)

#time def treeG_J016_part063 : IntSourceTree :=
  (.node 379 (sourceLit (List.headD (raw_ints% [91247335031595409135379700075]) 0) 54 false) (.node 377 (sourceLit (List.headD (raw_ints% [1793368952869008322163295225]) 0) 55 false) (.node 376 (sourceLit (List.headD (raw_ints% [65396866732521609184448266575]) 0) 51 false) (.node 375 (sourceLit (List.headD (raw_ints% [98674924870842286632178216275]) 0) 50 false) .empty .empty) .empty) (.node 378 (sourceLit (List.headD (raw_ints% [309329410726157506733724532460775]) 0) 40 true) .empty .empty)) (.node 382 (sourceLit (List.headD (raw_ints% [203751903980488879931868215383799925]) 0) 37 true) (.node 381 (sourceLit (List.headD (raw_ints% [19215824248479795361643886525]) 0) 59 true) (.node 380 (sourceLit (List.headD (raw_ints% [13527343327697700880264646407032825]) 0) 39 false) .empty .empty) .empty) (.node 383 (sourceLit (List.headD (raw_ints% [42526767834644275771959201975]) 0) 59 false) .empty .empty)))

#time def treeG_J016_part064 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [2529235520435476262945925]) 0) 65 false) (.node 387 (sourceLit (List.headD (raw_ints% [10469162205431126630722575]) 0) 63 false) (.node 386 (sourceLit (List.headD (raw_ints% [1112912371862401443925837471317083925]) 0) 33 true) (.node 385 (sourceLit (List.headD (raw_ints% [109592109335744333904595275]) 0) 67 true) .empty .empty) .empty) (.node 388 (sourceLit (List.headD (raw_ints% [424350256854448923259442549037428025]) 0) 32 true) .empty .empty)) (.node 391 (sourceLit (List.headD (raw_ints% [2453224784940146466339975]) 0) 65 false) (.node 390 (sourceLit (List.headD (raw_ints% [730023774899353587598222237419061425]) 0) 30 true) .empty .empty) (.node 392 (sourceLit (List.headD (raw_ints% [827703692810920651595915992127538555]) 0) 29 true) .empty .empty)))

#time def treeG_J016_part065 : IntSourceTree :=
  (.node 384 (sourceLit (List.headD (raw_ints% [513141485426029624070389789599738525]) 0) 36 false) treeG_J016_part063 treeG_J016_part064)

#time def treeG_J016_part066 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [36443070590371970289473359933669653915]) 0) 22 true) (.node 396 (sourceLit (List.headD (raw_ints% [12211142311896892436875022654077493085]) 0) 24 true) (.node 395 (sourceLit (List.headD (raw_ints% [145476464463967517339625]) 0) 69 false) (.node 394 (sourceLit (List.headD (raw_ints% [8629782439879019256348887614280448405]) 0) 25 true) .empty .empty) .empty) (.node 397 (sourceLit (List.headD (raw_ints% [8885785977430616123505]) 0) 73 false) .empty .empty)) (.node 414 (sourceLit (List.headD (raw_ints% [333913409285295300912846477225]) 0) 49 false) (.node 399 (sourceLit (List.headD (raw_ints% [8699241314166930867105]) 0) 73 false) .empty .empty) (.node 415 (sourceLit (List.headD (raw_ints% [202199722284074175043680676275]) 0) 50 false) .empty .empty)))

#time def treeG_J016_part067 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [366407797007713419063863645097326625]) 0) 36 false) (.node 419 (sourceLit (List.headD (raw_ints% [9621846030400632363177603221834925]) 0) 38 true) (.node 418 (sourceLit (List.headD (raw_ints% [24745227699694340700060781725]) 0) 53 true) (.node 417 (sourceLit (List.headD (raw_ints% [425976908452040093063303509018875]) 0) 39 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [46869896819181601504220084775]) 0) 57 false) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [2103365244776819912086138193138727825]) 0) 35 true) (.node 422 (sourceLit (List.headD (raw_ints% [112457696725715965151033466675]) 0) 58 true) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [49510312975856046983934654675]) 0) 60 false) .empty .empty)))

#time def treeG_J016_part068 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [66295202561583064550246454975]) 0) 51 false) treeG_J016_part066 treeG_J016_part067)

#time def treeG_J016_part069 : IntSourceTree :=
  (.node 393 (sourceLit (List.headD (raw_ints% [74582730812897015994225]) 0) 70 false) treeG_J016_part065 treeG_J016_part068)

#time def treeG_J016_part070 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [5899771842270928056965925]) 0) 64 false) (.node 428 (sourceLit (List.headD (raw_ints% [12273547706547476213431125]) 0) 63 false) (.node 427 (sourceLit (List.headD (raw_ints% [8408277250972306230307777994140011315]) 0) 31 true) (.node 426 (sourceLit (List.headD (raw_ints% [878969057090025743758434375]) 0) 65 true) .empty .empty) .empty) (.node 429 (sourceLit (List.headD (raw_ints% [5886245119295599439860170970039346355]) 0) 29 true) .empty .empty)) (.node 432 (sourceLit (List.headD (raw_ints% [1424413381322630599471755]) 0) 66 false) (.node 431 (sourceLit (List.headD (raw_ints% [4773938490025751329560488795548481145]) 0) 28 true) .empty .empty) (.node 433 (sourceLit (List.headD (raw_ints% [41536649212015939928962349390726711535]) 0) 24 true) .empty .empty)))

#time def treeG_J016_part071 : IntSourceTree :=
  (.node 439 (sourceLit (List.headD (raw_ints% [213334200459759956950815787111082197575]) 0) 20 true) (.node 437 (sourceLit (List.headD (raw_ints% [145359846992808333853613434042273040145]) 0) 21 true) (.node 436 (sourceLit (List.headD (raw_ints% [41942888602089227376165]) 0) 71 false) (.node 435 (sourceLit (List.headD (raw_ints% [52522873911602309138053418151855193695]) 0) 23 true) .empty .empty) .empty) (.node 438 (sourceLit (List.headD (raw_ints% [20437891699351510720035]) 0) 72 false) .empty .empty)) (.node 456 (sourceLit (List.headD (raw_ints% [34200713887888141464808102425]) 0) 53 false) (.node 455 (sourceLit (List.headD (raw_ints% [117619242207226507140334130475]) 0) 51 false) .empty .empty) (.node 457 (sourceLit (List.headD (raw_ints% [51948250938630997972940093175]) 0) 52 false) .empty .empty)))

#time def treeG_J016_part072 : IntSourceTree :=
  (.node 434 (sourceLit (List.headD (raw_ints% [345156365445678745111485]) 0) 68 false) treeG_J016_part070 treeG_J016_part071)

#time def treeG_J016_part073 : IntSourceTree :=
  (.node 463 (sourceLit (List.headD (raw_ints% [77492232280180120461496334325]) 0) 60 true) (.node 461 (sourceLit (List.headD (raw_ints% [85301545316141192227507857825]) 0) 58 false) (.node 460 (sourceLit (List.headD (raw_ints% [11574594679049166621721124814433875]) 0) 40 true) (.node 459 (sourceLit (List.headD (raw_ints% [14499070341411218729430060225]) 0) 57 true) .empty .empty) .empty) (.node 462 (sourceLit (List.headD (raw_ints% [285079850494101149497865930240563275]) 0) 38 false) .empty .empty)) (.node 465 (sourceLit (List.headD (raw_ints% [56524207973343684353828752275]) 0) 61 false) (.node 464 (sourceLit (List.headD (raw_ints% [1308253365101424768078263991369233175]) 0) 37 true) .empty .empty) (.node 466 (sourceLit (List.headD (raw_ints% [9359705595527468611124899725931565475]) 0) 34 false) .empty .empty)))

#time def treeG_J016_part074 : IntSourceTree :=
  (.node 472 (sourceLit (List.headD (raw_ints% [1973117398607415338982286401710471295]) 0) 30 true) (.node 470 (sourceLit (List.headD (raw_ints% [2578110672198122926130974366310142465]) 0) 31 true) (.node 469 (sourceLit (List.headD (raw_ints% [7215076665676523687539275]) 0) 64 false) (.node 468 (sourceLit (List.headD (raw_ints% [3991963497058928653524167722551291645]) 0) 33 true) .empty .empty) .empty) (.node 471 (sourceLit (List.headD (raw_ints% [1723273528665390795312975]) 0) 66 false) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [16453433386068460336306730888223131565]) 0) 26 true) (.node 473 (sourceLit (List.headD (raw_ints% [827751534819454471517955]) 0) 67 false) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [49919975245427806942965]) 0) 71 false) .empty .empty)))

#time def treeG_J016_part075 : IntSourceTree :=
  (.node 467 (sourceLit (List.headD (raw_ints% [7042221618925637076698197575]) 0) 63 true) treeG_J016_part073 treeG_J016_part074)

#time def treeG_J016_part076 : IntSourceTree :=
  (.node 458 (sourceLit (List.headD (raw_ints% [367653159589098799898514020739825]) 0) 41 false) treeG_J016_part072 treeG_J016_part075)

#time def treeG_J016_part077 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [17606498819192535778323961980546047025]) 0) 32 false) treeG_J016_part069 treeG_J016_part076)

#time def treeG_J016_part078 : IntSourceTree :=
  (.node 497 (sourceLit (List.headD (raw_ints% [694712084226278526455528391243525]) 0) 39 false) (.node 479 (sourceLit (List.headD (raw_ints% [5869325192592289926465]) 0) 74 false) (.node 478 (sourceLit (List.headD (raw_ints% [54458388201218181782070037054301693115]) 0) 23 true) (.node 477 (sourceLit (List.headD (raw_ints% [24171316647227995129155]) 0) 72 false) .empty .empty) .empty) (.node 496 (sourceLit (List.headD (raw_ints% [168943281852869949730421805975]) 0) 51 false) .empty .empty)) (.node 499 (sourceLit (List.headD (raw_ints% [15504296583826213161553827553672125]) 0) 38 false) (.node 498 (sourceLit (List.headD (raw_ints% [19173369659581334668250218725]) 0) 55 false) .empty .empty) (.node 500 (sourceLit (List.headD (raw_ints% [75868037502004038963080205225]) 0) 57 true) .empty .empty)))

#time def treeG_J016_part079 : IntSourceTree :=
  (.node 506 (sourceLit (List.headD (raw_ints% [63555960430063890303896227275]) 0) 62 false) (.node 504 (sourceLit (List.headD (raw_ints% [204494777536216287906927323325]) 0) 60 true) (.node 503 (sourceLit (List.headD (raw_ints% [6664642852682438304051993076987740225]) 0) 35 false) (.node 502 (sourceLit (List.headD (raw_ints% [283060787357998349606049182325]) 0) 58 false) .empty .empty) .empty) (.node 505 (sourceLit (List.headD (raw_ints% [101334714185683720935332857428176970225]) 0) 32 true) .empty .empty)) (.node 508 (sourceLit (List.headD (raw_ints% [14096716785557821629609826275]) 0) 63 true) (.node 507 (sourceLit (List.headD (raw_ints% [158163566779411804008306173609045058915]) 0) 31 false) .empty .empty) (.node 509 (sourceLit (List.headD (raw_ints% [121856586786590117472913196151601986285]) 0) 29 true) .empty .empty)))

#time def treeG_J016_part080 : IntSourceTree :=
  (.node 501 (sourceLit (List.headD (raw_ints% [736794826737286750958939639159210625]) 0) 36 true) treeG_J016_part078 treeG_J016_part079)

#time def treeG_J016_part081 : IntSourceTree :=
  (.node 515 (sourceLit (List.headD (raw_ints% [210732060265493056242854276059714911345]) 0) 23 true) (.node 513 (sourceLit (List.headD (raw_ints% [211022377809733223460770310028213614225]) 0) 24 true) (.node 512 (sourceLit (List.headD (raw_ints% [2022133676008150991154195]) 0) 66 false) (.node 511 (sourceLit (List.headD (raw_ints% [36475832265144215488535101065413798295]) 0) 28 true) .empty .empty) .empty) (.node 514 (sourceLit (List.headD (raw_ints% [241297584686887863203235]) 0) 69 false) .empty .empty)) (.node 517 (sourceLit (List.headD (raw_ints% [499627858602478333365240893922170169615]) 0) 21 true) (.node 516 (sourceLit (List.headD (raw_ints% [57897061888766386509765]) 0) 71 false) .empty .empty) (.node 518 (sourceLit (List.headD (raw_ints% [27904741595104479538275]) 0) 72 false) .empty .empty)))

#time def treeG_J016_part082 : IntSourceTree :=
  (.node 541 (sourceLit (List.headD (raw_ints% [80584791409072615595294031525]) 0) 59 true) (.node 539 (sourceLit (List.headD (raw_ints% [48171510342403772127110339175]) 0) 56 false) (.node 538 (sourceLit (List.headD (raw_ints% [40594234951919073341499650236125]) 0) 40 true) (.node 537 (sourceLit (List.headD (raw_ints% [3656094716069967242421303525]) 0) 57 false) .empty .empty) .empty) (.node 540 (sourceLit (List.headD (raw_ints% [38653485941924546404996077182539875]) 0) 39 false) .empty .empty)) (.node 543 (sourceLit (List.headD (raw_ints% [438045251918358590529041850975]) 0) 59 false) (.node 542 (sourceLit (List.headD (raw_ints% [1306954527725489049954671499640337175]) 0) 37 true) .empty .empty) (.node 544 (sourceLit (List.headD (raw_ints% [9281149582885287840208521059726206575]) 0) 36 false) .empty .empty)))

#time def treeG_J016_part083 : IntSourceTree :=
  (.node 519 (sourceLit (List.headD (raw_ints% [658000010759730951562304805757744892265]) 0) 20 true) treeG_J016_part081 treeG_J016_part082)

#time def treeG_J016_part084 : IntSourceTree :=
  (.node 510 (sourceLit (List.headD (raw_ints% [8530381489082119318112625]) 0) 64 false) treeG_J016_part080 treeG_J016_part083)

#time def treeG_J016_part085 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [116700365442193871620651247418981701355]) 0) 30 true) (.node 548 (sourceLit (List.headD (raw_ints% [166147493773529661315354509054147642205]) 0) 32 false) (.node 547 (sourceLit (List.headD (raw_ints% [35299091024494763690297212425]) 0) 64 false) (.node 546 (sourceLit (List.headD (raw_ints% [120054125376738658157582656880040101175]) 0) 33 true) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [7051965931111749076648682775]) 0) 65 true) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [32529597467929384810570528261992855705]) 0) 29 true) (.node 551 (sourceLit (List.headD (raw_ints% [5083834431751337727486675]) 0) 65 false) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [74648883824293532477265]) 0) 71 false) .empty .empty)))

#time def treeG_J016_part086 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [16166091209919899685345]) 0) 73 false) (.node 557 (sourceLit (List.headD (raw_ints% [16862872620769195690305]) 0) 73 false) (.node 556 (sourceLit (List.headD (raw_ints% [170420328665787639541675880561937210735]) 0) 24 true) (.node 555 (sourceLit (List.headD (raw_ints% [141457634196032249317305]) 0) 70 false) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [390711082200041969801100819813566783385]) 0) 22 true) .empty .empty)) (.node 581 (sourceLit (List.headD (raw_ints% [1355250601808079493438876874079848625]) 0) 36 false) (.node 580 (sourceLit (List.headD (raw_ints% [7752471740275488193136909025]) 0) 61 false) .empty .empty) (.node 582 (sourceLit (List.headD (raw_ints% [605399952994288811987225308425]) 0) 58 true) .empty .empty)))

#time def treeG_J016_part087 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [178115511037596302788156848251767351095]) 0) 25 true) treeG_J016_part085 treeG_J016_part086)

#time def treeG_J016_part088 : IntSourceTree :=
  (.node 588 (sourceLit (List.headD (raw_ints% [155293080883536876390798675975]) 0) 63 false) (.node 586 (sourceLit (List.headD (raw_ints% [324574945939623862564652302875]) 0) 62 true) (.node 585 (sourceLit (List.headD (raw_ints% [398331500838012931822005531339415580625]) 0) 32 false) (.node 584 (sourceLit (List.headD (raw_ints% [160635007363643719608992293575]) 0) 62 false) .empty .empty) .empty) (.node 587 (sourceLit (List.headD (raw_ints% [1118596569793321069268967428649365868315]) 0) 31 true) .empty .empty)) (.node 590 (sourceLit (List.headD (raw_ints% [28216394105936078425912843725]) 0) 64 true) (.node 589 (sourceLit (List.headD (raw_ints% [2780216487163064698518585341017964261565]) 0) 29 false) .empty .empty) (.node 591 (sourceLit (List.headD (raw_ints% [897127091272406757476674878286439812545]) 0) 28 true) .empty .empty)))

#time def treeG_J016_part089 : IntSourceTree :=
  (.node 597 (sourceLit (List.headD (raw_ints% [2227097400050123899301573195068825202145]) 0) 21 true) (.node 595 (sourceLit (List.headD (raw_ints% [1214192028035277366062400509954423897415]) 0) 23 true) (.node 594 (sourceLit (List.headD (raw_ints% [355893485907460396614885]) 0) 69 false) (.node 593 (sourceLit (List.headD (raw_ints% [1870871860137747404415743498739329150895]) 0) 24 true) .empty .empty) .empty) (.node 596 (sourceLit (List.headD (raw_ints% [20890143076816465701885]) 0) 73 false) .empty .empty)) (.node 599 (sourceLit (List.headD (raw_ints% [2467688646840604806846501752750789374815]) 0) 20 true) (.node 598 (sourceLit (List.headD (raw_ints% [39546748887972303222945]) 0) 72 false) .empty .empty) (.node 621 (sourceLit (List.headD (raw_ints% [142604565331276521140389303725]) 0) 59 false) .empty .empty)))

#time def treeG_J016_part090 : IntSourceTree :=
  (.node 592 (sourceLit (List.headD (raw_ints% [47839074308487292755195]) 0) 72 false) treeG_J016_part088 treeG_J016_part089)

#time def treeG_J016_part091 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [17120279074486350703689365074110437625]) 0) 35 true) treeG_J016_part087 treeG_J016_part090)

#time def treeG_J016_part092 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [16313686594347498266297254725]) 0) 65 true) treeG_J016_part084 treeG_J016_part091)

#time def treeG_J016_part093 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [20155865799852708350589197748888850305]) 0) 25 true) treeG_J016_part077 treeG_J016_part092)

#time def treeG_J016_part094 : IntSourceTree :=
  (.node 627 (sourceLit (List.headD (raw_ints% [395173127988613389945246727725]) 0) 63 true) (.node 625 (sourceLit (List.headD (raw_ints% [225889753741033712674181312475]) 0) 63 false) (.node 624 (sourceLit (List.headD (raw_ints% [3300178582171454817987235766729580525]) 0) 39 true) (.node 623 (sourceLit (List.headD (raw_ints% [130430650614080925314533394925]) 0) 62 true) .empty .empty) .empty) (.node 626 (sourceLit (List.headD (raw_ints% [64798203276843948747448523527431960225]) 0) 36 false) .empty .empty)) (.node 629 (sourceLit (List.headD (raw_ints% [169397012745760374544096041525]) 0) 64 false) (.node 628 (sourceLit (List.headD (raw_ints% [160593007945856341323040242212939188815]) 0) 35 true) .empty .empty) (.node 630 (sourceLit (List.headD (raw_ints% [362114606575657321267404573554618245365]) 0) 33 false) .empty .empty)))

#time def treeG_J016_part095 : IntSourceTree :=
  (.node 636 (sourceLit (List.headD (raw_ints% [130471462421186215815090578674060835835]) 0) 27 true) (.node 634 (sourceLit (List.headD (raw_ints% [211594543637518887703448331310945224975]) 0) 28 true) (.node 633 (sourceLit (List.headD (raw_ints% [116707413409655638543515]) 0) 71 false) (.node 632 (sourceLit (List.headD (raw_ints% [108074686725559671583263043753055869605]) 0) 32 true) .empty .empty) .empty) (.node 635 (sourceLit (List.headD (raw_ints% [53608962927857036824395]) 0) 72 false) .empty .empty)) (.node 638 (sourceLit (List.headD (raw_ints% [229548289731260241187559046906907302345]) 0) 25 true) (.node 637 (sourceLit (List.headD (raw_ints% [24917413532863735713465]) 0) 73 false) .empty .empty) (.node 639 (sourceLit (List.headD (raw_ints% [365322776219568805275]) 0) 79 false) .empty .empty)))

#time def treeG_J016_part096 : IntSourceTree :=
  (.node 631 (sourceLit (List.headD (raw_ints% [881921185636494680113760325]) 0) 70 true) treeG_J016_part094 treeG_J016_part095)

#time def treeG_J016_part097 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [945639336860763656281292131425]) 0) 63 true) (.node 666 (sourceLit (List.headD (raw_ints% [1228133960903758713261377552775]) 0) 62 false) (.node 665 (sourceLit (List.headD (raw_ints% [1243177217873905365226737887622188195025]) 0) 32 true) (.node 664 (sourceLit (List.headD (raw_ints% [421496308591805570238059083425]) 0) 62 true) .empty .empty) .empty) (.node 667 (sourceLit (List.headD (raw_ints% [5265681579511333789105672934405011322715]) 0) 31 false) .empty .empty)) (.node 670 (sourceLit (List.headD (raw_ints% [367010419597456827514104926775]) 0) 64 false) (.node 669 (sourceLit (List.headD (raw_ints% [23336121504232676387867736344274180429885]) 0) 29 true) .empty .empty) (.node 671 (sourceLit (List.headD (raw_ints% [24072461912114475318590567585782007515905]) 0) 28 false) .empty .empty)))

#time def treeG_J016_part098 : IntSourceTree :=
  (.node 677 (sourceLit (List.headD (raw_ints% [14473249789861711725030020875210961784735]) 0) 21 true) (.node 675 (sourceLit (List.headD (raw_ints% [12327858764765931446958292693946070500985]) 0) 23 true) (.node 674 (sourceLit (List.headD (raw_ints% [577765821369784711733235]) 0) 69 false) (.node 673 (sourceLit (List.headD (raw_ints% [53463367743348804446214934902825276086865]) 0) 24 true) .empty .empty) .empty) (.node 676 (sourceLit (List.headD (raw_ints% [16359409925520285561255]) 0) 74 false) .empty .empty)) (.node 679 (sourceLit (List.headD (raw_ints% [12223401895960050629157277249291277975265]) 0) 20 true) (.node 678 (sourceLit (List.headD (raw_ints% [60122905243482639630915]) 0) 72 false) .empty .empty) (.node 704 (sourceLit (List.headD (raw_ints% [64819348768126537594735638197708568225]) 0) 36 false) .empty .empty)))

#time def treeG_J016_part099 : IntSourceTree :=
  (.node 672 (sourceLit (List.headD (raw_ints% [882016863785111654699270715]) 0) 71 true) treeG_J016_part097 treeG_J016_part098)

#time def treeG_J016_part100 : IntSourceTree :=
  (.node 663 (sourceLit (List.headD (raw_ints% [38417920110754899050837752063871924025]) 0) 35 false) treeG_J016_part096 treeG_J016_part099)

#time def treeG_J016_part101 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [26233038356837934958006972932711126392805]) 0) 30 true) (.node 708 (sourceLit (List.headD (raw_ints% [6550425643078184519689994872108524833235]) 0) 32 false) (.node 707 (sourceLit (List.headD (raw_ints% [405826772223093025801656070125]) 0) 65 false) (.node 706 (sourceLit (List.headD (raw_ints% [1761562844088656955206326075841643876825]) 0) 33 true) .empty .empty) .empty) (.node 709 (sourceLit (List.headD (raw_ints% [557518174803262015412694086475]) 0) 65 true) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [24937059405918952691256671935806454472745]) 0) 29 false) (.node 711 (sourceLit (List.headD (raw_ints% [395231897537824657277745257175]) 0) 65 false) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [1764150434983632965037084945]) 0) 71 true) .empty .empty)))

#time def treeG_J016_part102 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [36742247565430236093315]) 0) 73 false) (.node 717 (sourceLit (List.headD (raw_ints% [40520226169217406531555]) 0) 73 false) (.node 716 (sourceLit (List.headD (raw_ints% [11284087065396441720437568064553583814305]) 0) 24 true) (.node 715 (sourceLit (List.headD (raw_ints% [363329969658356564435655]) 0) 70 false) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [12636863472011629795529548499955703365975]) 0) 22 true) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [3817678210235115844910339136375]) 0) 62 true) (.node 745 (sourceLit (List.headD (raw_ints% [3317396378453954568258278309948862378225]) 0) 32 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [19358184332220589430756281541138162337315]) 0) 31 true) .empty .empty)))

#time def treeG_J016_part103 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [51770611394248653344587348252337714287065]) 0) 25 true) treeG_J016_part101 treeG_J016_part102)

#time def treeG_J016_part104 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [1649435169722161776686641938794438362342545]) 0) 24 false) (.node 751 (sourceLit (List.headD (raw_ints% [233936768766817954982646351047471018658345]) 0) 28 true) (.node 750 (sourceLit (List.headD (raw_ints% [2597083118810504889164881272675]) 0) 64 true) (.node 749 (sourceLit (List.headD (raw_ints% [128142931793483628702907654298010577761645]) 0) 29 false) .empty .empty) .empty) (.node 752 (sourceLit (List.headD (raw_ints% [423456437178948230228121920055]) 0) 66 false) .empty .empty)) (.node 755 (sourceLit (List.headD (raw_ints% [401837032389223295309740493324755643795535]) 0) 23 true) (.node 754 (sourceLit (List.headD (raw_ints% [14113781245690433505008412795]) 0) 69 true) .empty .empty) (.node 756 (sourceLit (List.headD (raw_ints% [232454690254194279945615]) 0) 71 false) .empty .empty)))

#time def treeG_J016_part105 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [12954304987649386975223138206623343585275]) 0) 33 true) (.node 786 (sourceLit (List.headD (raw_ints% [2539479611271305761732302192895253127525]) 0) 34 false) (.node 759 (sourceLit (List.headD (raw_ints% [88871505880132987735079110750354348952535]) 0) 20 true) (.node 758 (sourceLit (List.headD (raw_ints% [101957999433386986495305]) 0) 72 false) .empty .empty) .empty) (.node 787 (sourceLit (List.headD (raw_ints% [5440985299127487948116963416875]) 0) 63 true) .empty .empty)) (.node 790 (sourceLit (List.headD (raw_ints% [77187985075160781830457313615360852077225]) 0) 31 false) (.node 789 (sourceLit (List.headD (raw_ints% [5307289864252031893519928865375]) 0) 64 false) .empty .empty) (.node 791 (sourceLit (List.headD (raw_ints% [1496157508174164773221313264925]) 0) 66 true) .empty .empty)))

#time def treeG_J016_part106 : IntSourceTree :=
  (.node 757 (sourceLit (List.headD (raw_ints% [166072143256481355801971068157646379244145]) 0) 21 true) treeG_J016_part104 treeG_J016_part105)

#time def treeG_J016_part107 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [4192253514645507862694540692425]) 0) 63 false) treeG_J016_part103 treeG_J016_part106)

#time def treeG_J016_part108 : IntSourceTree :=
  (.node 705 (sourceLit (List.headD (raw_ints% [161846515583209820728060098975]) 0) 65 true) treeG_J016_part100 treeG_J016_part107)

#time def treeG_J016_part109 : IntSourceTree :=
  (.node 797 (sourceLit (List.headD (raw_ints% [151414237915759466882505]) 0) 72 false) (.node 795 (sourceLit (List.headD (raw_ints% [7057072287830045930786424225]) 0) 71 true) (.node 794 (sourceLit (List.headD (raw_ints% [850602890558205215015614643523388038314805]) 0) 26 false) (.node 793 (sourceLit (List.headD (raw_ints% [451682844138686357668715279175]) 0) 67 false) .empty .empty) .empty) (.node 796 (sourceLit (List.headD (raw_ints% [195276472661913426794651462630101029990615]) 0) 25 true) .empty .empty)) (.node 799 (sourceLit (List.headD (raw_ints% [32607875933978375200995]) 0) 74 false) (.node 798 (sourceLit (List.headD (raw_ints% [76717639892234863003220759828845337939085]) 0) 23 true) .empty .empty) (.node 827 (sourceLit (List.headD (raw_ints% [59989858112561481618473116627462212377715]) 0) 31 false) .empty .empty)))

#time def treeG_J016_part110 : IntSourceTree :=
  (.node 833 (sourceLit (List.headD (raw_ints% [18217360172777323867816435409724196642732305]) 0) 24 true) (.node 831 (sourceLit (List.headD (raw_ints% [1468944529969390464269963368893244651893945]) 0) 28 false) (.node 830 (sourceLit (List.headD (raw_ints% [13211662847314568676204739003425]) 0) 64 false) (.node 829 (sourceLit (List.headD (raw_ints% [542680691398264011910048076909957572490445]) 0) 29 true) .empty .empty) .empty) (.node 832 (sourceLit (List.headD (raw_ints% [3415771453527277776670748449905]) 0) 66 true) .empty .empty)) (.node 835 (sourceLit (List.headD (raw_ints% [14011483281320506735559574789698964256832415]) 0) 23 false) (.node 834 (sourceLit (List.headD (raw_ints% [479910406630067224678732104765]) 0) 68 false) .empty .empty) (.node 836 (sourceLit (List.headD (raw_ints% [14114377030350346055852794065]) 0) 71 true) .empty .empty)))

#time def treeG_J016_part111 : IntSourceTree :=
  (.node 828 (sourceLit (List.headD (raw_ints% [15074224112900483758928467526175]) 0) 63 true) treeG_J016_part109 treeG_J016_part110)

#time def treeG_J016_part112 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [697056661548585575570962704140679276644895]) 0) 30 true) (.node 868 (sourceLit (List.headD (raw_ints% [85898468087860255568919393040708899548265]) 0) 32 false) (.node 839 (sourceLit (List.headD (raw_ints% [1138610732395624820316453046511171058072825]) 0) 20 true) (.node 838 (sourceLit (List.headD (raw_ints% [200870476398131947269705]) 0) 72 false) .empty .empty) .empty) (.node 869 (sourceLit (List.headD (raw_ints% [10190756988576257826224198195775]) 0) 65 true) .empty .empty)) (.node 872 (sourceLit (List.headD (raw_ints% [1727818358142127371943866391876522125025035]) 0) 29 false) (.node 871 (sourceLit (List.headD (raw_ints% [16203977863662898222647365533275]) 0) 65 false) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [483431787208245516792432966135]) 0) 70 true) .empty .empty)))

#time def treeG_J016_part113 : IntSourceTree :=
  (.node 879 (sourceLit (List.headD (raw_ints% [135654724530175196867715]) 0) 73 false) (.node 877 (sourceLit (List.headD (raw_ints% [7057264222294130907659838285]) 0) 73 true) (.node 876 (sourceLit (List.headD (raw_ints% [14402036226644333589148877714959166316813645]) 0) 24 false) (.node 875 (sourceLit (List.headD (raw_ints% [508138695781387408401877801665]) 0) 69 false) .empty .empty) .empty) (.node 878 (sourceLit (List.headD (raw_ints% [5929339702140278575620434216347895904577365]) 0) 22 true) .empty .empty)) (.node 910 (sourceLit (List.headD (raw_ints% [53974690801619599981101531786525]) 0) 64 true) (.node 909 (sourceLit (List.headD (raw_ints% [1917056180804028101012758365561299965262685]) 0) 29 false) .empty .empty) (.node 911 (sourceLit (List.headD (raw_ints% [7045397822358075068837665002018678865053105]) 0) 28 true) .empty .empty)))

#time def treeG_J016_part114 : IntSourceTree :=
  (.node 874 (sourceLit (List.headD (raw_ints% [19918565953893734297847664696770972719361915]) 0) 25 true) treeG_J016_part112 treeG_J016_part113)

#time def treeG_J016_part115 : IntSourceTree :=
  (.node 837 (sourceLit (List.headD (raw_ints% [6082774981924748301626875736005586580455535]) 0) 21 true) treeG_J016_part111 treeG_J016_part114)

#time def treeG_J016_part116 : IntSourceTree :=
  (.node 917 (sourceLit (List.headD (raw_ints% [236515354608234085728008919175352247649473855]) 0) 21 false) (.node 915 (sourceLit (List.headD (raw_ints% [173360010912470381118340892363866746011727735]) 0) 23 true) (.node 914 (sourceLit (List.headD (raw_ints% [4347364704296031359018195833845]) 0) 68 true) (.node 913 (sourceLit (List.headD (raw_ints% [128797735093873475672223884489821612644334545]) 0) 24 false) .empty .empty) .empty) (.node 916 (sourceLit (List.headD (raw_ints% [536367449842088100513583389795]) 0) 70 false) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [46296106884726603784647020684271996178546095]) 0) 20 true) (.node 918 (sourceLit (List.headD (raw_ints% [28229257759652921762586622845]) 0) 72 true) .empty .empty) (.node 950 (sourceLit (List.headD (raw_ints% [653528210588153419145930267425494810476895]) 0) 32 false) .empty .empty)))

#time def treeG_J016_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [46940511784778678676872442519706478082135345]) 0) 26 true) (.node 954 (sourceLit (List.headD (raw_ints% [37179075261941802492517887296648146340924115]) 0) 27 false) (.node 953 (sourceLit (List.headD (raw_ints% [5871800903714035033414394428065]) 0) 69 false) (.node 952 (sourceLit (List.headD (raw_ints% [2193304045125050610195382848473800247519535]) 0) 31 true) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [2427751700038709383710036817755]) 0) 70 true) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [60611173577593591075907338347925035888512805]) 0) 24 false) (.node 957 (sourceLit (List.headD (raw_ints% [564596506731264624144222742935]) 0) 71 false) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [13783883503113990203995845]) 0) 84 true) .empty .empty)))

#time def treeG_J016_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [8772333583160312275468612164975]) 0) 68 true) treeG_J016_part116 treeG_J016_part117)

#time def treeG_J016_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [148206441122729386476702341445]) 0) 74 false) (.node 996 (sourceLit (List.headD (raw_ints% [5391870849919506867933657025305]) 0) 70 true) (.node 995 (sourceLit (List.headD (raw_ints% [1363090419294608060878913285856607428921299415]) 0) 23 false) (.node 994 (sourceLit (List.headD (raw_ints% [27834568319152171492675773546105]) 0) 68 false) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [3240708108834069521047845240436566844906135935]) 0) 21 true) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [838999871693653641852313442885707061373031965]) 0) 25 true) (.node 999 (sourceLit (List.headD (raw_ints% [1985853661367721518213681847817873144610955855]) 0) 20 false) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [32690071719229590260095847181615]) 0) 69 false) .empty .empty)))

#time def treeG_J016_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [4760242821143637141003688025865]) 0) 73 false) (.node 1039 (sourceLit (List.headD (raw_ints% [155263789476323749461148214085]) 0) 75 false) (.node 1038 (sourceLit (List.headD (raw_ints% [3483152803144443885351474593828266988460187155]) 0) 22 true) (.node 1037 (sourceLit (List.headD (raw_ints% [372279209790673218254867485515]) 0) 75 true) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [8075089392843837195697420828942263919905555135]) 0) 23 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [1637323280285422259496172283505]) 0) 74 true) (.node 1077 (sourceLit (List.headD (raw_ints% [28054347571773633930430294135403500304903588655]) 0) 21 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [29851076086523272601025478598444009052292453095]) 0) 20 true) .empty .empty)))

#time def treeG_J016_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [1550852466433722775586403055935433341249840795]) 0) 24 false) treeG_J016_part119 treeG_J016_part120)

#time def treeG_J016_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [690283570645886431882241893699114476009335505]) 0) 24 true) treeG_J016_part118 treeG_J016_part121)

#time def treeG_J016_part123 : IntSourceTree :=
  (.node 912 (sourceLit (List.headD (raw_ints% [4904937329297543999829528495795]) 0) 68 false) treeG_J016_part115 treeG_J016_part122)

#time def treeG_J016_part124 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [129436914086368453836951511491638736565545]) 0) 30 true) treeG_J016_part108 treeG_J016_part123)

#time def treeG_J016_part125 : IntSourceTree :=
  (.node 622 (sourceLit (List.headD (raw_ints% [332775641191696067924193546715023225]) 0) 40 false) treeG_J016_part093 treeG_J016_part124)

#time def treeG_J016_part126 : IntSourceTree :=
  (.node 374 (sourceLit (List.headD (raw_ints% [153376731253431375233372048025]) 0) 50 false) treeG_J016_part062 treeG_J016_part125)

#time def treeG_J016 : IntSourceTree := treeG_J016_part126

#time def treeG_J017_part000 : IntSourceTree :=
  (.node 8 (sourceLit (List.headD (raw_ints% [120963911245531441305036036075]) 0) 46 false) (.node 6 (sourceLit (List.headD (raw_ints% [1001458738463711054601938072625]) 0) 43 false) (.node 5 (sourceLit (List.headD (raw_ints% [505819217750915711904742455975]) 0) 42 false) (.node 4 (sourceLit (List.headD (raw_ints% [2089168249579367692432528015875]) 0) 42 false) .empty .empty) .empty) (.node 7 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 42 false) .empty .empty)) (.node 11 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 46 true) (.node 10 (sourceLit (List.headD (raw_ints% [58744052690484308677010298675]) 0) 47 false) (.node 9 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty) .empty) (.node 12 (sourceLit (List.headD (raw_ints% [14316061614989096983196951775]) 0) 49 false) .empty .empty)))

#time def treeG_J017_part001 : IntSourceTree :=
  (.node 18 (sourceLit (List.headD (raw_ints% [72074535838565955423505082804475]) 0) 39 true) (.node 16 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 54 false) (.node 15 (sourceLit (List.headD (raw_ints% [13960535108245484673635817525]) 0) 49 true) (.node 14 (sourceLit (List.headD (raw_ints% [6996878218782075043084289625]) 0) 50 false) .empty .empty) .empty) (.node 17 (sourceLit (List.headD (raw_ints% [663843756034384296049396575]) 0) 55 true) .empty .empty)) (.node 20 (sourceLit (List.headD (raw_ints% [58776168389001233736462715316475]) 0) 38 true) (.node 19 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 54 false) .empty .empty) (.node 21 (sourceLit (List.headD (raw_ints% [52608106908135902579581125]) 0) 57 false) .empty .empty)))

#time def treeG_J017_part002 : IntSourceTree :=
  (.node 13 (sourceLit (List.headD (raw_ints% [6569080750011892362399252675]) 0) 49 true) treeG_J017_part000 treeG_J017_part001)

#time def treeG_J017_part003 : IntSourceTree :=
  (.node 27 (sourceLit (List.headD (raw_ints% [3139103755257088841969175]) 0) 61 false) (.node 25 (sourceLit (List.headD (raw_ints% [796223598026546681201925]) 0) 63 false) (.node 24 (sourceLit (List.headD (raw_ints% [219358589570633815267003691142375]) 0) 35 true) (.node 23 (sourceLit (List.headD (raw_ints% [51749199040247969476241025]) 0) 57 false) .empty .empty) .empty) (.node 26 (sourceLit (List.headD (raw_ints% [1349432100967235433474187046214225]) 0) 32 true) .empty .empty)) (.node 29 (sourceLit (List.headD (raw_ints% [387058189853318997303225]) 0) 64 false) (.node 28 (sourceLit (List.headD (raw_ints% [2142279786084298855319266544735685]) 0) 31 true) .empty .empty) (.node 30 (sourceLit (List.headD (raw_ints% [6932319689390900642129314816146045]) 0) 29 true) .empty .empty)))

#time def treeG_J017_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [246258496147598909353926063996732825]) 0) 23 true) (.node 34 (sourceLit (List.headD (raw_ints% [149372084187442385342552148534975825]) 0) 24 true) (.node 33 (sourceLit (List.headD (raw_ints% [2948374455750583249635]) 0) 71 false) (.node 32 (sourceLit (List.headD (raw_ints% [11343551176838629958171591546858655]) 0) 28 true) .empty .empty) .empty) (.node 35 (sourceLit (List.headD (raw_ints% [5827828038149823491835]) 0) 70 false) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [810074579729603496637136662987976415]) 0) 21 true) (.node 37 (sourceLit (List.headD (raw_ints% [720335500418863195965]) 0) 73 false) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [712617350715991619325]) 0) 73 false) .empty .empty)))

#time def treeG_J017_part005 : IntSourceTree :=
  (.node 31 (sourceLit (List.headD (raw_ints% [382073053341589264620675]) 0) 64 false) treeG_J017_part003 treeG_J017_part004)

#time def treeG_J017_part006 : IntSourceTree :=
  (.node 22 (sourceLit (List.headD (raw_ints% [150998281453547088472164588829425]) 0) 36 true) treeG_J017_part002 treeG_J017_part005)

#time def treeG_J017_part007 : IntSourceTree :=
  (.node 50 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 48 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 43 false) (.node 47 (sourceLit (List.headD (raw_ints% [1001458738463711054601938072625]) 0) 44 false) (.node 46 (sourceLit (List.headD (raw_ints% [505819217750915711904742455975]) 0) 43 false) .empty .empty) .empty) (.node 49 (sourceLit (List.headD (raw_ints% [120963911245531441305036036075]) 0) 47 false) .empty .empty)) (.node 52 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 47 true) (.node 51 (sourceLit (List.headD (raw_ints% [58744052690484308677010298675]) 0) 48 false) .empty .empty) (.node 53 (sourceLit (List.headD (raw_ints% [14316061614989096983196951775]) 0) 50 false) .empty .empty)))

#time def treeG_J017_part008 : IntSourceTree :=
  (.node 59 (sourceLit (List.headD (raw_ints% [72074535838565955423505082804475]) 0) 40 true) (.node 57 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 55 false) (.node 56 (sourceLit (List.headD (raw_ints% [13960535108245484673635817525]) 0) 50 true) (.node 55 (sourceLit (List.headD (raw_ints% [6996878218782075043084289625]) 0) 51 false) .empty .empty) .empty) (.node 58 (sourceLit (List.headD (raw_ints% [663843756034384296049396575]) 0) 56 true) .empty .empty)) (.node 61 (sourceLit (List.headD (raw_ints% [58776168389001233736462715316475]) 0) 39 true) (.node 60 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 55 false) .empty .empty) (.node 62 (sourceLit (List.headD (raw_ints% [52608106908135902579581125]) 0) 58 false) .empty .empty)))

#time def treeG_J017_part009 : IntSourceTree :=
  (.node 54 (sourceLit (List.headD (raw_ints% [6569080750011892362399252675]) 0) 50 true) treeG_J017_part007 treeG_J017_part008)

#time def treeG_J017_part010 : IntSourceTree :=
  (.node 68 (sourceLit (List.headD (raw_ints% [3139103755257088841969175]) 0) 62 false) (.node 66 (sourceLit (List.headD (raw_ints% [796223598026546681201925]) 0) 64 false) (.node 65 (sourceLit (List.headD (raw_ints% [219358589570633815267003691142375]) 0) 36 true) (.node 64 (sourceLit (List.headD (raw_ints% [51749199040247969476241025]) 0) 58 false) .empty .empty) .empty) (.node 67 (sourceLit (List.headD (raw_ints% [1349432100967235433474187046214225]) 0) 33 true) .empty .empty)) (.node 70 (sourceLit (List.headD (raw_ints% [387058189853318997303225]) 0) 65 false) (.node 69 (sourceLit (List.headD (raw_ints% [2142279786084298855319266544735685]) 0) 32 true) .empty .empty) (.node 71 (sourceLit (List.headD (raw_ints% [6932319689390900642129314816146045]) 0) 30 true) .empty .empty)))

#time def treeG_J017_part011 : IntSourceTree :=
  (.node 77 (sourceLit (List.headD (raw_ints% [246258496147598909353926063996732825]) 0) 24 true) (.node 75 (sourceLit (List.headD (raw_ints% [149372084187442385342552148534975825]) 0) 25 true) (.node 74 (sourceLit (List.headD (raw_ints% [2948374455750583249635]) 0) 72 false) (.node 73 (sourceLit (List.headD (raw_ints% [11343551176838629958171591546858655]) 0) 29 true) .empty .empty) .empty) (.node 76 (sourceLit (List.headD (raw_ints% [5827828038149823491835]) 0) 71 false) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [810074579729603496637136662987976415]) 0) 22 true) (.node 78 (sourceLit (List.headD (raw_ints% [720335500418863195965]) 0) 74 false) .empty .empty) (.node 86 (sourceLit (List.headD (raw_ints% [3176877760695024330263117959125]) 0) 43 false) .empty .empty)))

#time def treeG_J017_part012 : IntSourceTree :=
  (.node 72 (sourceLit (List.headD (raw_ints% [382073053341589264620675]) 0) 65 false) treeG_J017_part010 treeG_J017_part011)

#time def treeG_J017_part013 : IntSourceTree :=
  (.node 63 (sourceLit (List.headD (raw_ints% [150998281453547088472164588829425]) 0) 37 true) treeG_J017_part009 treeG_J017_part012)

#time def treeG_J017_part014 : IntSourceTree :=
  (.node 45 (sourceLit (List.headD (raw_ints% [2089168249579367692432528015875]) 0) 43 false) treeG_J017_part006 treeG_J017_part013)

#time def treeG_J017_part015 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [11106997768873802923453336725]) 0) 51 false) (.node 90 (sourceLit (List.headD (raw_ints% [183183769800578573933061773475]) 0) 47 false) (.node 89 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 44 false) (.node 88 (sourceLit (List.headD (raw_ints% [759530915972648171991866000475]) 0) 45 false) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 46 false) .empty .empty)) (.node 94 (sourceLit (List.headD (raw_ints% [21635245011196118923309613925]) 0) 50 false) (.node 93 (sourceLit (List.headD (raw_ints% [8114746808838219977081429775]) 0) 48 true) .empty .empty) (.node 95 (sourceLit (List.headD (raw_ints% [12315787891802084775961193175]) 0) 49 true) .empty .empty)))

#time def treeG_J017_part016 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [323164085292834830131712625]) 0) 56 false) (.node 99 (sourceLit (List.headD (raw_ints% [5739130347384181003686047475]) 0) 54 true) (.node 98 (sourceLit (List.headD (raw_ints% [128223198403394780324350634420475]) 0) 39 false) (.node 97 (sourceLit (List.headD (raw_ints% [3339035011695335936845472325]) 0) 51 true) .empty .empty) .empty) (.node 100 (sourceLit (List.headD (raw_ints% [517820118319526409651577947119325]) 0) 38 true) .empty .empty)) (.node 103 (sourceLit (List.headD (raw_ints% [158683228592295640842083475]) 0) 57 false) (.node 102 (sourceLit (List.headD (raw_ints% [789420412770472651311238856234175]) 0) 36 true) .empty .empty) (.node 104 (sourceLit (List.headD (raw_ints% [988627662057742892510313019493025]) 0) 35 true) .empty .empty)))

#time def treeG_J017_part017 : IntSourceTree :=
  (.node 96 (sourceLit (List.headD (raw_ints% [5283357022345648501920790125]) 0) 52 false) treeG_J017_part015 treeG_J017_part016)

#time def treeG_J017_part018 : IntSourceTree :=
  (.node 110 (sourceLit (List.headD (raw_ints% [27344156887957881042978949899624915]) 0) 29 true) (.node 108 (sourceLit (List.headD (raw_ints% [8653177021653584612474229824978115]) 0) 31 true) (.node 107 (sourceLit (List.headD (raw_ints% [9600473813167658057261625]) 0) 61 false) (.node 106 (sourceLit (List.headD (raw_ints% [5670042765293046655069931070341775]) 0) 32 true) .empty .empty) .empty) (.node 109 (sourceLit (List.headD (raw_ints% [2364987375550450847362725]) 0) 63 false) .empty .empty)) (.node 112 (sourceLit (List.headD (raw_ints% [44115006338288575178862926982309705]) 0) 28 true) (.node 111 (sourceLit (List.headD (raw_ints% [1166159706071686724592225]) 0) 64 false) .empty .empty) (.node 113 (sourceLit (List.headD (raw_ints% [287725070757570600632355]) 0) 66 false) .empty .empty)))

#time def treeG_J017_part019 : IntSourceTree :=
  (.node 119 (sourceLit (List.headD (raw_ints% [2168724650959461164535]) 0) 73 false) (.node 117 (sourceLit (List.headD (raw_ints% [4387157037312097099905]) 0) 72 false) (.node 116 (sourceLit (List.headD (raw_ints% [948718177351940173386491124283073775]) 0) 23 true) (.node 115 (sourceLit (List.headD (raw_ints% [17759167607854842505245]) 0) 70 false) .empty .empty) .empty) (.node 118 (sourceLit (List.headD (raw_ints% [3130061358631979053025680360959748785]) 0) 21 true) .empty .empty)) (.node 128 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 44 false) (.node 127 (sourceLit (List.headD (raw_ints% [543854755557828318915294971625]) 0) 46 false) .empty .empty) (.node 129 (sourceLit (List.headD (raw_ints% [517603093481585289381793928325]) 0) 46 false) .empty .empty)))

#time def treeG_J017_part020 : IntSourceTree :=
  (.node 114 (sourceLit (List.headD (raw_ints% [576615191130229931980429710463978095]) 0) 24 true) treeG_J017_part018 treeG_J017_part019)

#time def treeG_J017_part021 : IntSourceTree :=
  (.node 105 (sourceLit (List.headD (raw_ints% [39009621471823222577010225]) 0) 59 false) treeG_J017_part017 treeG_J017_part020)

#time def treeG_J017_part022 : IntSourceTree :=
  (.node 135 (sourceLit (List.headD (raw_ints% [3659591698103510970056331075]) 0) 53 false) (.node 133 (sourceLit (List.headD (raw_ints% [30111929460506114710616395125]) 0) 50 false) (.node 132 (sourceLit (List.headD (raw_ints% [21252908308862004701879935125]) 0) 48 false) (.node 131 (sourceLit (List.headD (raw_ints% [7777482319380891578503217175]) 0) 52 false) .empty .empty) .empty) (.node 134 (sourceLit (List.headD (raw_ints% [5023414691185564747717075575]) 0) 49 false) .empty .empty)) (.node 137 (sourceLit (List.headD (raw_ints% [3569835825909221960757290625]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [822373608221699948837312175]) 0) 51 false) .empty .empty) (.node 138 (sourceLit (List.headD (raw_ints% [7282465084854812799944872875]) 0) 52 false) .empty .empty)))

#time def treeG_J017_part023 : IntSourceTree :=
  (.node 144 (sourceLit (List.headD (raw_ints% [53467014776023835682921225]) 0) 59 false) (.node 142 (sourceLit (List.headD (raw_ints% [217947871476563024972550375]) 0) 57 false) (.node 141 (sourceLit (List.headD (raw_ints% [229521974965262587957557615901425]) 0) 40 true) (.node 140 (sourceLit (List.headD (raw_ints% [3083755323246643819488461175]) 0) 56 true) .empty .empty) .empty) (.node 143 (sourceLit (List.headD (raw_ints% [319211065658462781419537133702375]) 0) 38 true) .empty .empty)) (.node 146 (sourceLit (List.headD (raw_ints% [26270043903398475677779425]) 0) 60 false) (.node 145 (sourceLit (List.headD (raw_ints% [384634536243554538621654664175325]) 0) 37 true) .empty .empty) (.node 147 (sourceLit (List.headD (raw_ints% [2160305332162905610797872012063775]) 0) 34 true) .empty .empty)))

#time def treeG_J017_part024 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [100148867120980367873927858612475]) 0) 41 false) treeG_J017_part022 treeG_J017_part023)

#time def treeG_J017_part025 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [16385727580724972610345667717725525]) 0) 30 true) (.node 151 (sourceLit (List.headD (raw_ints% [10205918599283490200424817541739435]) 0) 31 true) (.node 150 (sourceLit (List.headD (raw_ints% [1590870995843812852756275]) 0) 64 false) (.node 149 (sourceLit (List.headD (raw_ints% [3255448617784642878577481640121215]) 0) 33 true) .empty .empty) .empty) (.node 152 (sourceLit (List.headD (raw_ints% [392043326365048729985775]) 0) 66 false) .empty .empty)) (.node 155 (sourceLit (List.headD (raw_ints% [213621553471393773318938780964501135]) 0) 26 true) (.node 154 (sourceLit (List.headD (raw_ints% [193377088173551936644035]) 0) 67 false) .empty .empty) (.node 156 (sourceLit (List.headD (raw_ints% [5965669784852509506705]) 0) 72 false) .empty .empty)))

#time def treeG_J017_part026 : IntSourceTree :=
  (.node 170 (sourceLit (List.headD (raw_ints% [167209661840503357724366077425]) 0) 48 false) (.node 168 (sourceLit (List.headD (raw_ints% [1415888106258665103669313886025]) 0) 45 false) (.node 159 (sourceLit (List.headD (raw_ints% [1159993389451187778194271848985886185]) 0) 23 true) (.node 158 (sourceLit (List.headD (raw_ints% [2946486036474370707975]) 0) 73 false) .empty .empty) .empty) (.node 169 (sourceLit (List.headD (raw_ints% [1219916936928679069887908276175]) 0) 44 false) .empty .empty)) (.node 172 (sourceLit (List.headD (raw_ints% [20002931508649763390559531975]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [123266868191399627270903623725]) 0) 47 false) .empty .empty) (.node 173 (sourceLit (List.headD (raw_ints% [50620563426562229380841300025]) 0) 48 false) .empty .empty)))

#time def treeG_J017_part027 : IntSourceTree :=
  (.node 157 (sourceLit (List.headD (raw_ints% [351229840602170632016282530143170475]) 0) 25 true) treeG_J017_part025 treeG_J017_part026)

#time def treeG_J017_part028 : IntSourceTree :=
  (.node 148 (sourceLit (List.headD (raw_ints% [3230685028955284607646225]) 0) 63 false) treeG_J017_part024 treeG_J017_part027)

#time def treeG_J017_part029 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 45 false) treeG_J017_part021 treeG_J017_part028)

#time def treeG_J017_part030 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [1755490226312001588375282641325]) 0) 42 false) treeG_J017_part014 treeG_J017_part029)

#time def treeG_J017_part031 : IntSourceTree :=
  (.node 179 (sourceLit (List.headD (raw_ints% [18760725779623174807316967825]) 0) 53 false) (.node 177 (sourceLit (List.headD (raw_ints% [4983782228138735834520096675]) 0) 51 false) (.node 176 (sourceLit (List.headD (raw_ints% [9355009770068395378304534175]) 0) 52 false) (.node 175 (sourceLit (List.headD (raw_ints% [22362617274173214271395344325]) 0) 49 false) .empty .empty) .empty) (.node 178 (sourceLit (List.headD (raw_ints% [11246818060001395114255735220475]) 0) 39 true) .empty .empty)) (.node 182 (sourceLit (List.headD (raw_ints% [6555282786117930163330604852611425]) 0) 36 true) (.node 181 (sourceLit (List.headD (raw_ints% [6490674731786122469108634975]) 0) 56 true) (.node 180 (sourceLit (List.headD (raw_ints% [2120201992255212295634423684918925]) 0) 38 false) .empty .empty) .empty) (.node 183 (sourceLit (List.headD (raw_ints% [277212514360830409103017275]) 0) 57 false) .empty .empty)))

#time def treeG_J017_part032 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [4096382682360118367929725]) 0) 63 false) (.node 187 (sourceLit (List.headD (raw_ints% [2083696261278852202564725]) 0) 64 false) (.node 186 (sourceLit (List.headD (raw_ints% [18946567554294443816715967436879025]) 0) 32 true) (.node 185 (sourceLit (List.headD (raw_ints% [67924408080224448788832225]) 0) 59 false) .empty .empty) .empty) (.node 188 (sourceLit (List.headD (raw_ints% [25911708292952905160291722368042285]) 0) 31 true) .empty .empty)) (.node 191 (sourceLit (List.headD (raw_ints% [2015582285615938980920325]) 0) 64 false) (.node 190 (sourceLit (List.headD (raw_ints% [76830198881150691071500462584253965]) 0) 29 true) .empty .empty) (.node 192 (sourceLit (List.headD (raw_ints% [119179691250247268027934153685521255]) 0) 28 true) .empty .empty)))

#time def treeG_J017_part033 : IntSourceTree :=
  (.node 184 (sourceLit (List.headD (raw_ints% [4118749388477661610202281119744975]) 0) 35 true) treeG_J017_part031 treeG_J017_part032)

#time def treeG_J017_part034 : IntSourceTree :=
  (.node 198 (sourceLit (List.headD (raw_ints% [8109293540637481171495360603621706415]) 0) 21 true) (.node 196 (sourceLit (List.headD (raw_ints% [2469226678190360199716529371148944385]) 0) 23 true) (.node 195 (sourceLit (List.headD (raw_ints% [122340417742132566623055]) 0) 68 false) (.node 194 (sourceLit (List.headD (raw_ints% [1520757939202566562143815757404889105]) 0) 24 true) .empty .empty) .empty) (.node 197 (sourceLit (List.headD (raw_ints% [7544182532392921913505]) 0) 72 false) .empty .empty)) (.node 209 (sourceLit (List.headD (raw_ints% [224571253194269953571879989425]) 0) 48 false) (.node 199 (sourceLit (List.headD (raw_ints% [3724247421989280251415]) 0) 73 false) .empty .empty) (.node 210 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 50 false) .empty .empty)))

#time def treeG_J017_part035 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [20717870057729814373720719975]) 0) 50 false) (.node 214 (sourceLit (List.headD (raw_ints% [22798574367688332316562112225]) 0) 50 false) (.node 213 (sourceLit (List.headD (raw_ints% [49899796574092938851621732775]) 0) 50 false) (.node 212 (sourceLit (List.headD (raw_ints% [12751744985317202821127961075]) 0) 51 false) .empty .empty) .empty) (.node 215 (sourceLit (List.headD (raw_ints% [23950247117402066617697852025]) 0) 51 false) .empty .empty)) (.node 218 (sourceLit (List.headD (raw_ints% [287335357089509620678097025]) 0) 55 true) (.node 217 (sourceLit (List.headD (raw_ints% [2892586972079586708773621775]) 0) 54 false) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [211544552301962130862111452445425]) 0) 40 true) .empty .empty)))

#time def treeG_J017_part036 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [104989803285456225096340340025]) 0) 49 false) treeG_J017_part034 treeG_J017_part035)

#time def treeG_J017_part037 : IntSourceTree :=
  (.node 193 (sourceLit (List.headD (raw_ints% [496361581972526859339195]) 0) 66 false) treeG_J017_part033 treeG_J017_part036)

#time def treeG_J017_part038 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [3349480315990552532958971791394325]) 0) 36 true) (.node 223 (sourceLit (List.headD (raw_ints% [5916860654801004600491530585206675]) 0) 37 true) (.node 222 (sourceLit (List.headD (raw_ints% [3354311301631342747040592675]) 0) 58 true) (.node 221 (sourceLit (List.headD (raw_ints% [2579245942185737471549538916721775]) 0) 39 false) .empty .empty) .empty) (.node 224 (sourceLit (List.headD (raw_ints% [170278484808782737737174825]) 0) 58 false) .empty .empty)) (.node 227 (sourceLit (List.headD (raw_ints% [14625956889968632595120223412751475]) 0) 33 true) (.node 226 (sourceLit (List.headD (raw_ints% [81356180032863228732525]) 0) 69 false) .empty .empty) (.node 228 (sourceLit (List.headD (raw_ints% [5104100016160124202612675]) 0) 63 false) .empty .empty)))

#time def treeG_J017_part039 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [37873061724871865336895]) 0) 70 false) (.node 232 (sourceLit (List.headD (raw_ints% [1231495632885841520948775]) 0) 65 false) (.node 231 (sourceLit (List.headD (raw_ints% [56418361682583710670650827500775095]) 0) 30 true) (.node 230 (sourceLit (List.headD (raw_ints% [1252755843258152757586725]) 0) 65 false) .empty .empty) .empty) (.node 233 (sourceLit (List.headD (raw_ints% [86408236088797322807242818250070205]) 0) 29 true) .empty .empty)) (.node 236 (sourceLit (List.headD (raw_ints% [74615059463312490569415]) 0) 69 false) (.node 235 (sourceLit (List.headD (raw_ints% [1093514832259779015505938195475886835]) 0) 25 true) .empty .empty) (.node 237 (sourceLit (List.headD (raw_ints% [1766766996986018935683964310862603435]) 0) 24 true) .empty .empty)))

#time def treeG_J017_part040 : IntSourceTree :=
  (.node 229 (sourceLit (List.headD (raw_ints% [19400811057383619403136759087799855]) 0) 32 true) treeG_J017_part038 treeG_J017_part039)

#time def treeG_J017_part041 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [153407356338513015757206077175]) 0) 48 false) (.node 251 (sourceLit (List.headD (raw_ints% [352798277927109278051206923075]) 0) 47 false) (.node 250 (sourceLit (List.headD (raw_ints% [281932844548036549419393901425]) 0) 48 false) (.node 239 (sourceLit (List.headD (raw_ints% [5789306761735105615106816905649934045]) 0) 22 true) .empty .empty) .empty) (.node 252 (sourceLit (List.headD (raw_ints% [64983940268156698315221276075]) 0) 50 false) .empty .empty)) (.node 255 (sourceLit (List.headD (raw_ints% [68831680196580114994853104575]) 0) 49 false) (.node 254 (sourceLit (List.headD (raw_ints% [61210979238369767205320289225]) 0) 50 false) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [7297618673666835619696658925]) 0) 53 false) .empty .empty)))

#time def treeG_J017_part042 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [47823217861089729708123227520159825]) 0) 36 false) (.node 260 (sourceLit (List.headD (raw_ints% [3812558410670909342531315304482325]) 0) 38 true) (.node 259 (sourceLit (List.headD (raw_ints% [21059408636339251772741744025]) 0) 53 true) (.node 258 (sourceLit (List.headD (raw_ints% [200815397862209189660443811866875]) 0) 39 false) .empty .empty) .empty) (.node 261 (sourceLit (List.headD (raw_ints% [44077096536181995023488082475]) 0) 55 false) .empty .empty)) (.node 264 (sourceLit (List.headD (raw_ints% [43216135849930375193729963561908425]) 0) 35 true) (.node 263 (sourceLit (List.headD (raw_ints% [13694457720886201397265387975]) 0) 57 true) .empty .empty) (.node 265 (sourceLit (List.headD (raw_ints% [12794259591069786118542825]) 0) 62 false) .empty .empty)))

#time def treeG_J017_part043 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [3933521957397769634800155825]) 0) 53 false) treeG_J017_part041 treeG_J017_part042)

#time def treeG_J017_part044 : IntSourceTree :=
  (.node 238 (sourceLit (List.headD (raw_ints% [2298848247959275602765]) 0) 74 false) treeG_J017_part040 treeG_J017_part043)

#time def treeG_J017_part045 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [31095747072609750085270812525]) 0) 54 false) treeG_J017_part037 treeG_J017_part044)

#time def treeG_J017_part046 : IntSourceTree :=
  (.node 271 (sourceLit (List.headD (raw_ints% [2995441087416672049426575]) 0) 64 false) (.node 269 (sourceLit (List.headD (raw_ints% [6111817349960130037295625]) 0) 63 false) (.node 268 (sourceLit (List.headD (raw_ints% [91095946826796155600670064933969515]) 0) 31 true) (.node 267 (sourceLit (List.headD (raw_ints% [3123099260824394436316875]) 0) 64 false) .empty .empty) .empty) (.node 270 (sourceLit (List.headD (raw_ints% [233582778036987219378687682820543715]) 0) 29 true) .empty .empty)) (.node 273 (sourceLit (List.headD (raw_ints% [183783512728328665402395]) 0) 68 false) (.node 272 (sourceLit (List.headD (raw_ints% [332167202210422417337272466320679505]) 0) 28 true) .empty .empty) (.node 274 (sourceLit (List.headD (raw_ints% [4009369170480462097519724610599604015]) 0) 24 true) .empty .empty)))

#time def treeG_J017_part047 : IntSourceTree :=
  (.node 291 (sourceLit (List.headD (raw_ints% [22117880157822540540381695175]) 0) 52 false) (.node 278 (sourceLit (List.headD (raw_ints% [20158978411138821799448068370179948545]) 0) 21 true) (.node 277 (sourceLit (List.headD (raw_ints% [44438329333740802915395]) 0) 70 false) (.node 276 (sourceLit (List.headD (raw_ints% [6278891979887871924330976192658150295]) 0) 23 true) .empty .empty) .empty) (.node 279 (sourceLit (List.headD (raw_ints% [5471145569847822159645]) 0) 73 false) .empty .empty)) (.node 293 (sourceLit (List.headD (raw_ints% [80068083962220457778820819375]) 0) 50 false) (.node 292 (sourceLit (List.headD (raw_ints% [250784318044571655482183234475]) 0) 48 false) .empty .empty) (.node 294 (sourceLit (List.headD (raw_ints% [107810207603136351124081852725]) 0) 49 false) .empty .empty)))

#time def treeG_J017_part048 : IntSourceTree :=
  (.node 275 (sourceLit (List.headD (raw_ints% [180644076056842356072105]) 0) 68 false) treeG_J017_part046 treeG_J017_part047)

#time def treeG_J017_part049 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [26077577854474500929006278275]) 0) 55 true) (.node 298 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 54 false) (.node 297 (sourceLit (List.headD (raw_ints% [2202515850793624455461518575]) 0) 55 false) (.node 296 (sourceLit (List.headD (raw_ints% [6014226267356287577641548075]) 0) 53 false) .empty .empty) .empty) (.node 299 (sourceLit (List.headD (raw_ints% [103089987541042830130638816078075]) 0) 42 false) .empty .empty)) (.node 302 (sourceLit (List.headD (raw_ints% [57494341742707366011650453175]) 0) 56 false) (.node 301 (sourceLit (List.headD (raw_ints% [1597951088214161703520213555301025]) 0) 41 true) .empty .empty) (.node 303 (sourceLit (List.headD (raw_ints% [13435019628972683577153689526341625]) 0) 39 false) .empty .empty)))

#time def treeG_J017_part050 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [17923783942353134049383326461542415]) 0) 34 true) (.node 307 (sourceLit (List.headD (raw_ints% [18402711416858651160712726618746975]) 0) 35 true) (.node 306 (sourceLit (List.headD (raw_ints% [7587464068966539479661225]) 0) 63 false) (.node 305 (sourceLit (List.headD (raw_ints% [9966663883484955665192747942628525]) 0) 38 true) .empty .empty) .empty) (.node 308 (sourceLit (List.headD (raw_ints% [7388297027137453542654825]) 0) 63 false) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [44291104088600877177009213829942155]) 0) 32 true) (.node 310 (sourceLit (List.headD (raw_ints% [3606305663443824522122175]) 0) 64 false) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [220493181816353816059725]) 0) 68 false) .empty .empty)))

#time def treeG_J017_part051 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [866546012855936508437660175]) 0) 62 true) treeG_J017_part049 treeG_J017_part050)

#time def treeG_J017_part052 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [2328795757560481286726402325]) 0) 55 false) treeG_J017_part048 treeG_J017_part051)

#time def treeG_J017_part053 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [26047543350066598093275]) 0) 71 false) (.node 316 (sourceLit (List.headD (raw_ints% [53014508296764932751345]) 0) 70 false) (.node 315 (sourceLit (List.headD (raw_ints% [728963584555170770503446603780929295]) 0) 27 true) (.node 314 (sourceLit (List.headD (raw_ints% [108037389278584934728605]) 0) 69 false) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [1128031245725463247161752970448886715]) 0) 26 true) .empty .empty)) (.node 332 (sourceLit (List.headD (raw_ints% [111959100994423626007832285325]) 0) 50 false) (.node 319 (sourceLit (List.headD (raw_ints% [3592417912350929046085312866132503625]) 0) 24 true) .empty .empty) (.node 333 (sourceLit (List.headD (raw_ints% [348161279750630295207160391775]) 0) 48 false) .empty .empty)))

#time def treeG_J017_part054 : IntSourceTree :=
  (.node 339 (sourceLit (List.headD (raw_ints% [39092179322646407277367143525]) 0) 53 false) (.node 337 (sourceLit (List.headD (raw_ints% [8094930577314805520482940325]) 0) 53 false) (.node 336 (sourceLit (List.headD (raw_ints% [11332747386817014674114559675]) 0) 53 false) (.node 335 (sourceLit (List.headD (raw_ints% [146788735009692587253310600875]) 0) 49 false) .empty .empty) .empty) (.node 338 (sourceLit (List.headD (raw_ints% [87872759733012754965808350795525]) 0) 39 false) .empty .empty)) (.node 341 (sourceLit (List.headD (raw_ints% [96232252245130996881500639025]) 0) 55 true) (.node 340 (sourceLit (List.headD (raw_ints% [7111438011984279906711757418980725]) 0) 38 false) .empty .empty) (.node 342 (sourceLit (List.headD (raw_ints% [150092087506796078733416895059425425]) 0) 36 true) .empty .empty)))

#time def treeG_J017_part055 : IntSourceTree :=
  (.node 334 (sourceLit (List.headD (raw_ints% [98925188686071148352321349525]) 0) 50 false) treeG_J017_part053 treeG_J017_part054)

#time def treeG_J017_part056 : IntSourceTree :=
  (.node 348 (sourceLit (List.headD (raw_ints% [497790818512680681542137186865933685]) 0) 31 true) (.node 346 (sourceLit (List.headD (raw_ints% [1187496174528671087906700606768711825]) 0) 32 true) (.node 345 (sourceLit (List.headD (raw_ints% [1745886285302942802993863175]) 0) 62 true) (.node 344 (sourceLit (List.headD (raw_ints% [473136763977056249662648028404840425]) 0) 35 false) .empty .empty) .empty) (.node 347 (sourceLit (List.headD (raw_ints% [2232182404071072521672175]) 0) 65 false) .empty .empty)) (.node 350 (sourceLit (List.headD (raw_ints% [913539394273613359781845210718170845]) 0) 29 true) (.node 349 (sourceLit (List.headD (raw_ints% [8664776704314777048014025]) 0) 63 false) .empty .empty) (.node 351 (sourceLit (List.headD (raw_ints% [4217170239470976994817775]) 0) 64 false) .empty .empty)))

#time def treeG_J017_part057 : IntSourceTree :=
  (.node 357 (sourceLit (List.headD (raw_ints% [61590687259789062587295]) 0) 70 false) (.node 355 (sourceLit (List.headD (raw_ints% [251505481057497382842315]) 0) 68 false) (.node 354 (sourceLit (List.headD (raw_ints% [11719204661303543952402172865919391185]) 0) 24 true) (.node 353 (sourceLit (List.headD (raw_ints% [257202850904378966717055]) 0) 68 false) .empty .empty) .empty) (.node 356 (sourceLit (List.headD (raw_ints% [17047942725877592731779315128331587145]) 0) 23 true) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [15105252210370953773985]) 0) 72 false) (.node 358 (sourceLit (List.headD (raw_ints% [52035021315290826018904121738548801215]) 0) 21 true) .empty .empty) (.node 373 (sourceLit (List.headD (raw_ints% [143850118026626794236843751275]) 0) 50 false) .empty .empty)))

#time def treeG_J017_part058 : IntSourceTree :=
  (.node 352 (sourceLit (List.headD (raw_ints% [1085148128624805652327022376237469455]) 0) 28 true) treeG_J017_part056 treeG_J017_part057)

#time def treeG_J017_part059 : IntSourceTree :=
  (.node 343 (sourceLit (List.headD (raw_ints% [35594399731796783704457920575]) 0) 58 false) treeG_J017_part055 treeG_J017_part058)

#time def treeG_J017_part060 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [61439741530406273632507412017652325]) 0) 31 true) treeG_J017_part052 treeG_J017_part059)

#time def treeG_J017_part061 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [88236802557403237237971129887739375]) 0) 32 true) treeG_J017_part045 treeG_J017_part060)

#time def treeG_J017_part062 : IntSourceTree :=
  (.node 174 (sourceLit (List.headD (raw_ints% [38588613909816110497923176325]) 0) 50 false) treeG_J017_part030 treeG_J017_part061)

#time def treeG_J017_part063 : IntSourceTree :=
  (.node 379 (sourceLit (List.headD (raw_ints% [324487190431158565556746913516775]) 0) 40 true) (.node 377 (sourceLit (List.headD (raw_ints% [6927715685229765763191522525]) 0) 54 false) (.node 376 (sourceLit (List.headD (raw_ints% [98674924870842286632178216275]) 0) 50 false) (.node 375 (sourceLit (List.headD (raw_ints% [61664456565103447764698912325]) 0) 51 false) .empty .empty) .empty) (.node 378 (sourceLit (List.headD (raw_ints% [1793368952869008322163295225]) 0) 55 false) .empty .empty)) (.node 382 (sourceLit (List.headD (raw_ints% [19215824248479795361643886525]) 0) 59 true) (.node 381 (sourceLit (List.headD (raw_ints% [13503242364840926720792611640184825]) 0) 39 false) (.node 380 (sourceLit (List.headD (raw_ints% [91247335031595409135379700075]) 0) 54 false) .empty .empty) .empty) (.node 383 (sourceLit (List.headD (raw_ints% [203832166022686813042031653164791925]) 0) 37 true) .empty .empty)))

#time def treeG_J017_part064 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [426095682743268145344603881019764025]) 0) 32 true) (.node 387 (sourceLit (List.headD (raw_ints% [1113885328861236483263849700293723925]) 0) 33 true) (.node 386 (sourceLit (List.headD (raw_ints% [109592109335744333904595275]) 0) 67 true) (.node 385 (sourceLit (List.headD (raw_ints% [513003419510996072323419020175354525]) 0) 36 false) .empty .empty) .empty) (.node 388 (sourceLit (List.headD (raw_ints% [10469162205431126630722575]) 0) 63 false) .empty .empty)) (.node 391 (sourceLit (List.headD (raw_ints% [736374977919209851073808355398402225]) 0) 30 true) (.node 390 (sourceLit (List.headD (raw_ints% [2529235520435476262945925]) 0) 65 false) .empty .empty) (.node 392 (sourceLit (List.headD (raw_ints% [2453224784940146466339975]) 0) 65 false) .empty .empty)))

#time def treeG_J017_part065 : IntSourceTree :=
  (.node 384 (sourceLit (List.headD (raw_ints% [42526767834644275771959201975]) 0) 59 false) treeG_J017_part063 treeG_J017_part064)

#time def treeG_J017_part066 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [8885785977430616123505]) 0) 73 false) (.node 396 (sourceLit (List.headD (raw_ints% [145476464463967517339625]) 0) 69 false) (.node 395 (sourceLit (List.headD (raw_ints% [8803350323082860870388386450795674005]) 0) 25 true) (.node 394 (sourceLit (List.headD (raw_ints% [74582730812897015994225]) 0) 70 false) .empty .empty) .empty) (.node 397 (sourceLit (List.headD (raw_ints% [12535817742975739743132303246536040285]) 0) 24 true) .empty .empty)) (.node 414 (sourceLit (List.headD (raw_ints% [188775047367182440121366153025]) 0) 50 false) (.node 399 (sourceLit (List.headD (raw_ints% [37665349665887109834562870274018786715]) 0) 22 true) .empty .empty) (.node 415 (sourceLit (List.headD (raw_ints% [333913409285295300912846477225]) 0) 49 false) .empty .empty)))

#time def treeG_J017_part067 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [46869896819181601504220084775]) 0) 57 false) (.node 419 (sourceLit (List.headD (raw_ints% [24745227699694340700060781725]) 0) 53 true) (.node 418 (sourceLit (List.headD (raw_ints% [366142015414205174090711269402875]) 0) 39 false) (.node 417 (sourceLit (List.headD (raw_ints% [66295202561583064550246454975]) 0) 51 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [9707335535433548431165732727114925]) 0) 38 true) .empty .empty)) (.node 423 (sourceLit (List.headD (raw_ints% [112457696725715965151033466675]) 0) 58 true) (.node 422 (sourceLit (List.headD (raw_ints% [366143965344250906266098681302382625]) 0) 36 false) .empty .empty) (.node 424 (sourceLit (List.headD (raw_ints% [2103794092158550753998901253723175825]) 0) 35 true) .empty .empty)))

#time def treeG_J017_part068 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [38998961791469418416469792975]) 0) 52 false) treeG_J017_part066 treeG_J017_part067)

#time def treeG_J017_part069 : IntSourceTree :=
  (.node 393 (sourceLit (List.headD (raw_ints% [839389162503180557796992728166860155]) 0) 29 true) treeG_J017_part065 treeG_J017_part068)

#time def treeG_J017_part070 : IntSourceTree :=
  (.node 430 (sourceLit (List.headD (raw_ints% [5903991529618676965731816885598053555]) 0) 29 true) (.node 428 (sourceLit (List.headD (raw_ints% [8413291812377211184568660415483857715]) 0) 31 true) (.node 427 (sourceLit (List.headD (raw_ints% [878969057090025743758434375]) 0) 65 true) (.node 426 (sourceLit (List.headD (raw_ints% [17603605598880545402256109252380056625]) 0) 32 false) .empty .empty) .empty) (.node 429 (sourceLit (List.headD (raw_ints% [12273547706547476213431125]) 0) 63 false) .empty .empty)) (.node 432 (sourceLit (List.headD (raw_ints% [4805851694728873156263444466949748345]) 0) 28 true) (.node 431 (sourceLit (List.headD (raw_ints% [5899771842270928056965925]) 0) 64 false) .empty .empty) (.node 433 (sourceLit (List.headD (raw_ints% [1424413381322630599471755]) 0) 66 false) .empty .empty)))

#time def treeG_J017_part071 : IntSourceTree :=
  (.node 439 (sourceLit (List.headD (raw_ints% [20437891699351510720035]) 0) 72 false) (.node 437 (sourceLit (List.headD (raw_ints% [41942888602089227376165]) 0) 71 false) (.node 436 (sourceLit (List.headD (raw_ints% [53378859858785294231327776478033804895]) 0) 23 true) (.node 435 (sourceLit (List.headD (raw_ints% [345156365445678745111485]) 0) 68 false) .empty .empty) .empty) (.node 438 (sourceLit (List.headD (raw_ints% [148538062572321009871212730206027843345]) 0) 21 true) .empty .empty)) (.node 456 (sourceLit (List.headD (raw_ints% [117619242207226507140334130475]) 0) 51 false) (.node 455 (sourceLit (List.headD (raw_ints% [31777647700519748089166810175]) 0) 53 false) .empty .empty) (.node 457 (sourceLit (List.headD (raw_ints% [25143530421009886890086747925]) 0) 53 false) .empty .empty)))

#time def treeG_J017_part072 : IntSourceTree :=
  (.node 434 (sourceLit (List.headD (raw_ints% [42001701738900011746605361736759658735]) 0) 24 true) treeG_J017_part070 treeG_J017_part071)

#time def treeG_J017_part073 : IntSourceTree :=
  (.node 463 (sourceLit (List.headD (raw_ints% [284988065683468859654065167233587275]) 0) 38 false) (.node 461 (sourceLit (List.headD (raw_ints% [11605288950137237575979172183649875]) 0) 40 true) (.node 460 (sourceLit (List.headD (raw_ints% [14499070341411218729430060225]) 0) 57 true) (.node 459 (sourceLit (List.headD (raw_ints% [345314602922681869823729091459825]) 0) 41 false) .empty .empty) .empty) (.node 462 (sourceLit (List.headD (raw_ints% [85301545316141192227507857825]) 0) 58 false) .empty .empty)) (.node 465 (sourceLit (List.headD (raw_ints% [1308398755834773413161160136949265175]) 0) 37 true) (.node 464 (sourceLit (List.headD (raw_ints% [77492232280180120461496334325]) 0) 60 true) .empty .empty) (.node 466 (sourceLit (List.headD (raw_ints% [56524207973343684353828752275]) 0) 61 false) .empty .empty)))

#time def treeG_J017_part074 : IntSourceTree :=
  (.node 472 (sourceLit (List.headD (raw_ints% [1723273528665390795312975]) 0) 66 false) (.node 470 (sourceLit (List.headD (raw_ints% [7215076665676523687539275]) 0) 64 false) (.node 469 (sourceLit (List.headD (raw_ints% [3993598064816971519612028267232046845]) 0) 33 true) (.node 468 (sourceLit (List.headD (raw_ints% [7042221618925637076698197575]) 0) 63 true) .empty .empty) .empty) (.node 471 (sourceLit (List.headD (raw_ints% [2583808275849733557329004265099825665]) 0) 31 true) .empty .empty)) (.node 474 (sourceLit (List.headD (raw_ints% [827751534819454471517955]) 0) 67 false) (.node 473 (sourceLit (List.headD (raw_ints% [1983231266112846299233225869391444095]) 0) 30 true) .empty .empty) (.node 475 (sourceLit (List.headD (raw_ints% [16599175707908575438108487642981992365]) 0) 26 true) .empty .empty)))

#time def treeG_J017_part075 : IntSourceTree :=
  (.node 467 (sourceLit (List.headD (raw_ints% [9358745463870890942759979476336890275]) 0) 34 false) treeG_J017_part073 treeG_J017_part074)

#time def treeG_J017_part076 : IntSourceTree :=
  (.node 458 (sourceLit (List.headD (raw_ints% [51948250938630997972940093175]) 0) 52 false) treeG_J017_part072 treeG_J017_part075)

#time def treeG_J017_part077 : IntSourceTree :=
  (.node 425 (sourceLit (List.headD (raw_ints% [49510312975856046983934654675]) 0) 60 false) treeG_J017_part069 treeG_J017_part076)

#time def treeG_J017_part078 : IntSourceTree :=
  (.node 497 (sourceLit (List.headD (raw_ints% [168943281852869949730421805975]) 0) 51 false) (.node 479 (sourceLit (List.headD (raw_ints% [55436356453216950018324929966004528315]) 0) 23 true) (.node 478 (sourceLit (List.headD (raw_ints% [24171316647227995129155]) 0) 72 false) (.node 477 (sourceLit (List.headD (raw_ints% [20421521057904777244097736615748882305]) 0) 25 true) .empty .empty) .empty) (.node 496 (sourceLit (List.headD (raw_ints% [88111629010609573940197447725]) 0) 52 false) .empty .empty)) (.node 499 (sourceLit (List.headD (raw_ints% [19173369659581334668250218725]) 0) 55 false) (.node 498 (sourceLit (List.headD (raw_ints% [457761189421446799523651286603525]) 0) 39 false) .empty .empty) (.node 500 (sourceLit (List.headD (raw_ints% [15232369182196458348345398190472125]) 0) 38 false) .empty .empty)))

#time def treeG_J017_part079 : IntSourceTree :=
  (.node 506 (sourceLit (List.headD (raw_ints% [101341125972306043844570358017133027825]) 0) 32 true) (.node 504 (sourceLit (List.headD (raw_ints% [6663603143094052508463943929460572225]) 0) 35 false) (.node 503 (sourceLit (List.headD (raw_ints% [283060787357998349606049182325]) 0) 58 false) (.node 502 (sourceLit (List.headD (raw_ints% [737513211748642508697432191179178625]) 0) 36 true) .empty .empty) .empty) (.node 505 (sourceLit (List.headD (raw_ints% [204494777536216287906927323325]) 0) 60 true) .empty .empty)) (.node 508 (sourceLit (List.headD (raw_ints% [158153219234311466268728332036874102115]) 0) 31 false) (.node 507 (sourceLit (List.headD (raw_ints% [63555960430063890303896227275]) 0) 62 false) .empty .empty) (.node 509 (sourceLit (List.headD (raw_ints% [14096716785557821629609826275]) 0) 63 true) .empty .empty)))

#time def treeG_J017_part080 : IntSourceTree :=
  (.node 501 (sourceLit (List.headD (raw_ints% [75868037502004038963080205225]) 0) 57 true) treeG_J017_part078 treeG_J017_part079)

#time def treeG_J017_part081 : IntSourceTree :=
  (.node 515 (sourceLit (List.headD (raw_ints% [241297584686887863203235]) 0) 69 false) (.node 513 (sourceLit (List.headD (raw_ints% [2022133676008150991154195]) 0) 66 false) (.node 512 (sourceLit (List.headD (raw_ints% [36535080718866863761000623774647462295]) 0) 28 true) (.node 511 (sourceLit (List.headD (raw_ints% [8530381489082119318112625]) 0) 64 false) .empty .empty) .empty) (.node 514 (sourceLit (List.headD (raw_ints% [211851900323544314555247549545345185425]) 0) 24 true) .empty .empty)) (.node 517 (sourceLit (List.headD (raw_ints% [57897061888766386509765]) 0) 71 false) (.node 516 (sourceLit (List.headD (raw_ints% [212207951467751912778408025809678072945]) 0) 23 true) .empty .empty) (.node 518 (sourceLit (List.headD (raw_ints% [504950611280631861939914841497936390415]) 0) 21 true) .empty .empty)))

#time def treeG_J017_part082 : IntSourceTree :=
  (.node 541 (sourceLit (List.headD (raw_ints% [38442947082470933500303742557771875]) 0) 39 false) (.node 539 (sourceLit (List.headD (raw_ints% [232868016423916940123806896316125]) 0) 40 true) (.node 538 (sourceLit (List.headD (raw_ints% [3656094716069967242421303525]) 0) 57 false) (.node 537 (sourceLit (List.headD (raw_ints% [7871012323699960881263837475]) 0) 56 false) .empty .empty) .empty) (.node 540 (sourceLit (List.headD (raw_ints% [48171510342403772127110339175]) 0) 56 false) .empty .empty)) (.node 543 (sourceLit (List.headD (raw_ints% [1307489343115580228005562525646353175]) 0) 37 true) (.node 542 (sourceLit (List.headD (raw_ints% [80584791409072615595294031525]) 0) 59 true) .empty .empty) (.node 544 (sourceLit (List.headD (raw_ints% [438045251918358590529041850975]) 0) 59 false) .empty .empty)))

#time def treeG_J017_part083 : IntSourceTree :=
  (.node 519 (sourceLit (List.headD (raw_ints% [27904741595104479538275]) 0) 72 false) treeG_J017_part081 treeG_J017_part082)

#time def treeG_J017_part084 : IntSourceTree :=
  (.node 510 (sourceLit (List.headD (raw_ints% [121891146544524411661853087665827445485]) 0) 29 true) treeG_J017_part080 treeG_J017_part083)

#time def treeG_J017_part085 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [7051965931111749076648682775]) 0) 65 true) (.node 548 (sourceLit (List.headD (raw_ints% [35299091024494763690297212425]) 0) 64 false) (.node 547 (sourceLit (List.headD (raw_ints% [120058616900047825730090316969806808375]) 0) 33 true) (.node 546 (sourceLit (List.headD (raw_ints% [16313686594347498266297254725]) 0) 65 true) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [166140415363945409307952388571338195805]) 0) 32 false) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [5083834431751337727486675]) 0) 65 false) (.node 551 (sourceLit (List.headD (raw_ints% [116723529992824944547195079135627794155]) 0) 30 true) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [32568618186641171162534172035864574105]) 0) 29 true) .empty .empty)))

#time def treeG_J017_part086 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [394077898374197961903264981565927333785]) 0) 22 true) (.node 557 (sourceLit (List.headD (raw_ints% [171364909351942358290212552578180308335]) 0) 24 true) (.node 556 (sourceLit (List.headD (raw_ints% [141457634196032249317305]) 0) 70 false) (.node 555 (sourceLit (List.headD (raw_ints% [178653548907727163679030574259381200695]) 0) 25 true) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [16862872620769195690305]) 0) 73 false) .empty .empty)) (.node 581 (sourceLit (List.headD (raw_ints% [7752471740275488193136909025]) 0) 61 false) (.node 580 (sourceLit (List.headD (raw_ints% [17095313313587793869335853361001125]) 0) 38 true) .empty .empty) (.node 582 (sourceLit (List.headD (raw_ints% [1352600365068177444702292072103528625]) 0) 36 false) .empty .empty)))

#time def treeG_J017_part087 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [74648883824293532477265]) 0) 71 false) treeG_J017_part085 treeG_J017_part086)

#time def treeG_J017_part088 : IntSourceTree :=
  (.node 588 (sourceLit (List.headD (raw_ints% [1118622154434694072109450867795328569115]) 0) 31 true) (.node 586 (sourceLit (List.headD (raw_ints% [398313946924741222557730812524624310225]) 0) 32 false) (.node 585 (sourceLit (List.headD (raw_ints% [160635007363643719608992293575]) 0) 62 false) (.node 584 (sourceLit (List.headD (raw_ints% [17123517888018694332508444134631397625]) 0) 35 true) .empty .empty) .empty) (.node 587 (sourceLit (List.headD (raw_ints% [324574945939623862564652302875]) 0) 62 true) .empty .empty)) (.node 590 (sourceLit (List.headD (raw_ints% [2780137792367650960589091304807238578365]) 0) 29 false) (.node 589 (sourceLit (List.headD (raw_ints% [155293080883536876390798675975]) 0) 63 false) .empty .empty) (.node 591 (sourceLit (List.headD (raw_ints% [28216394105936078425912843725]) 0) 64 true) .empty .empty)))

#time def treeG_J017_part089 : IntSourceTree :=
  (.node 597 (sourceLit (List.headD (raw_ints% [20890143076816465701885]) 0) 73 false) (.node 595 (sourceLit (List.headD (raw_ints% [355893485907460396614885]) 0) 69 false) (.node 594 (sourceLit (List.headD (raw_ints% [1872539663621490639846939460749987557295]) 0) 24 true) (.node 593 (sourceLit (List.headD (raw_ints% [47839074308487292755195]) 0) 72 false) .empty .empty) .empty) (.node 596 (sourceLit (List.headD (raw_ints% [1217020439794065396653836568265371532615]) 0) 23 true) .empty .empty)) (.node 599 (sourceLit (List.headD (raw_ints% [39546748887972303222945]) 0) 72 false) (.node 598 (sourceLit (List.headD (raw_ints% [2236887938350445870703485999752948542945]) 0) 21 true) .empty .empty) (.node 621 (sourceLit (List.headD (raw_ints% [6942282549507340921204949489846625]) 0) 42 true) .empty .empty)))

#time def treeG_J017_part090 : IntSourceTree :=
  (.node 592 (sourceLit (List.headD (raw_ints% [897253159223732692616560009310374890945]) 0) 28 true) treeG_J017_part088 treeG_J017_part089)

#time def treeG_J017_part091 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [605399952994288811987225308425]) 0) 58 true) treeG_J017_part087 treeG_J017_part090)

#time def treeG_J017_part092 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [9280400654763599334786264203359102575]) 0) 36 false) treeG_J017_part084 treeG_J017_part091)

#time def treeG_J017_part093 : IntSourceTree :=
  (.node 476 (sourceLit (List.headD (raw_ints% [49919975245427806942965]) 0) 71 false) treeG_J017_part077 treeG_J017_part092)

#time def treeG_J017_part094 : IntSourceTree :=
  (.node 627 (sourceLit (List.headD (raw_ints% [64796570478098631035977641186803889825]) 0) 36 false) (.node 625 (sourceLit (List.headD (raw_ints% [3300489817847786708411838542248812525]) 0) 39 true) (.node 624 (sourceLit (List.headD (raw_ints% [130430650614080925314533394925]) 0) 62 true) (.node 623 (sourceLit (List.headD (raw_ints% [332511213522969709088481824718735225]) 0) 40 false) .empty .empty) .empty) (.node 626 (sourceLit (List.headD (raw_ints% [225889753741033712674181312475]) 0) 63 false) .empty .empty)) (.node 629 (sourceLit (List.headD (raw_ints% [160595321224829935177175407045833345615]) 0) 35 true) (.node 628 (sourceLit (List.headD (raw_ints% [395173127988613389945246727725]) 0) 63 true) .empty .empty) (.node 630 (sourceLit (List.headD (raw_ints% [169397012745760374544096041525]) 0) 64 false) .empty .empty)))

#time def treeG_J017_part095 : IntSourceTree :=
  (.node 636 (sourceLit (List.headD (raw_ints% [53608962927857036824395]) 0) 72 false) (.node 634 (sourceLit (List.headD (raw_ints% [116707413409655638543515]) 0) 71 false) (.node 633 (sourceLit (List.headD (raw_ints% [108085567629636440181753229659313789605]) 0) 32 true) (.node 632 (sourceLit (List.headD (raw_ints% [881921185636494680113760325]) 0) 70 true) .empty .empty) .empty) (.node 635 (sourceLit (List.headD (raw_ints% [211735764339220434520988610811325794575]) 0) 28 true) .empty .empty)) (.node 638 (sourceLit (List.headD (raw_ints% [24917413532863735713465]) 0) 73 false) (.node 637 (sourceLit (List.headD (raw_ints% [130706941305265379795453001960898903035]) 0) 27 true) .empty .empty) (.node 639 (sourceLit (List.headD (raw_ints% [230351254997030988600027627273377651145]) 0) 25 true) .empty .empty)))

#time def treeG_J017_part096 : IntSourceTree :=
  (.node 631 (sourceLit (List.headD (raw_ints% [362107665295059488142035797992858296565]) 0) 33 false) treeG_J017_part094 treeG_J017_part095)

#time def treeG_J017_part097 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [5265602665033006458412019903750777517915]) 0) 31 false) (.node 666 (sourceLit (List.headD (raw_ints% [1243239340293774619911161479340320316625]) 0) 32 true) (.node 665 (sourceLit (List.headD (raw_ints% [421496308591805570238059083425]) 0) 62 true) (.node 664 (sourceLit (List.headD (raw_ints% [38404235553488755714171280916630452025]) 0) 35 false) .empty .empty) .empty) (.node 667 (sourceLit (List.headD (raw_ints% [1228133960903758713261377552775]) 0) 62 false) .empty .empty)) (.node 670 (sourceLit (List.headD (raw_ints% [23336338909145882663267543406673906817085]) 0) 29 true) (.node 669 (sourceLit (List.headD (raw_ints% [945639336860763656281292131425]) 0) 63 true) .empty .empty) (.node 671 (sourceLit (List.headD (raw_ints% [367010419597456827514104926775]) 0) 64 false) .empty .empty)))

#time def treeG_J017_part098 : IntSourceTree :=
  (.node 677 (sourceLit (List.headD (raw_ints% [16359409925520285561255]) 0) 74 false) (.node 675 (sourceLit (List.headD (raw_ints% [577765821369784711733235]) 0) 69 false) (.node 674 (sourceLit (List.headD (raw_ints% [53467270962752366733210714124818672720465]) 0) 24 true) (.node 673 (sourceLit (List.headD (raw_ints% [882016863785111654699270715]) 0) 71 true) .empty .empty) .empty) (.node 676 (sourceLit (List.headD (raw_ints% [12334068477916042412689434523659479320185]) 0) 23 true) .empty .empty)) (.node 679 (sourceLit (List.headD (raw_ints% [60122905243482639630915]) 0) 72 false) (.node 678 (sourceLit (List.headD (raw_ints% [14493600548723522743114498251242111045535]) 0) 21 true) .empty .empty) (.node 704 (sourceLit (List.headD (raw_ints% [2219263419232042299065049682725]) 0) 59 false) .empty .empty)))

#time def treeG_J017_part099 : IntSourceTree :=
  (.node 672 (sourceLit (List.headD (raw_ints% [24072143738107539933706851080853305871105]) 0) 28 false) treeG_J017_part097 treeG_J017_part098)

#time def treeG_J017_part100 : IntSourceTree :=
  (.node 663 (sourceLit (List.headD (raw_ints% [1175818214319394896548782523325]) 0) 58 false) treeG_J017_part096 treeG_J017_part099)

#time def treeG_J017_part101 : IntSourceTree :=
  (.node 710 (sourceLit (List.headD (raw_ints% [557518174803262015412694086475]) 0) 65 true) (.node 708 (sourceLit (List.headD (raw_ints% [405826772223093025801656070125]) 0) 65 false) (.node 707 (sourceLit (List.headD (raw_ints% [1761611904118563668198982608834751435225]) 0) 33 true) (.node 706 (sourceLit (List.headD (raw_ints% [161846515583209820728060098975]) 0) 65 true) .empty .empty) .empty) (.node 709 (sourceLit (List.headD (raw_ints% [6550365234831645939829423160117444282835]) 0) 32 false) .empty .empty)) (.node 712 (sourceLit (List.headD (raw_ints% [395231897537824657277745257175]) 0) 65 false) (.node 711 (sourceLit (List.headD (raw_ints% [26233200231506358568403829790616773189605]) 0) 30 true) .empty .empty) (.node 713 (sourceLit (List.headD (raw_ints% [24936828279144631455160876918127816187945]) 0) 29 false) .empty .empty)))

#time def treeG_J017_part102 : IntSourceTree :=
  (.node 719 (sourceLit (List.headD (raw_ints% [12650790508747274834314277233055089836375]) 0) 22 true) (.node 717 (sourceLit (List.headD (raw_ints% [11288412947473919374325810507972288095905]) 0) 24 true) (.node 716 (sourceLit (List.headD (raw_ints% [363329969658356564435655]) 0) 70 false) (.node 715 (sourceLit (List.headD (raw_ints% [51773384848038603257042805238328066363865]) 0) 25 true) .empty .empty) .empty) (.node 718 (sourceLit (List.headD (raw_ints% [40520226169217406531555]) 0) 73 false) .empty .empty)) (.node 746 (sourceLit (List.headD (raw_ints% [3317100271374448200118073135488190787825]) 0) 32 false) (.node 745 (sourceLit (List.headD (raw_ints% [3905248653599264580017286016425]) 0) 60 false) .empty .empty) (.node 747 (sourceLit (List.headD (raw_ints% [3817678210235115844910339136375]) 0) 62 true) .empty .empty)))

#time def treeG_J017_part103 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [1764150434983632965037084945]) 0) 71 true) treeG_J017_part101 treeG_J017_part102)

#time def treeG_J017_part104 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [423456437178948230228121920055]) 0) 66 false) (.node 751 (sourceLit (List.headD (raw_ints% [2597083118810504889164881272675]) 0) 64 true) (.node 750 (sourceLit (List.headD (raw_ints% [128142182666452217700538313968553015342445]) 0) 29 false) (.node 749 (sourceLit (List.headD (raw_ints% [4192253514645507862694540692425]) 0) 63 false) .empty .empty) .empty) (.node 752 (sourceLit (List.headD (raw_ints% [233937745590158408480937489405787491387945]) 0) 28 true) .empty .empty)) (.node 755 (sourceLit (List.headD (raw_ints% [14113781245690433505008412795]) 0) 69 true) (.node 754 (sourceLit (List.headD (raw_ints% [1649424280828008779863506836884998908748945]) 0) 24 false) .empty .empty) (.node 756 (sourceLit (List.headD (raw_ints% [401853010306392783643653007382965051590735]) 0) 23 true) .empty .empty)))

#time def treeG_J017_part105 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [5440985299127487948116963416875]) 0) 63 true) (.node 786 (sourceLit (List.headD (raw_ints% [6494792902930621711666247600025]) 0) 61 false) (.node 759 (sourceLit (List.headD (raw_ints% [101957999433386986495305]) 0) 72 false) (.node 758 (sourceLit (List.headD (raw_ints% [166121006610859187246098469876314498488945]) 0) 21 true) .empty .empty) .empty) (.node 787 (sourceLit (List.headD (raw_ints% [2539356087746505934158527872161471111525]) 0) 34 false) .empty .empty)) (.node 790 (sourceLit (List.headD (raw_ints% [5307289864252031893519928865375]) 0) 64 false) (.node 789 (sourceLit (List.headD (raw_ints% [12954431566406580871916651967273116641275]) 0) 33 true) .empty .empty) (.node 791 (sourceLit (List.headD (raw_ints% [77187691448979288134471071879584894266025]) 0) 31 false) .empty .empty)))

#time def treeG_J017_part106 : IntSourceTree :=
  (.node 757 (sourceLit (List.headD (raw_ints% [232454690254194279945615]) 0) 71 false) treeG_J017_part104 treeG_J017_part105)

#time def treeG_J017_part107 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [19358497897981515804003880774428788999715]) 0) 31 true) treeG_J017_part103 treeG_J017_part106)

#time def treeG_J017_part108 : IntSourceTree :=
  (.node 705 (sourceLit (List.headD (raw_ints% [64808154096271049381465989254620952225]) 0) 36 false) treeG_J017_part100 treeG_J017_part107)

#time def treeG_J017_part109 : IntSourceTree :=
  (.node 797 (sourceLit (List.headD (raw_ints% [195282298679459432134663598437496381747415]) 0) 25 true) (.node 795 (sourceLit (List.headD (raw_ints% [850598832838023691560274821061663487556405]) 0) 26 false) (.node 794 (sourceLit (List.headD (raw_ints% [451682844138686357668715279175]) 0) 67 false) (.node 793 (sourceLit (List.headD (raw_ints% [129437286934651519968049183161957653787945]) 0) 30 true) .empty .empty) .empty) (.node 796 (sourceLit (List.headD (raw_ints% [7057072287830045930786424225]) 0) 71 true) .empty .empty)) (.node 799 (sourceLit (List.headD (raw_ints% [76735108051055956205892096321629704326285]) 0) 23 true) (.node 798 (sourceLit (List.headD (raw_ints% [151414237915759466882505]) 0) 72 false) .empty .empty) (.node 827 (sourceLit (List.headD (raw_ints% [644529444572858597286036671025]) 0) 66 false) .empty .empty)))

#time def treeG_J017_part110 : IntSourceTree :=
  (.node 833 (sourceLit (List.headD (raw_ints% [3415771453527277776670748449905]) 0) 66 true) (.node 831 (sourceLit (List.headD (raw_ints% [13211662847314568676204739003425]) 0) 64 false) (.node 830 (sourceLit (List.headD (raw_ints% [542683992791462805601871176921292747863245]) 0) 29 true) (.node 829 (sourceLit (List.headD (raw_ints% [15074224112900483758928467526175]) 0) 63 true) .empty .empty) .empty) (.node 832 (sourceLit (List.headD (raw_ints% [1468940808773827018632474639479145799644345]) 0) 28 false) .empty .empty)) (.node 835 (sourceLit (List.headD (raw_ints% [479910406630067224678732104765]) 0) 68 false) (.node 834 (sourceLit (List.headD (raw_ints% [18217397008463403335773802281615578593605905]) 0) 24 true) .empty .empty) (.node 836 (sourceLit (List.headD (raw_ints% [14011434335714771848608050144369580852493215]) 0) 23 false) .empty .empty)))

#time def treeG_J017_part111 : IntSourceTree :=
  (.node 828 (sourceLit (List.headD (raw_ints% [59988195301925610750540326729012326784115]) 0) 31 false) treeG_J017_part109 treeG_J017_part110)

#time def treeG_J017_part112 : IntSourceTree :=
  (.node 870 (sourceLit (List.headD (raw_ints% [10190756988576257826224198195775]) 0) 65 true) (.node 868 (sourceLit (List.headD (raw_ints% [15753456412293225504693550153275]) 0) 63 false) (.node 839 (sourceLit (List.headD (raw_ints% [200870476398131947269705]) 0) 72 false) (.node 838 (sourceLit (List.headD (raw_ints% [6082912551131842641063136680123569717428335]) 0) 21 true) .empty .empty) .empty) (.node 869 (sourceLit (List.headD (raw_ints% [85897058434738772494373630663558560066665]) 0) 32 false) .empty .empty)) (.node 872 (sourceLit (List.headD (raw_ints% [16203977863662898222647365533275]) 0) 65 false) (.node 871 (sourceLit (List.headD (raw_ints% [697059375689421381870813320680462536395295]) 0) 30 true) .empty .empty) (.node 873 (sourceLit (List.headD (raw_ints% [1727815382643130058568573005803061107220235]) 0) 29 false) .empty .empty)))

#time def treeG_J017_part113 : IntSourceTree :=
  (.node 879 (sourceLit (List.headD (raw_ints% [5929442335029730728651352487480310308775765]) 0) 22 true) (.node 877 (sourceLit (List.headD (raw_ints% [14401998933073690712877377341244573615988045]) 0) 24 false) (.node 876 (sourceLit (List.headD (raw_ints% [508138695781387408401877801665]) 0) 69 false) (.node 875 (sourceLit (List.headD (raw_ints% [19918594674139450718894351923738905568718715]) 0) 25 true) .empty .empty) .empty) (.node 878 (sourceLit (List.headD (raw_ints% [7057264222294130907659838285]) 0) 73 true) .empty .empty)) (.node 910 (sourceLit (List.headD (raw_ints% [1917036927747283165511849267538229708929885]) 0) 29 false) (.node 909 (sourceLit (List.headD (raw_ints% [46581136937486934768315567832725]) 0) 63 false) .empty .empty) (.node 911 (sourceLit (List.headD (raw_ints% [53974690801619599981101531786525]) 0) 64 true) .empty .empty)))

#time def treeG_J017_part114 : IntSourceTree :=
  (.node 874 (sourceLit (List.headD (raw_ints% [483431787208245516792432966135]) 0) 70 true) treeG_J017_part112 treeG_J017_part113)

#time def treeG_J017_part115 : IntSourceTree :=
  (.node 837 (sourceLit (List.headD (raw_ints% [14114377030350346055852794065]) 0) 71 true) treeG_J017_part111 treeG_J017_part114)

#time def treeG_J017_part116 : IntSourceTree :=
  (.node 917 (sourceLit (List.headD (raw_ints% [536367449842088100513583389795]) 0) 70 false) (.node 915 (sourceLit (List.headD (raw_ints% [4347364704296031359018195833845]) 0) 68 true) (.node 914 (sourceLit (List.headD (raw_ints% [128797581497623727084162474653011489455700945]) 0) 24 false) (.node 913 (sourceLit (List.headD (raw_ints% [4904937329297543999829528495795]) 0) 68 false) .empty .empty) .empty) (.node 916 (sourceLit (List.headD (raw_ints% [173360191728830377599762865534280825402242935]) 0) 23 true) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [28229257759652921762586622845]) 0) 72 true) (.node 918 (sourceLit (List.headD (raw_ints% [236514895480310894047101174140036747573237055]) 0) 21 false) .empty .empty) (.node 950 (sourceLit (List.headD (raw_ints% [66962650914639450420763964224275]) 0) 64 false) .empty .empty)))

#time def treeG_J017_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [2427751700038709383710036817755]) 0) 70 true) (.node 954 (sourceLit (List.headD (raw_ints% [5871800903714035033414394428065]) 0) 69 false) (.node 953 (sourceLit (List.headD (raw_ints% [2193307799233082033041888552681476799506735]) 0) 31 true) (.node 952 (sourceLit (List.headD (raw_ints% [8772333583160312275468612164975]) 0) 68 true) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [37179044042940794450764206644187598756104915]) 0) 27 false) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [564596506731264624144222742935]) 0) 71 false) (.node 957 (sourceLit (List.headD (raw_ints% [46940547665476017078160060718881349754557745]) 0) 26 true) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [60611084453835156193938131656879264470503205]) 0) 24 false) .empty .empty)))

#time def treeG_J017_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [653524075859176136845665647054673061331295]) 0) 32 false) treeG_J017_part116 treeG_J017_part117)

#time def treeG_J017_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [3240709946070775987049345060148443131864932735]) 0) 21 true) (.node 996 (sourceLit (List.headD (raw_ints% [1363089601102935800024217478148283985597600215]) 0) 23 false) (.node 995 (sourceLit (List.headD (raw_ints% [27834568319152171492675773546105]) 0) 68 false) (.node 994 (sourceLit (List.headD (raw_ints% [690284378101292727542885944139469550129425105]) 0) 24 true) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [5391870849919506867933657025305]) 0) 70 true) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [14160702699666101792090573626905]) 0) 70 true) (.node 999 (sourceLit (List.headD (raw_ints% [148206441122729386476702341445]) 0) 74 false) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [839000554273055905345942770716219945153844765]) 0) 25 true) .empty .empty)))

#time def treeG_J017_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [8075094035287383042791759643878043546828358335]) 0) 23 true) (.node 1039 (sourceLit (List.headD (raw_ints% [3483154283886116611825097586775960189746945555]) 0) 22 true) (.node 1038 (sourceLit (List.headD (raw_ints% [372279209790673218254867485515]) 0) 75 true) (.node 1037 (sourceLit (List.headD (raw_ints% [1550851791764839868336857721023809384615831195]) 0) 24 false) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [141120189916480985829400362561345]) 0) 68 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [28054338614308213880439068596529393285718231855]) 0) 21 false) (.node 1077 (sourceLit (List.headD (raw_ints% [4760242821143637141003688025865]) 0) 73 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [1637323280285422259496172283505]) 0) 74 true) .empty .empty)))

#time def treeG_J017_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [32690071719229590260095847181615]) 0) 69 false) treeG_J017_part119 treeG_J017_part120)

#time def treeG_J017_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [22449604495618168550766752825745]) 0) 68 true) treeG_J017_part118 treeG_J017_part121)

#time def treeG_J017_part123 : IntSourceTree :=
  (.node 912 (sourceLit (List.headD (raw_ints% [7045415814289198073598981204922846090806705]) 0) 28 true) treeG_J017_part115 treeG_J017_part122)

#time def treeG_J017_part124 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [1496157508174164773221313264925]) 0) 66 true) treeG_J017_part108 treeG_J017_part123)

#time def treeG_J017_part125 : IntSourceTree :=
  (.node 622 (sourceLit (List.headD (raw_ints% [142604565331276521140389303725]) 0) 59 false) treeG_J017_part093 treeG_J017_part124)

#time def treeG_J017_part126 : IntSourceTree :=
  (.node 374 (sourceLit (List.headD (raw_ints% [120175536073746972041539269525]) 0) 50 false) treeG_J017_part062 treeG_J017_part125)

#time def treeG_J017 : IntSourceTree := treeG_J017_part126

#time def treeG_J018_part000 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [16530039795781559212573282875]) 0) 45 true) (.node 8 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 44 false) (.node 7 (sourceLit (List.headD (raw_ints% [1001458738463711054601938072625]) 0) 43 false) (.node 6 (sourceLit (List.headD (raw_ints% [664507599790418680345445971575]) 0) 41 false) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [120963911245531441305036036075]) 0) 46 false) .empty .empty)) (.node 12 (sourceLit (List.headD (raw_ints% [14383281380744993081070259125]) 0) 47 true) (.node 11 (sourceLit (List.headD (raw_ints% [58744052690484308677010298675]) 0) 47 false) .empty .empty) (.node 13 (sourceLit (List.headD (raw_ints% [14316061614989096983196951775]) 0) 49 false) .empty .empty)))

#time def treeG_J018_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [72074535838565955423505082804475]) 0) 39 true) (.node 17 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [1846212236931446873092600425]) 0) 52 true) (.node 15 (sourceLit (List.headD (raw_ints% [6996878218782075043084289625]) 0) 50 false) .empty .empty) .empty) (.node 18 (sourceLit (List.headD (raw_ints% [2702972835149660143674350175]) 0) 53 true) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [58776168389001233736462715316475]) 0) 38 true) (.node 20 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 55 false) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [99848039641972223263286625]) 0) 56 false) .empty .empty)))

#time def treeG_J018_part002 : IntSourceTree :=
  (.node 14 (sourceLit (List.headD (raw_ints% [14872081758322549677166332225]) 0) 48 true) treeG_J018_part000 treeG_J018_part001)

#time def treeG_J018_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [1495382901114067105901475]) 0) 62 false) (.node 26 (sourceLit (List.headD (raw_ints% [6061702266383006140808625]) 0) 60 false) (.node 25 (sourceLit (List.headD (raw_ints% [219358589570633815267003691142375]) 0) 35 true) (.node 24 (sourceLit (List.headD (raw_ints% [12295452847917477142379475]) 0) 59 false) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [1349432100967235433474187046214225]) 0) 32 true) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [738310666906545497669775]) 0) 63 false) (.node 29 (sourceLit (List.headD (raw_ints% [2142279786084298855319266544735685]) 0) 31 true) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [6932319689390900642129314816146045]) 0) 29 true) .empty .empty)))

#time def treeG_J018_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [2786411480825734442205]) 0) 71 false) (.node 34 (sourceLit (List.headD (raw_ints% [11268487371388073512665]) 0) 69 false) (.node 33 (sourceLit (List.headD (raw_ints% [11343551176838629958171591546858655]) 0) 28 true) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [149372084187442385342552148534975825]) 0) 24 true) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [1378642738986775271205]) 0) 72 false) (.node 37 (sourceLit (List.headD (raw_ints% [246258496147598909353926063996732825]) 0) 23 true) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [810074579729603496637136662987976415]) 0) 21 true) .empty .empty)))

#time def treeG_J018_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [22796731777394918849175]) 0) 68 false) treeG_J018_part003 treeG_J018_part004)

#time def treeG_J018_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [150998281453547088472164588829425]) 0) 36 true) treeG_J018_part002 treeG_J018_part005)

#time def treeG_J018_part007 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [58744052690484308677010298675]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [120963911245531441305036036075]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 45 false) (.node 48 (sourceLit (List.headD (raw_ints% [1001458738463711054601938072625]) 0) 44 false) .empty .empty) .empty) (.node 51 (sourceLit (List.headD (raw_ints% [16530039795781559212573282875]) 0) 46 true) .empty .empty)) (.node 54 (sourceLit (List.headD (raw_ints% [14316061614989096983196951775]) 0) 50 false) (.node 53 (sourceLit (List.headD (raw_ints% [14383281380744993081070259125]) 0) 48 true) .empty .empty) (.node 55 (sourceLit (List.headD (raw_ints% [14872081758322549677166332225]) 0) 49 true) .empty .empty)))

#time def treeG_J018_part008 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [72074535838565955423505082804475]) 0) 40 true) (.node 58 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 55 false) (.node 57 (sourceLit (List.headD (raw_ints% [1846212236931446873092600425]) 0) 53 true) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [2702972835149660143674350175]) 0) 54 true) .empty .empty)) (.node 62 (sourceLit (List.headD (raw_ints% [58776168389001233736462715316475]) 0) 39 true) (.node 61 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 56 false) .empty .empty) (.node 63 (sourceLit (List.headD (raw_ints% [99848039641972223263286625]) 0) 57 false) .empty .empty)))

#time def treeG_J018_part009 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [6996878218782075043084289625]) 0) 51 false) treeG_J018_part007 treeG_J018_part008)

#time def treeG_J018_part010 : IntSourceTree :=
  (.node 69 (sourceLit (List.headD (raw_ints% [1495382901114067105901475]) 0) 63 false) (.node 67 (sourceLit (List.headD (raw_ints% [6061702266383006140808625]) 0) 61 false) (.node 66 (sourceLit (List.headD (raw_ints% [219358589570633815267003691142375]) 0) 36 true) (.node 65 (sourceLit (List.headD (raw_ints% [12295452847917477142379475]) 0) 60 false) .empty .empty) .empty) (.node 68 (sourceLit (List.headD (raw_ints% [1349432100967235433474187046214225]) 0) 33 true) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [738310666906545497669775]) 0) 64 false) (.node 70 (sourceLit (List.headD (raw_ints% [2142279786084298855319266544735685]) 0) 32 true) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [6932319689390900642129314816146045]) 0) 30 true) .empty .empty)))

#time def treeG_J018_part011 : IntSourceTree :=
  (.node 77 (sourceLit (List.headD (raw_ints% [2786411480825734442205]) 0) 72 false) (.node 75 (sourceLit (List.headD (raw_ints% [11268487371388073512665]) 0) 70 false) (.node 74 (sourceLit (List.headD (raw_ints% [11343551176838629958171591546858655]) 0) 29 true) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [149372084187442385342552148534975825]) 0) 25 true) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [1378642738986775271205]) 0) 73 false) (.node 78 (sourceLit (List.headD (raw_ints% [246258496147598909353926063996732825]) 0) 24 true) .empty .empty) (.node 88 (sourceLit (List.headD (raw_ints% [604999456525605067180182153225]) 0) 43 false) .empty .empty)))

#time def treeG_J018_part012 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [22796731777394918849175]) 0) 69 false) treeG_J018_part010 treeG_J018_part011)

#time def treeG_J018_part013 : IntSourceTree :=
  (.node 64 (sourceLit (List.headD (raw_ints% [150998281453547088472164588829425]) 0) 37 true) treeG_J018_part009 treeG_J018_part012)

#time def treeG_J018_part014 : IntSourceTree :=
  (.node 47 (sourceLit (List.headD (raw_ints% [664507599790418680345445971575]) 0) 42 false) treeG_J018_part006 treeG_J018_part013)

#time def treeG_J018_part015 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [13894481003167436484974186025]) 0) 48 true) (.node 92 (sourceLit (List.headD (raw_ints% [1073379207518283065751511875]) 0) 48 true) (.node 91 (sourceLit (List.headD (raw_ints% [183183769800578573933061773475]) 0) 47 false) (.node 90 (sourceLit (List.headD (raw_ints% [76038183060595172377837101225]) 0) 45 false) .empty .empty) .empty) (.node 93 (sourceLit (List.headD (raw_ints% [11106997768873802923453336725]) 0) 51 false) .empty .empty)) (.node 96 (sourceLit (List.headD (raw_ints% [7487232810596762184795930525]) 0) 50 true) (.node 95 (sourceLit (List.headD (raw_ints% [21635245011196118923309613925]) 0) 50 false) .empty .empty) (.node 97 (sourceLit (List.headD (raw_ints% [5283357022345648501920790125]) 0) 52 false) .empty .empty)))

#time def treeG_J018_part016 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [789420412770472651311238856234175]) 0) 36 true) (.node 101 (sourceLit (List.headD (raw_ints% [517820118319526409651577947119325]) 0) 38 true) (.node 100 (sourceLit (List.headD (raw_ints% [90809056841818260604326525]) 0) 60 true) (.node 99 (sourceLit (List.headD (raw_ints% [128223198403394780324350634420475]) 0) 39 false) .empty .empty) .empty) (.node 102 (sourceLit (List.headD (raw_ints% [305985927935076168064910625]) 0) 56 false) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [988627662057742892510313019493025]) 0) 35 true) (.node 104 (sourceLit (List.headD (raw_ints% [75257133946137268978527675]) 0) 58 false) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [18529203429451948143950325]) 0) 60 false) .empty .empty)))

#time def treeG_J018_part017 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [989451638713233602510850675]) 0) 53 true) treeG_J018_part015 treeG_J018_part016)

#time def treeG_J018_part018 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [555936812687386146876375]) 0) 65 false) (.node 110 (sourceLit (List.headD (raw_ints% [2252455135321588714133175]) 0) 63 false) (.node 109 (sourceLit (List.headD (raw_ints% [8653177021653584612474229824978115]) 0) 31 true) (.node 108 (sourceLit (List.headD (raw_ints% [2283159682634469517453575]) 0) 63 false) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [27344156887957881042978949899624915]) 0) 29 true) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [34324976183401764185685]) 0) 69 false) (.node 113 (sourceLit (List.headD (raw_ints% [44115006338288575178862926982309705]) 0) 28 true) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [576615191130229931980429710463978095]) 0) 24 true) .empty .empty)))

#time def treeG_J018_part019 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [545491313260791454014918334875]) 0) 44 false) (.node 118 (sourceLit (List.headD (raw_ints% [4194180222664693613205]) 0) 72 false) (.node 117 (sourceLit (List.headD (raw_ints% [948718177351940173386491124283073775]) 0) 23 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [3130061358631979053025680360959748785]) 0) 21 true) .empty .empty)) (.node 131 (sourceLit (List.headD (raw_ints% [23142055714094182897602596025]) 0) 48 false) (.node 130 (sourceLit (List.headD (raw_ints% [517603093481585289381793928325]) 0) 46 false) .empty .empty) (.node 132 (sourceLit (List.headD (raw_ints% [7777482319380891578503217175]) 0) 52 false) .empty .empty)))

#time def treeG_J018_part020 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [2120518972640584767615]) 0) 73 false) treeG_J018_part018 treeG_J018_part019)

#time def treeG_J018_part021 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [5670042765293046655069931070341775]) 0) 32 true) treeG_J018_part017 treeG_J018_part020)

#time def treeG_J018_part022 : IntSourceTree :=
  (.node 138 (sourceLit (List.headD (raw_ints% [3569835825909221960757290625]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [3659591698103510970056331075]) 0) 53 false) (.node 135 (sourceLit (List.headD (raw_ints% [122200094394389149024018275]) 0) 52 false) (.node 134 (sourceLit (List.headD (raw_ints% [30111929460506114710616395125]) 0) 50 false) .empty .empty) .empty) (.node 137 (sourceLit (List.headD (raw_ints% [102383862870974692425528825]) 0) 51 true) .empty .empty)) (.node 140 (sourceLit (List.headD (raw_ints% [100148867120980367873927858612475]) 0) 41 false) (.node 139 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 56 false) .empty .empty) (.node 141 (sourceLit (List.headD (raw_ints% [3108806802726708535002547425]) 0) 56 true) .empty .empty)))

#time def treeG_J018_part023 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [384634536243554538621654664175325]) 0) 37 true) (.node 144 (sourceLit (List.headD (raw_ints% [319211065658462781419537133702375]) 0) 38 true) (.node 143 (sourceLit (List.headD (raw_ints% [3220904504579749137525375]) 0) 63 false) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [50666228250302314693768725]) 0) 59 false) .empty .empty)) (.node 148 (sourceLit (List.headD (raw_ints% [2160305332162905610797872012063775]) 0) 34 true) (.node 147 (sourceLit (List.headD (raw_ints% [3116875290767235500785425]) 0) 63 false) .empty .empty) (.node 149 (sourceLit (List.headD (raw_ints% [3070936464154871929005675]) 0) 63 false) .empty .empty)))

#time def treeG_J018_part024 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [229521974965262587957557615901425]) 0) 40 true) treeG_J018_part022 treeG_J018_part023)

#time def treeG_J018_part025 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [5764122203003422668255]) 0) 72 false) (.node 153 (sourceLit (List.headD (raw_ints% [373562958468226796082975]) 0) 66 false) (.node 152 (sourceLit (List.headD (raw_ints% [10205918599283490200424817541739435]) 0) 31 true) (.node 151 (sourceLit (List.headD (raw_ints% [189268058551880402057925]) 0) 67 false) .empty .empty) .empty) (.node 154 (sourceLit (List.headD (raw_ints% [16385727580724972610345667717725525]) 0) 30 true) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [5695664409736604628255]) 0) 72 false) (.node 156 (sourceLit (List.headD (raw_ints% [213621553471393773318938780964501135]) 0) 26 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [351229840602170632016282530143170475]) 0) 25 true) .empty .empty)))

#time def treeG_J018_part026 : IntSourceTree :=
  (.node 173 (sourceLit (List.headD (raw_ints% [20002931508649763390559531975]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [167209661840503357724366077425]) 0) 48 false) (.node 170 (sourceLit (List.headD (raw_ints% [234726565100098140818540616825]) 0) 46 false) .empty .empty) (.node 172 (sourceLit (List.headD (raw_ints% [47357490635706648860956703925]) 0) 48 false) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [38588613909816110497923176325]) 0) 50 false) (.node 174 (sourceLit (List.headD (raw_ints% [38367526934584290384108656775]) 0) 48 false) .empty .empty) (.node 176 (sourceLit (List.headD (raw_ints% [8464833565751875376988076725]) 0) 50 false) .empty .empty)))

#time def treeG_J018_part027 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [175971092729869896375]) 0) 77 false) treeG_J018_part025 treeG_J018_part026)

#time def treeG_J018_part028 : IntSourceTree :=
  (.node 150 (sourceLit (List.headD (raw_ints% [3255448617784642878577481640121215]) 0) 33 true) treeG_J018_part024 treeG_J018_part027)

#time def treeG_J018_part029 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [12236522965708426949567235375]) 0) 48 false) treeG_J018_part021 treeG_J018_part028)

#time def treeG_J018_part030 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [759530915972648171991866000475]) 0) 45 false) treeG_J018_part014 treeG_J018_part029)

#time def treeG_J018_part031 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [6523599533388493238070005475]) 0) 56 true) (.node 180 (sourceLit (List.headD (raw_ints% [1154852753843652720125487075]) 0) 57 false) (.node 179 (sourceLit (List.headD (raw_ints% [11246818060001395114255735220475]) 0) 39 true) (.node 178 (sourceLit (List.headD (raw_ints% [1876519414555492512596172525]) 0) 52 false) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [2120201992255212295634423684918925]) 0) 38 false) .empty .empty)) (.node 184 (sourceLit (List.headD (raw_ints% [130880754346966675823096325]) 0) 58 false) (.node 183 (sourceLit (List.headD (raw_ints% [6555282786117930163330604852611425]) 0) 36 true) .empty .empty) (.node 185 (sourceLit (List.headD (raw_ints% [4118749388477661610202281119744975]) 0) 35 true) .empty .empty)))

#time def treeG_J018_part032 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [76830198881150691071500462584253965]) 0) 29 true) (.node 189 (sourceLit (List.headD (raw_ints% [25911708292952905160291722368042285]) 0) 31 true) (.node 188 (sourceLit (List.headD (raw_ints% [3950590898900001484117275]) 0) 63 false) (.node 187 (sourceLit (List.headD (raw_ints% [18946567554294443816715967436879025]) 0) 32 true) .empty .empty) .empty) (.node 190 (sourceLit (List.headD (raw_ints% [3889417792988155143878175]) 0) 63 false) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [119179691250247268027934153685521255]) 0) 28 true) (.node 192 (sourceLit (List.headD (raw_ints% [958207655727657069587025]) 0) 65 false) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [236263053734619739340235]) 0) 67 false) .empty .empty)))

#time def treeG_J018_part033 : IntSourceTree :=
  (.node 186 (sourceLit (List.headD (raw_ints% [1004282025651573954681825]) 0) 65 false) treeG_J018_part031 treeG_J018_part032)

#time def treeG_J018_part034 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [188442453671909775023335424775]) 0) 47 false) (.node 198 (sourceLit (List.headD (raw_ints% [7197148596808515643305]) 0) 72 false) (.node 197 (sourceLit (List.headD (raw_ints% [2469226678190360199716529371148944385]) 0) 23 true) (.node 196 (sourceLit (List.headD (raw_ints% [113862600948838684395]) 0) 78 false) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [8109293540637481171495360603621706415]) 0) 21 true) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [82478458305704870772346172475]) 0) 48 false) (.node 212 (sourceLit (List.headD (raw_ints% [104989803285456225096340340025]) 0) 49 false) .empty .empty) (.node 214 (sourceLit (List.headD (raw_ints% [49899796574092938851621732775]) 0) 50 false) .empty .empty)))

#time def treeG_J018_part035 : IntSourceTree :=
  (.node 219 (sourceLit (List.headD (raw_ints% [1550522978317360569730826475]) 0) 53 true) (.node 217 (sourceLit (List.headD (raw_ints% [4283608714311425034706802775]) 0) 52 false) (.node 216 (sourceLit (List.headD (raw_ints% [23950247117402066617697852025]) 0) 51 false) .empty .empty) (.node 218 (sourceLit (List.headD (raw_ints% [2892586972079586708773621775]) 0) 54 false) .empty .empty)) (.node 221 (sourceLit (List.headD (raw_ints% [7728217818101319415504495725]) 0) 56 false) (.node 220 (sourceLit (List.headD (raw_ints% [211544552301962130862111452445425]) 0) 40 true) .empty .empty) (.node 222 (sourceLit (List.headD (raw_ints% [2579245942185737471549538916721775]) 0) 39 false) .empty .empty)))

#time def treeG_J018_part036 : IntSourceTree :=
  (.node 215 (sourceLit (List.headD (raw_ints% [37389926179429177191916510575]) 0) 49 false) treeG_J018_part034 treeG_J018_part035)

#time def treeG_J018_part037 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [1520757939202566562143815757404889105]) 0) 24 true) treeG_J018_part033 treeG_J018_part036)

#time def treeG_J018_part038 : IntSourceTree :=
  (.node 228 (sourceLit (List.headD (raw_ints% [14625956889968632595120223412751475]) 0) 33 true) (.node 226 (sourceLit (List.headD (raw_ints% [3349480315990552532958971791394325]) 0) 36 true) (.node 225 (sourceLit (List.headD (raw_ints% [5013407881041522570582975]) 0) 63 false) (.node 224 (sourceLit (List.headD (raw_ints% [5916860654801004600491530585206675]) 0) 37 true) .empty .empty) .empty) (.node 227 (sourceLit (List.headD (raw_ints% [4917380914445356136669175]) 0) 63 false) .empty .empty)) (.node 230 (sourceLit (List.headD (raw_ints% [19400811057383619403136759087799855]) 0) 32 true) (.node 229 (sourceLit (List.headD (raw_ints% [4830245333645131039228875]) 0) 63 false) .empty .empty) (.node 231 (sourceLit (List.headD (raw_ints% [2375273324573111927414775]) 0) 64 false) .empty .empty)))

#time def treeG_J018_part039 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [1093514832259779015505938195475886835]) 0) 25 true) (.node 234 (sourceLit (List.headD (raw_ints% [86408236088797322807242818250070205]) 0) 29 true) (.node 233 (sourceLit (List.headD (raw_ints% [292322348629715136752025]) 0) 67 false) .empty .empty) (.node 235 (sourceLit (List.headD (raw_ints% [144037098486564976648155]) 0) 68 false) .empty .empty)) (.node 238 (sourceLit (List.headD (raw_ints% [1766766996986018935683964310862603435]) 0) 24 true) (.node 237 (sourceLit (List.headD (raw_ints% [8878748511714746974305]) 0) 72 false) .empty .empty) (.node 239 (sourceLit (List.headD (raw_ints% [4381611113130597301305]) 0) 73 false) .empty .empty)))

#time def treeG_J018_part040 : IntSourceTree :=
  (.node 232 (sourceLit (List.headD (raw_ints% [56418361682583710670650827500775095]) 0) 30 true) treeG_J018_part038 treeG_J018_part039)

#time def treeG_J018_part041 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [7297618673666835619696658925]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [61210979238369767205320289225]) 0) 50 false) (.node 254 (sourceLit (List.headD (raw_ints% [126589389676825451160583688175]) 0) 48 false) (.node 253 (sourceLit (List.headD (raw_ints% [64983940268156698315221276075]) 0) 50 false) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [14462546306838650907464216925]) 0) 51 false) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [200815397862209189660443811866875]) 0) 39 false) (.node 258 (sourceLit (List.headD (raw_ints% [6690698014067357556817433025]) 0) 52 false) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [10789345009066582330734723075]) 0) 54 true) .empty .empty)))

#time def treeG_J018_part042 : IntSourceTree :=
  (.node 265 (sourceLit (List.headD (raw_ints% [43216135849930375193729963561908425]) 0) 35 true) (.node 263 (sourceLit (List.headD (raw_ints% [47823217861089729708123227520159825]) 0) 36 false) (.node 262 (sourceLit (List.headD (raw_ints% [21980035169591132069078996925]) 0) 56 false) .empty .empty) (.node 264 (sourceLit (List.headD (raw_ints% [857577272003570482336840725]) 0) 61 true) .empty .empty)) (.node 267 (sourceLit (List.headD (raw_ints% [88236802557403237237971129887739375]) 0) 32 true) (.node 266 (sourceLit (List.headD (raw_ints% [3004843829738374661219325]) 0) 64 false) .empty .empty) (.node 268 (sourceLit (List.headD (raw_ints% [5884170929990710789221075]) 0) 63 false) .empty .empty)))

#time def treeG_J018_part043 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [3812558410670909342531315304482325]) 0) 38 true) treeG_J018_part041 treeG_J018_part042)

#time def treeG_J018_part044 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [70542481518101563081189360425]) 0) 49 false) treeG_J018_part040 treeG_J018_part043)

#time def treeG_J018_part045 : IntSourceTree :=
  (.node 223 (sourceLit (List.headD (raw_ints% [6729737421681597182871629475]) 0) 57 true) treeG_J018_part037 treeG_J018_part044)

#time def treeG_J018_part046 : IntSourceTree :=
  (.node 274 (sourceLit (List.headD (raw_ints% [348381643524810534163815]) 0) 67 false) (.node 272 (sourceLit (List.headD (raw_ints% [708532834422727428913875]) 0) 66 false) (.node 271 (sourceLit (List.headD (raw_ints% [233582778036987219378687682820543715]) 0) 29 true) (.node 270 (sourceLit (List.headD (raw_ints% [5771072874302106934579575]) 0) 63 false) .empty .empty) .empty) (.node 273 (sourceLit (List.headD (raw_ints% [332167202210422417337272466320679505]) 0) 28 true) .empty .empty)) (.node 276 (sourceLit (List.headD (raw_ints% [85739446800759570237915]) 0) 69 false) (.node 275 (sourceLit (List.headD (raw_ints% [4009369170480462097519724610599604015]) 0) 24 true) .empty .empty) (.node 277 (sourceLit (List.headD (raw_ints% [6278891979887871924330976192658150295]) 0) 23 true) .empty .empty)))

#time def treeG_J018_part047 : IntSourceTree :=
  (.node 296 (sourceLit (List.headD (raw_ints% [2328795757560481286726402325]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [80068083962220457778820819375]) 0) 50 false) (.node 293 (sourceLit (List.headD (raw_ints% [199691467766701381552411269225]) 0) 48 false) (.node 279 (sourceLit (List.headD (raw_ints% [20158978411138821799448068370179948545]) 0) 21 true) .empty .empty) .empty) (.node 295 (sourceLit (List.headD (raw_ints% [696870808573408390380212325]) 0) 56 false) .empty .empty)) (.node 298 (sourceLit (List.headD (raw_ints% [2202515850793624455461518575]) 0) 55 false) (.node 297 (sourceLit (List.headD (raw_ints% [5089468796263612936378707075]) 0) 53 false) .empty .empty) (.node 299 (sourceLit (List.headD (raw_ints% [2060305248096179531637064875]) 0) 55 false) .empty .empty)))

#time def treeG_J018_part048 : IntSourceTree :=
  (.node 278 (sourceLit (List.headD (raw_ints% [10560348426620978305305]) 0) 72 false) treeG_J018_part046 treeG_J018_part047)

#time def treeG_J018_part049 : IntSourceTree :=
  (.node 305 (sourceLit (List.headD (raw_ints% [867604087765653527478006675]) 0) 62 true) (.node 303 (sourceLit (List.headD (raw_ints% [897180393477272789123457075]) 0) 62 false) (.node 302 (sourceLit (List.headD (raw_ints% [1597951088214161703520213555301025]) 0) 41 true) (.node 301 (sourceLit (List.headD (raw_ints% [26245780645269221161743714525]) 0) 55 true) .empty .empty) .empty) (.node 304 (sourceLit (List.headD (raw_ints% [13435019628972683577153689526341625]) 0) 39 false) .empty .empty)) (.node 307 (sourceLit (List.headD (raw_ints% [7101994404508142508208125]) 0) 63 false) (.node 306 (sourceLit (List.headD (raw_ints% [9966663883484955665192747942628525]) 0) 38 true) .empty .empty) (.node 308 (sourceLit (List.headD (raw_ints% [18402711416858651160712726618746975]) 0) 35 true) .empty .empty)))

#time def treeG_J018_part050 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [208105242896506146080925]) 0) 68 false) (.node 311 (sourceLit (List.headD (raw_ints% [26529683982257773493475]) 0) 71 false) (.node 310 (sourceLit (List.headD (raw_ints% [17923783942353134049383326461542415]) 0) 34 true) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [44291104088600877177009213829942155]) 0) 32 true) .empty .empty)) (.node 315 (sourceLit (List.headD (raw_ints% [51086136259561389378915]) 0) 70 false) (.node 314 (sourceLit (List.headD (raw_ints% [61439741530406273632507412017652325]) 0) 31 true) .empty .empty) (.node 316 (sourceLit (List.headD (raw_ints% [728963584555170770503446603780929295]) 0) 27 true) .empty .empty)))

#time def treeG_J018_part051 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [6938096526336290539213275]) 0) 63 false) treeG_J018_part049 treeG_J018_part050)

#time def treeG_J018_part052 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [103089987541042830130638816078075]) 0) 42 false) treeG_J018_part048 treeG_J018_part051)

#time def treeG_J018_part053 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [30137185441859486076869371875]) 0) 51 false) (.node 334 (sourceLit (List.headD (raw_ints% [272793545856577311944238850275]) 0) 48 false) (.node 319 (sourceLit (List.headD (raw_ints% [193085541046574406375]) 0) 78 false) (.node 318 (sourceLit (List.headD (raw_ints% [1128031245725463247161752970448886715]) 0) 26 true) .empty .empty) .empty) (.node 335 (sourceLit (List.headD (raw_ints% [98925188686071148352321349525]) 0) 50 false) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [13667177170987094188697395275]) 0) 52 false) (.node 337 (sourceLit (List.headD (raw_ints% [11332747386817014674114559675]) 0) 53 false) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [87872759733012754965808350795525]) 0) 39 false) .empty .empty)))

#time def treeG_J018_part054 : IntSourceTree :=
  (.node 344 (sourceLit (List.headD (raw_ints% [4446298845912661638830669025]) 0) 61 false) (.node 342 (sourceLit (List.headD (raw_ints% [24112907907430176615411355725]) 0) 57 true) (.node 341 (sourceLit (List.headD (raw_ints% [7111438011984279906711757418980725]) 0) 38 false) .empty .empty) (.node 343 (sourceLit (List.headD (raw_ints% [150092087506796078733416895059425425]) 0) 36 true) .empty .empty)) (.node 346 (sourceLit (List.headD (raw_ints% [873613775425130276800445325]) 0) 63 true) (.node 345 (sourceLit (List.headD (raw_ints% [473136763977056249662648028404840425]) 0) 35 false) .empty .empty) (.node 347 (sourceLit (List.headD (raw_ints% [1187496174528671087906700606768711825]) 0) 32 true) .empty .empty)))

#time def treeG_J018_part055 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [19030566001451300457282982575]) 0) 54 false) treeG_J018_part053 treeG_J018_part054)

#time def treeG_J018_part056 : IntSourceTree :=
  (.node 353 (sourceLit (List.headD (raw_ints% [1085148128624805652327022376237469455]) 0) 28 true) (.node 351 (sourceLit (List.headD (raw_ints% [913539394273613359781845210718170845]) 0) 29 true) (.node 350 (sourceLit (List.headD (raw_ints% [8105120178370474143846975]) 0) 63 false) (.node 349 (sourceLit (List.headD (raw_ints% [497790818512680681542137186865933685]) 0) 31 true) .empty .empty) .empty) (.node 352 (sourceLit (List.headD (raw_ints% [989366940441770074668525]) 0) 66 false) .empty .empty)) (.node 355 (sourceLit (List.headD (raw_ints% [11719204661303543952402172865919391185]) 0) 24 true) (.node 354 (sourceLit (List.headD (raw_ints% [484039328061214050159885]) 0) 67 false) .empty .empty) (.node 356 (sourceLit (List.headD (raw_ints% [118605098237485987277745]) 0) 69 false) .empty .empty)))

#time def treeG_J018_part057 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [61664456565103447764698912325]) 0) 51 false) (.node 359 (sourceLit (List.headD (raw_ints% [52035021315290826018904121738548801215]) 0) 21 true) (.node 358 (sourceLit (List.headD (raw_ints% [29103755900658625730085]) 0) 71 false) .empty .empty) (.node 375 (sourceLit (List.headD (raw_ints% [183594082359181037975571672675]) 0) 49 false) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [6927715685229765763191522525]) 0) 54 false) (.node 377 (sourceLit (List.headD (raw_ints% [19958247849332260204111957725]) 0) 52 false) .empty .empty) (.node 379 (sourceLit (List.headD (raw_ints% [5425956178602376062149135775]) 0) 53 false) .empty .empty)))

#time def treeG_J018_part058 : IntSourceTree :=
  (.node 357 (sourceLit (List.headD (raw_ints% [17047942725877592731779315128331587145]) 0) 23 true) treeG_J018_part056 treeG_J018_part057)

#time def treeG_J018_part059 : IntSourceTree :=
  (.node 348 (sourceLit (List.headD (raw_ints% [8319817879025574227195175]) 0) 63 false) treeG_J018_part055 treeG_J018_part058)

#time def treeG_J018_part060 : IntSourceTree :=
  (.node 317 (sourceLit (List.headD (raw_ints% [50224452753900582340695]) 0) 70 false) treeG_J018_part052 treeG_J018_part059)

#time def treeG_J018_part061 : IntSourceTree :=
  (.node 269 (sourceLit (List.headD (raw_ints% [91095946826796155600670064933969515]) 0) 31 true) treeG_J018_part045 treeG_J018_part060)

#time def treeG_J018_part062 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [9355009770068395378304534175]) 0) 52 false) treeG_J018_part030 treeG_J018_part061)

#time def treeG_J018_part063 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [1328475733419578791577168925]) 0) 64 false) (.node 383 (sourceLit (List.headD (raw_ints% [38467794203066541241386668925]) 0) 58 true) (.node 382 (sourceLit (List.headD (raw_ints% [13503242364840926720792611640184825]) 0) 39 false) (.node 381 (sourceLit (List.headD (raw_ints% [11319086661680130404756674275]) 0) 57 false) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [203832166022686813042031653164791925]) 0) 37 true) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [1754329545254768696109098775]) 0) 63 true) (.node 386 (sourceLit (List.headD (raw_ints% [513003419510996072323419020175354525]) 0) 36 false) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [1113885328861236483263849700293723925]) 0) 33 true) .empty .empty)))

#time def treeG_J018_part064 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [839389162503180557796992728166860155]) 0) 29 true) (.node 392 (sourceLit (List.headD (raw_ints% [736374977919209851073808355398402225]) 0) 30 true) (.node 391 (sourceLit (List.headD (raw_ints% [4709320628641479136682175]) 0) 64 false) (.node 390 (sourceLit (List.headD (raw_ints% [426095682743268145344603881019764025]) 0) 32 true) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [573156454648757782506675]) 0) 67 false) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [8803350323082860870388386450795674005]) 0) 25 true) (.node 395 (sourceLit (List.headD (raw_ints% [279694783022968492644225]) 0) 68 false) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [34190322741792702468525]) 0) 71 false) .empty .empty)))

#time def treeG_J018_part065 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [9701539231714857915177075]) 0) 63 false) treeG_J018_part063 treeG_J018_part064)

#time def treeG_J018_part066 : IntSourceTree :=
  (.node 419 (sourceLit (List.headD (raw_ints% [366142015414205174090711269402875]) 0) 39 false) (.node 417 (sourceLit (List.headD (raw_ints% [38998961791469418416469792975]) 0) 52 false) (.node 416 (sourceLit (List.headD (raw_ints% [123319711475462065821832928925]) 0) 50 false) (.node 399 (sourceLit (List.headD (raw_ints% [16746281273677863722085]) 0) 72 false) .empty .empty) .empty) (.node 418 (sourceLit (List.headD (raw_ints% [26249318527677426219526520175]) 0) 52 false) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [9707335535433548431165732727114925]) 0) 38 true) (.node 420 (sourceLit (List.headD (raw_ints% [850288113928057774695865425]) 0) 58 true) .empty .empty) (.node 422 (sourceLit (List.headD (raw_ints% [46751081230790437424924704275]) 0) 57 false) .empty .empty)))

#time def treeG_J018_part067 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [17603605598880545402256109252380056625]) 0) 32 false) (.node 425 (sourceLit (List.headD (raw_ints% [2103794092158550753998901253723175825]) 0) 35 true) (.node 424 (sourceLit (List.headD (raw_ints% [56252989586717187796709345025]) 0) 59 true) .empty .empty) (.node 426 (sourceLit (List.headD (raw_ints% [6187516709103445443109121025]) 0) 63 false) .empty .empty)) (.node 429 (sourceLit (List.headD (raw_ints% [8413291812377211184568660415483857715]) 0) 31 true) (.node 428 (sourceLit (List.headD (raw_ints% [3516978908388562966445392725]) 0) 63 true) .empty .empty) (.node 430 (sourceLit (List.headD (raw_ints% [11297958285059241686507175]) 0) 63 false) .empty .empty)))

#time def treeG_J018_part068 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [366143965344250906266098681302382625]) 0) 36 false) treeG_J018_part066 treeG_J018_part067)

#time def treeG_J018_part069 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [12535817742975739743132303246536040285]) 0) 24 true) treeG_J018_part065 treeG_J018_part068)

#time def treeG_J018_part070 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [10068105299092656585405]) 0) 73 false) (.node 434 (sourceLit (List.headD (raw_ints% [662273581236301514853465]) 0) 67 false) (.node 433 (sourceLit (List.headD (raw_ints% [4805851694728873156263444466949748345]) 0) 28 true) (.node 432 (sourceLit (List.headD (raw_ints% [2730586747757938987345125]) 0) 65 false) .empty .empty) .empty) (.node 435 (sourceLit (List.headD (raw_ints% [42001701738900011746605361736759658735]) 0) 24 true) .empty .empty)) (.node 438 (sourceLit (List.headD (raw_ints% [39276889582926779206965]) 0) 71 false) (.node 437 (sourceLit (List.headD (raw_ints% [53378859858785294231327776478033804895]) 0) 23 true) .empty .empty) (.node 439 (sourceLit (List.headD (raw_ints% [148538062572321009871212730206027843345]) 0) 21 true) .empty .empty)))

#time def treeG_J018_part071 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [14720239117392361503540135975]) 0) 57 true) (.node 459 (sourceLit (List.headD (raw_ints% [1301460146817190634836086525]) 0) 57 false) (.node 458 (sourceLit (List.headD (raw_ints% [25143530421009886890086747925]) 0) 53 false) .empty .empty) (.node 460 (sourceLit (List.headD (raw_ints% [345314602922681869823729091459825]) 0) 41 false) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [5326179714616061166644460825]) 0) 62 false) (.node 462 (sourceLit (List.headD (raw_ints% [11605288950137237575979172183649875]) 0) 40 true) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [284988065683468859654065167233587275]) 0) 38 false) .empty .empty)))

#time def treeG_J018_part072 : IntSourceTree :=
  (.node 457 (sourceLit (List.headD (raw_ints% [83403215776797545413609013475]) 0) 51 false) treeG_J018_part070 treeG_J018_part071)

#time def treeG_J018_part073 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [3993598064816971519612028267232046845]) 0) 33 true) (.node 468 (sourceLit (List.headD (raw_ints% [9358745463870890942759979476336890275]) 0) 34 false) (.node 467 (sourceLit (List.headD (raw_ints% [14129362963461659582327340825]) 0) 63 false) (.node 466 (sourceLit (List.headD (raw_ints% [1308398755834773413161160136949265175]) 0) 37 true) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [7043659356008840790805962525]) 0) 63 true) .empty .empty)) (.node 472 (sourceLit (List.headD (raw_ints% [2583808275849733557329004265099825665]) 0) 31 true) (.node 471 (sourceLit (List.headD (raw_ints% [823579707052220318728125]) 0) 67 false) .empty .empty) (.node 473 (sourceLit (List.headD (raw_ints% [1584273838460423422331775]) 0) 66 false) .empty .empty)))

#time def treeG_J018_part074 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [20421521057904777244097736615748882305]) 0) 25 true) (.node 476 (sourceLit (List.headD (raw_ints% [16599175707908575438108487642981992365]) 0) 26 true) (.node 475 (sourceLit (List.headD (raw_ints% [47822349776666627776155]) 0) 71 false) .empty .empty) (.node 477 (sourceLit (List.headD (raw_ints% [46354519650948550214715]) 0) 71 false) .empty .empty)) (.node 498 (sourceLit (List.headD (raw_ints% [14288474312280029798520623325]) 0) 54 false) (.node 479 (sourceLit (List.headD (raw_ints% [1408163019328057217805]) 0) 76 false) .empty .empty) (.node 499 (sourceLit (List.headD (raw_ints% [457761189421446799523651286603525]) 0) 39 false) .empty .empty)))

#time def treeG_J018_part075 : IntSourceTree :=
  (.node 474 (sourceLit (List.headD (raw_ints% [1983231266112846299233225869391444095]) 0) 30 true) treeG_J018_part073 treeG_J018_part074)

#time def treeG_J018_part076 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [77508601321430448461944047825]) 0) 60 true) treeG_J018_part072 treeG_J018_part075)

#time def treeG_J018_part077 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [5903991529618676965731816885598053555]) 0) 29 true) treeG_J018_part069 treeG_J018_part076)

#time def treeG_J018_part078 : IntSourceTree :=
  (.node 505 (sourceLit (List.headD (raw_ints% [6663603143094052508463943929460572225]) 0) 35 false) (.node 503 (sourceLit (List.headD (raw_ints% [737513211748642508697432191179178625]) 0) 36 true) (.node 502 (sourceLit (List.headD (raw_ints% [76191559465575160432004976225]) 0) 57 true) (.node 501 (sourceLit (List.headD (raw_ints% [15232369182196458348345398190472125]) 0) 38 false) .empty .empty) .empty) (.node 504 (sourceLit (List.headD (raw_ints% [141471865020574166463020718225]) 0) 59 false) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [101341125972306043844570358017133027825]) 0) 32 true) (.node 506 (sourceLit (List.headD (raw_ints% [102258668157844230234380531925]) 0) 61 true) .empty .empty) (.node 508 (sourceLit (List.headD (raw_ints% [31775704835311882131100074375]) 0) 63 false) .empty .empty)))

#time def treeG_J018_part079 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [461000128612060953739155]) 0) 68 false) (.node 512 (sourceLit (List.headD (raw_ints% [3858050908659823562479875]) 0) 65 false) (.node 511 (sourceLit (List.headD (raw_ints% [121891146544524411661853087665827445485]) 0) 29 true) (.node 510 (sourceLit (List.headD (raw_ints% [14098616670302740823298432225]) 0) 63 true) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [36535080718866863761000623774647462295]) 0) 28 true) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [27686139178481314605345]) 0) 72 false) (.node 515 (sourceLit (List.headD (raw_ints% [211851900323544314555247549545345185425]) 0) 24 true) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [212207951467751912778408025809678072945]) 0) 23 true) .empty .empty)))

#time def treeG_J018_part080 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [158153219234311466268728332036874102115]) 0) 31 false) treeG_J018_part078 treeG_J018_part079)

#time def treeG_J018_part081 : IntSourceTree :=
  (.node 542 (sourceLit (List.headD (raw_ints% [38442947082470933500303742557771875]) 0) 39 false) (.node 540 (sourceLit (List.headD (raw_ints% [232868016423916940123806896316125]) 0) 40 true) (.node 539 (sourceLit (List.headD (raw_ints% [9082633725011267259176277225]) 0) 55 false) (.node 519 (sourceLit (List.headD (raw_ints% [504950611280631861939914841497936390415]) 0) 21 true) .empty .empty) .empty) (.node 541 (sourceLit (List.headD (raw_ints% [23327232160373355141667943775]) 0) 57 false) .empty .empty)) (.node 544 (sourceLit (List.headD (raw_ints% [1307489343115580228005562525646353175]) 0) 37 true) (.node 543 (sourceLit (List.headD (raw_ints% [161410434899432139098316349425]) 0) 58 true) .empty .empty) (.node 545 (sourceLit (List.headD (raw_ints% [109490233171002307462482383025]) 0) 61 false) .empty .empty)))

#time def treeG_J018_part082 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [166140415363945409307952388571338195805]) 0) 32 false) (.node 548 (sourceLit (List.headD (raw_ints% [120058616900047825730090316969806808375]) 0) 33 true) (.node 547 (sourceLit (List.headD (raw_ints% [130517394084767549399035213575]) 0) 62 true) .empty .empty) (.node 549 (sourceLit (List.headD (raw_ints% [70595069026632605053006111275]) 0) 63 false) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [116723529992824944547195079135627794155]) 0) 30 true) (.node 551 (sourceLit (List.headD (raw_ints% [14105205307959158585848257225]) 0) 64 true) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [568444267549850035037025]) 0) 68 false) .empty .empty)))

#time def treeG_J018_part083 : IntSourceTree :=
  (.node 546 (sourceLit (List.headD (raw_ints% [9280400654763599334786264203359102575]) 0) 36 false) treeG_J018_part081 treeG_J018_part082)

#time def treeG_J018_part084 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [53432149718970321222465]) 0) 71 false) treeG_J018_part080 treeG_J018_part083)

#time def treeG_J018_part085 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [30901541409721405737585]) 0) 72 false) (.node 557 (sourceLit (List.headD (raw_ints% [64390037062976708206665]) 0) 71 false) (.node 556 (sourceLit (List.headD (raw_ints% [178653548907727163679030574259381200695]) 0) 25 true) (.node 555 (sourceLit (List.headD (raw_ints% [269710729505394442634535]) 0) 69 false) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [171364909351942358290212552578180308335]) 0) 24 true) .empty .empty)) (.node 581 (sourceLit (List.headD (raw_ints% [17095313313587793869335853361001125]) 0) 38 true) (.node 580 (sourceLit (List.headD (raw_ints% [475640682030273621048469425]) 0) 56 false) .empty .empty) (.node 582 (sourceLit (List.headD (raw_ints% [122846023786321870715340863775]) 0) 57 false) .empty .empty)))

#time def treeG_J018_part086 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [398313946924741222557730812524624310225]) 0) 32 false) (.node 585 (sourceLit (List.headD (raw_ints% [17123517888018694332508444134631397625]) 0) 35 true) (.node 584 (sourceLit (List.headD (raw_ints% [151441149960003152780668533825]) 0) 60 true) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [321239134499848845159345297975]) 0) 61 false) .empty .empty)) (.node 589 (sourceLit (List.headD (raw_ints% [1118622154434694072109450867795328569115]) 0) 31 true) (.node 588 (sourceLit (List.headD (raw_ints% [81146549460039715765067643975]) 0) 64 true) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [155288754723567950929310654775]) 0) 63 false) .empty .empty)))

#time def treeG_J018_part087 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [1352600365068177444702292072103528625]) 0) 36 false) treeG_J018_part085 treeG_J018_part086)

#time def treeG_J018_part088 : IntSourceTree :=
  (.node 596 (sourceLit (List.headD (raw_ints% [158966172791469184213155]) 0) 70 false) (.node 594 (sourceLit (List.headD (raw_ints% [675888406487639116334895]) 0) 68 false) (.node 593 (sourceLit (List.headD (raw_ints% [897253159223732692616560009310374890945]) 0) 28 true) (.node 592 (sourceLit (List.headD (raw_ints% [3527265839716954602352684275]) 0) 67 true) .empty .empty) .empty) (.node 595 (sourceLit (List.headD (raw_ints% [1872539663621490639846939460749987557295]) 0) 24 true) .empty .empty)) (.node 598 (sourceLit (List.headD (raw_ints% [75347924406983095190865]) 0) 71 false) (.node 597 (sourceLit (List.headD (raw_ints% [1217020439794065396653836568265371532615]) 0) 23 true) .empty .empty) (.node 599 (sourceLit (List.headD (raw_ints% [2236887938350445870703485999752948542945]) 0) 21 true) .empty .empty)))

#time def treeG_J018_part089 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [130465691565502730121575458425]) 0) 62 true) (.node 623 (sourceLit (List.headD (raw_ints% [17766028667859625613353575825]) 0) 62 false) (.node 622 (sourceLit (List.headD (raw_ints% [6942282549507340921204949489846625]) 0) 42 true) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [332511213522969709088481824718735225]) 0) 40 false) .empty .empty)) (.node 627 (sourceLit (List.headD (raw_ints% [225878264292308197279190255775]) 0) 63 false) (.node 626 (sourceLit (List.headD (raw_ints% [3300489817847786708411838542248812525]) 0) 39 true) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [64796570478098631035977641186803889825]) 0) 36 false) .empty .empty)))

#time def treeG_J018_part090 : IntSourceTree :=
  (.node 621 (sourceLit (List.headD (raw_ints% [11425795739171540760309737175]) 0) 58 true) treeG_J018_part088 treeG_J018_part089)

#time def treeG_J018_part091 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [2780137792367650960589091304807238578365]) 0) 29 false) treeG_J018_part087 treeG_J018_part090)

#time def treeG_J018_part092 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [32568618186641171162534172035864574105]) 0) 29 true) treeG_J018_part084 treeG_J018_part091)

#time def treeG_J018_part093 : IntSourceTree :=
  (.node 500 (sourceLit (List.headD (raw_ints% [1075874130372624204765975975]) 0) 59 false) treeG_J018_part077 treeG_J018_part092)

#time def treeG_J018_part094 : IntSourceTree :=
  (.node 634 (sourceLit (List.headD (raw_ints% [108085567629636440181753229659313789605]) 0) 32 true) (.node 632 (sourceLit (List.headD (raw_ints% [362107665295059488142035797992858296565]) 0) 33 false) (.node 631 (sourceLit (List.headD (raw_ints% [165423789093288192885897375]) 0) 74 false) (.node 630 (sourceLit (List.headD (raw_ints% [160595321224829935177175407045833345615]) 0) 35 true) .empty .empty) .empty) (.node 633 (sourceLit (List.headD (raw_ints% [881958570996126113096930325]) 0) 70 true) .empty .empty)) (.node 636 (sourceLit (List.headD (raw_ints% [211735764339220434520988610811325794575]) 0) 28 true) (.node 635 (sourceLit (List.headD (raw_ints% [50772209622780584212545]) 0) 72 false) .empty .empty) (.node 637 (sourceLit (List.headD (raw_ints% [47288067864246238003245]) 0) 72 false) .empty .empty)))

#time def treeG_J018_part095 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [843101900761859765645647131675]) 0) 61 true) (.node 664 (sourceLit (List.headD (raw_ints% [293569379302880157687497140425]) 0) 60 false) (.node 663 (sourceLit (List.headD (raw_ints% [2241212531405117082616525606803896625]) 0) 36 true) (.node 639 (sourceLit (List.headD (raw_ints% [1388949468664427795415]) 0) 77 false) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [38404235553488755714171280916630452025]) 0) 35 false) .empty .empty)) (.node 668 (sourceLit (List.headD (raw_ints% [153512406876173956522128949875]) 0) 65 false) (.node 667 (sourceLit (List.headD (raw_ints% [1243239340293774619911161479340320316625]) 0) 32 true) .empty .empty) (.node 669 (sourceLit (List.headD (raw_ints% [5265602665033006458412019903750777517915]) 0) 31 false) .empty .empty)))

#time def treeG_J018_part096 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [130706941305265379795453001960898903035]) 0) 27 true) treeG_J018_part094 treeG_J018_part095)

#time def treeG_J018_part097 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [53467270962752366733210714124818672720465]) 0) 24 true) (.node 673 (sourceLit (List.headD (raw_ints% [24072143738107539933706851080853305871105]) 0) 28 false) (.node 672 (sourceLit (List.headD (raw_ints% [45875755847598731981142412275]) 0) 67 false) (.node 671 (sourceLit (List.headD (raw_ints% [23336338909145882663267543406673906817085]) 0) 29 true) .empty .empty) .empty) (.node 674 (sourceLit (List.headD (raw_ints% [7056344456375496543891777495]) 0) 68 true) .empty .empty)) (.node 677 (sourceLit (List.headD (raw_ints% [12334068477916042412689434523659479320185]) 0) 23 true) (.node 676 (sourceLit (List.headD (raw_ints% [247211504190775489487205]) 0) 70 false) .empty .empty) (.node 678 (sourceLit (List.headD (raw_ints% [113804347050001856822115]) 0) 71 false) .empty .empty)))

#time def treeG_J018_part098 : IntSourceTree :=
  (.node 707 (sourceLit (List.headD (raw_ints% [1294858429346476160204027643225]) 0) 62 true) (.node 705 (sourceLit (List.headD (raw_ints% [554500762433885617930648057275]) 0) 61 false) (.node 704 (sourceLit (List.headD (raw_ints% [4901302239588874755324380204553778425]) 0) 37 true) .empty .empty) (.node 706 (sourceLit (List.headD (raw_ints% [64808154096271049381465989254620952225]) 0) 36 false) .empty .empty)) (.node 709 (sourceLit (List.headD (raw_ints% [1623280521876183120290308286175]) 0) 63 false) (.node 708 (sourceLit (List.headD (raw_ints% [1761611904118563668198982608834751435225]) 0) 33 true) .empty .empty) (.node 710 (sourceLit (List.headD (raw_ints% [6550365234831645939829423160117444282835]) 0) 32 false) .empty .empty)))

#time def treeG_J018_part099 : IntSourceTree :=
  (.node 679 (sourceLit (List.headD (raw_ints% [14493600548723522743114498251242111045535]) 0) 21 true) treeG_J018_part097 treeG_J018_part098)

#time def treeG_J018_part100 : IntSourceTree :=
  (.node 670 (sourceLit (List.headD (raw_ints% [945651288457150887155864029125]) 0) 63 true) treeG_J018_part096 treeG_J018_part099)

#time def treeG_J018_part101 : IntSourceTree :=
  (.node 716 (sourceLit (List.headD (raw_ints% [51773384848038603257042805238328066363865]) 0) 25 true) (.node 714 (sourceLit (List.headD (raw_ints% [24936828279144631455160876918127816187945]) 0) 29 false) (.node 713 (sourceLit (List.headD (raw_ints% [49403590131583236433530133575]) 0) 68 false) (.node 712 (sourceLit (List.headD (raw_ints% [26233200231506358568403829790616773189605]) 0) 30 true) .empty .empty) .empty) (.node 715 (sourceLit (List.headD (raw_ints% [7056750634052478788565477855]) 0) 69 true) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [11288412947473919374325810507972288095905]) 0) 24 true) (.node 717 (sourceLit (List.headD (raw_ints% [152635368462283013480715]) 0) 71 false) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [69357964052740167368835]) 0) 72 false) .empty .empty)))

#time def treeG_J018_part102 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [19358497897981515804003880774428788999715]) 0) 31 true) (.node 747 (sourceLit (List.headD (raw_ints% [3317100271374448200118073135488190787825]) 0) 32 false) (.node 746 (sourceLit (List.headD (raw_ints% [1952103425629631001506943246225]) 0) 61 false) .empty .empty) (.node 748 (sourceLit (List.headD (raw_ints% [1908908056851171986292543442725]) 0) 63 true) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [128142182666452217700538313968553015342445]) 0) 29 false) (.node 750 (sourceLit (List.headD (raw_ints% [4192212332209517127736480601475]) 0) 63 false) .empty .empty) (.node 752 (sourceLit (List.headD (raw_ints% [1298548271879072924595592590225]) 0) 65 true) .empty .empty)))

#time def treeG_J018_part103 : IntSourceTree :=
  (.node 745 (sourceLit (List.headD (raw_ints% [77614653470199753756766322553060679425]) 0) 35 true) treeG_J018_part101 treeG_J018_part102)

#time def treeG_J018_part104 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [191466389874564170139315]) 0) 71 false) (.node 756 (sourceLit (List.headD (raw_ints% [1764249461389167391013741265]) 0) 72 true) (.node 755 (sourceLit (List.headD (raw_ints% [1649424280828008779863506836884998908748945]) 0) 24 false) (.node 754 (sourceLit (List.headD (raw_ints% [105863524719541969410952044645]) 0) 68 false) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [401853010306392783643653007382965051590735]) 0) 23 true) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [71211403783235401569116155903840815825]) 0) 37 true) (.node 759 (sourceLit (List.headD (raw_ints% [166121006610859187246098469876314498488945]) 0) 21 true) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [1623480927488053580855485444725]) 0) 63 false) .empty .empty)))

#time def treeG_J018_part105 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [77187691448979288134471071879584894266025]) 0) 31 false) (.node 790 (sourceLit (List.headD (raw_ints% [12954431566406580871916651967273116641275]) 0) 33 true) (.node 789 (sourceLit (List.headD (raw_ints% [5441096635578527092875395171625]) 0) 63 true) .empty .empty) (.node 791 (sourceLit (List.headD (raw_ints% [663407197587274390550937942825]) 0) 67 false) .empty .empty)) (.node 794 (sourceLit (List.headD (raw_ints% [129437286934651519968049183161957653787945]) 0) 30 true) (.node 793 (sourceLit (List.headD (raw_ints% [1496162632405405870329713124525]) 0) 66 true) .empty .empty) (.node 795 (sourceLit (List.headD (raw_ints% [28230068838398612049879380625]) 0) 71 false) .empty .empty)))

#time def treeG_J018_part106 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [2539356087746505934158527872161471111525]) 0) 34 false) treeG_J018_part104 treeG_J018_part105)

#time def treeG_J018_part107 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [233937745590158408480937489405787491387945]) 0) 28 true) treeG_J018_part103 treeG_J018_part106)

#time def treeG_J018_part108 : IntSourceTree :=
  (.node 711 (sourceLit (List.headD (raw_ints% [1115045248488677996671022941125]) 0) 64 true) treeG_J018_part100 treeG_J018_part107)

#time def treeG_J018_part109 : IntSourceTree :=
  (.node 828 (sourceLit (List.headD (raw_ints% [5155869911827279148003514332175]) 0) 63 false) (.node 799 (sourceLit (List.headD (raw_ints% [7631776613864000173155]) 0) 76 false) (.node 798 (sourceLit (List.headD (raw_ints% [195282298679459432134663598437496381747415]) 0) 25 true) (.node 797 (sourceLit (List.headD (raw_ints% [7057150480925131847068445775]) 0) 71 true) .empty .empty) .empty) (.node 827 (sourceLit (List.headD (raw_ints% [7874630113501513900541507113334003000625]) 0) 32 true) .empty .empty)) (.node 830 (sourceLit (List.headD (raw_ints% [15074405603366571313487270944725]) 0) 63 true) (.node 829 (sourceLit (List.headD (raw_ints% [59988195301925610750540326729012326784115]) 0) 31 false) .empty .empty) (.node 831 (sourceLit (List.headD (raw_ints% [542683992791462805601871176921292747863245]) 0) 29 true) .empty .empty)))

#time def treeG_J018_part110 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [14997159149893889720446560945]) 0) 73 false) (.node 834 (sourceLit (List.headD (raw_ints% [1707889681844489809151617213815]) 0) 67 true) (.node 833 (sourceLit (List.headD (raw_ints% [1468940808773827018632474639479145799644345]) 0) 28 false) .empty .empty) (.node 835 (sourceLit (List.headD (raw_ints% [18217397008463403335773802281615578593605905]) 0) 24 true) .empty .empty)) (.node 838 (sourceLit (List.headD (raw_ints% [14114492428240138258307030865]) 0) 71 true) (.node 837 (sourceLit (List.headD (raw_ints% [14011434335714771848608050144369580852493215]) 0) 23 false) .empty .empty) (.node 839 (sourceLit (List.headD (raw_ints% [6082912551131842641063136680123569717428335]) 0) 21 true) .empty .empty)))

#time def treeG_J018_part111 : IntSourceTree :=
  (.node 832 (sourceLit (List.headD (raw_ints% [6605805852577268049003096132825]) 0) 65 false) treeG_J018_part109 treeG_J018_part110)

#time def treeG_J018_part112 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [4050984242491336959666404628675]) 0) 67 false) (.node 871 (sourceLit (List.headD (raw_ints% [20381663184064766437894774487325]) 0) 64 true) (.node 870 (sourceLit (List.headD (raw_ints% [85897058434738772494373630663558560066665]) 0) 32 false) (.node 869 (sourceLit (List.headD (raw_ints% [15752836459233085388882423835975]) 0) 63 false) .empty .empty) .empty) (.node 872 (sourceLit (List.headD (raw_ints% [697059375689421381870813320680462536395295]) 0) 30 true) .empty .empty)) (.node 875 (sourceLit (List.headD (raw_ints% [1933730232551678705550652258815]) 0) 68 true) (.node 874 (sourceLit (List.headD (raw_ints% [1727815382643130058568573005803061107220235]) 0) 29 false) .empty .empty) (.node 876 (sourceLit (List.headD (raw_ints% [19918594674139450718894351923738905568718715]) 0) 25 true) .empty .empty)))

#time def treeG_J018_part113 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [46580078521832742091252118616675]) 0) 63 false) (.node 879 (sourceLit (List.headD (raw_ints% [14114614536665960082309801345]) 0) 72 true) (.node 878 (sourceLit (List.headD (raw_ints% [14401998933073690712877377341244573615988045]) 0) 24 false) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [163614933613881816901408829590267888573515]) 0) 31 true) .empty .empty)) (.node 912 (sourceLit (List.headD (raw_ints% [13493734518321017243448935310075]) 0) 66 true) (.node 911 (sourceLit (List.headD (raw_ints% [1917036927747283165511849267538229708929885]) 0) 29 false) .empty .empty) (.node 913 (sourceLit (List.headD (raw_ints% [7045415814289198073598981204922846090806705]) 0) 28 true) .empty .empty)))

#time def treeG_J018_part114 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [127034423680076249610640933335]) 0) 71 false) treeG_J018_part112 treeG_J018_part113)

#time def treeG_J018_part115 : IntSourceTree :=
  (.node 868 (sourceLit (List.headD (raw_ints% [12953342288994525768858562857656945223675]) 0) 33 true) treeG_J018_part111 treeG_J018_part114)

#time def treeG_J018_part116 : IntSourceTree :=
  (.node 919 (sourceLit (List.headD (raw_ints% [236514895480310894047101174140036747573237055]) 0) 21 false) (.node 917 (sourceLit (List.headD (raw_ints% [173360191728830377599762865534280825402242935]) 0) 23 true) (.node 916 (sourceLit (List.headD (raw_ints% [2173684778949980941077797233935]) 0) 69 true) (.node 915 (sourceLit (List.headD (raw_ints% [128797581497623727084162474653011489455700945]) 0) 24 false) .empty .empty) .empty) (.node 918 (sourceLit (List.headD (raw_ints% [268183339788392637479588897535]) 0) 71 false) .empty .empty)) (.node 951 (sourceLit (List.headD (raw_ints% [523138607077324285383960102375]) 0) 71 false) (.node 950 (sourceLit (List.headD (raw_ints% [62377998012155147348945615063456612160045]) 0) 34 true) .empty .empty) (.node 952 (sourceLit (List.headD (raw_ints% [653524075859176136845665647054673061331295]) 0) 32 false) .empty .empty)))

#time def treeG_J018_part117 : IntSourceTree :=
  (.node 957 (sourceLit (List.headD (raw_ints% [2427753626310133440299079100605]) 0) 70 true) (.node 955 (sourceLit (List.headD (raw_ints% [2935897099844710608508769682495]) 0) 70 false) (.node 954 (sourceLit (List.headD (raw_ints% [2193307799233082033041888552681476799506735]) 0) 31 true) .empty .empty) (.node 956 (sourceLit (List.headD (raw_ints% [37179044042940794450764206644187598756104915]) 0) 27 false) .empty .empty)) (.node 959 (sourceLit (List.headD (raw_ints% [2205452768164520293452333585]) 0) 79 false) (.node 958 (sourceLit (List.headD (raw_ints% [46940547665476017078160060718881349754557745]) 0) 26 true) .empty .empty) (.node 993 (sourceLit (List.headD (raw_ints% [27958186241782834452660281910672384053408145]) 0) 28 false) .empty .empty)))

#time def treeG_J018_part118 : IntSourceTree :=
  (.node 953 (sourceLit (List.headD (raw_ints% [8772359380406177101557669969375]) 0) 68 true) treeG_J018_part116 treeG_J018_part117)

#time def treeG_J018_part119 : IntSourceTree :=
  (.node 999 (sourceLit (List.headD (raw_ints% [3240709946070775987049345060148443131864932735]) 0) 21 true) (.node 997 (sourceLit (List.headD (raw_ints% [1363089601102935800024217478148283985597600215]) 0) 23 false) (.node 996 (sourceLit (List.headD (raw_ints% [13917273178328823375112875963915]) 0) 69 false) (.node 995 (sourceLit (List.headD (raw_ints% [690284378101292727542885944139469550129425105]) 0) 24 true) .empty .empty) .empty) (.node 998 (sourceLit (List.headD (raw_ints% [673984241524631519444666999535]) 0) 73 true) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [56642884087830714568750185078645]) 0) 68 true) (.node 1034 (sourceLit (List.headD (raw_ints% [36731417438715162584827836121398291251435085]) 0) 29 false) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [839000554273055905345942770716219945153844765]) 0) 25 true) .empty .empty)))

#time def treeG_J018_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [551251228641871390186430164395]) 0) 76 true) (.node 1039 (sourceLit (List.headD (raw_ints% [744558730105896168835141674255]) 0) 74 true) (.node 1038 (sourceLit (List.headD (raw_ints% [1550851791764839868336857721023809384615831195]) 0) 24 false) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [3041095094179063132971867455908960190221270545]) 0) 24 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [4760240942684370723297655765665]) 0) 73 false) (.node 1077 (sourceLit (List.headD (raw_ints% [8075094035287383042791759643878043546828358335]) 0) 23 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [28054338614308213880439068596529393285718231855]) 0) 21 false) .empty .empty)))

#time def treeG_J018_part121 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [2043128350579869601926494383065]) 0) 73 false) treeG_J018_part119 treeG_J018_part120)

#time def treeG_J018_part122 : IntSourceTree :=
  (.node 994 (sourceLit (List.headD (raw_ints% [44899295688451872134715106348665]) 0) 67 true) treeG_J018_part118 treeG_J018_part121)

#time def treeG_J018_part123 : IntSourceTree :=
  (.node 914 (sourceLit (List.headD (raw_ints% [9809858166827163728484426471165]) 0) 67 false) treeG_J018_part115 treeG_J018_part122)

#time def treeG_J018_part124 : IntSourceTree :=
  (.node 796 (sourceLit (List.headD (raw_ints% [850598832838023691560274821061663487556405]) 0) 26 false) treeG_J018_part108 treeG_J018_part123)

#time def treeG_J018_part125 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [395181266866791468113276687175]) 0) 63 true) treeG_J018_part093 treeG_J018_part124)

#time def treeG_J018_part126 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [324487190431158565556746913516775]) 0) 40 true) treeG_J018_part062 treeG_J018_part125)

#time def treeG_J018 : IntSourceTree := treeG_J018_part126

#time def treeG_J019_part000 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [56566946197449035575855924725]) 0) 47 false) (.node 8 (sourceLit (List.headD (raw_ints% [116373571101001340402752549125]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [664507599790418680345445971575]) 0) 41 false) (.node 6 (sourceLit (List.headD (raw_ints% [962368926858033459606360048375]) 0) 43 false) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 44 false) .empty .empty)) (.node 12 (sourceLit (List.headD (raw_ints% [13796238303230921470011189825]) 0) 49 false) (.node 11 (sourceLit (List.headD (raw_ints% [16530039795781559212573282875]) 0) 45 true) .empty .empty) (.node 13 (sourceLit (List.headD (raw_ints% [14383281380744993081070259125]) 0) 47 true) .empty .empty)))

#time def treeG_J019_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [2702972835149660143674350175]) 0) 53 true) (.node 17 (sourceLit (List.headD (raw_ints% [1846212236931446873092600425]) 0) 52 true) (.node 16 (sourceLit (List.headD (raw_ints% [413349411421067805982423125]) 0) 54 false) (.node 15 (sourceLit (List.headD (raw_ints% [14872081758322549677166332225]) 0) 48 true) .empty .empty) .empty) (.node 18 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 55 false) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 55 false) (.node 20 (sourceLit (List.headD (raw_ints% [72774449914858835512296786356475]) 0) 39 true) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [60109338058130529143685007796475]) 0) 38 true) .empty .empty)))

#time def treeG_J019_part002 : IntSourceTree :=
  (.node 14 (sourceLit (List.headD (raw_ints% [6747365483160630476563990575]) 0) 50 false) treeG_J019_part000 treeG_J019_part001)

#time def treeG_J019_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [1424878941929531466351626556332625]) 0) 32 true) (.node 26 (sourceLit (List.headD (raw_ints% [229152169887854934919363627551975]) 0) 35 true) (.node 25 (sourceLit (List.headD (raw_ints% [12295452847917477142379475]) 0) 59 false) (.node 24 (sourceLit (List.headD (raw_ints% [156099104535433088291102055709425]) 0) 36 true) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [6061702266383006140808625]) 0) 60 false) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [2287970237597698091220529047033285]) 0) 31 true) (.node 29 (sourceLit (List.headD (raw_ints% [1495382901114067105901475]) 0) 62 false) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [738310666906545497669775]) 0) 63 false) .empty .empty)))

#time def treeG_J019_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [166372029758922930955081198488870225]) 0) 24 true) (.node 34 (sourceLit (List.headD (raw_ints% [12437297675003738591330629687274655]) 0) 28 true) (.node 33 (sourceLit (List.headD (raw_ints% [22796731777394918849175]) 0) 68 false) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [11268487371388073512665]) 0) 69 false) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [279339471313723214329658269312419225]) 0) 23 true) (.node 37 (sourceLit (List.headD (raw_ints% [2786411480825734442205]) 0) 71 false) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [1378642738986775271205]) 0) 72 false) .empty .empty)))

#time def treeG_J019_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [7496282727507284781101943857298045]) 0) 29 true) treeG_J019_part003 treeG_J019_part004)

#time def treeG_J019_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [99848039641972223263286625]) 0) 56 false) treeG_J019_part002 treeG_J019_part005)

#time def treeG_J019_part007 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [16530039795781559212573282875]) 0) 46 true) (.node 50 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 45 false) (.node 49 (sourceLit (List.headD (raw_ints% [116373571101001340402752549125]) 0) 47 false) (.node 48 (sourceLit (List.headD (raw_ints% [664507599790418680345445971575]) 0) 42 false) .empty .empty) .empty) (.node 51 (sourceLit (List.headD (raw_ints% [56566946197449035575855924725]) 0) 48 false) .empty .empty)) (.node 54 (sourceLit (List.headD (raw_ints% [14383281380744993081070259125]) 0) 48 true) (.node 53 (sourceLit (List.headD (raw_ints% [13796238303230921470011189825]) 0) 50 false) .empty .empty) (.node 55 (sourceLit (List.headD (raw_ints% [6747365483160630476563990575]) 0) 51 false) .empty .empty)))

#time def treeG_J019_part008 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [2702972835149660143674350175]) 0) 54 true) (.node 58 (sourceLit (List.headD (raw_ints% [1846212236931446873092600425]) 0) 53 true) (.node 57 (sourceLit (List.headD (raw_ints% [413349411421067805982423125]) 0) 55 false) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 56 false) .empty .empty)) (.node 62 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 56 false) (.node 61 (sourceLit (List.headD (raw_ints% [72774449914858835512296786356475]) 0) 40 true) .empty .empty) (.node 63 (sourceLit (List.headD (raw_ints% [60109338058130529143685007796475]) 0) 39 true) .empty .empty)))

#time def treeG_J019_part009 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [14872081758322549677166332225]) 0) 49 true) treeG_J019_part007 treeG_J019_part008)

#time def treeG_J019_part010 : IntSourceTree :=
  (.node 69 (sourceLit (List.headD (raw_ints% [1424878941929531466351626556332625]) 0) 33 true) (.node 67 (sourceLit (List.headD (raw_ints% [229152169887854934919363627551975]) 0) 36 true) (.node 66 (sourceLit (List.headD (raw_ints% [12295452847917477142379475]) 0) 60 false) (.node 65 (sourceLit (List.headD (raw_ints% [156099104535433088291102055709425]) 0) 37 true) .empty .empty) .empty) (.node 68 (sourceLit (List.headD (raw_ints% [6061702266383006140808625]) 0) 61 false) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [2287970237597698091220529047033285]) 0) 32 true) (.node 70 (sourceLit (List.headD (raw_ints% [1495382901114067105901475]) 0) 63 false) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [738310666906545497669775]) 0) 64 false) .empty .empty)))

#time def treeG_J019_part011 : IntSourceTree :=
  (.node 77 (sourceLit (List.headD (raw_ints% [166372029758922930955081198488870225]) 0) 25 true) (.node 75 (sourceLit (List.headD (raw_ints% [12437297675003738591330629687274655]) 0) 29 true) (.node 74 (sourceLit (List.headD (raw_ints% [22796731777394918849175]) 0) 69 false) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [11268487371388073512665]) 0) 70 false) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [279339471313723214329658269312419225]) 0) 24 true) (.node 78 (sourceLit (List.headD (raw_ints% [2786411480825734442205]) 0) 72 false) .empty .empty) (.node 88 (sourceLit (List.headD (raw_ints% [729621784656030778800854950125]) 0) 45 false) .empty .empty)))

#time def treeG_J019_part012 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [7496282727507284781101943857298045]) 0) 30 true) treeG_J019_part010 treeG_J019_part011)

#time def treeG_J019_part013 : IntSourceTree :=
  (.node 64 (sourceLit (List.headD (raw_ints% [99848039641972223263286625]) 0) 57 false) treeG_J019_part009 treeG_J019_part012)

#time def treeG_J019_part014 : IntSourceTree :=
  (.node 47 (sourceLit (List.headD (raw_ints% [962368926858033459606360048375]) 0) 44 false) treeG_J019_part006 treeG_J019_part013)

#time def treeG_J019_part015 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [20845111123301212463458389075]) 0) 50 false) (.node 92 (sourceLit (List.headD (raw_ints% [10692676973554528526461183725]) 0) 51 false) (.node 91 (sourceLit (List.headD (raw_ints% [76038183060595172377837101225]) 0) 45 false) (.node 90 (sourceLit (List.headD (raw_ints% [176180196004553645229649173525]) 0) 47 false) .empty .empty) .empty) (.node 93 (sourceLit (List.headD (raw_ints% [1073379207518283065751511875]) 0) 48 true) .empty .empty)) (.node 96 (sourceLit (List.headD (raw_ints% [5093967837476359252634298075]) 0) 52 false) (.node 95 (sourceLit (List.headD (raw_ints% [13894481003167436484974186025]) 0) 48 true) .empty .empty) (.node 97 (sourceLit (List.headD (raw_ints% [7487232810596762184795930525]) 0) 50 true) .empty .empty)))

#time def treeG_J019_part016 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [305985927935076168064910625]) 0) 56 false) (.node 101 (sourceLit (List.headD (raw_ints% [90809056841818260604326525]) 0) 60 true) (.node 100 (sourceLit (List.headD (raw_ints% [125967919713117722260466256308475]) 0) 39 false) (.node 99 (sourceLit (List.headD (raw_ints% [989451638713233602510850675]) 0) 53 true) .empty .empty) .empty) (.node 102 (sourceLit (List.headD (raw_ints% [522086261260740154954689283055325]) 0) 38 true) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [75257133946137268978527675]) 0) 58 false) (.node 104 (sourceLit (List.headD (raw_ints% [805650304394655378007858069034175]) 0) 36 true) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [1019640666395609771409452818123425]) 0) 35 true) .empty .empty)))

#time def treeG_J019_part017 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [623781839053611416300747625]) 0) 55 false) treeG_J019_part015 treeG_J019_part016)

#time def treeG_J019_part018 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [29111241074055884678426520895234515]) 0) 29 true) (.node 110 (sourceLit (List.headD (raw_ints% [9111061297838553639592483403627715]) 0) 31 true) (.node 109 (sourceLit (List.headD (raw_ints% [2283159682634469517453575]) 0) 63 false) (.node 108 (sourceLit (List.headD (raw_ints% [5907990494481826451068009525330575]) 0) 32 true) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [2252455135321588714133175]) 0) 63 false) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [47532964145054539657484921171109705]) 0) 28 true) (.node 113 (sourceLit (List.headD (raw_ints% [555936812687386146876375]) 0) 65 false) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [34324976183401764185685]) 0) 69 false) .empty .empty)))

#time def treeG_J019_part019 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [496874642454028097995349851875]) 0) 46 false) (.node 118 (sourceLit (List.headD (raw_ints% [1051636766757660233310991318598542575]) 0) 23 true) (.node 117 (sourceLit (List.headD (raw_ints% [2120518972640584767615]) 0) 73 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [4194180222664693613205]) 0) 72 false) .empty .empty)) (.node 131 (sourceLit (List.headD (raw_ints% [3737914056472019051681039025]) 0) 53 false) (.node 130 (sourceLit (List.headD (raw_ints% [545491313260791454014918334875]) 0) 44 false) .empty .empty) (.node 132 (sourceLit (List.headD (raw_ints% [23142055714094182897602596025]) 0) 48 false) .empty .empty)))

#time def treeG_J019_part020 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [629615021441316338890079101496707695]) 0) 24 true) treeG_J019_part018 treeG_J019_part019)

#time def treeG_J019_part021 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [18529203429451948143950325]) 0) 60 false) treeG_J019_part017 treeG_J019_part020)

#time def treeG_J019_part022 : IntSourceTree :=
  (.node 138 (sourceLit (List.headD (raw_ints% [102383862870974692425528825]) 0) 51 true) (.node 136 (sourceLit (List.headD (raw_ints% [122200094394389149024018275]) 0) 52 false) (.node 135 (sourceLit (List.headD (raw_ints% [3524436410035145496723599625]) 0) 53 false) (.node 134 (sourceLit (List.headD (raw_ints% [12236522965708426949567235375]) 0) 48 false) .empty .empty) .empty) (.node 137 (sourceLit (List.headD (raw_ints% [3440570191792088028704605575]) 0) 53 false) .empty .empty)) (.node 140 (sourceLit (List.headD (raw_ints% [428380299109106635290874875]) 0) 56 false) (.node 139 (sourceLit (List.headD (raw_ints% [52608106908135902579581125]) 0) 59 false) .empty .empty) (.node 141 (sourceLit (List.headD (raw_ints% [99371184813988278886381521332475]) 0) 41 false) .empty .empty)))

#time def treeG_J019_part023 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [50666228250302314693768725]) 0) 59 false) (.node 144 (sourceLit (List.headD (raw_ints% [3220904504579749137525375]) 0) 63 false) (.node 143 (sourceLit (List.headD (raw_ints% [230988461601304812905502137629425]) 0) 40 true) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [324775599929611144858378006662375]) 0) 38 true) .empty .empty)) (.node 148 (sourceLit (List.headD (raw_ints% [3116875290767235500785425]) 0) 63 false) (.node 147 (sourceLit (List.headD (raw_ints% [395244248253877418245044595285725]) 0) 37 true) .empty .empty) (.node 149 (sourceLit (List.headD (raw_ints% [2241555776276147492358191484498975]) 0) 34 true) .empty .empty)))

#time def treeG_J019_part024 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [3108806802726708535002547425]) 0) 56 true) treeG_J019_part022 treeG_J019_part023)

#time def treeG_J019_part025 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [17547833235025400533077145741917525]) 0) 30 true) (.node 153 (sourceLit (List.headD (raw_ints% [10807479173274299948662288518968235]) 0) 31 true) (.node 152 (sourceLit (List.headD (raw_ints% [189268058551880402057925]) 0) 67 false) (.node 151 (sourceLit (List.headD (raw_ints% [3411545530120427774185977178297215]) 0) 33 true) .empty .empty) .empty) (.node 154 (sourceLit (List.headD (raw_ints% [373562958468226796082975]) 0) 66 false) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [231621495841196703967498951503918735]) 0) 26 true) (.node 156 (sourceLit (List.headD (raw_ints% [5764122203003422668255]) 0) 72 false) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [5695664409736604628255]) 0) 72 false) .empty .empty)))

#time def treeG_J019_part026 : IntSourceTree :=
  (.node 173 (sourceLit (List.headD (raw_ints% [47357490635706648860956703925]) 0) 48 false) (.node 171 (sourceLit (List.headD (raw_ints% [234726565100098140818540616825]) 0) 46 false) (.node 170 (sourceLit (List.headD (raw_ints% [160347223224737226382850339175]) 0) 48 false) .empty .empty) (.node 172 (sourceLit (List.headD (raw_ints% [19210635478221623886987128475]) 0) 51 false) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [38367526934584290384108656775]) 0) 48 false) (.node 174 (sourceLit (List.headD (raw_ints% [37103828058673172808208701075]) 0) 50 false) .empty .empty) (.node 176 (sourceLit (List.headD (raw_ints% [9003777802664222734260100425]) 0) 52 false) .empty .empty)))

#time def treeG_J019_part027 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [386148647721968509490666524643061675]) 0) 25 true) treeG_J019_part025 treeG_J019_part026)

#time def treeG_J019_part028 : IntSourceTree :=
  (.node 150 (sourceLit (List.headD (raw_ints% [3070936464154871929005675]) 0) 63 false) treeG_J019_part024 treeG_J019_part027)

#time def treeG_J019_part029 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [28974469590987192635833545075]) 0) 50 false) treeG_J019_part021 treeG_J019_part028)

#time def treeG_J019_part030 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [604999456525605067180182153225]) 0) 43 false) treeG_J019_part014 treeG_J019_part029)

#time def treeG_J019_part031 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [2112025218284552617136793624374925]) 0) 38 false) (.node 180 (sourceLit (List.headD (raw_ints% [15640723094506697893892540852475]) 0) 39 true) (.node 179 (sourceLit (List.headD (raw_ints% [1876519414555492512596172525]) 0) 52 false) (.node 178 (sourceLit (List.headD (raw_ints% [2193006513684865196103110325]) 0) 54 false) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [1154852753843652720125487075]) 0) 57 false) .empty .empty)) (.node 184 (sourceLit (List.headD (raw_ints% [6585980466847098634968210335107425]) 0) 36 true) (.node 183 (sourceLit (List.headD (raw_ints% [6523599533388493238070005475]) 0) 56 true) .empty .empty) (.node 185 (sourceLit (List.headD (raw_ints% [130880754346966675823096325]) 0) 58 false) .empty .empty)))

#time def treeG_J019_part032 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [3889417792988155143878175]) 0) 63 false) (.node 189 (sourceLit (List.headD (raw_ints% [3950590898900001484117275]) 0) 63 false) (.node 188 (sourceLit (List.headD (raw_ints% [19387641393766328316614844572955825]) 0) 32 true) (.node 187 (sourceLit (List.headD (raw_ints% [1004282025651573954681825]) 0) 65 false) .empty .empty) .empty) (.node 190 (sourceLit (List.headD (raw_ints% [26753831122579806238138580348355885]) 0) 31 true) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [958207655727657069587025]) 0) 65 false) (.node 192 (sourceLit (List.headD (raw_ints% [80058215889797804095524748810276365]) 0) 29 true) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [125386702627334259521111695132382055]) 0) 28 true) .empty .empty)))

#time def treeG_J019_part033 : IntSourceTree :=
  (.node 186 (sourceLit (List.headD (raw_ints% [4176768932478168546324595288474575]) 0) 35 true) treeG_J019_part031 treeG_J019_part032)

#time def treeG_J019_part034 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [100540598321184921555953714775]) 0) 49 false) (.node 198 (sourceLit (List.headD (raw_ints% [2654307166701487030168991905464157185]) 0) 23 true) (.node 197 (sourceLit (List.headD (raw_ints% [113862600948838684395]) 0) 78 false) (.node 196 (sourceLit (List.headD (raw_ints% [1616507632641934929343795553468735505]) 0) 24 true) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [7197148596808515643305]) 0) 72 false) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [47868072321899302912114968825]) 0) 50 false) (.node 212 (sourceLit (List.headD (raw_ints% [188442453671909775023335424775]) 0) 47 false) .empty .empty) (.node 214 (sourceLit (List.headD (raw_ints% [82478458305704870772346172475]) 0) 48 false) .empty .empty)))

#time def treeG_J019_part035 : IntSourceTree :=
  (.node 219 (sourceLit (List.headD (raw_ints% [1351276803154690754829812325]) 0) 55 false) (.node 217 (sourceLit (List.headD (raw_ints% [2781603805436067352777747425]) 0) 54 false) (.node 216 (sourceLit (List.headD (raw_ints% [37389926179429177191916510575]) 0) 49 false) .empty .empty) (.node 218 (sourceLit (List.headD (raw_ints% [4283608714311425034706802775]) 0) 52 false) .empty .empty)) (.node 221 (sourceLit (List.headD (raw_ints% [214383092722483255666655583517425]) 0) 40 true) (.node 220 (sourceLit (List.headD (raw_ints% [1550522978317360569730826475]) 0) 53 true) .empty .empty) (.node 222 (sourceLit (List.headD (raw_ints% [7728217818101319415504495725]) 0) 56 false) .empty .empty)))

#time def treeG_J019_part036 : IntSourceTree :=
  (.node 215 (sourceLit (List.headD (raw_ints% [23006082418532590821314302575]) 0) 51 false) treeG_J019_part034 treeG_J019_part035)

#time def treeG_J019_part037 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [236263053734619739340235]) 0) 67 false) treeG_J019_part033 treeG_J019_part036)

#time def treeG_J019_part038 : IntSourceTree :=
  (.node 228 (sourceLit (List.headD (raw_ints% [4917380914445356136669175]) 0) 63 false) (.node 226 (sourceLit (List.headD (raw_ints% [5013407881041522570582975]) 0) 63 false) (.node 225 (sourceLit (List.headD (raw_ints% [5936429266987876345251454321782675]) 0) 37 true) (.node 224 (sourceLit (List.headD (raw_ints% [6729737421681597182871629475]) 0) 57 true) .empty .empty) .empty) (.node 227 (sourceLit (List.headD (raw_ints% [3386280435970413709834506097903125]) 0) 36 true) .empty .empty)) (.node 230 (sourceLit (List.headD (raw_ints% [4830245333645131039228875]) 0) 63 false) (.node 229 (sourceLit (List.headD (raw_ints% [14904529841214033331898461603957875]) 0) 33 true) .empty .empty) (.node 231 (sourceLit (List.headD (raw_ints% [19930740062338950689766625991761455]) 0) 32 true) .empty .empty)))

#time def treeG_J019_part039 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [144037098486564976648155]) 0) 68 false) (.node 234 (sourceLit (List.headD (raw_ints% [292322348629715136752025]) 0) 67 false) (.node 233 (sourceLit (List.headD (raw_ints% [58443257543249204198200171772339895]) 0) 30 true) .empty .empty) (.node 235 (sourceLit (List.headD (raw_ints% [90291036157283458454957403648547005]) 0) 29 true) .empty .empty)) (.node 238 (sourceLit (List.headD (raw_ints% [8878748511714746974305]) 0) 72 false) (.node 237 (sourceLit (List.headD (raw_ints% [1153264640959541521408797650460898035]) 0) 25 true) .empty .empty) (.node 239 (sourceLit (List.headD (raw_ints% [1882009871257550011187658856178033835]) 0) 24 true) .empty .empty)))

#time def treeG_J019_part040 : IntSourceTree :=
  (.node 232 (sourceLit (List.headD (raw_ints% [2375273324573111927414775]) 0) 64 false) treeG_J019_part038 treeG_J019_part039)

#time def treeG_J019_part041 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [14462546306838650907464216925]) 0) 51 false) (.node 255 (sourceLit (List.headD (raw_ints% [126589389676825451160583688175]) 0) 48 false) (.node 254 (sourceLit (List.headD (raw_ints% [58632316585125433016021236575]) 0) 50 false) (.node 253 (sourceLit (List.headD (raw_ints% [70542481518101563081189360425]) 0) 49 false) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [7001152307934184043527101075]) 0) 53 false) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [6690698014067357556817433025]) 0) 52 false) (.node 258 (sourceLit (List.headD (raw_ints% [3370201097187269509452384525]) 0) 54 false) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [192755276237598324510945701914875]) 0) 39 false) .empty .empty)))

#time def treeG_J019_part042 : IntSourceTree :=
  (.node 265 (sourceLit (List.headD (raw_ints% [857577272003570482336840725]) 0) 61 true) (.node 263 (sourceLit (List.headD (raw_ints% [21980035169591132069078996925]) 0) 56 false) (.node 262 (sourceLit (List.headD (raw_ints% [3827089960064418662470038292514325]) 0) 38 true) .empty .empty) (.node 264 (sourceLit (List.headD (raw_ints% [47770014730641694522132976729247825]) 0) 36 false) .empty .empty)) (.node 267 (sourceLit (List.headD (raw_ints% [3004843829738374661219325]) 0) 64 false) (.node 266 (sourceLit (List.headD (raw_ints% [43314665203424842215687039285786825]) 0) 35 true) .empty .empty) (.node 268 (sourceLit (List.headD (raw_ints% [88973332557286910398089350559944175]) 0) 32 true) .empty .empty)))

#time def treeG_J019_part043 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [10789345009066582330734723075]) 0) 54 true) treeG_J019_part041 treeG_J019_part042)

#time def treeG_J019_part044 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [62119327364741673781979457825]) 0) 50 false) treeG_J019_part040 treeG_J019_part043)

#time def treeG_J019_part045 : IntSourceTree :=
  (.node 223 (sourceLit (List.headD (raw_ints% [2574002141487162242947797899633775]) 0) 39 false) treeG_J019_part037 treeG_J019_part044)

#time def treeG_J019_part046 : IntSourceTree :=
  (.node 274 (sourceLit (List.headD (raw_ints% [342159357718659374064489679046337105]) 0) 28 true) (.node 272 (sourceLit (List.headD (raw_ints% [238833625107625406940741267057906915]) 0) 29 true) (.node 271 (sourceLit (List.headD (raw_ints% [5771072874302106934579575]) 0) 63 false) (.node 270 (sourceLit (List.headD (raw_ints% [92482407607132460417049112483307115]) 0) 31 true) .empty .empty) .empty) (.node 273 (sourceLit (List.headD (raw_ints% [708532834422727428913875]) 0) 66 false) .empty .empty)) (.node 276 (sourceLit (List.headD (raw_ints% [4162118681424206411773478280038272815]) 0) 24 true) (.node 275 (sourceLit (List.headD (raw_ints% [348381643524810534163815]) 0) 67 false) .empty .empty) (.node 277 (sourceLit (List.headD (raw_ints% [85739446800759570237915]) 0) 69 false) .empty .empty)))

#time def treeG_J019_part047 : IntSourceTree :=
  (.node 296 (sourceLit (List.headD (raw_ints% [696870808573408390380212325]) 0) 56 false) (.node 294 (sourceLit (List.headD (raw_ints% [199691467766701381552411269225]) 0) 48 false) (.node 293 (sourceLit (List.headD (raw_ints% [76370582407584044651843946825]) 0) 50 false) (.node 279 (sourceLit (List.headD (raw_ints% [10560348426620978305305]) 0) 72 false) .empty .empty) .empty) (.node 295 (sourceLit (List.headD (raw_ints% [2226639635412052637169183375]) 0) 55 false) .empty .empty)) (.node 298 (sourceLit (List.headD (raw_ints% [5089468796263612936378707075]) 0) 53 false) (.node 297 (sourceLit (List.headD (raw_ints% [2109774251249058345374676825]) 0) 55 false) .empty .empty) (.node 299 (sourceLit (List.headD (raw_ints% [252365536754072344327821525]) 0) 58 false) .empty .empty)))

#time def treeG_J019_part048 : IntSourceTree :=
  (.node 278 (sourceLit (List.headD (raw_ints% [6571809960974845141101389298223027095]) 0) 23 true) treeG_J019_part046 treeG_J019_part047)

#time def treeG_J019_part049 : IntSourceTree :=
  (.node 305 (sourceLit (List.headD (raw_ints% [13426610999407392716846107762757625]) 0) 39 false) (.node 303 (sourceLit (List.headD (raw_ints% [1600273025387895226354459048037025]) 0) 41 true) (.node 302 (sourceLit (List.headD (raw_ints% [26245780645269221161743714525]) 0) 55 true) (.node 301 (sourceLit (List.headD (raw_ints% [101784592240020395044400321358075]) 0) 42 false) .empty .empty) .empty) (.node 304 (sourceLit (List.headD (raw_ints% [897180393477272789123457075]) 0) 62 false) .empty .empty)) (.node 307 (sourceLit (List.headD (raw_ints% [9982096191863607126463133296970925]) 0) 38 true) (.node 306 (sourceLit (List.headD (raw_ints% [867604087765653527478006675]) 0) 62 true) .empty .empty) (.node 308 (sourceLit (List.headD (raw_ints% [7101994404508142508208125]) 0) 63 false) .empty .empty)))

#time def treeG_J019_part050 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [45097591891094050685635273821391755]) 0) 32 true) (.node 311 (sourceLit (List.headD (raw_ints% [18137916886198377431820621622886415]) 0) 34 true) (.node 310 (sourceLit (List.headD (raw_ints% [6938096526336290539213275]) 0) 63 false) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [26529683982257773493475]) 0) 71 false) .empty .empty)) (.node 315 (sourceLit (List.headD (raw_ints% [62967080390343978902383068849447525]) 0) 31 true) (.node 314 (sourceLit (List.headD (raw_ints% [208105242896506146080925]) 0) 68 false) .empty .empty) (.node 316 (sourceLit (List.headD (raw_ints% [51086136259561389378915]) 0) 70 false) .empty .empty)))

#time def treeG_J019_part051 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [18517200679018219266547722238996575]) 0) 35 true) treeG_J019_part049 treeG_J019_part050)

#time def treeG_J019_part052 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [2060305248096179531637064875]) 0) 55 false) treeG_J019_part048 treeG_J019_part051)

#time def treeG_J019_part053 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [10811964775362237053826365925]) 0) 53 false) (.node 334 (sourceLit (List.headD (raw_ints% [94108848230042656287666657075]) 0) 50 false) (.node 319 (sourceLit (List.headD (raw_ints% [1172450022429323782478432610511248315]) 0) 26 true) (.node 318 (sourceLit (List.headD (raw_ints% [50224452753900582340695]) 0) 70 false) .empty .empty) .empty) (.node 335 (sourceLit (List.headD (raw_ints% [272793545856577311944238850275]) 0) 48 false) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [5068895907808963872046322775]) 0) 54 false) (.node 337 (sourceLit (List.headD (raw_ints% [30137185441859486076869371875]) 0) 51 false) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [13667177170987094188697395275]) 0) 52 false) .empty .empty)))

#time def treeG_J019_part054 : IntSourceTree :=
  (.node 344 (sourceLit (List.headD (raw_ints% [150187488355466989008818355803617425]) 0) 36 true) (.node 342 (sourceLit (List.headD (raw_ints% [7084196911745071303890848575972725]) 0) 38 false) (.node 341 (sourceLit (List.headD (raw_ints% [19030566001451300457282982575]) 0) 54 false) .empty .empty) (.node 343 (sourceLit (List.headD (raw_ints% [24112907907430176615411355725]) 0) 57 true) .empty .empty)) (.node 346 (sourceLit (List.headD (raw_ints% [472966217184461409154762487694030825]) 0) 35 false) (.node 345 (sourceLit (List.headD (raw_ints% [4446298845912661638830669025]) 0) 61 false) .empty .empty) (.node 347 (sourceLit (List.headD (raw_ints% [873613775425130276800445325]) 0) 63 true) .empty .empty)))

#time def treeG_J019_part055 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [71869168829839838014944081483525]) 0) 39 false) treeG_J019_part053 treeG_J019_part054)

#time def treeG_J019_part056 : IntSourceTree :=
  (.node 353 (sourceLit (List.headD (raw_ints% [989366940441770074668525]) 0) 66 false) (.node 351 (sourceLit (List.headD (raw_ints% [8105120178370474143846975]) 0) 63 false) (.node 350 (sourceLit (List.headD (raw_ints% [500068014121450556112477999164583285]) 0) 31 true) (.node 349 (sourceLit (List.headD (raw_ints% [8319817879025574227195175]) 0) 63 false) .empty .empty) .empty) (.node 352 (sourceLit (List.headD (raw_ints% [921993055609070748695778516806823645]) 0) 29 true) .empty .empty)) (.node 355 (sourceLit (List.headD (raw_ints% [484039328061214050159885]) 0) 67 false) (.node 354 (sourceLit (List.headD (raw_ints% [1100963582796350247875839083238199055]) 0) 28 true) .empty .empty) (.node 356 (sourceLit (List.headD (raw_ints% [11957453898503852187236587345420293585]) 0) 24 true) .empty .empty)))

#time def treeG_J019_part057 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [183594082359181037975571672675]) 0) 49 false) (.node 359 (sourceLit (List.headD (raw_ints% [29103755900658625730085]) 0) 71 false) (.node 358 (sourceLit (List.headD (raw_ints% [17499022362742473981816055738395971145]) 0) 23 true) .empty .empty) (.node 375 (sourceLit (List.headD (raw_ints% [58482614063449814092959723075]) 0) 51 false) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [19958247849332260204111957725]) 0) 52 false) (.node 377 (sourceLit (List.headD (raw_ints% [6592416272864120363077012275]) 0) 54 false) .empty .empty) (.node 379 (sourceLit (List.headD (raw_ints% [3049971613776385117423750575]) 0) 55 false) .empty .empty)))

#time def treeG_J019_part058 : IntSourceTree :=
  (.node 357 (sourceLit (List.headD (raw_ints% [118605098237485987277745]) 0) 69 false) treeG_J019_part056 treeG_J019_part057)

#time def treeG_J019_part059 : IntSourceTree :=
  (.node 348 (sourceLit (List.headD (raw_ints% [1188734980001254801789191711452334225]) 0) 32 true) treeG_J019_part055 treeG_J019_part058)

#time def treeG_J019_part060 : IntSourceTree :=
  (.node 317 (sourceLit (List.headD (raw_ints% [752213510116166222591170157394343695]) 0) 27 true) treeG_J019_part052 treeG_J019_part059)

#time def treeG_J019_part061 : IntSourceTree :=
  (.node 269 (sourceLit (List.headD (raw_ints% [5884170929990710789221075]) 0) 63 false) treeG_J019_part045 treeG_J019_part060)

#time def treeG_J019_part062 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [8464833565751875376988076725]) 0) 50 false) treeG_J019_part030 treeG_J019_part061)

#time def treeG_J019_part063 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [203893932353096559876202786854647925]) 0) 37 true) (.node 383 (sourceLit (List.headD (raw_ints% [13485289013296652209308684768120825]) 0) 39 false) (.node 382 (sourceLit (List.headD (raw_ints% [11319086661680130404756674275]) 0) 57 false) (.node 381 (sourceLit (List.headD (raw_ints% [335269200130241742162657203948775]) 0) 40 true) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [38467794203066541241386668925]) 0) 58 true) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [512894601951915837660615020881914525]) 0) 36 false) (.node 386 (sourceLit (List.headD (raw_ints% [1328475733419578791577168925]) 0) 64 false) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [1754329545254768696109098775]) 0) 63 true) .empty .empty)))

#time def treeG_J019_part064 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [573156454648757782506675]) 0) 67 false) (.node 392 (sourceLit (List.headD (raw_ints% [4709320628641479136682175]) 0) 64 false) (.node 391 (sourceLit (List.headD (raw_ints% [427516346576657046385195512673037625]) 0) 32 true) (.node 390 (sourceLit (List.headD (raw_ints% [9701539231714857915177075]) 0) 63 false) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [741602688044694545953237421521256625]) 0) 30 true) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [279694783022968492644225]) 0) 68 false) (.node 395 (sourceLit (List.headD (raw_ints% [849095261234974332266306807840408955]) 0) 29 true) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [8948599858039187296871906715842918805]) 0) 25 true) .empty .empty)))

#time def treeG_J019_part065 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [1114666177285181924723000822496347925]) 0) 33 true) treeG_J019_part063 treeG_J019_part064)

#time def treeG_J019_part066 : IntSourceTree :=
  (.node 419 (sourceLit (List.headD (raw_ints% [26249318527677426219526520175]) 0) 52 false) (.node 417 (sourceLit (List.headD (raw_ints% [123319711475462065821832928925]) 0) 50 false) (.node 416 (sourceLit (List.headD (raw_ints% [36858684512725339985306991225]) 0) 52 false) (.node 399 (sourceLit (List.headD (raw_ints% [12809222273025178851902325296350977885]) 0) 24 true) .empty .empty) .empty) (.node 418 (sourceLit (List.headD (raw_ints% [8115936637919276854107701775]) 0) 54 false) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [850288113928057774695865425]) 0) 58 true) (.node 420 (sourceLit (List.headD (raw_ints% [327896710531058512096021753882875]) 0) 39 false) .empty .empty) (.node 422 (sourceLit (List.headD (raw_ints% [9766350512787005241192106207562925]) 0) 38 true) .empty .empty)))

#time def treeG_J019_part067 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [6187516709103445443109121025]) 0) 63 false) (.node 425 (sourceLit (List.headD (raw_ints% [56252989586717187796709345025]) 0) 59 true) (.node 424 (sourceLit (List.headD (raw_ints% [365952112568213424357757312093550625]) 0) 36 false) .empty .empty) (.node 426 (sourceLit (List.headD (raw_ints% [2104117676009233888164384782531214225]) 0) 35 true) .empty .empty)) (.node 429 (sourceLit (List.headD (raw_ints% [3516978908388562966445392725]) 0) 63 true) (.node 428 (sourceLit (List.headD (raw_ints% [17601362242462561606928872379673599025]) 0) 32 false) .empty .empty) (.node 430 (sourceLit (List.headD (raw_ints% [8417261404160004841671528580806200115]) 0) 31 true) .empty .empty)))

#time def treeG_J019_part068 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [46751081230790437424924704275]) 0) 57 false) treeG_J019_part066 treeG_J019_part067)

#time def treeG_J019_part069 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [34190322741792702468525]) 0) 71 false) treeG_J019_part065 treeG_J019_part068)

#time def treeG_J019_part070 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [42384642820534505077807048356365879535]) 0) 24 true) (.node 434 (sourceLit (List.headD (raw_ints% [4831857921561206119750060288931853945]) 0) 28 true) (.node 433 (sourceLit (List.headD (raw_ints% [2730586747757938987345125]) 0) 65 false) (.node 432 (sourceLit (List.headD (raw_ints% [5918268489617441993467349685961778355]) 0) 29 true) .empty .empty) .empty) (.node 435 (sourceLit (List.headD (raw_ints% [662273581236301514853465]) 0) 67 false) .empty .empty)) (.node 438 (sourceLit (List.headD (raw_ints% [54089776501571024393159197988347379295]) 0) 23 true) (.node 437 (sourceLit (List.headD (raw_ints% [10068105299092656585405]) 0) 73 false) .empty .empty) (.node 439 (sourceLit (List.headD (raw_ints% [39276889582926779206965]) 0) 71 false) .empty .empty)))

#time def treeG_J019_part071 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [331582955330650127129339478915825]) 0) 41 false) (.node 459 (sourceLit (List.headD (raw_ints% [158311407004465366771373475]) 0) 60 false) (.node 458 (sourceLit (List.headD (raw_ints% [83403215776797545413609013475]) 0) 51 false) .empty .empty) (.node 460 (sourceLit (List.headD (raw_ints% [1301460146817190634836086525]) 0) 57 false) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [11625819763041828725250395487841875]) 0) 40 true) (.node 462 (sourceLit (List.headD (raw_ints% [14720239117392361503540135975]) 0) 57 true) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [5326179714616061166644460825]) 0) 62 false) .empty .empty)))

#time def treeG_J019_part072 : IntSourceTree :=
  (.node 457 (sourceLit (List.headD (raw_ints% [23673851966997099259152966675]) 0) 53 false) treeG_J019_part070 treeG_J019_part071)

#time def treeG_J019_part073 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [7043659356008840790805962525]) 0) 63 true) (.node 468 (sourceLit (List.headD (raw_ints% [14129362963461659582327340825]) 0) 63 false) (.node 467 (sourceLit (List.headD (raw_ints% [1308506138980574862912499901706564375]) 0) 37 true) (.node 466 (sourceLit (List.headD (raw_ints% [77508601321430448461944047825]) 0) 60 true) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [9358014209873871765825936601084973475]) 0) 34 false) .empty .empty)) (.node 472 (sourceLit (List.headD (raw_ints% [823579707052220318728125]) 0) 67 false) (.node 471 (sourceLit (List.headD (raw_ints% [3994872528791673897643166534066581245]) 0) 33 true) .empty .empty) (.node 473 (sourceLit (List.headD (raw_ints% [2588332900786373723757056132220260865]) 0) 31 true) .empty .empty)))

#time def treeG_J019_part074 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [46354519650948550214715]) 0) 71 false) (.node 476 (sourceLit (List.headD (raw_ints% [47822349776666627776155]) 0) 71 false) (.node 475 (sourceLit (List.headD (raw_ints% [1991381330163115893741876740545722495]) 0) 30 true) .empty .empty) (.node 477 (sourceLit (List.headD (raw_ints% [16718021481247658890467570820261480365]) 0) 26 true) .empty .empty)) (.node 498 (sourceLit (List.headD (raw_ints% [3889478832269455601261316225]) 0) 56 false) (.node 479 (sourceLit (List.headD (raw_ints% [20640277114272922770628436345998200705]) 0) 25 true) .empty .empty) (.node 499 (sourceLit (List.headD (raw_ints% [14288474312280029798520623325]) 0) 54 false) .empty .empty)))

#time def treeG_J019_part075 : IntSourceTree :=
  (.node 474 (sourceLit (List.headD (raw_ints% [1584273838460423422331775]) 0) 66 false) treeG_J019_part073 treeG_J019_part074)

#time def treeG_J019_part076 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [284923022460654992116980049474099275]) 0) 38 false) treeG_J019_part072 treeG_J019_part075)

#time def treeG_J019_part077 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [11297958285059241686507175]) 0) 63 false) treeG_J019_part069 treeG_J019_part076)

#time def treeG_J019_part078 : IntSourceTree :=
  (.node 505 (sourceLit (List.headD (raw_ints% [141471865020574166463020718225]) 0) 59 false) (.node 503 (sourceLit (List.headD (raw_ints% [76191559465575160432004976225]) 0) 57 true) (.node 502 (sourceLit (List.headD (raw_ints% [15071677798077407275261537870216125]) 0) 38 false) (.node 501 (sourceLit (List.headD (raw_ints% [1075874130372624204765975975]) 0) 59 false) .empty .empty) .empty) (.node 504 (sourceLit (List.headD (raw_ints% [737978344985551943565769967704490625]) 0) 36 true) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [102258668157844230234380531925]) 0) 61 true) (.node 506 (sourceLit (List.headD (raw_ints% [6662886035379713762036065574116802625]) 0) 35 false) .empty .empty) (.node 508 (sourceLit (List.headD (raw_ints% [101345755137219352833328866088893719025]) 0) 32 true) .empty .empty)))

#time def treeG_J019_part079 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [36581468491020773460362837826592319895]) 0) 28 true) (.node 512 (sourceLit (List.headD (raw_ints% [121917652431716122731113979404168821485]) 0) 29 true) (.node 511 (sourceLit (List.headD (raw_ints% [14098616670302740823298432225]) 0) 63 true) (.node 510 (sourceLit (List.headD (raw_ints% [158145488762141953094886514198165775715]) 0) 31 false) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [3858050908659823562479875]) 0) 65 false) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [212512167440344329321153174433486599825]) 0) 24 true) (.node 515 (sourceLit (List.headD (raw_ints% [461000128612060953739155]) 0) 68 false) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [27686139178481314605345]) 0) 72 false) .empty .empty)))

#time def treeG_J019_part080 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [31775704835311882131100074375]) 0) 63 false) treeG_J019_part078 treeG_J019_part079)

#time def treeG_J019_part081 : IntSourceTree :=
  (.node 542 (sourceLit (List.headD (raw_ints% [23327232160373355141667943775]) 0) 57 false) (.node 540 (sourceLit (List.headD (raw_ints% [9082633725011267259176277225]) 0) 55 false) (.node 539 (sourceLit (List.headD (raw_ints% [2622987576233732667090328425]) 0) 57 false) (.node 519 (sourceLit (List.headD (raw_ints% [53432149718970321222465]) 0) 71 false) .empty .empty) .empty) (.node 541 (sourceLit (List.headD (raw_ints% [327056453547901660644061860028125]) 0) 40 true) .empty .empty)) (.node 544 (sourceLit (List.headD (raw_ints% [161410434899432139098316349425]) 0) 58 true) (.node 543 (sourceLit (List.headD (raw_ints% [38323317324161064725762328845899875]) 0) 39 false) .empty .empty) (.node 545 (sourceLit (List.headD (raw_ints% [1307824389906861927799730066652689175]) 0) 37 true) .empty .empty)))

#time def treeG_J019_part082 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [70595069026632605053006111275]) 0) 63 false) (.node 548 (sourceLit (List.headD (raw_ints% [130517394084767549399035213575]) 0) 62 true) (.node 547 (sourceLit (List.headD (raw_ints% [9279898313340863487861065377529931375]) 0) 36 false) .empty .empty) (.node 549 (sourceLit (List.headD (raw_ints% [120061783556967096364980739291063665975]) 0) 33 true) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [14105205307959158585848257225]) 0) 64 true) (.node 551 (sourceLit (List.headD (raw_ints% [166135233819725300890172847266298938205]) 0) 32 false) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [116740986630143375283599867139728299755]) 0) 30 true) .empty .empty)))

#time def treeG_J019_part083 : IntSourceTree :=
  (.node 546 (sourceLit (List.headD (raw_ints% [109490233171002307462482383025]) 0) 61 false) treeG_J019_part081 treeG_J019_part082)

#time def treeG_J019_part084 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [213398567198391517854321935135836306545]) 0) 23 true) treeG_J019_part080 treeG_J019_part083)

#time def treeG_J019_part085 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [172118012969845672313065062443839905135]) 0) 24 true) (.node 557 (sourceLit (List.headD (raw_ints% [179076124477849011540218032792963639095]) 0) 25 true) (.node 556 (sourceLit (List.headD (raw_ints% [269710729505394442634535]) 0) 69 false) (.node 555 (sourceLit (List.headD (raw_ints% [32598705830694541672879084345500874905]) 0) 29 true) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [64390037062976708206665]) 0) 71 false) .empty .empty)) (.node 581 (sourceLit (List.headD (raw_ints% [475640682030273621048469425]) 0) 56 false) (.node 580 (sourceLit (List.headD (raw_ints% [1039091453255032638948837011482875]) 0) 39 false) .empty .empty) (.node 582 (sourceLit (List.headD (raw_ints% [17688129426460620560414032750441125]) 0) 38 true) .empty .empty)))

#time def treeG_J019_part086 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [321239134499848845159345297975]) 0) 61 false) (.node 585 (sourceLit (List.headD (raw_ints% [151441149960003152780668533825]) 0) 60 true) (.node 584 (sourceLit (List.headD (raw_ints% [1351151422172128979177967229238888625]) 0) 36 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [17125481154634609184433906107338316025]) 0) 35 true) .empty .empty)) (.node 589 (sourceLit (List.headD (raw_ints% [81146549460039715765067643975]) 0) 64 true) (.node 588 (sourceLit (List.headD (raw_ints% [398302501164126984444882958169851523025]) 0) 32 false) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [1118639757217878724014732428526675103515]) 0) 31 true) .empty .empty)))

#time def treeG_J019_part087 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [122846023786321870715340863775]) 0) 57 false) treeG_J019_part085 treeG_J019_part086)

#time def treeG_J019_part088 : IntSourceTree :=
  (.node 596 (sourceLit (List.headD (raw_ints% [1873805005724106337743108223678569394095]) 0) 24 true) (.node 594 (sourceLit (List.headD (raw_ints% [897346424550126228808436099291234078145]) 0) 28 true) (.node 593 (sourceLit (List.headD (raw_ints% [3527265839716954602352684275]) 0) 67 true) (.node 592 (sourceLit (List.headD (raw_ints% [2780081393547320936973879535664951832765]) 0) 29 false) .empty .empty) .empty) (.node 595 (sourceLit (List.headD (raw_ints% [675888406487639116334895]) 0) 68 false) .empty .empty)) (.node 598 (sourceLit (List.headD (raw_ints% [1219210428624400574467422327207872806215]) 0) 23 true) (.node 597 (sourceLit (List.headD (raw_ints% [158966172791469184213155]) 0) 70 false) .empty .empty) (.node 599 (sourceLit (List.headD (raw_ints% [75347924406983095190865]) 0) 71 false) .empty .empty)))

#time def treeG_J019_part089 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [332371976509873863372212161986447225]) 0) 40 false) (.node 623 (sourceLit (List.headD (raw_ints% [7001430843827710660772045199542625]) 0) 42 true) (.node 622 (sourceLit (List.headD (raw_ints% [11425795739171540760309737175]) 0) 58 true) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [17766028667859625613353575825]) 0) 62 false) .empty .empty)) (.node 627 (sourceLit (List.headD (raw_ints% [3300672433496934084036871435608530925]) 0) 39 true) (.node 626 (sourceLit (List.headD (raw_ints% [130465691565502730121575458425]) 0) 62 true) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [225878264292308197279190255775]) 0) 63 false) .empty .empty)))

#time def treeG_J019_part090 : IntSourceTree :=
  (.node 621 (sourceLit (List.headD (raw_ints% [170768488350366787449112358938875]) 0) 43 false) treeG_J019_part088 treeG_J019_part089)

#time def treeG_J019_part091 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [155288754723567950929310654775]) 0) 63 false) treeG_J019_part087 treeG_J019_part090)

#time def treeG_J019_part092 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [568444267549850035037025]) 0) 68 false) treeG_J019_part084 treeG_J019_part091)

#time def treeG_J019_part093 : IntSourceTree :=
  (.node 500 (sourceLit (List.headD (raw_ints% [336109457113398593614617097803525]) 0) 39 false) treeG_J019_part077 treeG_J019_part092)

#time def treeG_J019_part094 : IntSourceTree :=
  (.node 634 (sourceLit (List.headD (raw_ints% [881958570996126113096930325]) 0) 70 true) (.node 632 (sourceLit (List.headD (raw_ints% [165423789093288192885897375]) 0) 74 false) (.node 631 (sourceLit (List.headD (raw_ints% [160596873879700503113113159474121755215]) 0) 35 true) (.node 630 (sourceLit (List.headD (raw_ints% [395181266866791468113276687175]) 0) 63 true) .empty .empty) .empty) (.node 633 (sourceLit (List.headD (raw_ints% [362102797522183039032184925350585016565]) 0) 33 false) .empty .empty)) (.node 636 (sourceLit (List.headD (raw_ints% [50772209622780584212545]) 0) 72 false) (.node 635 (sourceLit (List.headD (raw_ints% [108093464839928960891944626868216650405]) 0) 32 true) .empty .empty) (.node 637 (sourceLit (List.headD (raw_ints% [211841110155782165775361273860700719375]) 0) 28 true) .empty .empty)))

#time def treeG_J019_part095 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [38397287651266536440255484474470938425]) 0) 35 false) (.node 664 (sourceLit (List.headD (raw_ints% [2247334570182075943756789014780344625]) 0) 36 true) (.node 663 (sourceLit (List.headD (raw_ints% [168549206743008033756579812475]) 0) 57 true) (.node 639 (sourceLit (List.headD (raw_ints% [130886551956819362769294658095504112635]) 0) 27 true) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [293569379302880157687497140425]) 0) 60 false) .empty .empty)) (.node 668 (sourceLit (List.headD (raw_ints% [1243274644139342109958322045685635439825]) 0) 32 true) (.node 667 (sourceLit (List.headD (raw_ints% [843101900761859765645647131675]) 0) 61 true) .empty .empty) (.node 669 (sourceLit (List.headD (raw_ints% [153512406876173956522128949875]) 0) 65 false) .empty .empty)))

#time def treeG_J019_part096 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [47288067864246238003245]) 0) 72 false) treeG_J019_part094 treeG_J019_part095)

#time def treeG_J019_part097 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [7056344456375496543891777495]) 0) 68 true) (.node 673 (sourceLit (List.headD (raw_ints% [45875755847598731981142412275]) 0) 67 false) (.node 672 (sourceLit (List.headD (raw_ints% [23336481250148985335452363948352536500285]) 0) 29 true) (.node 671 (sourceLit (List.headD (raw_ints% [945651288457150887155864029125]) 0) 63 true) .empty .empty) .empty) (.node 674 (sourceLit (List.headD (raw_ints% [24071925465969840726868271321728675138305]) 0) 28 false) .empty .empty)) (.node 677 (sourceLit (List.headD (raw_ints% [247211504190775489487205]) 0) 70 false) (.node 676 (sourceLit (List.headD (raw_ints% [53470048992319521638932540732848355613265]) 0) 24 true) .empty .empty) (.node 678 (sourceLit (List.headD (raw_ints% [12338620621345658035155699199876973233785]) 0) 23 true) .empty .empty)))

#time def treeG_J019_part098 : IntSourceTree :=
  (.node 707 (sourceLit (List.headD (raw_ints% [64802667119242009112550455959339185825]) 0) 36 false) (.node 705 (sourceLit (List.headD (raw_ints% [4906310382261066850734486310671922425]) 0) 37 true) (.node 704 (sourceLit (List.headD (raw_ints% [452805665428762043570237025675]) 0) 58 true) .empty .empty) (.node 706 (sourceLit (List.headD (raw_ints% [554500762433885617930648057275]) 0) 61 false) .empty .empty)) (.node 709 (sourceLit (List.headD (raw_ints% [1761638928860436190768185743146550628825]) 0) 33 true) (.node 708 (sourceLit (List.headD (raw_ints% [1294858429346476160204027643225]) 0) 62 true) .empty .empty) (.node 710 (sourceLit (List.headD (raw_ints% [1623280521876183120290308286175]) 0) 63 false) .empty .empty)))

#time def treeG_J019_part099 : IntSourceTree :=
  (.node 679 (sourceLit (List.headD (raw_ints% [113804347050001856822115]) 0) 71 false) treeG_J019_part097 treeG_J019_part098)

#time def treeG_J019_part100 : IntSourceTree :=
  (.node 670 (sourceLit (List.headD (raw_ints% [5265554034986631370493642008213996615515]) 0) 31 false) treeG_J019_part096 treeG_J019_part099)

#time def treeG_J019_part101 : IntSourceTree :=
  (.node 716 (sourceLit (List.headD (raw_ints% [7056750634052478788565477855]) 0) 69 true) (.node 714 (sourceLit (List.headD (raw_ints% [49403590131583236433530133575]) 0) 68 false) (.node 713 (sourceLit (List.headD (raw_ints% [26233303630326449647709843351157216632805]) 0) 30 true) (.node 712 (sourceLit (List.headD (raw_ints% [1115045248488677996671022941125]) 0) 64 true) .empty .empty) .empty) (.node 715 (sourceLit (List.headD (raw_ints% [24936673184689272414003828336674408341545]) 0) 29 false) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [152635368462283013480715]) 0) 71 false) (.node 717 (sourceLit (List.headD (raw_ints% [51775320111073264312729650541962749858265]) 0) 25 true) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [11291528205691103133001341935112940332705]) 0) 24 true) .empty .empty)))

#time def treeG_J019_part102 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [1908908056851171986292543442725]) 0) 63 true) (.node 747 (sourceLit (List.headD (raw_ints% [1952103425629631001506943246225]) 0) 61 false) (.node 746 (sourceLit (List.headD (raw_ints% [77647770709355071246131374959846317825]) 0) 35 true) .empty .empty) (.node 748 (sourceLit (List.headD (raw_ints% [3316959991955086401559936636384489386225]) 0) 32 false) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [4192212332209517127736480601475]) 0) 63 false) (.node 750 (sourceLit (List.headD (raw_ints% [19358665465870120896639127953386401646115]) 0) 31 true) .empty .empty) (.node 752 (sourceLit (List.headD (raw_ints% [128141745666536751661829120492464067016045]) 0) 29 false) .empty .empty)))

#time def treeG_J019_part103 : IntSourceTree :=
  (.node 745 (sourceLit (List.headD (raw_ints% [1039944424034522358945231306525]) 0) 59 true) treeG_J019_part101 treeG_J019_part102)

#time def treeG_J019_part104 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [401863940267240456466681505135825025632335]) 0) 23 true) (.node 756 (sourceLit (List.headD (raw_ints% [1649417132812432956135177554280010489472145]) 0) 24 false) (.node 755 (sourceLit (List.headD (raw_ints% [105863524719541969410952044645]) 0) 68 false) (.node 754 (sourceLit (List.headD (raw_ints% [233938354508581437908547018130986408200745]) 0) 28 true) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [1764249461389167391013741265]) 0) 72 true) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [2148945948902293594806527421075]) 0) 60 true) (.node 759 (sourceLit (List.headD (raw_ints% [191466389874564170139315]) 0) 71 false) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [71225218914298540179340915459592751825]) 0) 37 true) .empty .empty)))

#time def treeG_J019_part105 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [663407197587274390550937942825]) 0) 67 false) (.node 790 (sourceLit (List.headD (raw_ints% [5441096635578527092875395171625]) 0) 63 true) (.node 789 (sourceLit (List.headD (raw_ints% [2539299460407761296164061189765520007525]) 0) 34 false) .empty .empty) (.node 791 (sourceLit (List.headD (raw_ints% [12954497245947178146018837618696686151675]) 0) 33 true) .empty .empty)) (.node 794 (sourceLit (List.headD (raw_ints% [1496162632405405870329713124525]) 0) 66 true) (.node 793 (sourceLit (List.headD (raw_ints% [77187524648431600654769481921810641824425]) 0) 31 false) .empty .empty) (.node 795 (sourceLit (List.headD (raw_ints% [129437513846635355161275423233830408271145]) 0) 30 true) .empty .empty)))

#time def treeG_J019_part106 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [1623480927488053580855485444725]) 0) 63 false) treeG_J019_part104 treeG_J019_part105)

#time def treeG_J019_part107 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [1298548271879072924595592590225]) 0) 65 true) treeG_J019_part103 treeG_J019_part106)

#time def treeG_J019_part108 : IntSourceTree :=
  (.node 711 (sourceLit (List.headD (raw_ints% [6550329026024235395398547284006970657235]) 0) 32 false) treeG_J019_part100 treeG_J019_part107)

#time def treeG_J019_part109 : IntSourceTree :=
  (.node 828 (sourceLit (List.headD (raw_ints% [7875374002470192973037755225798425503025]) 0) 32 true) (.node 799 (sourceLit (List.headD (raw_ints% [195286206030774676666840081600356042649815]) 0) 25 true) (.node 798 (sourceLit (List.headD (raw_ints% [7057150480925131847068445775]) 0) 71 true) (.node 797 (sourceLit (List.headD (raw_ints% [850596226461753110223953602410986619665205]) 0) 26 false) .empty .empty) .empty) (.node 827 (sourceLit (List.headD (raw_ints% [1025262343632981149078367666825]) 0) 63 true) .empty .empty)) (.node 830 (sourceLit (List.headD (raw_ints% [59987456832394301635264106989634721766515]) 0) 31 false) (.node 829 (sourceLit (List.headD (raw_ints% [5155869911827279148003514332175]) 0) 63 false) .empty .empty) (.node 831 (sourceLit (List.headD (raw_ints% [15074405603366571313487270944725]) 0) 63 true) .empty .empty)))

#time def treeG_J019_part110 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [18217418905181758416778431728210302748178705]) 0) 24 true) (.node 834 (sourceLit (List.headD (raw_ints% [1468938748883487048384858728879956677391545]) 0) 28 false) (.node 833 (sourceLit (List.headD (raw_ints% [6605805852577268049003096132825]) 0) 65 false) .empty .empty) (.node 835 (sourceLit (List.headD (raw_ints% [1707889681844489809151617213815]) 0) 67 true) .empty .empty)) (.node 838 (sourceLit (List.headD (raw_ints% [14011403563655290220049939143711610940275615]) 0) 23 false) (.node 837 (sourceLit (List.headD (raw_ints% [14997159149893889720446560945]) 0) 73 false) .empty .empty) (.node 839 (sourceLit (List.headD (raw_ints% [14114492428240138258307030865]) 0) 71 true) .empty .empty)))

#time def treeG_J019_part111 : IntSourceTree :=
  (.node 832 (sourceLit (List.headD (raw_ints% [542685657536846452334431924290758023869645]) 0) 29 true) treeG_J019_part109 treeG_J019_part110)

#time def treeG_J019_part112 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [697060706833709653643970888134379307518495]) 0) 30 true) (.node 871 (sourceLit (List.headD (raw_ints% [85896451324288657927301782227028094069865]) 0) 32 false) (.node 870 (sourceLit (List.headD (raw_ints% [15752836459233085388882423835975]) 0) 63 false) (.node 869 (sourceLit (List.headD (raw_ints% [12953972923285715565365877605329465518075]) 0) 33 true) .empty .empty) .empty) (.node 872 (sourceLit (List.headD (raw_ints% [20381663184064766437894774487325]) 0) 64 true) .empty .empty)) (.node 875 (sourceLit (List.headD (raw_ints% [1727813776576757758707409575347617493933835]) 0) 29 false) (.node 874 (sourceLit (List.headD (raw_ints% [4050984242491336959666404628675]) 0) 67 false) .empty .empty) (.node 876 (sourceLit (List.headD (raw_ints% [1933730232551678705550652258815]) 0) 68 true) .empty .empty)))

#time def treeG_J019_part113 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [163619240218680026158191127832270445911115]) 0) 31 true) (.node 879 (sourceLit (List.headD (raw_ints% [14401975975716839573383619306912323025575245]) 0) 24 false) (.node 878 (sourceLit (List.headD (raw_ints% [127034423680076249610640933335]) 0) 71 false) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [12503881141335310906027955888925]) 0) 63 true) .empty .empty)) (.node 912 (sourceLit (List.headD (raw_ints% [1917028878725464979171260439923207528987485]) 0) 29 false) (.node 911 (sourceLit (List.headD (raw_ints% [46580078521832742091252118616675]) 0) 63 false) .empty .empty) (.node 913 (sourceLit (List.headD (raw_ints% [13493734518321017243448935310075]) 0) 66 true) .empty .empty)))

#time def treeG_J019_part114 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [19918611358105264637226338933032275987509115]) 0) 25 true) treeG_J019_part112 treeG_J019_part113)

#time def treeG_J019_part115 : IntSourceTree :=
  (.node 868 (sourceLit (List.headD (raw_ints% [3674005614754015879012220778375]) 0) 63 true) treeG_J019_part111 treeG_J019_part114)

#time def treeG_J019_part116 : IntSourceTree :=
  (.node 919 (sourceLit (List.headD (raw_ints% [268183339788392637479588897535]) 0) 71 false) (.node 917 (sourceLit (List.headD (raw_ints% [2173684778949980941077797233935]) 0) 69 true) (.node 916 (sourceLit (List.headD (raw_ints% [128797500606094254974052644550457822359944145]) 0) 24 false) (.node 915 (sourceLit (List.headD (raw_ints% [9809858166827163728484426471165]) 0) 67 false) .empty .empty) .empty) (.node 918 (sourceLit (List.headD (raw_ints% [173360294428497407317860650607969818840348535]) 0) 23 true) .empty .empty)) (.node 951 (sourceLit (List.headD (raw_ints% [62378922885742171021373227514824634995245]) 0) 34 true) (.node 950 (sourceLit (List.headD (raw_ints% [40760598741903707200938335613825]) 0) 63 true) .empty .empty) (.node 952 (sourceLit (List.headD (raw_ints% [523138607077324285383960102375]) 0) 71 false) .empty .empty)))

#time def treeG_J019_part117 : IntSourceTree :=
  (.node 957 (sourceLit (List.headD (raw_ints% [37179027991049879902819745870872524586863315]) 0) 27 false) (.node 955 (sourceLit (List.headD (raw_ints% [2193309545032480509061008852325652157868335]) 0) 31 true) (.node 954 (sourceLit (List.headD (raw_ints% [8772359380406177101557669969375]) 0) 68 true) .empty .empty) (.node 956 (sourceLit (List.headD (raw_ints% [2935897099844710608508769682495]) 0) 70 false) .empty .empty)) (.node 959 (sourceLit (List.headD (raw_ints% [46940567601053561722811067478720535466480945]) 0) 26 true) (.node 958 (sourceLit (List.headD (raw_ints% [2427753626310133440299079100605]) 0) 70 true) .empty .empty) (.node 993 (sourceLit (List.headD (raw_ints% [46974605371269771508022381862075]) 0) 66 false) .empty .empty)))

#time def treeG_J019_part118 : IntSourceTree :=
  (.node 953 (sourceLit (List.headD (raw_ints% [653522396389793658203807832014396709126495]) 0) 32 false) treeG_J019_part116 treeG_J019_part117)

#time def treeG_J019_part119 : IntSourceTree :=
  (.node 999 (sourceLit (List.headD (raw_ints% [673984241524631519444666999535]) 0) 73 true) (.node 997 (sourceLit (List.headD (raw_ints% [13917273178328823375112875963915]) 0) 69 false) (.node 996 (sourceLit (List.headD (raw_ints% [690284744134409265293670910745824774774237905]) 0) 24 true) (.node 995 (sourceLit (List.headD (raw_ints% [44899295688451872134715106348665]) 0) 67 true) .empty .empty) .empty) (.node 998 (sourceLit (List.headD (raw_ints% [1363089190142093564208092518475890605619974615]) 0) 23 false) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [36731379268156483376302511867718294461060685]) 0) 29 false) (.node 1034 (sourceLit (List.headD (raw_ints% [64519324132082125711137721800825]) 0) 67 false) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [56642884087830714568750185078645]) 0) 68 true) .empty .empty)))

#time def treeG_J019_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [3041093017296424201377031670279795620282121745]) 0) 24 false) (.node 1039 (sourceLit (List.headD (raw_ints% [1550851460546307811099336788390772747485898395]) 0) 24 false) (.node 1038 (sourceLit (List.headD (raw_ints% [2043128350579869601926494383065]) 0) 73 false) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [173937943952616123556990549950315]) 0) 67 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [8075096038930963843447691672310409590593503935]) 0) 23 true) (.node 1077 (sourceLit (List.headD (raw_ints% [551251228641871390186430164395]) 0) 76 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [4760240942684370723297655765665]) 0) 73 false) .empty .empty)))

#time def treeG_J019_part121 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [839000856098608784904949894229314873121691165]) 0) 25 true) treeG_J019_part119 treeG_J019_part120)

#time def treeG_J019_part122 : IntSourceTree :=
  (.node 994 (sourceLit (List.headD (raw_ints% [27958141088026561340058476458415685829587345]) 0) 28 false) treeG_J019_part118 treeG_J019_part121)

#time def treeG_J019_part123 : IntSourceTree :=
  (.node 914 (sourceLit (List.headD (raw_ints% [7045424403553164277536625833954991137539505]) 0) 28 true) treeG_J019_part115 treeG_J019_part122)

#time def treeG_J019_part124 : IntSourceTree :=
  (.node 796 (sourceLit (List.headD (raw_ints% [28230068838398612049879380625]) 0) 71 false) treeG_J019_part108 treeG_J019_part123)

#time def treeG_J019_part125 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [64795535590136760101232962182614398625]) 0) 36 false) treeG_J019_part093 treeG_J019_part124)

#time def treeG_J019_part126 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [5425956178602376062149135775]) 0) 53 false) treeG_J019_part062 treeG_J019_part125)

#time def treeG_J019 : IntSourceTree := treeG_J019_part126

#time def treeG_J020_part000 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 8 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 44 false) (.node 7 (sourceLit (List.headD (raw_ints% [962368926858033459606360048375]) 0) 43 false) (.node 6 (sourceLit (List.headD (raw_ints% [375468046789895416399878853875]) 0) 42 false) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [116373571101001340402752549125]) 0) 46 false) .empty .empty)) (.node 12 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 47 true) (.node 11 (sourceLit (List.headD (raw_ints% [56566946197449035575855924725]) 0) 47 false) .empty .empty) (.node 13 (sourceLit (List.headD (raw_ints% [13796238303230921470011189825]) 0) 49 false) .empty .empty)))

#time def treeG_J020_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 55 false) (.node 17 (sourceLit (List.headD (raw_ints% [413349411421067805982423125]) 0) 54 false) (.node 16 (sourceLit (List.headD (raw_ints% [1020535923455844514822206675]) 0) 52 true) (.node 15 (sourceLit (List.headD (raw_ints% [6747365483160630476563990575]) 0) 50 false) .empty .empty) .empty) (.node 18 (sourceLit (List.headD (raw_ints% [241486037094158525018846925]) 0) 55 true) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [72774449914858835512296786356475]) 0) 39 true) (.node 20 (sourceLit (List.headD (raw_ints% [685889057976841245701792475]) 0) 55 true) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 57 false) .empty .empty)))

#time def treeG_J020_part002 : IntSourceTree :=
  (.node 14 (sourceLit (List.headD (raw_ints% [4376084461420692498833086875]) 0) 49 true) treeG_J020_part000 treeG_J020_part001)

#time def treeG_J020_part003 : IntSourceTree :=
  (.node 28 (sourceLit (List.headD (raw_ints% [1448673487732721951627355]) 0) 62 false) (.node 26 (sourceLit (List.headD (raw_ints% [733806069739038499157955]) 0) 63 false) (.node 25 (sourceLit (List.headD (raw_ints% [156099104535433088291102055709425]) 0) 36 true) (.node 24 (sourceLit (List.headD (raw_ints% [11903342734316464203898125]) 0) 59 false) .empty .empty) .empty) (.node 27 (sourceLit (List.headD (raw_ints% [229152169887854934919363627551975]) 0) 35 true) .empty .empty)) (.node 30 (sourceLit (List.headD (raw_ints% [357733154518475152853865]) 0) 64 false) (.node 29 (sourceLit (List.headD (raw_ints% [1424878941929531466351626556332625]) 0) 32 true) .empty .empty) (.node 31 (sourceLit (List.headD (raw_ints% [2287970237597698091220529047033285]) 0) 31 true) .empty .empty)))

#time def treeG_J020_part004 : IntSourceTree :=
  (.node 36 (sourceLit (List.headD (raw_ints% [2702369558422758804825]) 0) 71 false) (.node 34 (sourceLit (List.headD (raw_ints% [2731464120561156471825]) 0) 71 false) (.node 33 (sourceLit (List.headD (raw_ints% [7496282727507284781101943857298045]) 0) 29 true) .empty .empty) (.node 35 (sourceLit (List.headD (raw_ints% [12437297675003738591330629687274655]) 0) 28 true) .empty .empty)) (.node 38 (sourceLit (List.headD (raw_ints% [668690152373505606225]) 0) 73 false) (.node 37 (sourceLit (List.headD (raw_ints% [166372029758922930955081198488870225]) 0) 24 true) .empty .empty) (.node 39 (sourceLit (List.headD (raw_ints% [279339471313723214329658269312419225]) 0) 23 true) .empty .empty)))

#time def treeG_J020_part005 : IntSourceTree :=
  (.node 32 (sourceLit (List.headD (raw_ints% [22097657690020577631525]) 0) 68 false) treeG_J020_part003 treeG_J020_part004)

#time def treeG_J020_part006 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [60109338058130529143685007796475]) 0) 38 true) treeG_J020_part002 treeG_J020_part005)

#time def treeG_J020_part007 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [56566946197449035575855924725]) 0) 48 false) (.node 50 (sourceLit (List.headD (raw_ints% [116373571101001340402752549125]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 45 false) (.node 48 (sourceLit (List.headD (raw_ints% [962368926858033459606360048375]) 0) 44 false) .empty .empty) .empty) (.node 51 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)) (.node 54 (sourceLit (List.headD (raw_ints% [13796238303230921470011189825]) 0) 50 false) (.node 53 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 48 true) .empty .empty) (.node 55 (sourceLit (List.headD (raw_ints% [4376084461420692498833086875]) 0) 50 true) .empty .empty)))

#time def treeG_J020_part008 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 56 false) (.node 58 (sourceLit (List.headD (raw_ints% [413349411421067805982423125]) 0) 55 false) (.node 57 (sourceLit (List.headD (raw_ints% [1020535923455844514822206675]) 0) 53 true) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [241486037094158525018846925]) 0) 56 true) .empty .empty)) (.node 62 (sourceLit (List.headD (raw_ints% [72774449914858835512296786356475]) 0) 40 true) (.node 61 (sourceLit (List.headD (raw_ints% [685889057976841245701792475]) 0) 56 true) .empty .empty) (.node 63 (sourceLit (List.headD (raw_ints% [48313567568696237062880625]) 0) 58 false) .empty .empty)))

#time def treeG_J020_part009 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [6747365483160630476563990575]) 0) 51 false) treeG_J020_part007 treeG_J020_part008)

#time def treeG_J020_part010 : IntSourceTree :=
  (.node 69 (sourceLit (List.headD (raw_ints% [1448673487732721951627355]) 0) 63 false) (.node 67 (sourceLit (List.headD (raw_ints% [733806069739038499157955]) 0) 64 false) (.node 66 (sourceLit (List.headD (raw_ints% [156099104535433088291102055709425]) 0) 37 true) (.node 65 (sourceLit (List.headD (raw_ints% [11903342734316464203898125]) 0) 60 false) .empty .empty) .empty) (.node 68 (sourceLit (List.headD (raw_ints% [229152169887854934919363627551975]) 0) 36 true) .empty .empty)) (.node 71 (sourceLit (List.headD (raw_ints% [357733154518475152853865]) 0) 65 false) (.node 70 (sourceLit (List.headD (raw_ints% [1424878941929531466351626556332625]) 0) 33 true) .empty .empty) (.node 72 (sourceLit (List.headD (raw_ints% [2287970237597698091220529047033285]) 0) 32 true) .empty .empty)))

#time def treeG_J020_part011 : IntSourceTree :=
  (.node 77 (sourceLit (List.headD (raw_ints% [2702369558422758804825]) 0) 72 false) (.node 75 (sourceLit (List.headD (raw_ints% [2731464120561156471825]) 0) 72 false) (.node 74 (sourceLit (List.headD (raw_ints% [7496282727507284781101943857298045]) 0) 30 true) .empty .empty) (.node 76 (sourceLit (List.headD (raw_ints% [12437297675003738591330629687274655]) 0) 29 true) .empty .empty)) (.node 79 (sourceLit (List.headD (raw_ints% [668690152373505606225]) 0) 74 false) (.node 78 (sourceLit (List.headD (raw_ints% [166372029758922930955081198488870225]) 0) 25 true) .empty .empty) (.node 88 (sourceLit (List.headD (raw_ints% [162938963701275369381079502625]) 0) 45 false) .empty .empty)))

#time def treeG_J020_part012 : IntSourceTree :=
  (.node 73 (sourceLit (List.headD (raw_ints% [22097657690020577631525]) 0) 69 false) treeG_J020_part010 treeG_J020_part011)

#time def treeG_J020_part013 : IntSourceTree :=
  (.node 64 (sourceLit (List.headD (raw_ints% [60109338058130529143685007796475]) 0) 39 true) treeG_J020_part009 treeG_J020_part012)

#time def treeG_J020_part014 : IntSourceTree :=
  (.node 47 (sourceLit (List.headD (raw_ints% [375468046789895416399878853875]) 0) 43 false) treeG_J020_part006 treeG_J020_part013)

#time def treeG_J020_part015 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [1568784995603644480713748125]) 0) 50 true) (.node 92 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 47 false) (.node 91 (sourceLit (List.headD (raw_ints% [176180196004553645229649173525]) 0) 47 false) (.node 90 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 46 false) .empty .empty) .empty) (.node 93 (sourceLit (List.headD (raw_ints% [10692676973554528526461183725]) 0) 51 false) .empty .empty)) (.node 96 (sourceLit (List.headD (raw_ints% [2335012614509003469188673525]) 0) 51 true) (.node 95 (sourceLit (List.headD (raw_ints% [20845111123301212463458389075]) 0) 50 false) .empty .empty) (.node 97 (sourceLit (List.headD (raw_ints% [5093967837476359252634298075]) 0) 52 false) .empty .empty)))

#time def treeG_J020_part016 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [522086261260740154954689283055325]) 0) 38 true) (.node 101 (sourceLit (List.headD (raw_ints% [125967919713117722260466256308475]) 0) 39 false) (.node 100 (sourceLit (List.headD (raw_ints% [280055090399792854373595225]) 0) 55 true) (.node 99 (sourceLit (List.headD (raw_ints% [623781839053611416300747625]) 0) 55 false) .empty .empty) .empty) (.node 102 (sourceLit (List.headD (raw_ints% [183550656386384370691168275]) 0) 59 true) .empty .empty)) (.node 105 (sourceLit (List.headD (raw_ints% [805650304394655378007858069034175]) 0) 36 true) (.node 104 (sourceLit (List.headD (raw_ints% [9102556208594943214745625]) 0) 61 false) .empty .empty) (.node 106 (sourceLit (List.headD (raw_ints% [8968118455360310207266305]) 0) 61 false) .empty .empty)))

#time def treeG_J020_part017 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [537563849267527464784512825]) 0) 54 true) treeG_J020_part015 treeG_J020_part016)

#time def treeG_J020_part018 : IntSourceTree :=
  (.node 112 (sourceLit (List.headD (raw_ints% [269342523758392842327765]) 0) 66 false) (.node 110 (sourceLit (List.headD (raw_ints% [545470166607123399386745]) 0) 65 false) (.node 109 (sourceLit (List.headD (raw_ints% [5907990494481826451068009525330575]) 0) 32 true) (.node 108 (sourceLit (List.headD (raw_ints% [4421775070179586041636285]) 0) 62 false) .empty .empty) .empty) (.node 111 (sourceLit (List.headD (raw_ints% [9111061297838553639592483403627715]) 0) 31 true) .empty .empty)) (.node 114 (sourceLit (List.headD (raw_ints% [16634729448898264687875]) 0) 70 false) (.node 113 (sourceLit (List.headD (raw_ints% [29111241074055884678426520895234515]) 0) 29 true) .empty .empty) (.node 115 (sourceLit (List.headD (raw_ints% [47532964145054539657484921171109705]) 0) 28 true) .empty .empty)))

#time def treeG_J020_part019 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [276287808015206061124439156625]) 0) 45 false) (.node 118 (sourceLit (List.headD (raw_ints% [254209925756156649825]) 0) 76 false) (.node 117 (sourceLit (List.headD (raw_ints% [629615021441316338890079101496707695]) 0) 24 true) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [1051636766757660233310991318598542575]) 0) 23 true) .empty .empty)) (.node 131 (sourceLit (List.headD (raw_ints% [49590119387344677637719848625]) 0) 47 false) (.node 130 (sourceLit (List.headD (raw_ints% [496874642454028097995349851875]) 0) 46 false) .empty .empty) (.node 132 (sourceLit (List.headD (raw_ints% [3737914056472019051681039025]) 0) 53 false) .empty .empty)))

#time def treeG_J020_part020 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [8223486923821867082475]) 0) 71 false) treeG_J020_part018 treeG_J020_part019)

#time def treeG_J020_part021 : IntSourceTree :=
  (.node 107 (sourceLit (List.headD (raw_ints% [1019640666395609771409452818123425]) 0) 35 true) treeG_J020_part017 treeG_J020_part020)

#time def treeG_J020_part022 : IntSourceTree :=
  (.node 138 (sourceLit (List.headD (raw_ints% [3440570191792088028704605575]) 0) 53 false) (.node 136 (sourceLit (List.headD (raw_ints% [3524436410035145496723599625]) 0) 53 false) (.node 135 (sourceLit (List.headD (raw_ints% [1238514470213403537405590625]) 0) 50 false) (.node 134 (sourceLit (List.headD (raw_ints% [28974469590987192635833545075]) 0) 50 false) .empty .empty) .empty) (.node 137 (sourceLit (List.headD (raw_ints% [293940767597314439544260175]) 0) 52 true) .empty .empty)) (.node 140 (sourceLit (List.headD (raw_ints% [52608106908135902579581125]) 0) 59 false) (.node 139 (sourceLit (List.headD (raw_ints% [54591775079210414746818975]) 0) 55 true) .empty .empty) (.node 141 (sourceLit (List.headD (raw_ints% [202916983788524195664098625]) 0) 57 false) .empty .empty)))

#time def treeG_J020_part023 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [324775599929611144858378006662375]) 0) 38 true) (.node 144 (sourceLit (List.headD (raw_ints% [230988461601304812905502137629425]) 0) 40 true) (.node 143 (sourceLit (List.headD (raw_ints% [782516193114233719827553725]) 0) 58 true) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [24506882100063308655084375]) 0) 60 false) .empty .empty)) (.node 148 (sourceLit (List.headD (raw_ints% [395244248253877418245044595285725]) 0) 37 true) (.node 147 (sourceLit (List.headD (raw_ints% [6032894176404156210634485]) 0) 62 false) .empty .empty) (.node 149 (sourceLit (List.headD (raw_ints% [1486550791223432045004465]) 0) 64 false) .empty .empty)))

#time def treeG_J020_part024 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [99371184813988278886381521332475]) 0) 41 false) treeG_J020_part022 treeG_J020_part023)

#time def treeG_J020_part025 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [11171801207775951744225]) 0) 71 false) (.node 153 (sourceLit (List.headD (raw_ints% [180951892998310531801665]) 0) 67 false) (.node 152 (sourceLit (List.headD (raw_ints% [3411545530120427774185977178297215]) 0) 33 true) (.node 151 (sourceLit (List.headD (raw_ints% [733207178695771645919625]) 0) 65 false) .empty .empty) .empty) (.node 154 (sourceLit (List.headD (raw_ints% [10807479173274299948662288518968235]) 0) 31 true) .empty .empty)) (.node 157 (sourceLit (List.headD (raw_ints% [2760558682699554138825]) 0) 73 false) (.node 156 (sourceLit (List.headD (raw_ints% [17547833235025400533077145741917525]) 0) 30 true) .empty .empty) (.node 158 (sourceLit (List.headD (raw_ints% [231621495841196703967498951503918735]) 0) 26 true) .empty .empty)))

#time def treeG_J020_part026 : IntSourceTree :=
  (.node 173 (sourceLit (List.headD (raw_ints% [19210635478221623886987128475]) 0) 51 false) (.node 171 (sourceLit (List.headD (raw_ints% [160347223224737226382850339175]) 0) 48 false) (.node 170 (sourceLit (List.headD (raw_ints% [7084302769620668233959978375]) 0) 51 false) .empty .empty) (.node 172 (sourceLit (List.headD (raw_ints% [91666584322061373815179114125]) 0) 47 false) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [37103828058673172808208701075]) 0) 50 false) (.node 174 (sourceLit (List.headD (raw_ints% [4541219724115812970487165625]) 0) 51 false) .empty .empty) (.node 176 (sourceLit (List.headD (raw_ints% [1786763542361203503297132075]) 0) 52 false) .empty .empty)))

#time def treeG_J020_part027 : IntSourceTree :=
  (.node 159 (sourceLit (List.headD (raw_ints% [1364989253675747592375]) 0) 74 false) treeG_J020_part025 treeG_J020_part026)

#time def treeG_J020_part028 : IntSourceTree :=
  (.node 150 (sourceLit (List.headD (raw_ints% [2241555776276147492358191484498975]) 0) 34 true) treeG_J020_part024 treeG_J020_part027)

#time def treeG_J020_part029 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [7513654452627981460260583125]) 0) 49 false) treeG_J020_part021 treeG_J020_part028)

#time def treeG_J020_part030 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [729621784656030778800854950125]) 0) 45 false) treeG_J020_part014 treeG_J020_part029)

#time def treeG_J020_part031 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [570018296561292937046435175]) 0) 58 false) (.node 180 (sourceLit (List.headD (raw_ints% [170871540241372024879957275]) 0) 55 false) (.node 179 (sourceLit (List.headD (raw_ints% [2193006513684865196103110325]) 0) 54 false) (.node 178 (sourceLit (List.headD (raw_ints% [781186930937740490024765475]) 0) 53 false) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [15640723094506697893892540852475]) 0) 39 true) .empty .empty)) (.node 184 (sourceLit (List.headD (raw_ints% [818926417948613492686536225]) 0) 59 true) (.node 183 (sourceLit (List.headD (raw_ints% [2112025218284552617136793624374925]) 0) 38 false) .empty .empty) (.node 185 (sourceLit (List.headD (raw_ints% [6585980466847098634968210335107425]) 0) 36 true) .empty .empty)))

#time def treeG_J020_part032 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [26753831122579806238138580348355885]) 0) 31 true) (.node 189 (sourceLit (List.headD (raw_ints% [19387641393766328316614844572955825]) 0) 32 true) (.node 188 (sourceLit (List.headD (raw_ints% [7644013282628726379632685]) 0) 62 false) (.node 187 (sourceLit (List.headD (raw_ints% [4176768932478168546324595288474575]) 0) 35 true) .empty .empty) .empty) (.node 190 (sourceLit (List.headD (raw_ints% [117635078077038580702215]) 0) 68 false) .empty .empty)) (.node 193 (sourceLit (List.headD (raw_ints% [80058215889797804095524748810276365]) 0) 29 true) (.node 192 (sourceLit (List.headD (raw_ints% [115966163734344700897965]) 0) 68 false) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [114412975202717473050165]) 0) 68 false) .empty .empty)))

#time def treeG_J020_part033 : IntSourceTree :=
  (.node 186 (sourceLit (List.headD (raw_ints% [7769381822351499223909035]) 0) 62 false) treeG_J020_part031 treeG_J020_part032)

#time def treeG_J020_part034 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [177107569240516705848999459375]) 0) 47 false) (.node 198 (sourceLit (List.headD (raw_ints% [1743718979674927539525]) 0) 74 false) (.node 197 (sourceLit (List.headD (raw_ints% [1616507632641934929343795553468735505]) 0) 24 true) (.node 196 (sourceLit (List.headD (raw_ints% [14120115491730036405975]) 0) 71 false) .empty .empty) .empty) (.node 199 (sourceLit (List.headD (raw_ints% [2654307166701487030168991905464157185]) 0) 23 true) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [76639275416805410894657947875]) 0) 48 false) (.node 212 (sourceLit (List.headD (raw_ints% [100540598321184921555953714775]) 0) 49 false) .empty .empty) (.node 214 (sourceLit (List.headD (raw_ints% [47868072321899302912114968825]) 0) 50 false) .empty .empty)))

#time def treeG_J020_part035 : IntSourceTree :=
  (.node 219 (sourceLit (List.headD (raw_ints% [890370481096161319518403425]) 0) 54 false) (.node 217 (sourceLit (List.headD (raw_ints% [3867467852319721446138524325]) 0) 52 false) (.node 216 (sourceLit (List.headD (raw_ints% [23006082418532590821314302575]) 0) 51 false) .empty .empty) (.node 218 (sourceLit (List.headD (raw_ints% [2781603805436067352777747425]) 0) 54 false) .empty .empty)) (.node 221 (sourceLit (List.headD (raw_ints% [234962427335676366448239975]) 0) 56 true) (.node 220 (sourceLit (List.headD (raw_ints% [1351276803154690754829812325]) 0) 55 false) .empty .empty) (.node 222 (sourceLit (List.headD (raw_ints% [214383092722483255666655583517425]) 0) 40 true) .empty .empty)))

#time def treeG_J020_part036 : IntSourceTree :=
  (.node 215 (sourceLit (List.headD (raw_ints% [16926364426249848344543071875]) 0) 50 false) treeG_J020_part034 treeG_J020_part035)

#time def treeG_J020_part037 : IntSourceTree :=
  (.node 195 (sourceLit (List.headD (raw_ints% [125386702627334259521111695132382055]) 0) 28 true) treeG_J020_part033 treeG_J020_part036)

#time def treeG_J020_part038 : IntSourceTree :=
  (.node 228 (sourceLit (List.headD (raw_ints% [3386280435970413709834506097903125]) 0) 36 true) (.node 226 (sourceLit (List.headD (raw_ints% [5936429266987876345251454321782675]) 0) 37 true) (.node 225 (sourceLit (List.headD (raw_ints% [105429162506084600167702575]) 0) 63 true) (.node 224 (sourceLit (List.headD (raw_ints% [2574002141487162242947797899633775]) 0) 39 false) .empty .empty) .empty) (.node 227 (sourceLit (List.headD (raw_ints% [9505869468298842237183585]) 0) 62 false) .empty .empty)) (.node 230 (sourceLit (List.headD (raw_ints% [14904529841214033331898461603957875]) 0) 33 true) (.node 229 (sourceLit (List.headD (raw_ints% [4670911700181862289623755]) 0) 63 false) .empty .empty) (.node 231 (sourceLit (List.headD (raw_ints% [1148954070536845645315815]) 0) 65 false) .empty .empty)))

#time def treeG_J020_part039 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [90291036157283458454957403648547005]) 0) 29 true) (.node 234 (sourceLit (List.headD (raw_ints% [58443257543249204198200171772339895]) 0) 30 true) (.node 233 (sourceLit (List.headD (raw_ints% [282912761939068271790195]) 0) 67 false) .empty .empty) (.node 235 (sourceLit (List.headD (raw_ints% [69725770371613666073265]) 0) 69 false) .empty .empty)) (.node 238 (sourceLit (List.headD (raw_ints% [1153264640959541521408797650460898035]) 0) 25 true) (.node 237 (sourceLit (List.headD (raw_ints% [8598998126330928128325]) 0) 72 false) .empty .empty) (.node 239 (sourceLit (List.headD (raw_ints% [2122448705674107486675]) 0) 74 false) .empty .empty)))

#time def treeG_J020_part040 : IntSourceTree :=
  (.node 232 (sourceLit (List.headD (raw_ints% [19930740062338950689766625991761455]) 0) 32 true) treeG_J020_part038 treeG_J020_part039)

#time def treeG_J020_part041 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [7001152307934184043527101075]) 0) 53 false) (.node 255 (sourceLit (List.headD (raw_ints% [58632316585125433016021236575]) 0) 50 false) (.node 254 (sourceLit (List.headD (raw_ints% [58474396520342159012709285375]) 0) 49 false) (.node 253 (sourceLit (List.headD (raw_ints% [62119327364741673781979457825]) 0) 50 false) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [13352837341527441337948807725]) 0) 51 false) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [3370201097187269509452384525]) 0) 54 false) (.node 258 (sourceLit (List.headD (raw_ints% [1543140460690990478056879425]) 0) 54 false) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [359749470427394647319223075]) 0) 56 false) .empty .empty)))

#time def treeG_J020_part042 : IntSourceTree :=
  (.node 265 (sourceLit (List.headD (raw_ints% [47770014730641694522132976729247825]) 0) 36 false) (.node 263 (sourceLit (List.headD (raw_ints% [3827089960064418662470038292514325]) 0) 38 true) (.node 262 (sourceLit (List.headD (raw_ints% [1374999020458262240541110325]) 0) 57 true) .empty .empty) (.node 264 (sourceLit (List.headD (raw_ints% [685369801046358271651740075]) 0) 61 false) .empty .empty)) (.node 267 (sourceLit (List.headD (raw_ints% [43314665203424842215687039285786825]) 0) 35 true) (.node 266 (sourceLit (List.headD (raw_ints% [429486031846689899894719335]) 0) 62 true) .empty .empty) (.node 268 (sourceLit (List.headD (raw_ints% [11367725653968958094734485]) 0) 62 false) .empty .empty)))

#time def treeG_J020_part043 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [192755276237598324510945701914875]) 0) 39 false) treeG_J020_part041 treeG_J020_part042)

#time def treeG_J020_part044 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [262548554158972037882819804625]) 0) 47 false) treeG_J020_part040 treeG_J020_part043)

#time def treeG_J020_part045 : IntSourceTree :=
  (.node 223 (sourceLit (List.headD (raw_ints% [1922552786236819593920424075]) 0) 58 false) treeG_J020_part037 treeG_J020_part044)

#time def treeG_J020_part046 : IntSourceTree :=
  (.node 274 (sourceLit (List.headD (raw_ints% [84249893368175399370015]) 0) 69 false) (.node 272 (sourceLit (List.headD (raw_ints% [685089415599466841723955]) 0) 66 false) (.node 271 (sourceLit (List.headD (raw_ints% [92482407607132460417049112483307115]) 0) 31 true) (.node 270 (sourceLit (List.headD (raw_ints% [2788750450949244998388315]) 0) 64 false) .empty .empty) .empty) (.node 273 (sourceLit (List.headD (raw_ints% [238833625107625406940741267057906915]) 0) 29 true) .empty .empty)) (.node 276 (sourceLit (List.headD (raw_ints% [41485539388153593261315]) 0) 70 false) (.node 275 (sourceLit (List.headD (raw_ints% [342159357718659374064489679046337105]) 0) 28 true) .empty .empty) (.node 277 (sourceLit (List.headD (raw_ints% [4162118681424206411773478280038272815]) 0) 24 true) .empty .empty)))

#time def treeG_J020_part047 : IntSourceTree :=
  (.node 296 (sourceLit (List.headD (raw_ints% [2226639635412052637169183375]) 0) 55 false) (.node 294 (sourceLit (List.headD (raw_ints% [76370582407584044651843946825]) 0) 50 false) (.node 293 (sourceLit (List.headD (raw_ints% [92954639371083313494080928375]) 0) 49 false) (.node 279 (sourceLit (List.headD (raw_ints% [6571809960974845141101389298223027095]) 0) 23 true) .empty .empty) .empty) (.node 295 (sourceLit (List.headD (raw_ints% [10387008023523077667041553375]) 0) 52 false) .empty .empty)) (.node 298 (sourceLit (List.headD (raw_ints% [2109774251249058345374676825]) 0) 55 false) (.node 297 (sourceLit (List.headD (raw_ints% [1185671186150964986476285425]) 0) 55 false) .empty .empty) (.node 299 (sourceLit (List.headD (raw_ints% [2195910440285819636595355425]) 0) 54 false) .empty .empty)))

#time def treeG_J020_part048 : IntSourceTree :=
  (.node 278 (sourceLit (List.headD (raw_ints% [5111560166981073049275]) 0) 73 false) treeG_J020_part046 treeG_J020_part047)

#time def treeG_J020_part049 : IntSourceTree :=
  (.node 305 (sourceLit (List.headD (raw_ints% [896228126058527471987145225]) 0) 62 false) (.node 303 (sourceLit (List.headD (raw_ints% [51524246979610653663461475]) 0) 64 true) (.node 302 (sourceLit (List.headD (raw_ints% [101784592240020395044400321358075]) 0) 42 false) (.node 301 (sourceLit (List.headD (raw_ints% [954461368190465661086686125]) 0) 56 false) .empty .empty) .empty) (.node 304 (sourceLit (List.headD (raw_ints% [1600273025387895226354459048037025]) 0) 41 true) .empty .empty)) (.node 307 (sourceLit (List.headD (raw_ints% [868477933161678642026622255]) 0) 62 true) (.node 306 (sourceLit (List.headD (raw_ints% [13426610999407392716846107762757625]) 0) 39 false) .empty .empty) (.node 308 (sourceLit (List.headD (raw_ints% [9982096191863607126463133296970925]) 0) 38 true) .empty .empty)))

#time def treeG_J020_part050 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [6284010213443727655215]) 0) 73 false) (.node 311 (sourceLit (List.headD (raw_ints% [409949095103099838268125]) 0) 67 false) (.node 310 (sourceLit (List.headD (raw_ints% [18517200679018219266547722238996575]) 0) 35 true) .empty .empty) (.node 312 (sourceLit (List.headD (raw_ints% [18137916886198377431820621622886415]) 0) 34 true) .empty .empty)) (.node 315 (sourceLit (List.headD (raw_ints% [98774016364737132666765]) 0) 69 false) (.node 314 (sourceLit (List.headD (raw_ints% [45097591891094050685635273821391755]) 0) 32 true) .empty .empty) (.node 316 (sourceLit (List.headD (raw_ints% [62967080390343978902383068849447525]) 0) 31 true) .empty .empty)))

#time def treeG_J020_part051 : IntSourceTree :=
  (.node 309 (sourceLit (List.headD (raw_ints% [3348406976893547902555365]) 0) 64 false) treeG_J020_part049 treeG_J020_part050)

#time def treeG_J020_part052 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [252365536754072344327821525]) 0) 58 false) treeG_J020_part048 treeG_J020_part051)

#time def treeG_J020_part053 : IntSourceTree :=
  (.node 336 (sourceLit (List.headD (raw_ints% [28195194752564869330217405775]) 0) 51 false) (.node 334 (sourceLit (List.headD (raw_ints% [127434882221824467975452571375]) 0) 49 false) (.node 319 (sourceLit (List.headD (raw_ints% [373638932663370695325]) 0) 77 false) (.node 318 (sourceLit (List.headD (raw_ints% [752213510116166222591170157394343695]) 0) 27 true) .empty .empty) .empty) (.node 335 (sourceLit (List.headD (raw_ints% [94108848230042656287666657075]) 0) 50 false) .empty .empty)) (.node 338 (sourceLit (List.headD (raw_ints% [3199544283912869467848262275]) 0) 54 false) (.node 337 (sourceLit (List.headD (raw_ints% [10811964775362237053826365925]) 0) 53 false) .empty .empty) (.node 339 (sourceLit (List.headD (raw_ints% [5068895907808963872046322775]) 0) 54 false) .empty .empty)))

#time def treeG_J020_part054 : IntSourceTree :=
  (.node 344 (sourceLit (List.headD (raw_ints% [1509757752720128730267123675]) 0) 61 true) (.node 342 (sourceLit (List.headD (raw_ints% [1164730194324363950813898225]) 0) 58 false) (.node 341 (sourceLit (List.headD (raw_ints% [71869168829839838014944081483525]) 0) 39 false) .empty .empty) (.node 343 (sourceLit (List.headD (raw_ints% [7084196911745071303890848575972725]) 0) 38 false) .empty .empty)) (.node 346 (sourceLit (List.headD (raw_ints% [2221942283963744843869009785]) 0) 62 false) (.node 345 (sourceLit (List.headD (raw_ints% [150187488355466989008818355803617425]) 0) 36 true) .empty .empty) (.node 347 (sourceLit (List.headD (raw_ints% [472966217184461409154762487694030825]) 0) 35 false) .empty .empty)))

#time def treeG_J020_part055 : IntSourceTree :=
  (.node 340 (sourceLit (List.headD (raw_ints% [1476411499431030341956909275]) 0) 55 false) treeG_J020_part053 treeG_J020_part054)

#time def treeG_J020_part056 : IntSourceTree :=
  (.node 353 (sourceLit (List.headD (raw_ints% [921993055609070748695778516806823645]) 0) 29 true) (.node 351 (sourceLit (List.headD (raw_ints% [500068014121450556112477999164583285]) 0) 31 true) (.node 350 (sourceLit (List.headD (raw_ints% [3908063502837850806722415]) 0) 64 false) (.node 349 (sourceLit (List.headD (raw_ints% [1188734980001254801789191711452334225]) 0) 32 true) .empty .empty) .empty) (.node 352 (sourceLit (List.headD (raw_ints% [954706964812932511348545]) 0) 66 false) .empty .empty)) (.node 355 (sourceLit (List.headD (raw_ints% [1100963582796350247875839083238199055]) 0) 28 true) (.node 354 (sourceLit (List.headD (raw_ints% [116838433462023885596865]) 0) 69 false) .empty .empty) (.node 356 (sourceLit (List.headD (raw_ints% [28644238488291769702725]) 0) 71 false) .empty .empty)))

#time def treeG_J020_part057 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [58482614063449814092959723075]) 0) 51 false) (.node 359 (sourceLit (List.headD (raw_ints% [17499022362742473981816055738395971145]) 0) 23 true) (.node 358 (sourceLit (List.headD (raw_ints% [14064422801529590906115]) 0) 72 false) .empty .empty) (.node 375 (sourceLit (List.headD (raw_ints% [85886850127732157307286357875]) 0) 50 false) .empty .empty)) (.node 378 (sourceLit (List.headD (raw_ints% [6592416272864120363077012275]) 0) 54 false) (.node 377 (sourceLit (List.headD (raw_ints% [18709825263357149438407122375]) 0) 52 false) .empty .empty) (.node 379 (sourceLit (List.headD (raw_ints% [4203178127539919299101169125]) 0) 54 false) .empty .empty)))

#time def treeG_J020_part058 : IntSourceTree :=
  (.node 357 (sourceLit (List.headD (raw_ints% [11957453898503852187236587345420293585]) 0) 24 true) treeG_J020_part056 treeG_J020_part057)

#time def treeG_J020_part059 : IntSourceTree :=
  (.node 348 (sourceLit (List.headD (raw_ints% [1748323591977326242147978995]) 0) 62 true) treeG_J020_part055 treeG_J020_part058)

#time def treeG_J020_part060 : IntSourceTree :=
  (.node 317 (sourceLit (List.headD (raw_ints% [24287543135491737004665]) 0) 71 false) treeG_J020_part052 treeG_J020_part059)

#time def treeG_J020_part061 : IntSourceTree :=
  (.node 269 (sourceLit (List.headD (raw_ints% [88973332557286910398089350559944175]) 0) 32 true) treeG_J020_part045 treeG_J020_part060)

#time def treeG_J020_part062 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [9003777802664222734260100425]) 0) 52 false) treeG_J020_part030 treeG_J020_part061)

#time def treeG_J020_part063 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [601496469694664050563567225]) 0) 64 true) (.node 383 (sourceLit (List.headD (raw_ints% [2813506097671904868044665425]) 0) 59 false) (.node 382 (sourceLit (List.headD (raw_ints% [335269200130241742162657203948775]) 0) 40 true) (.node 381 (sourceLit (List.headD (raw_ints% [260975065620282340435111575]) 0) 57 false) .empty .empty) .empty) (.node 384 (sourceLit (List.headD (raw_ints% [13485289013296652209308684768120825]) 0) 39 false) .empty .empty)) (.node 387 (sourceLit (List.headD (raw_ints% [5312362501089168329764641825]) 0) 62 false) (.node 386 (sourceLit (List.headD (raw_ints% [203893932353096559876202786854647925]) 0) 37 true) .empty .empty) (.node 388 (sourceLit (List.headD (raw_ints% [512894601951915837660615020881914525]) 0) 36 false) .empty .empty)))

#time def treeG_J020_part064 : IntSourceTree :=
  (.node 394 (sourceLit (List.headD (raw_ints% [741602688044694545953237421521256625]) 0) 30 true) (.node 392 (sourceLit (List.headD (raw_ints% [427516346576657046385195512673037625]) 0) 32 true) (.node 391 (sourceLit (List.headD (raw_ints% [2268267122425451453649915]) 0) 65 false) (.node 390 (sourceLit (List.headD (raw_ints% [1114666177285181924723000822496347925]) 0) 33 true) .empty .empty) .empty) (.node 393 (sourceLit (List.headD (raw_ints% [552530311152533941414785]) 0) 67 false) .empty .empty)) (.node 396 (sourceLit (List.headD (raw_ints% [849095261234974332266306807840408955]) 0) 29 true) (.node 395 (sourceLit (List.headD (raw_ints% [134902850559310638526965]) 0) 69 false) .empty .empty) (.node 397 (sourceLit (List.headD (raw_ints% [33000933841091802400785]) 0) 71 false) .empty .empty)))

#time def treeG_J020_part065 : IntSourceTree :=
  (.node 389 (sourceLit (List.headD (raw_ints% [1755020405931113337953089725]) 0) 63 true) treeG_J020_part063 treeG_J020_part064)

#time def treeG_J020_part066 : IntSourceTree :=
  (.node 419 (sourceLit (List.headD (raw_ints% [8115936637919276854107701775]) 0) 54 false) (.node 417 (sourceLit (List.headD (raw_ints% [36858684512725339985306991225]) 0) 52 false) (.node 416 (sourceLit (List.headD (raw_ints% [14422913843791821994267238025]) 0) 53 false) (.node 399 (sourceLit (List.headD (raw_ints% [8086199878915659780915]) 0) 73 false) .empty .empty) .empty) (.node 418 (sourceLit (List.headD (raw_ints% [12310736695531410502710597825]) 0) 53 false) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [327896710531058512096021753882875]) 0) 39 false) (.node 420 (sourceLit (List.headD (raw_ints% [1363383314054444478572129925]) 0) 56 false) .empty .empty) (.node 422 (sourceLit (List.headD (raw_ints% [451877564352040805189393325]) 0) 59 true) .empty .empty)))

#time def treeG_J020_part067 : IntSourceTree :=
  (.node 427 (sourceLit (List.headD (raw_ints% [2104117676009233888164384782531214225]) 0) 35 true) (.node 425 (sourceLit (List.headD (raw_ints% [365952112568213424357757312093550625]) 0) 36 false) (.node 424 (sourceLit (List.headD (raw_ints% [5833021603112162328578912775]) 0) 60 false) .empty .empty) (.node 426 (sourceLit (List.headD (raw_ints% [7033914041521057248377547585]) 0) 62 true) .empty .empty)) (.node 429 (sourceLit (List.headD (raw_ints% [17601362242462561606928872379673599025]) 0) 32 false) (.node 428 (sourceLit (List.headD (raw_ints% [12373048594155662901677262645]) 0) 62 false) .empty .empty) (.node 430 (sourceLit (List.headD (raw_ints% [439732117358487797189953035]) 0) 66 true) .empty .empty)))

#time def treeG_J020_part068 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [9766350512787005241192106207562925]) 0) 38 true) treeG_J020_part066 treeG_J020_part067)

#time def treeG_J020_part069 : IntSourceTree :=
  (.node 398 (sourceLit (List.headD (raw_ints% [8948599858039187296871906715842918805]) 0) 25 true) treeG_J020_part065 treeG_J020_part068)

#time def treeG_J020_part070 : IntSourceTree :=
  (.node 436 (sourceLit (List.headD (raw_ints% [77614373582727099121515]) 0) 70 false) (.node 434 (sourceLit (List.headD (raw_ints% [318853444228486170221055]) 0) 68 false) (.node 433 (sourceLit (List.headD (raw_ints% [5918268489617441993467349685961778355]) 0) 29 true) (.node 432 (sourceLit (List.headD (raw_ints% [656780078806259471150685]) 0) 67 false) .empty .empty) .empty) (.node 435 (sourceLit (List.headD (raw_ints% [4831857921561206119750060288931853945]) 0) 28 true) .empty .empty)) (.node 438 (sourceLit (List.headD (raw_ints% [9468255519781105747335]) 0) 73 false) (.node 437 (sourceLit (List.headD (raw_ints% [42384642820534505077807048356365879535]) 0) 24 true) .empty .empty) (.node 439 (sourceLit (List.headD (raw_ints% [54089776501571024393159197988347379295]) 0) 23 true) .empty .empty)))

#time def treeG_J020_part071 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [551204124217081069068509175]) 0) 58 false) (.node 459 (sourceLit (List.headD (raw_ints% [2026889641997872800902357175]) 0) 56 false) (.node 458 (sourceLit (List.headD (raw_ints% [23673851966997099259152966675]) 0) 53 false) .empty .empty) (.node 460 (sourceLit (List.headD (raw_ints% [158311407004465366771373475]) 0) 60 false) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [3717261226375986478423452075]) 0) 59 true) (.node 462 (sourceLit (List.headD (raw_ints% [331582955330650127129339478915825]) 0) 41 false) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [11625819763041828725250395487841875]) 0) 40 true) .empty .empty)))

#time def treeG_J020_part072 : IntSourceTree :=
  (.node 457 (sourceLit (List.headD (raw_ints% [38981830111810138538661829725]) 0) 52 false) treeG_J020_part070 treeG_J020_part071)

#time def treeG_J020_part073 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [9358014209873871765825936601084973475]) 0) 34 false) (.node 468 (sourceLit (List.headD (raw_ints% [1308506138980574862912499901706564375]) 0) 37 true) (.node 467 (sourceLit (List.headD (raw_ints% [19380190584131282826519736995]) 0) 62 true) (.node 466 (sourceLit (List.headD (raw_ints% [284923022460654992116980049474099275]) 0) 38 false) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [7064034500043388119815176185]) 0) 64 false) .empty .empty)) (.node 472 (sourceLit (List.headD (raw_ints% [3994872528791673897643166534066581245]) 0) 33 true) (.node 471 (sourceLit (List.headD (raw_ints% [1761196736556376640213462055]) 0) 65 true) .empty .empty) (.node 473 (sourceLit (List.headD (raw_ints% [761029846459985000886585]) 0) 67 false) .empty .empty)))

#time def treeG_J020_part074 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [16718021481247658890467570820261480365]) 0) 26 true) (.node 476 (sourceLit (List.headD (raw_ints% [1991381330163115893741876740545722495]) 0) 30 true) (.node 475 (sourceLit (List.headD (raw_ints% [91975296834587765847045]) 0) 70 false) .empty .empty) (.node 477 (sourceLit (List.headD (raw_ints% [22306719870817648360365]) 0) 72 false) .empty .empty)) (.node 498 (sourceLit (List.headD (raw_ints% [6667773354069682008987807975]) 0) 55 false) (.node 479 (sourceLit (List.headD (raw_ints% [10850311160646551713755]) 0) 73 false) .empty .empty) (.node 499 (sourceLit (List.headD (raw_ints% [3889478832269455601261316225]) 0) 56 false) .empty .empty)))

#time def treeG_J020_part075 : IntSourceTree :=
  (.node 474 (sourceLit (List.headD (raw_ints% [2588332900786373723757056132220260865]) 0) 31 true) treeG_J020_part073 treeG_J020_part074)

#time def treeG_J020_part076 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [10644993360669474733087450575]) 0) 61 false) treeG_J020_part072 treeG_J020_part075)

#time def treeG_J020_part077 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [8417261404160004841671528580806200115]) 0) 31 true) treeG_J020_part069 treeG_J020_part076)

#time def treeG_J020_part078 : IntSourceTree :=
  (.node 505 (sourceLit (List.headD (raw_ints% [737978344985551943565769967704490625]) 0) 36 true) (.node 503 (sourceLit (List.headD (raw_ints% [15071677798077407275261537870216125]) 0) 38 false) (.node 502 (sourceLit (List.headD (raw_ints% [250770422142280468564475625]) 0) 61 false) (.node 501 (sourceLit (List.headD (raw_ints% [336109457113398593614617097803525]) 0) 39 false) .empty .empty) .empty) (.node 504 (sourceLit (List.headD (raw_ints% [4775141414744074403501182425]) 0) 61 true) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [6662886035379713762036065574116802625]) 0) 35 false) (.node 506 (sourceLit (List.headD (raw_ints% [1104931712636908248841562385]) 0) 66 false) .empty .empty) (.node 508 (sourceLit (List.headD (raw_ints% [51133429762418228554716736635]) 0) 62 true) .empty .empty)))

#time def treeG_J020_part079 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [221088201115749415332765]) 0) 69 false) (.node 512 (sourceLit (List.headD (raw_ints% [1762510296713989159155763425]) 0) 66 true) (.node 511 (sourceLit (List.headD (raw_ints% [158145488762141953094886514198165775715]) 0) 31 false) (.node 510 (sourceLit (List.headD (raw_ints% [7943498734760363714195082255]) 0) 65 false) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [121917652431716122731113979404168821485]) 0) 29 true) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [106336220086448432572575]) 0) 70 false) (.node 515 (sourceLit (List.headD (raw_ints% [36581468491020773460362837826592319895]) 0) 28 true) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [212512167440344329321153174433486599825]) 0) 24 true) .empty .empty)))

#time def treeG_J020_part080 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [101345755137219352833328866088893719025]) 0) 32 true) treeG_J020_part078 treeG_J020_part079)

#time def treeG_J020_part081 : IntSourceTree :=
  (.node 542 (sourceLit (List.headD (raw_ints% [327056453547901660644061860028125]) 0) 40 true) (.node 540 (sourceLit (List.headD (raw_ints% [2622987576233732667090328425]) 0) 57 false) (.node 539 (sourceLit (List.headD (raw_ints% [290055232004488075505340675]) 0) 60 false) (.node 519 (sourceLit (List.headD (raw_ints% [213398567198391517854321935135836306545]) 0) 23 true) .empty .empty) .empty) (.node 541 (sourceLit (List.headD (raw_ints% [1587987721507138985095566075]) 0) 57 false) .empty .empty)) (.node 544 (sourceLit (List.headD (raw_ints% [38323317324161064725762328845899875]) 0) 39 false) (.node 543 (sourceLit (List.headD (raw_ints% [5723424603514230226939257075]) 0) 59 false) .empty .empty) (.node 545 (sourceLit (List.headD (raw_ints% [20195276190157623540089815425]) 0) 61 true) .empty .empty)))

#time def treeG_J020_part082 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [120061783556967096364980739291063665975]) 0) 33 true) (.node 548 (sourceLit (List.headD (raw_ints% [9279898313340863487861065377529931375]) 0) 36 false) (.node 547 (sourceLit (List.headD (raw_ints% [54738005388512346789449733315]) 0) 62 false) .empty .empty) (.node 549 (sourceLit (List.headD (raw_ints% [65261498762505004794347089005]) 0) 63 true) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [166135233819725300890172847266298938205]) 0) 32 false) (.node 551 (sourceLit (List.headD (raw_ints% [17648194206077104068603626565]) 0) 65 false) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [881635663280224572078325005]) 0) 68 true) .empty .empty)))

#time def treeG_J020_part083 : IntSourceTree :=
  (.node 546 (sourceLit (List.headD (raw_ints% [1307824389906861927799730066652689175]) 0) 37 true) treeG_J020_part081 treeG_J020_part082)

#time def treeG_J020_part084 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [6419232175518271306515]) 0) 74 false) treeG_J020_part080 treeG_J020_part083)

#time def treeG_J020_part085 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [14826617541426533512305]) 0) 73 false) (.node 557 (sourceLit (List.headD (raw_ints% [61722780344813135851845]) 0) 71 false) (.node 556 (sourceLit (List.headD (raw_ints% [32598705830694541672879084345500874905]) 0) 29 true) (.node 555 (sourceLit (List.headD (raw_ints% [16139113035145206185715]) 0) 73 false) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [179076124477849011540218032792963639095]) 0) 25 true) .empty .empty)) (.node 581 (sourceLit (List.headD (raw_ints% [1039091453255032638948837011482875]) 0) 39 false) (.node 580 (sourceLit (List.headD (raw_ints% [6591371454202317292938317175]) 0) 56 false) .empty .empty) (.node 582 (sourceLit (List.headD (raw_ints% [418175655631104763420238925]) 0) 58 true) .empty .empty)))

#time def treeG_J020_part086 : IntSourceTree :=
  (.node 587 (sourceLit (List.headD (raw_ints% [17125481154634609184433906107338316025]) 0) 35 true) (.node 585 (sourceLit (List.headD (raw_ints% [1351151422172128979177967229238888625]) 0) 36 false) (.node 584 (sourceLit (List.headD (raw_ints% [15273707433002379033941621925]) 0) 60 false) .empty .empty) (.node 586 (sourceLit (List.headD (raw_ints% [37874183592348155521554813585]) 0) 62 true) .empty .empty)) (.node 589 (sourceLit (List.headD (raw_ints% [398302501164126984444882958169851523025]) 0) 32 false) (.node 588 (sourceLit (List.headD (raw_ints% [160609440539442922133616203265]) 0) 62 false) .empty .empty) (.node 590 (sourceLit (List.headD (raw_ints% [81148496232025732222737253515]) 0) 64 true) .empty .empty)))

#time def treeG_J020_part087 : IntSourceTree :=
  (.node 583 (sourceLit (List.headD (raw_ints% [17688129426460620560414032750441125]) 0) 38 true) treeG_J020_part085 treeG_J020_part086)

#time def treeG_J020_part088 : IntSourceTree :=
  (.node 596 (sourceLit (List.headD (raw_ints% [151889588475874866398865]) 0) 70 false) (.node 594 (sourceLit (List.headD (raw_ints% [440928375740670160746828885]) 0) 70 true) (.node 593 (sourceLit (List.headD (raw_ints% [2780081393547320936973879535664951832765]) 0) 29 false) (.node 592 (sourceLit (List.headD (raw_ints% [9705352251395546613879694995]) 0) 67 false) .empty .empty) .empty) (.node 595 (sourceLit (List.headD (raw_ints% [897346424550126228808436099291234078145]) 0) 28 true) .empty .empty)) (.node 598 (sourceLit (List.headD (raw_ints% [36045851642740050625785]) 0) 72 false) (.node 597 (sourceLit (List.headD (raw_ints% [1873805005724106337743108223678569394095]) 0) 24 true) .empty .empty) (.node 599 (sourceLit (List.headD (raw_ints% [1219210428624400574467422327207872806215]) 0) 23 true) .empty .empty)))

#time def treeG_J020_part089 : IntSourceTree :=
  (.node 625 (sourceLit (List.headD (raw_ints% [17734491811580001287015718675]) 0) 62 false) (.node 623 (sourceLit (List.headD (raw_ints% [95962504049145859224367125]) 0) 65 true) (.node 622 (sourceLit (List.headD (raw_ints% [170768488350366787449112358938875]) 0) 43 false) .empty .empty) (.node 624 (sourceLit (List.headD (raw_ints% [7001430843827710660772045199542625]) 0) 42 true) .empty .empty)) (.node 627 (sourceLit (List.headD (raw_ints% [130486372573208657832559360485]) 0) 62 true) (.node 626 (sourceLit (List.headD (raw_ints% [332371976509873863372212161986447225]) 0) 40 false) .empty .empty) (.node 628 (sourceLit (List.headD (raw_ints% [3300672433496934084036871435608530925]) 0) 39 true) .empty .empty)))

#time def treeG_J020_part090 : IntSourceTree :=
  (.node 621 (sourceLit (List.headD (raw_ints% [1250845933173794576960687775]) 0) 59 false) treeG_J020_part088 treeG_J020_part089)

#time def treeG_J020_part091 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [1118639757217878724014732428526675103515]) 0) 31 true) treeG_J020_part087 treeG_J020_part090)

#time def treeG_J020_part092 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [116740986630143375283599867139728299755]) 0) 30 true) treeG_J020_part084 treeG_J020_part091)

#time def treeG_J020_part093 : IntSourceTree :=
  (.node 500 (sourceLit (List.headD (raw_ints% [2690395969941301123232584425]) 0) 56 false) treeG_J020_part077 treeG_J020_part092)

#time def treeG_J020_part094 : IntSourceTree :=
  (.node 634 (sourceLit (List.headD (raw_ints% [362102797522183039032184925350585016565]) 0) 33 false) (.node 632 (sourceLit (List.headD (raw_ints% [160596873879700503113113159474121755215]) 0) 35 true) (.node 631 (sourceLit (List.headD (raw_ints% [6174793152381427268208805005]) 0) 69 true) (.node 630 (sourceLit (List.headD (raw_ints% [64795535590136760101232962182614398625]) 0) 36 false) .empty .empty) .empty) (.node 633 (sourceLit (List.headD (raw_ints% [330843372333617849561188125]) 0) 73 false) .empty .empty)) (.node 636 (sourceLit (List.headD (raw_ints% [108093464839928960891944626868216650405]) 0) 32 true) (.node 635 (sourceLit (List.headD (raw_ints% [440992932192810741571571745]) 0) 71 true) .empty .empty) (.node 637 (sourceLit (List.headD (raw_ints% [22541702032765432636755]) 0) 73 false) .empty .empty)))

#time def treeG_J020_part095 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [73343167215508158095586250935]) 0) 62 false) (.node 664 (sourceLit (List.headD (raw_ints% [21415307692147714024301117925]) 0) 60 true) (.node 663 (sourceLit (List.headD (raw_ints% [28617312680884094957157223722529125]) 0) 38 false) (.node 639 (sourceLit (List.headD (raw_ints% [2652404262664189639185]) 0) 76 false) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [2247334570182075943756789014780344625]) 0) 36 true) .empty .empty)) (.node 668 (sourceLit (List.headD (raw_ints% [421582185685860237798734924235]) 0) 62 true) (.node 667 (sourceLit (List.headD (raw_ints% [38397287651266536440255484474470938425]) 0) 35 false) .empty .empty) (.node 669 (sourceLit (List.headD (raw_ints% [1243274644139342109958322045685635439825]) 0) 32 true) .empty .empty)))

#time def treeG_J020_part096 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [211841110155782165775361273860700719375]) 0) 28 true) treeG_J020_part094 treeG_J020_part095)

#time def treeG_J020_part097 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [24071925465969840726868271321728675138305]) 0) 28 false) (.node 673 (sourceLit (List.headD (raw_ints% [23336481250148985335452363948352536500285]) 0) 29 true) (.node 672 (sourceLit (List.headD (raw_ints% [59103697470446964759550135035]) 0) 67 true) (.node 671 (sourceLit (List.headD (raw_ints% [5265554034986631370493642008213996615515]) 0) 31 false) .empty .empty) .empty) (.node 674 (sourceLit (List.headD (raw_ints% [5734422333078555753725838885]) 0) 70 false) .empty .empty)) (.node 677 (sourceLit (List.headD (raw_ints% [53470048992319521638932540732848355613265]) 0) 24 true) (.node 676 (sourceLit (List.headD (raw_ints% [1764123618359718841152685845]) 0) 70 true) .empty .empty) (.node 678 (sourceLit (List.headD (raw_ints% [54120956488321679921235]) 0) 72 false) .empty .empty)))

#time def treeG_J020_part098 : IntSourceTree :=
  (.node 707 (sourceLit (List.headD (raw_ints% [277172707004224974023731862355]) 0) 62 false) (.node 705 (sourceLit (List.headD (raw_ints% [56884291315307716598332555275]) 0) 61 true) (.node 704 (sourceLit (List.headD (raw_ints% [84628759431505780243333585318870125]) 0) 39 false) .empty .empty) (.node 706 (sourceLit (List.headD (raw_ints% [4906310382261066850734486310671922425]) 0) 37 true) .empty .empty)) (.node 709 (sourceLit (List.headD (raw_ints% [647453124987808164726698216505]) 0) 63 true) (.node 708 (sourceLit (List.headD (raw_ints% [64802667119242009112550455959339185825]) 0) 36 false) .empty .empty) (.node 710 (sourceLit (List.headD (raw_ints% [1761638928860436190768185743146550628825]) 0) 33 true) .empty .empty)))

#time def treeG_J020_part099 : IntSourceTree :=
  (.node 679 (sourceLit (List.headD (raw_ints% [12338620621345658035155699199876973233785]) 0) 23 true) treeG_J020_part097 treeG_J020_part098)

#time def treeG_J020_part100 : IntSourceTree :=
  (.node 670 (sourceLit (List.headD (raw_ints% [307019435533973659150700545785]) 0) 64 false) treeG_J020_part096 treeG_J020_part099)

#time def treeG_J020_part101 : IntSourceTree :=
  (.node 716 (sourceLit (List.headD (raw_ints% [24936673184689272414003828336674408341545]) 0) 29 false) (.node 714 (sourceLit (List.headD (raw_ints% [26233303630326449647709843351157216632805]) 0) 30 true) (.node 713 (sourceLit (List.headD (raw_ints% [69690685385122735945508155035]) 0) 68 true) (.node 712 (sourceLit (List.headD (raw_ints% [6550329026024235395398547284006970657235]) 0) 32 false) .empty .empty) .empty) (.node 715 (sourceLit (List.headD (raw_ints% [3087707632635683247648705315]) 0) 72 false) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [51775320111073264312729650541962749858265]) 0) 25 true) (.node 717 (sourceLit (List.headD (raw_ints% [1764213785167849902883232865]) 0) 71 true) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [32901722387008162807755]) 0) 73 false) .empty .empty)))

#time def treeG_J020_part102 : IntSourceTree :=
  (.node 749 (sourceLit (List.headD (raw_ints% [3316959991955086401559936636384489386225]) 0) 32 false) (.node 747 (sourceLit (List.headD (raw_ints% [77647770709355071246131374959846317825]) 0) 35 true) (.node 746 (sourceLit (List.headD (raw_ints% [65113729265407937346959403105]) 0) 63 true) .empty .empty) (.node 748 (sourceLit (List.headD (raw_ints% [975927599694310185846198648945]) 0) 62 false) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [19358665465870120896639127953386401646115]) 0) 31 true) (.node 750 (sourceLit (List.headD (raw_ints% [477236280260890911938699381145]) 0) 65 true) .empty .empty) (.node 752 (sourceLit (List.headD (raw_ints% [524023520912970424961141695935]) 0) 66 false) .empty .empty)))

#time def treeG_J020_part103 : IntSourceTree :=
  (.node 745 (sourceLit (List.headD (raw_ints% [3601394721086168427650126379882266625]) 0) 36 false) treeG_J020_part101 treeG_J020_part102)

#time def treeG_J020_part104 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [441066976531084556140788525]) 0) 74 true) (.node 756 (sourceLit (List.headD (raw_ints% [26465784679445184822342328365]) 0) 70 false) (.node 755 (sourceLit (List.headD (raw_ints% [233938354508581437908547018130986408200745]) 0) 28 true) (.node 754 (sourceLit (List.headD (raw_ints% [81159530051279847452959832805]) 0) 69 true) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [1649417132812432956135177554280010489472145]) 0) 24 false) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [4253852551673617639192306345277094525]) 0) 38 false) (.node 759 (sourceLit (List.headD (raw_ints% [401863940267240456466681505135825025632335]) 0) 23 true) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [537627624065856723411569474775]) 0) 62 true) .empty .empty)))

#time def treeG_J020_part105 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [12954497245947178146018837618696686151675]) 0) 33 true) (.node 790 (sourceLit (List.headD (raw_ints% [2539299460407761296164061189765520007525]) 0) 34 false) (.node 789 (sourceLit (List.headD (raw_ints% [811690362341059175286448432725]) 0) 64 false) .empty .empty) (.node 791 (sourceLit (List.headD (raw_ints% [1360288686493858319319440188155]) 0) 65 true) .empty .empty)) (.node 794 (sourceLit (List.headD (raw_ints% [77187524648431600654769481921810641824425]) 0) 31 false) (.node 793 (sourceLit (List.headD (raw_ints% [663404891683215896852158006005]) 0) 67 false) .empty .empty) (.node 795 (sourceLit (List.headD (raw_ints% [93510360581822580443554654065]) 0) 70 true) .empty .empty)))

#time def treeG_J020_part106 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [71225218914298540179340915459592751825]) 0) 37 true) treeG_J020_part104 treeG_J020_part105)

#time def treeG_J020_part107 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [128141745666536751661829120492464067016045]) 0) 29 false) treeG_J020_part103 treeG_J020_part106)

#time def treeG_J020_part108 : IntSourceTree :=
  (.node 711 (sourceLit (List.headD (raw_ints% [405816125972076495442041425865]) 0) 65 false) treeG_J020_part100 treeG_J020_part107)

#time def treeG_J020_part109 : IntSourceTree :=
  (.node 828 (sourceLit (List.headD (raw_ints% [2051182847826023632669337598495]) 0) 62 true) (.node 799 (sourceLit (List.headD (raw_ints% [1764300807846725232725961855]) 0) 73 true) (.node 798 (sourceLit (List.headD (raw_ints% [850596226461753110223953602410986619665205]) 0) 26 false) (.node 797 (sourceLit (List.headD (raw_ints% [14114999232306517362612780615]) 0) 72 false) .empty .empty) .empty) (.node 827 (sourceLit (List.headD (raw_ints% [145709411536132953473208276484279830225]) 0) 35 false) .empty .empty)) (.node 830 (sourceLit (List.headD (raw_ints% [644463321300975043612573906935]) 0) 66 false) (.node 829 (sourceLit (List.headD (raw_ints% [7875374002470192973037755225798425503025]) 0) 32 true) .empty .empty) (.node 831 (sourceLit (List.headD (raw_ints% [59987456832394301635264106989634721766515]) 0) 31 false) .empty .empty)))

#time def treeG_J020_part110 : IntSourceTree :=
  (.node 836 (sourceLit (List.headD (raw_ints% [213486505843090345709451636495]) 0) 70 true) (.node 834 (sourceLit (List.headD (raw_ints% [825723951785775591758077671615]) 0) 68 false) (.node 833 (sourceLit (List.headD (raw_ints% [542685657536846452334431924290758023869645]) 0) 29 true) .empty .empty) (.node 835 (sourceLit (List.headD (raw_ints% [1468938748883487048384858728879956677391545]) 0) 28 false) .empty .empty)) (.node 838 (sourceLit (List.headD (raw_ints% [14997133185368686474894357665]) 0) 73 false) (.node 837 (sourceLit (List.headD (raw_ints% [18217418905181758416778431728210302748178705]) 0) 24 true) .empty .empty) (.node 839 (sourceLit (List.headD (raw_ints% [14011403563655290220049939143711610940275615]) 0) 23 false) .empty .empty)))

#time def treeG_J020_part111 : IntSourceTree :=
  (.node 832 (sourceLit (List.headD (raw_ints% [942156103703414372140290942045]) 0) 67 true) treeG_J020_part109 treeG_J020_part110)

#time def treeG_J020_part112 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [2547717099090044641132739890095]) 0) 67 true) (.node 871 (sourceLit (List.headD (raw_ints% [3938141971697758493769735815895]) 0) 65 false) (.node 870 (sourceLit (List.headD (raw_ints% [12953972923285715565365877605329465518075]) 0) 33 true) (.node 869 (sourceLit (List.headD (raw_ints% [3674563572508141983242234463945]) 0) 63 true) .empty .empty) .empty) (.node 872 (sourceLit (List.headD (raw_ints% [85896451324288657927301782227028094069865]) 0) 32 false) .empty .empty)) (.node 875 (sourceLit (List.headD (raw_ints% [1012744672949420752645186979745]) 0) 69 false) (.node 874 (sourceLit (List.headD (raw_ints% [697060706833709653643970888134379307518495]) 0) 30 true) .empty .empty) (.node 876 (sourceLit (List.headD (raw_ints% [1727813776576757758707409575347617493933835]) 0) 29 false) .empty .empty)))

#time def treeG_J020_part113 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [6252416857712042157692530091685]) 0) 64 true) (.node 879 (sourceLit (List.headD (raw_ints% [31758567178584098182514677185]) 0) 73 false) (.node 878 (sourceLit (List.headD (raw_ints% [19918611358105264637226338933032275987509115]) 0) 25 true) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [17096489182141554055658238662709316187025]) 0) 32 false) .empty .empty)) (.node 912 (sourceLit (List.headD (raw_ints% [5822454179104587238050317699985]) 0) 66 false) (.node 911 (sourceLit (List.headD (raw_ints% [163619240218680026158191127832270445911115]) 0) 31 true) .empty .empty) (.node 913 (sourceLit (List.headD (raw_ints% [1917028878725464979171260439923207528987485]) 0) 29 false) .empty .empty)))

#time def treeG_J020_part114 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [241716504307703380434677197725]) 0) 71 true) treeG_J020_part112 treeG_J020_part113)

#time def treeG_J020_part115 : IntSourceTree :=
  (.node 868 (sourceLit (List.headD (raw_ints% [288159849364730033831890107403465333875]) 0) 36 false) treeG_J020_part111 treeG_J020_part114)

#time def treeG_J020_part116 : IntSourceTree :=
  (.node 919 (sourceLit (List.headD (raw_ints% [173360294428497407317860650607969818840348535]) 0) 23 true) (.node 917 (sourceLit (List.headD (raw_ints% [128797500606094254974052644550457822359944145]) 0) 24 false) (.node 916 (sourceLit (List.headD (raw_ints% [76639448674531943647164913515]) 0) 74 false) (.node 915 (sourceLit (List.headD (raw_ints% [7045424403553164277536625833954991137539505]) 0) 28 true) .empty .empty) .empty) (.node 918 (sourceLit (List.headD (raw_ints% [271710770678440753384465913055]) 0) 72 true) .empty .empty)) (.node 951 (sourceLit (List.headD (raw_ints% [2547639707352450162865566476895]) 0) 67 true) (.node 950 (sourceLit (List.headD (raw_ints% [7512615526356817405256029067009695426275]) 0) 35 false) .empty .empty) (.node 952 (sourceLit (List.headD (raw_ints% [62378922885742171021373227514824634995245]) 0) 34 true) .empty .empty)))

#time def treeG_J020_part117 : IntSourceTree :=
  (.node 957 (sourceLit (List.headD (raw_ints% [1467947683100214478789315813965]) 0) 71 false) (.node 955 (sourceLit (List.headD (raw_ints% [4386185723825240985536004541455]) 0) 69 true) (.node 954 (sourceLit (List.headD (raw_ints% [653522396389793658203807832014396709126495]) 0) 32 false) .empty .empty) (.node 956 (sourceLit (List.headD (raw_ints% [2193309545032480509061008852325652157868335]) 0) 31 true) .empty .empty)) (.node 959 (sourceLit (List.headD (raw_ints% [9483416808032026611468143445]) 0) 78 true) (.node 958 (sourceLit (List.headD (raw_ints% [37179027991049879902819745870872524586863315]) 0) 27 false) .empty .empty) (.node 993 (sourceLit (List.headD (raw_ints% [5909279943412963924539147000871984168683165]) 0) 29 true) .empty .empty)))

#time def treeG_J020_part118 : IntSourceTree :=
  (.node 953 (sourceLit (List.headD (raw_ints% [130783926221791123112235274845]) 0) 73 false) treeG_J020_part116 treeG_J020_part117)

#time def treeG_J020_part119 : IntSourceTree :=
  (.node 999 (sourceLit (List.headD (raw_ints% [1363089190142093564208092518475890605619974615]) 0) 23 false) (.node 997 (sourceLit (List.headD (raw_ints% [690284744134409265293670910745824774774237905]) 0) 24 true) (.node 996 (sourceLit (List.headD (raw_ints% [5612416902617752083890643157695]) 0) 70 true) (.node 995 (sourceLit (List.headD (raw_ints% [27958141088026561340058476458415685829587345]) 0) 28 false) .empty .empty) .empty) (.node 998 (sourceLit (List.headD (raw_ints% [434914613444663808043445431755]) 0) 74 false) .empty .empty)) (.node 1035 (sourceLit (List.headD (raw_ints% [16129798052895693097609879693245]) 0) 69 false) (.node 1034 (sourceLit (List.headD (raw_ints% [8523369528972138557354378328929571005189145]) 0) 30 true) .empty .empty) (.node 1036 (sourceLit (List.headD (raw_ints% [36731379268156483376302511867718294461060685]) 0) 29 false) .empty .empty)))

#time def treeG_J020_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [5435553738878361295375130712735]) 0) 72 false) (.node 1039 (sourceLit (List.headD (raw_ints% [510781947908920020935190579315]) 0) 75 false) (.node 1038 (sourceLit (List.headD (raw_ints% [839000856098608784904949894229314873121691165]) 0) 25 true) .empty .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [96145097319803669798893503089852253871100505]) 0) 28 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [1102502879937077724356717587335]) 0) 75 true) (.node 1077 (sourceLit (List.headD (raw_ints% [3041093017296424201377031670279795620282121745]) 0) 24 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [8075096038930963843447691672310409590593503935]) 0) 23 true) .empty .empty)))

#time def treeG_J020_part121 : IntSourceTree :=
  (.node 1037 (sourceLit (List.headD (raw_ints% [1770091146429491640669989742915]) 0) 73 true) treeG_J020_part119 treeG_J020_part120)

#time def treeG_J020_part122 : IntSourceTree :=
  (.node 994 (sourceLit (List.headD (raw_ints% [5871806164535226056036937575895]) 0) 69 false) treeG_J020_part118 treeG_J020_part121)

#time def treeG_J020_part123 : IntSourceTree :=
  (.node 914 (sourceLit (List.headD (raw_ints% [1686720525437910116445408780855]) 0) 69 true) treeG_J020_part115 treeG_J020_part122)

#time def treeG_J020_part124 : IntSourceTree :=
  (.node 796 (sourceLit (List.headD (raw_ints% [129437513846635355161275423233830408271145]) 0) 30 true) treeG_J020_part108 treeG_J020_part123)

#time def treeG_J020_part125 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [112935469650973963463981646135]) 0) 64 false) treeG_J020_part093 treeG_J020_part124)

#time def treeG_J020_part126 : IntSourceTree :=
  (.node 380 (sourceLit (List.headD (raw_ints% [3049971613776385117423750575]) 0) 55 false) treeG_J020_part062 treeG_J020_part125)

#time def treeG_J020 : IntSourceTree := treeG_J020_part126

-- kcost: 1.806s estimated (602 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J012_check : treeG_J012.check 40 (sourceBaseG momentData 12) = true := by
  decide +kernel

-- kcost: 1.773s estimated (591 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J013_check : treeG_J013.check 40 (sourceBaseG momentData 13) = true := by
  decide +kernel

-- kcost: 1.773s estimated (591 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J014_check : treeG_J014.check 40 (sourceBaseG momentData 14) = true := by
  decide +kernel

-- kcost: 1.773s estimated (591 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J015_check : treeG_J015.check 40 (sourceBaseG momentData 15) = true := by
  decide +kernel

-- kcost: 1.734s estimated (578 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J016_check : treeG_J016.check 40 (sourceBaseG momentData 16) = true := by
  decide +kernel

-- kcost: 1.734s estimated (578 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J017_check : treeG_J017.check 40 (sourceBaseG momentData 17) = true := by
  decide +kernel

-- kcost: 1.650s estimated (550 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J018_check : treeG_J018.check 40 (sourceBaseG momentData 18) = true := by
  decide +kernel

-- kcost: 1.650s estimated (550 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J019_check : treeG_J019.check 40 (sourceBaseG momentData 19) = true := by
  decide +kernel

-- kcost: 1.650s estimated (550 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J020_check : treeG_J020.check 40 (sourceBaseG momentData 20) = true := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
