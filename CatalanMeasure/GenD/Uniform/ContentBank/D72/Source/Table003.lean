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

#time def treeG_J001_part000 : IntSourceTree :=
  (.node 5 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 42 false) (.node 3 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 false) (.node 2 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 true) (.node 1 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty) .empty) (.node 4 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 38 true) .empty .empty)) (.node 7 (sourceLit (List.headD (raw_ints% [4790405532817495859803737377175]) 0) 42 false) (.node 6 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 36 false) .empty .empty) (.node 8 (sourceLit (List.headD (raw_ints% [62334780069892259790613849721625]) 0) 35 false) .empty .empty)))

#time def treeG_J001_part001 : IntSourceTree :=
  (.node 13 (sourceLit (List.headD (raw_ints% [31752508556949937235958360375]) 0) 49 false) (.node 11 (sourceLit (List.headD (raw_ints% [265897497286429081047964521675]) 0) 46 false) (.node 10 (sourceLit (List.headD (raw_ints% [741025154005091517940447698003375]) 0) 32 false) .empty .empty) (.node 12 (sourceLit (List.headD (raw_ints% [1777018649595849385974479674518075]) 0) 31 false) .empty .empty)) (.node 15 (sourceLit (List.headD (raw_ints% [30510414231391394723293135875]) 0) 49 false) (.node 14 (sourceLit (List.headD (raw_ints% [7879345425092528734260293631526275]) 0) 29 false) .empty .empty) (.node 16 (sourceLit (List.headD (raw_ints% [16814846677690901988344829607056225]) 0) 28 false) .empty .empty)))

#time def treeG_J001_part002 : IntSourceTree :=
  (.node 9 (sourceLit (List.headD (raw_ints% [140269194838489231032407571825]) 0) 47 false) treeG_J001_part000 treeG_J001_part001)

#time def treeG_J001_part003 : IntSourceTree :=
  (.node 46 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 43 false) (.node 44 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 40 false) (.node 43 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 40 true) (.node 42 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty) .empty) (.node 45 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 39 true) .empty .empty)) (.node 48 (sourceLit (List.headD (raw_ints% [4790405532817495859803737377175]) 0) 43 false) (.node 47 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 37 false) .empty .empty) (.node 49 (sourceLit (List.headD (raw_ints% [62334780069892259790613849721625]) 0) 36 false) .empty .empty)))

#time def treeG_J001_part004 : IntSourceTree :=
  (.node 54 (sourceLit (List.headD (raw_ints% [31752508556949937235958360375]) 0) 50 false) (.node 52 (sourceLit (List.headD (raw_ints% [265897497286429081047964521675]) 0) 47 false) (.node 51 (sourceLit (List.headD (raw_ints% [741025154005091517940447698003375]) 0) 33 false) .empty .empty) (.node 53 (sourceLit (List.headD (raw_ints% [1777018649595849385974479674518075]) 0) 32 false) .empty .empty)) (.node 56 (sourceLit (List.headD (raw_ints% [30510414231391394723293135875]) 0) 50 false) (.node 55 (sourceLit (List.headD (raw_ints% [7879345425092528734260293631526275]) 0) 30 false) .empty .empty) (.node 57 (sourceLit (List.headD (raw_ints% [16814846677690901988344829607056225]) 0) 29 false) .empty .empty)))

#time def treeG_J001_part005 : IntSourceTree :=
  (.node 50 (sourceLit (List.headD (raw_ints% [140269194838489231032407571825]) 0) 48 false) treeG_J001_part003 treeG_J001_part004)

#time def treeG_J001_part006 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [230057671567286016523955025]) 0) 56 false) treeG_J001_part002 treeG_J001_part005)

#time def treeG_J001_part007 : IntSourceTree :=
  (.node 88 (sourceLit (List.headD (raw_ints% [37341359898670542261203046014625]) 0) 35 true) (.node 86 (sourceLit (List.headD (raw_ints% [253058379233619889985284387533375]) 0) 36 true) (.node 85 (sourceLit (List.headD (raw_ints% [36448737749698338063724088739375]) 0) 41 false) (.node 84 (sourceLit (List.headD (raw_ints% [359280414961312189485280303288125]) 0) 38 true) .empty .empty) .empty) (.node 87 (sourceLit (List.headD (raw_ints% [16037444609867268748038599045325]) 0) 42 false) .empty .empty)) (.node 90 (sourceLit (List.headD (raw_ints% [1253687808231460795359195493088625]) 0) 32 false) (.node 89 (sourceLit (List.headD (raw_ints% [3668251974109582011544476802575]) 0) 44 false) .empty .empty) (.node 91 (sourceLit (List.headD (raw_ints% [856256061421484767211296052925]) 0) 46 false) .empty .empty)))

#time def treeG_J001_part008 : IntSourceTree :=
  (.node 96 (sourceLit (List.headD (raw_ints% [46219916723049327885737519445153975]) 0) 28 false) (.node 94 (sourceLit (List.headD (raw_ints% [20552952968441061441331381160762925]) 0) 29 false) (.node 93 (sourceLit (List.headD (raw_ints% [202392480172529206576047800925]) 0) 48 false) .empty .empty) (.node 95 (sourceLit (List.headD (raw_ints% [96499619996408354220540305625]) 0) 49 false) .empty .empty)) (.node 124 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 41 true) (.node 97 (sourceLit (List.headD (raw_ints% [23148568741238242194526575075]) 0) 51 false) .empty .empty) (.node 125 (sourceLit (List.headD (raw_ints% [171829763677149308014699275485625]) 0) 40 true) .empty .empty)))

#time def treeG_J001_part009 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [4151182582444882757549101909508925]) 0) 31 false) treeG_J001_part007 treeG_J001_part008)

#time def treeG_J001_part010 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [138887463058629332104131080175]) 0) 49 false) (.node 130 (sourceLit (List.headD (raw_ints% [2546098415401668163285216227975]) 0) 45 false) (.node 128 (sourceLit (List.headD (raw_ints% [5623519538524886444117430834075]) 0) 44 false) (.node 127 (sourceLit (List.headD (raw_ints% [128091278377511302338230368998375]) 0) 38 true) .empty .empty) (.node 129 (sourceLit (List.headD (raw_ints% [49838069984281401025908447868125]) 0) 37 true) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [295179282067527843081665765625]) 0) 48 false) (.node 131 (sourceLit (List.headD (raw_ints% [256331327113184638709373897542625]) 0) 34 false) .empty .empty) (.node 133 (sourceLit (List.headD (raw_ints% [1187081966424516685787311117495425]) 0) 33 false) .empty .empty))) (.node 165 (sourceLit (List.headD (raw_ints% [130174063391779778799014602640625]) 0) 41 true) (.node 136 (sourceLit (List.headD (raw_ints% [32994602882508479748623584875]) 0) 51 false) (.node 135 (sourceLit (List.headD (raw_ints% [6336803771674266353535543764618325]) 0) 31 false) .empty .empty) (.node 137 (sourceLit (List.headD (raw_ints% [14702535022679212948696344919048875]) 0) 30 false) .empty .empty)) (.node 167 (sourceLit (List.headD (raw_ints% [36032180746844642771567242010925]) 0) 42 false) (.node 166 (sourceLit (List.headD (raw_ints% [5245494058435157966485092428006625]) 0) 36 true) .empty .empty) (.node 168 (sourceLit (List.headD (raw_ints% [2012119094141510295150482857959375]) 0) 35 true) .empty .empty))))

#time def treeG_J001_part011 : IntSourceTree :=
  (.node 126 (sourceLit (List.headD (raw_ints% [26034812678355955759802920528125]) 0) 42 false) treeG_J001_part009 treeG_J001_part010)

#time def treeG_J001_part012 : IntSourceTree :=
  (.node 83 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 true) treeG_J001_part006 treeG_J001_part011)

#time def treeG_J001_part013 : IntSourceTree :=
  (.node 174 (sourceLit (List.headD (raw_ints% [17433669957143472503862574599090675]) 0) 29 false) (.node 172 (sourceLit (List.headD (raw_ints% [49881348633928538199119548826925]) 0) 31 true) (.node 171 (sourceLit (List.headD (raw_ints% [844921176990091698036960087525]) 0) 47 false) (.node 170 (sourceLit (List.headD (raw_ints% [4443324287225470461017336156648625]) 0) 32 true) .empty .empty) .empty) (.node 173 (sourceLit (List.headD (raw_ints% [387966083962526479587283730325]) 0) 48 false) .empty .empty)) (.node 176 (sourceLit (List.headD (raw_ints% [55168943623738933770831180788739225]) 0) 28 false) (.node 175 (sourceLit (List.headD (raw_ints% [181275306120850309987721854725]) 0) 49 false) .empty .empty) (.node 177 (sourceLit (List.headD (raw_ints% [42840637023778717302720594675]) 0) 51 false) .empty .empty)))

#time def treeG_J001_part014 : IntSourceTree :=
  (.node 210 (sourceLit (List.headD (raw_ints% [157271521485578834793911519925]) 0) 50 false) (.node 208 (sourceLit (List.headD (raw_ints% [24785141669794869883332380342775]) 0) 43 false) (.node 207 (sourceLit (List.headD (raw_ints% [4989311501680135361808631690009875]) 0) 37 true) .empty .empty) (.node 209 (sourceLit (List.headD (raw_ints% [1912442954172947493098665962223125]) 0) 36 true) .empty .empty)) (.node 212 (sourceLit (List.headD (raw_ints% [137435473730640963738823580475]) 0) 50 false) (.node 211 (sourceLit (List.headD (raw_ints% [4955986941451839738436083951733875]) 0) 33 true) .empty .empty) (.node 213 (sourceLit (List.headD (raw_ints% [2424045281482961909773741783817775]) 0) 32 true) .empty .empty)))

#time def treeG_J001_part015 : IntSourceTree :=
  (.node 206 (sourceLit (List.headD (raw_ints% [78104438035067867279408761584375]) 0) 43 true) treeG_J001_part013 treeG_J001_part014)

#time def treeG_J001_part016 : IntSourceTree :=
  (.node 248 (sourceLit (List.headD (raw_ints% [37902372919299572599318570662119625]) 0) 35 true) (.node 217 (sourceLit (List.headD (raw_ints% [25763873578380507873438490950641475]) 0) 29 false) (.node 216 (sourceLit (List.headD (raw_ints% [115286100355833350490474684975]) 0) 50 false) (.node 215 (sourceLit (List.headD (raw_ints% [4760062413794939796791487069854025]) 0) 30 false) .empty .empty) .empty) (.node 247 (sourceLit (List.headD (raw_ints% [348449932887116111889202288348425]) 0) 42 true) .empty .empty)) (.node 250 (sourceLit (List.headD (raw_ints% [56754850246308849318139974634491375]) 0) 32 true) (.node 249 (sourceLit (List.headD (raw_ints% [1075397160428417437915124717325]) 0) 48 false) .empty .empty) (.node 251 (sourceLit (List.headD (raw_ints% [1671423166779169658665624231275]) 0) 47 false) .empty .empty)))

#time def treeG_J001_part017 : IntSourceTree :=
  (.node 256 (sourceLit (List.headD (raw_ints% [17088444313379415396499284229907025]) 0) 28 true) (.node 254 (sourceLit (List.headD (raw_ints% [56218394460870863060242443140175075]) 0) 29 true) (.node 253 (sourceLit (List.headD (raw_ints% [711517705882601230323304913475]) 0) 48 false) .empty .empty) (.node 255 (sourceLit (List.headD (raw_ints% [316881935686943984978583445575]) 0) 49 false) .empty .empty)) (.node 288 (sourceLit (List.headD (raw_ints% [1457949509987933522548963549575]) 0) 51 true) (.node 257 (sourceLit (List.headD (raw_ints% [18111365833013658296938522575]) 0) 53 false) .empty .empty) (.node 289 (sourceLit (List.headD (raw_ints% [8997482491281656276554976174974125]) 0) 38 true) .empty .empty)))

#time def treeG_J001_part018 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [39598014182980789369289552065044075]) 0) 31 true) treeG_J001_part016 treeG_J001_part017)

#time def treeG_J001_part019 : IntSourceTree :=
  (.node 214 (sourceLit (List.headD (raw_ints% [124539310451948573741576325075]) 0) 50 false) treeG_J001_part015 treeG_J001_part018)

#time def treeG_J001_part020 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [15244614218666450714258482552507275]) 0) 32 true) (.node 293 (sourceLit (List.headD (raw_ints% [9293492225374456864878952570306575]) 0) 34 true) (.node 292 (sourceLit (List.headD (raw_ints% [1121681271856605803710329909375]) 0) 48 false) (.node 291 (sourceLit (List.headD (raw_ints% [12949715826214252394925972670689375]) 0) 35 true) .empty .empty) .empty) (.node 294 (sourceLit (List.headD (raw_ints% [462439084978704082840152263325]) 0) 49 false) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [10713079472939980817484443795137125]) 0) 31 true) (.node 296 (sourceLit (List.headD (raw_ints% [25199479416388829311013595075]) 0) 53 false) .empty .empty) (.node 330 (sourceLit (List.headD (raw_ints% [1094922908637743154080896975762196625]) 0) 32 true) .empty .empty)))

#time def treeG_J001_part021 : IntSourceTree :=
  (.node 335 (sourceLit (List.headD (raw_ints% [607996234270464180701721081075]) 0) 49 false) (.node 333 (sourceLit (List.headD (raw_ints% [1531844837830610377097354905275]) 0) 48 false) (.node 332 (sourceLit (List.headD (raw_ints% [374792892255875287268341573397015925]) 0) 31 true) .empty .empty) (.node 334 (sourceLit (List.headD (raw_ints% [538565107963094376292010521359445725]) 0) 29 true) .empty .empty)) (.node 337 (sourceLit (List.headD (raw_ints% [32287592999764000325088667575]) 0) 53 false) (.node 336 (sourceLit (List.headD (raw_ints% [470739210683947007459772157450325775]) 0) 28 true) .empty .empty) (.node 371 (sourceLit (List.headD (raw_ints% [1043124045332886144501193085079439125]) 0) 33 true) .empty .empty)))

#time def treeG_J001_part022 : IntSourceTree :=
  (.node 331 (sourceLit (List.headD (raw_ints% [4415409772878908487952789188525]) 0) 47 false) treeG_J001_part020 treeG_J001_part021)

#time def treeG_J001_part023 : IntSourceTree :=
  (.node 414 (sourceLit (List.headD (raw_ints% [4863337665706944980649201688493188275]) 0) 29 true) (.node 376 (sourceLit (List.headD (raw_ints% [406400398939353546213612320475]) 0) 50 false) (.node 374 (sourceLit (List.headD (raw_ints% [534702876425953147128601320975]) 0) 50 false) (.node 373 (sourceLit (List.headD (raw_ints% [337618923354377459808825763115789625]) 0) 32 true) .empty .empty) (.node 375 (sourceLit (List.headD (raw_ints% [477586651088428573434976591149416625]) 0) 30 true) .empty .empty)) (.node 412 (sourceLit (List.headD (raw_ints% [7970199470407213868741203107238497075]) 0) 31 true) (.node 377 (sourceLit (List.headD (raw_ints% [427886892792187084189834382269777275]) 0) 29 true) .empty .empty) (.node 413 (sourceLit (List.headD (raw_ints% [5055612164213994991387563653025]) 0) 48 false) .empty .empty))) (.node 454 (sourceLit (List.headD (raw_ints% [3986206411362088697130361011075]) 0) 49 false) (.node 416 (sourceLit (List.headD (raw_ints% [3349953998023481580020040571745007225]) 0) 28 true) (.node 415 (sourceLit (List.headD (raw_ints% [1530815271433348407812684202825]) 0) 49 false) .empty .empty) (.node 417 (sourceLit (List.headD (raw_ints% [277250026940297544913257650175]) 0) 51 false) .empty .empty)) (.node 456 (sourceLit (List.headD (raw_ints% [562207436246997430799535941175]) 0) 51 false) (.node 455 (sourceLit (List.headD (raw_ints% [2192875507309258203607112548671885825]) 0) 31 true) .empty .empty) (.node 457 (sourceLit (List.headD (raw_ints% [1461033552615647247915103094737614975]) 0) 30 true) .empty .empty))))

#time def treeG_J001_part024 : IntSourceTree :=
  (.node 372 (sourceLit (List.headD (raw_ints% [1646864250511151342121229639575]) 0) 49 false) treeG_J001_part022 treeG_J001_part023)

#time def treeG_J001_part025 : IntSourceTree :=
  (.node 290 (sourceLit (List.headD (raw_ints% [760854117457259768327301677475]) 0) 49 false) treeG_J001_part019 treeG_J001_part024)

#time def treeG_J001_part026 : IntSourceTree :=
  (.node 169 (sourceLit (List.headD (raw_ints% [7578787102940190876690384865575]) 0) 44 false) treeG_J001_part012 treeG_J001_part025)

#time def treeG_J001 : IntSourceTree := treeG_J001_part026

#time def treeG_J002_part000 : IntSourceTree :=
  (.node 7 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 36 false) (.node 4 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 false) (.node 2 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 38 true) (.node 1 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 false) .empty .empty) (.node 3 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 true) .empty .empty)) (.node 6 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 41 false) (.node 5 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 38 true) .empty .empty) .empty)) (.node 10 (sourceLit (List.headD (raw_ints% [412306421191922891216470741425]) 0) 45 false) (.node 9 (sourceLit (List.headD (raw_ints% [62334780069892259790613849721625]) 0) 35 false) (.node 8 (sourceLit (List.headD (raw_ints% [862868077339797390896325366075]) 0) 44 false) .empty .empty) .empty) (.node 12 (sourceLit (List.headD (raw_ints% [99137303606388623952809636775]) 0) 47 false) (.node 11 (sourceLit (List.headD (raw_ints% [741025154005091517940447698003375]) 0) 32 false) .empty .empty) .empty)))

#time def treeG_J002_part001 : IntSourceTree :=
  (.node 19 (sourceLit (List.headD (raw_ints% [280970815398555888174405366533235375]) 0) 24 false) (.node 16 (sourceLit (List.headD (raw_ints% [2903493643317072740418532875]) 0) 52 false) (.node 15 (sourceLit (List.headD (raw_ints% [7879345425092528734260293631526275]) 0) 29 false) (.node 14 (sourceLit (List.headD (raw_ints% [47899734789210989900606278875]) 0) 48 false) .empty .empty) .empty) (.node 18 (sourceLit (List.headD (raw_ints% [1412081073429181496900765325]) 0) 53 false) (.node 17 (sourceLit (List.headD (raw_ints% [16814846677690901988344829607056225]) 0) 28 false) .empty .empty) .empty)) (.node 42 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 40 false) (.node 21 (sourceLit (List.headD (raw_ints% [579140529595865211022877280990198375]) 0) 23 false) (.node 20 (sourceLit (List.headD (raw_ints% [344190663382661775486303525]) 0) 55 false) .empty .empty) .empty) (.node 44 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 40 true) (.node 43 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 true) .empty .empty) .empty)))

#time def treeG_J002_part002 : IntSourceTree :=
  (.node 13 (sourceLit (List.headD (raw_ints% [1777018649595849385974479674518075]) 0) 31 false) treeG_J002_part000 treeG_J002_part001)

#time def treeG_J002_part003 : IntSourceTree :=
  (.node 51 (sourceLit (List.headD (raw_ints% [412306421191922891216470741425]) 0) 46 false) (.node 48 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 37 false) (.node 47 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 42 false) (.node 46 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 39 true) .empty .empty) .empty) (.node 50 (sourceLit (List.headD (raw_ints% [62334780069892259790613849721625]) 0) 36 false) (.node 49 (sourceLit (List.headD (raw_ints% [862868077339797390896325366075]) 0) 45 false) .empty .empty) .empty)) (.node 54 (sourceLit (List.headD (raw_ints% [1777018649595849385974479674518075]) 0) 32 false) (.node 53 (sourceLit (List.headD (raw_ints% [99137303606388623952809636775]) 0) 48 false) (.node 52 (sourceLit (List.headD (raw_ints% [741025154005091517940447698003375]) 0) 33 false) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [7879345425092528734260293631526275]) 0) 30 false) (.node 55 (sourceLit (List.headD (raw_ints% [47899734789210989900606278875]) 0) 49 false) .empty .empty) .empty)))

#time def treeG_J002_part004 : IntSourceTree :=
  (.node 84 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 42 true) (.node 60 (sourceLit (List.headD (raw_ints% [280970815398555888174405366533235375]) 0) 25 false) (.node 59 (sourceLit (List.headD (raw_ints% [1412081073429181496900765325]) 0) 54 false) (.node 58 (sourceLit (List.headD (raw_ints% [16814846677690901988344829607056225]) 0) 29 false) .empty .empty) .empty) (.node 83 (sourceLit (List.headD (raw_ints% [234313314105203601838226284753125]) 0) 39 false) (.node 61 (sourceLit (List.headD (raw_ints% [344190663382661775486303525]) 0) 56 false) .empty .empty) .empty)) (.node 87 (sourceLit (List.headD (raw_ints% [253058379233619889985284387533375]) 0) 36 true) (.node 86 (sourceLit (List.headD (raw_ints% [23952027664087479299018686885875]) 0) 41 false) (.node 85 (sourceLit (List.headD (raw_ints% [359280414961312189485280303288125]) 0) 38 true) .empty .empty) .empty) (.node 89 (sourceLit (List.headD (raw_ints% [37341359898670542261203046014625]) 0) 35 true) (.node 88 (sourceLit (List.headD (raw_ints% [5564011395260072830952167015725]) 0) 43 false) .empty .empty) .empty)))

#time def treeG_J002_part005 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [2903493643317072740418532875]) 0) 53 false) treeG_J002_part003 treeG_J002_part004)

#time def treeG_J002_part006 : IntSourceTree :=
  (.node 45 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 41 false) treeG_J002_part002 treeG_J002_part005)

#time def treeG_J002_part007 : IntSourceTree :=
  (.node 96 (sourceLit (List.headD (raw_ints% [36285760215942698938932147375]) 0) 50 false) (.node 93 (sourceLit (List.headD (raw_ints% [4151182582444882757549101909508925]) 0) 31 false) (.node 92 (sourceLit (List.headD (raw_ints% [156584558792767133631830552325]) 0) 48 false) (.node 91 (sourceLit (List.headD (raw_ints% [1253687808231460795359195493088625]) 0) 32 false) .empty .empty) .empty) (.node 95 (sourceLit (List.headD (raw_ints% [20552952968441061441331381160762925]) 0) 29 false) (.node 94 (sourceLit (List.headD (raw_ints% [150374872423566258005012994675]) 0) 48 false) .empty .empty) .empty)) (.node 99 (sourceLit (List.headD (raw_ints% [795179371973661839079663728318363025]) 0) 24 false) (.node 98 (sourceLit (List.headD (raw_ints% [4394906213204963983936300425]) 0) 53 false) (.node 97 (sourceLit (List.headD (raw_ints% [46219916723049327885737519445153975]) 0) 28 false) .empty .empty) .empty) (.node 101 (sourceLit (List.headD (raw_ints% [1668625993592581894372365651275684625]) 0) 23 false) (.node 100 (sourceLit (List.headD (raw_ints% [133486301255814965176807725]) 0) 58 false) .empty .empty) .empty)))

#time def treeG_J002_part008 : IntSourceTree :=
  (.node 130 (sourceLit (List.headD (raw_ints% [49838069984281401025908447868125]) 0) 37 true) (.node 127 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 46 false) (.node 126 (sourceLit (List.headD (raw_ints% [171829763677149308014699275485625]) 0) 40 true) (.node 125 (sourceLit (List.headD (raw_ints% [78104438035067867279408761584375]) 0) 41 true) .empty .empty) .empty) (.node 129 (sourceLit (List.headD (raw_ints% [3838275240580478049159516283575]) 0) 44 false) (.node 128 (sourceLit (List.headD (raw_ints% [128091278377511302338230368998375]) 0) 38 true) .empty .empty) .empty)) (.node 133 (sourceLit (List.headD (raw_ints% [214031813979145643310851467875]) 0) 48 false) (.node 132 (sourceLit (List.headD (raw_ints% [256331327113184638709373897542625]) 0) 34 false) (.node 131 (sourceLit (List.headD (raw_ints% [225280828073937249839927312325]) 0) 48 false) .empty .empty) .empty) (.node 135 (sourceLit (List.headD (raw_ints% [12809392204294408513050839475]) 0) 52 false) (.node 134 (sourceLit (List.headD (raw_ints% [1187081966424516685787311117495425]) 0) 33 false) .empty .empty) .empty)))

#time def treeG_J002_part009 : IntSourceTree :=
  (.node 124 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 41 false) treeG_J002_part007 treeG_J002_part008)

#time def treeG_J002_part010 : IntSourceTree :=
  (.node 165 (sourceLit (List.headD (raw_ints% [2608688230371266767132252636918125]) 0) 38 false) (.node 139 (sourceLit (List.headD (raw_ints% [745706284943945621758883775]) 0) 56 false) (.node 138 (sourceLit (List.headD (raw_ints% [14702535022679212948696344919048875]) 0) 30 false) (.node 137 (sourceLit (List.headD (raw_ints% [24671785642674407977258015875]) 0) 51 false) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [723699746663857945928158275]) 0) 56 false) (.node 140 (sourceLit (List.headD (raw_ints% [257104278287552975452629180892563825]) 0) 26 false) .empty .empty) .empty)) (.node 168 (sourceLit (List.headD (raw_ints% [11098268718887738855321702122275]) 0) 43 false) (.node 167 (sourceLit (List.headD (raw_ints% [5245494058435157966485092428006625]) 0) 36 true) (.node 166 (sourceLit (List.headD (raw_ints% [180160903734223213857836210054625]) 0) 41 true) .empty .empty) .empty) (.node 170 (sourceLit (List.headD (raw_ints% [1262422753546403079291668146425]) 0) 46 false) (.node 169 (sourceLit (List.headD (raw_ints% [2012119094141510295150482857959375]) 0) 35 true) .empty .empty) .empty)))

#time def treeG_J002_part011 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [55168943623738933770831180788739225]) 0) 28 false) (.node 174 (sourceLit (List.headD (raw_ints% [277688755534725028616689941075]) 0) 48 false) (.node 173 (sourceLit (List.headD (raw_ints% [49881348633928538199119548826925]) 0) 31 true) (.node 172 (sourceLit (List.headD (raw_ints% [293977097355107366048024072325]) 0) 48 false) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [66189377418412569165474568425]) 0) 50 false) (.node 175 (sourceLit (List.headD (raw_ints% [17433669957143472503862574599090675]) 0) 29 false) .empty .empty) .empty)) (.node 180 (sourceLit (List.headD (raw_ints% [478733682432315691405268325]) 0) 57 false) (.node 179 (sourceLit (List.headD (raw_ints% [1086745110929277418353468421319892975]) 0) 24 false) (.node 178 (sourceLit (List.headD (raw_ints% [15881973216264480009385415025]) 0) 52 false) .empty .empty) .empty) (.node 206 (sourceLit (List.headD (raw_ints% [2952347757725565383161651187889375]) 0) 39 false) (.node 181 (sourceLit (List.headD (raw_ints% [2445042459008265712869701243005336575]) 0) 23 false) .empty .empty) .empty)))

#time def treeG_J002_part012 : IntSourceTree :=
  (.node 171 (sourceLit (List.headD (raw_ints% [4443324287225470461017336156648625]) 0) 32 true) treeG_J002_part010 treeG_J002_part011)

#time def treeG_J002_part013 : IntSourceTree :=
  (.node 136 (sourceLit (List.headD (raw_ints% [6336803771674266353535543764618325]) 0) 31 false) treeG_J002_part009 treeG_J002_part012)

#time def treeG_J002_part014 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [1313429733487671890576179990725]) 0) 45 false) treeG_J002_part006 treeG_J002_part013)

#time def treeG_J002_part015 : IntSourceTree :=
  (.node 214 (sourceLit (List.headD (raw_ints% [2424045281482961909773741783817775]) 0) 32 true) (.node 211 (sourceLit (List.headD (raw_ints% [811861097398528579611813521775]) 0) 47 false) (.node 209 (sourceLit (List.headD (raw_ints% [1814998369576815201540546459675]) 0) 46 false) (.node 208 (sourceLit (List.headD (raw_ints% [4989311501680135361808631690009875]) 0) 37 true) .empty .empty) (.node 210 (sourceLit (List.headD (raw_ints% [1912442954172947493098665962223125]) 0) 36 true) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [373922380731069088785196676775]) 0) 48 false) (.node 212 (sourceLit (List.headD (raw_ints% [4955986941451839738436083951733875]) 0) 33 true) .empty .empty) .empty)) (.node 217 (sourceLit (List.headD (raw_ints% [20758795887869080594108276275]) 0) 52 false) (.node 216 (sourceLit (List.headD (raw_ints% [4760062413794939796791487069854025]) 0) 30 false) (.node 215 (sourceLit (List.headD (raw_ints% [175213617900369760512283225275]) 0) 49 false) .empty .empty) .empty) (.node 219 (sourceLit (List.headD (raw_ints% [9916322936712915035314344825]) 0) 53 false) (.node 218 (sourceLit (List.headD (raw_ints% [25763873578380507873438490950641475]) 0) 29 false) .empty .empty) .empty)))

#time def treeG_J002_part016 : IntSourceTree :=
  (.node 251 (sourceLit (List.headD (raw_ints% [56754850246308849318139974634491375]) 0) 32 true) (.node 248 (sourceLit (List.headD (raw_ints% [51980363141814691099857945328725]) 0) 45 true) (.node 247 (sourceLit (List.headD (raw_ints% [52483058182044204097071511434236625]) 0) 36 false) (.node 221 (sourceLit (List.headD (raw_ints% [1191234983065404819692915025]) 0) 56 false) .empty .empty) .empty) (.node 250 (sourceLit (List.headD (raw_ints% [2367573985607227323789424772925]) 0) 46 false) (.node 249 (sourceLit (List.headD (raw_ints% [37902372919299572599318570662119625]) 0) 35 true) .empty .empty) .empty)) (.node 254 (sourceLit (List.headD (raw_ints% [470156005927413148953703412475]) 0) 48 false) (.node 253 (sourceLit (List.headD (raw_ints% [39598014182980789369289552065044075]) 0) 31 true) (.node 252 (sourceLit (List.headD (raw_ints% [258942000021710606781894724725]) 0) 49 false) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [54512120240978595673404328425]) 0) 51 false) (.node 255 (sourceLit (List.headD (raw_ints% [56218394460870863060242443140175075]) 0) 29 true) .empty .empty) .empty)))

#time def treeG_J002_part017 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [572536554354171467448210059534765325]) 0) 25 false) treeG_J002_part015 treeG_J002_part016)

#time def treeG_J002_part018 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [3362210094461969143837405736775]) 0) 50 true) (.node 260 (sourceLit (List.headD (raw_ints% [6086453477254389504072198225]) 0) 54 false) (.node 259 (sourceLit (List.headD (raw_ints% [562142798087075085546594999521161425]) 0) 24 false) (.node 258 (sourceLit (List.headD (raw_ints% [25635618559473681178831137525]) 0) 52 false) .empty .empty) .empty) (.node 288 (sourceLit (List.headD (raw_ints% [14368092420931084864720035781061625]) 0) 39 false) (.node 261 (sourceLit (List.headD (raw_ints% [2135249975825106026715979233272786025]) 0) 23 false) .empty .empty) .empty)) (.node 292 (sourceLit (List.headD (raw_ints% [12949715826214252394925972670689375]) 0) 35 true) (.node 291 (sourceLit (List.headD (raw_ints% [777856444104349372088805625575]) 0) 48 false) (.node 290 (sourceLit (List.headD (raw_ints% [8997482491281656276554976174974125]) 0) 38 true) .empty .empty) .empty) (.node 294 (sourceLit (List.headD (raw_ints% [9293492225374456864878952570306575]) 0) 34 true) (.node 293 (sourceLit (List.headD (raw_ints% [661845619355773338342382222125]) 0) 48 false) .empty .empty) .empty)))

#time def treeG_J002_part019 : IntSourceTree :=
  (.node 301 (sourceLit (List.headD (raw_ints% [3703983511123579864686368175]) 0) 55 false) (.node 298 (sourceLit (List.headD (raw_ints% [10713079472939980817484443795137125]) 0) 31 true) (.node 297 (sourceLit (List.headD (raw_ints% [16876662176554757539648026075]) 0) 53 false) (.node 296 (sourceLit (List.headD (raw_ints% [15244614218666450714258482552507275]) 0) 32 true) .empty .empty) .empty) (.node 300 (sourceLit (List.headD (raw_ints% [2598439066774095475403765003400975]) 0) 27 true) (.node 299 (sourceLit (List.headD (raw_ints% [3929823905690191535879198175]) 0) 55 false) .empty .empty) .empty)) (.node 332 (sourceLit (List.headD (raw_ints% [259457222041319382653455450425]) 0) 50 false) (.node 331 (sourceLit (List.headD (raw_ints% [1094922908637743154080896975762196625]) 0) 32 true) (.node 330 (sourceLit (List.headD (raw_ints% [109958297008390239926586408349725]) 0) 46 true) .empty .empty) .empty) (.node 334 (sourceLit (List.headD (raw_ints% [853535232784133527731061031775]) 0) 48 false) (.node 333 (sourceLit (List.headD (raw_ints% [374792892255875287268341573397015925]) 0) 31 true) .empty .empty) .empty)))

#time def treeG_J002_part020 : IntSourceTree :=
  (.node 295 (sourceLit (List.headD (raw_ints% [4608474812922552944397190425]) 0) 55 false) treeG_J002_part018 treeG_J002_part019)

#time def treeG_J002_part021 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [17088444313379415396499284229907025]) 0) 28 true) treeG_J002_part017 treeG_J002_part020)

#time def treeG_J002_part022 : IntSourceTree :=
  (.node 341 (sourceLit (List.headD (raw_ints% [2218400025961877081928899713381617225]) 0) 23 true) (.node 338 (sourceLit (List.headD (raw_ints% [41871030146745348979760966775]) 0) 52 false) (.node 337 (sourceLit (List.headD (raw_ints% [470739210683947007459772157450325775]) 0) 28 true) (.node 336 (sourceLit (List.headD (raw_ints% [92959073772543098547305765175]) 0) 51 false) .empty .empty) .empty) (.node 340 (sourceLit (List.headD (raw_ints% [9632842145506376639444594475]) 0) 54 false) (.node 339 (sourceLit (List.headD (raw_ints% [3304691143159710174822612611076265425]) 0) 24 true) .empty .empty) .empty)) (.node 373 (sourceLit (List.headD (raw_ints% [1413812156974781722885261381275]) 0) 48 false) (.node 372 (sourceLit (List.headD (raw_ints% [1043124045332886144501193085079439125]) 0) 33 true) (.node 371 (sourceLit (List.headD (raw_ints% [111514009896598938670764019600875]) 0) 47 true) .empty .empty) .empty) (.node 375 (sourceLit (List.headD (raw_ints% [558592844757090139289640844575]) 0) 49 false) (.node 374 (sourceLit (List.headD (raw_ints% [337618923354377459808825763115789625]) 0) 32 true) .empty .empty) .empty)))

#time def treeG_J002_part023 : IntSourceTree :=
  (.node 412 (sourceLit (List.headD (raw_ints% [112551838784764216201377841402575]) 0) 48 true) (.node 379 (sourceLit (List.headD (raw_ints% [26151734523984582836244174075]) 0) 53 false) (.node 378 (sourceLit (List.headD (raw_ints% [427886892792187084189834382269777275]) 0) 29 true) (.node 377 (sourceLit (List.headD (raw_ints% [59205749419433583468009713025]) 0) 52 false) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [1482214658595699193689556575]) 0) 57 false) (.node 380 (sourceLit (List.headD (raw_ints% [3294297386892613792920997551062661525]) 0) 25 true) .empty .empty) .empty)) (.node 415 (sourceLit (List.headD (raw_ints% [4863337665706944980649201688493188275]) 0) 29 true) (.node 414 (sourceLit (List.headD (raw_ints% [1974089081165429918039461730775]) 0) 48 false) (.node 413 (sourceLit (List.headD (raw_ints% [7970199470407213868741203107238497075]) 0) 31 true) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [3349953998023481580020040571745007225]) 0) 28 true) (.node 416 (sourceLit (List.headD (raw_ints% [372674697212003942195029314225]) 0) 50 false) .empty .empty) .empty)))

#time def treeG_J002_part024 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [477586651088428573434976591149416625]) 0) 30 true) treeG_J002_part022 treeG_J002_part023)

#time def treeG_J002_part025 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [2192875507309258203607112548671885825]) 0) 31 true) (.node 421 (sourceLit (List.headD (raw_ints% [24135979069179033261439080695119674975]) 0) 23 true) (.node 420 (sourceLit (List.headD (raw_ints% [1032430773654887887299973725]) 0) 58 false) (.node 419 (sourceLit (List.headD (raw_ints% [24080069995540263213326787854189480175]) 0) 24 true) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [176937029551042472343727610775]) 0) 52 false) (.node 454 (sourceLit (List.headD (raw_ints% [3816290273526418204466188672061353725]) 0) 33 true) .empty .empty) .empty)) (.node 459 (sourceLit (List.headD (raw_ints% [3149295885508577195000892825]) 0) 57 false) (.node 458 (sourceLit (List.headD (raw_ints% [1461033552615647247915103094737614975]) 0) 30 true) (.node 457 (sourceLit (List.headD (raw_ints% [254263198373136775259009888175]) 0) 51 false) .empty .empty) .empty) (.node 461 (sourceLit (List.headD (raw_ints% [2647508436023852355510338325]) 0) 57 false) (.node 460 (sourceLit (List.headD (raw_ints% [10392886304323824710202895151563409325]) 0) 26 true) .empty .empty) .empty)))

#time def treeG_J002_part026 : IntSourceTree :=
  (.node 501 (sourceLit (List.headD (raw_ints% [142150201800002162101807241729894874225]) 0) 23 true) (.node 498 (sourceLit (List.headD (raw_ints% [44430682420253739325687857225]) 0) 54 false) (.node 497 (sourceLit (List.headD (raw_ints% [31736054118924649677693760207005165975]) 0) 28 true) (.node 496 (sourceLit (List.headD (raw_ints% [1042821539196335836554791571975]) 0) 50 false) .empty .empty) .empty) (.node 500 (sourceLit (List.headD (raw_ints% [529216277963422326925229775]) 0) 60 false) (.node 499 (sourceLit (List.headD (raw_ints% [162932224739262584519806408272225236625]) 0) 24 true) .empty .empty) .empty)) (.node 539 (sourceLit (List.headD (raw_ints% [31833498878219430545684285925]) 0) 55 false) (.node 538 (sourceLit (List.headD (raw_ints% [28813987013693355181863554017529936025]) 0) 29 true) (.node 537 (sourceLit (List.headD (raw_ints% [98569792602899882661972710475]) 0) 54 false) .empty .empty) .empty) (.node 541 (sourceLit (List.headD (raw_ints% [5819952011390904875293338075]) 0) 57 false) (.node 540 (sourceLit (List.headD (raw_ints% [142146452130614935099400617969098417975]) 0) 25 true) .empty .empty) .empty)))

#time def treeG_J002_part027 : IntSourceTree :=
  (.node 495 (sourceLit (List.headD (raw_ints% [117257951087138437562268835817470130925]) 0) 29 true) treeG_J002_part025 treeG_J002_part026)

#time def treeG_J002_part028 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [76540468692121817956258459275]) 0) 52 false) treeG_J002_part024 treeG_J002_part027)

#time def treeG_J002_part029 : IntSourceTree :=
  (.node 335 (sourceLit (List.headD (raw_ints% [538565107963094376292010521359445725]) 0) 29 true) treeG_J002_part021 treeG_J002_part028)

#time def treeG_J002_part030 : IntSourceTree :=
  (.node 207 (sourceLit (List.headD (raw_ints% [196823183848371025544110079192625]) 0) 42 true) treeG_J002_part014 treeG_J002_part029)

#time def treeG_J002 : IntSourceTree := treeG_J002_part030

#time def treeG_J003_part000 : IntSourceTree :=
  (.node 8 (sourceLit (List.headD (raw_ints% [54003640012818353947476915152625]) 0) 36 true) (.node 4 (sourceLit (List.headD (raw_ints% [57276587892383102671566425161875]) 0) 39 true) (.node 2 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 false) (.node 1 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 37 false) .empty .empty) (.node 3 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 38 true) .empty .empty)) (.node 6 (sourceLit (List.headD (raw_ints% [32283167721161385142155621454875]) 0) 38 true) (.node 5 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 false) .empty .empty) (.node 7 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 41 false) .empty .empty))) (.node 12 (sourceLit (List.headD (raw_ints% [2402866693950428470991334483375]) 0) 32 false) (.node 10 (sourceLit (List.headD (raw_ints% [39225784435389640011436400262375]) 0) 35 true) (.node 9 (sourceLit (List.headD (raw_ints% [862868077339797390896325366075]) 0) 44 false) .empty .empty) (.node 11 (sourceLit (List.headD (raw_ints% [412306421191922891216470741425]) 0) 45 false) .empty .empty)) (.node 14 (sourceLit (List.headD (raw_ints% [413408273021435066953944849558075]) 0) 31 false) (.node 13 (sourceLit (List.headD (raw_ints% [99137303606388623952809636775]) 0) 47 false) .empty .empty) .empty)))

#time def treeG_J003_part001 : IntSourceTree :=
  (.node 23 (sourceLit (List.headD (raw_ints% [168123321346386760710657525]) 0) 56 false) (.node 19 (sourceLit (List.headD (raw_ints% [1412081073429181496900765325]) 0) 53 false) (.node 17 (sourceLit (List.headD (raw_ints% [2903493643317072740418532875]) 0) 52 false) (.node 16 (sourceLit (List.headD (raw_ints% [2788533352548048609916963618342275]) 0) 29 false) .empty .empty) (.node 18 (sourceLit (List.headD (raw_ints% [7232141599960115871933855464592225]) 0) 28 false) .empty .empty)) (.node 21 (sourceLit (List.headD (raw_ints% [344190663382661775486303525]) 0) 55 false) (.node 20 (sourceLit (List.headD (raw_ints% [135717180536110288094070600584307375]) 0) 24 false) .empty .empty) (.node 22 (sourceLit (List.headD (raw_ints% [302466939381683115631763441087478375]) 0) 23 false) .empty .empty))) (.node 27 (sourceLit (List.headD (raw_ints% [10076467348591616515848525]) 0) 60 false) (.node 25 (sourceLit (List.headD (raw_ints% [20564835608788960755090375]) 0) 59 false) (.node 24 (sourceLit (List.headD (raw_ints% [1308160951860274259364296845120065825]) 0) 21 false) .empty .empty) (.node 26 (sourceLit (List.headD (raw_ints% [2774552942499584100904661137462202175]) 0) 20 false) .empty .empty)) (.node 29 (sourceLit (List.headD (raw_ints% [2471753826752411630663487]) 0) 62 false) (.node 28 (sourceLit (List.headD (raw_ints% [23228764209513386927820352865695003875]) 0) 17 false) .empty .empty) .empty)))

#time def treeG_J003_part002 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [47899734789210989900606278875]) 0) 48 false) treeG_J003_part000 treeG_J003_part001)

#time def treeG_J003_part003 : IntSourceTree :=
  (.node 45 (sourceLit (List.headD (raw_ints% [57276587892383102671566425161875]) 0) 40 true) (.node 34 (sourceLit (List.headD (raw_ints% [406073904433779631422615862668736652145]) 0) 13 false) (.node 32 (sourceLit (List.headD (raw_ints% [198297574365996166009357310450762436075]) 0) 14 false) (.node 31 (sourceLit (List.headD (raw_ints% [1213974169562333931240203]) 0) 63 false) .empty .empty) (.node 33 (sourceLit (List.headD (raw_ints% [37300634875283502525803]) 0) 68 false) .empty .empty)) (.node 43 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 41 false) (.node 42 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 38 false) .empty .empty) (.node 44 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 true) .empty .empty))) (.node 49 (sourceLit (List.headD (raw_ints% [54003640012818353947476915152625]) 0) 37 true) (.node 47 (sourceLit (List.headD (raw_ints% [32283167721161385142155621454875]) 0) 39 true) (.node 46 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 41 false) .empty .empty) (.node 48 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 42 false) .empty .empty)) (.node 51 (sourceLit (List.headD (raw_ints% [39225784435389640011436400262375]) 0) 36 true) (.node 50 (sourceLit (List.headD (raw_ints% [862868077339797390896325366075]) 0) 45 false) .empty .empty) .empty)))

#time def treeG_J003_part004 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [1412081073429181496900765325]) 0) 54 false) (.node 56 (sourceLit (List.headD (raw_ints% [47899734789210989900606278875]) 0) 49 false) (.node 54 (sourceLit (List.headD (raw_ints% [99137303606388623952809636775]) 0) 48 false) (.node 53 (sourceLit (List.headD (raw_ints% [2402866693950428470991334483375]) 0) 33 false) .empty .empty) (.node 55 (sourceLit (List.headD (raw_ints% [413408273021435066953944849558075]) 0) 32 false) .empty .empty)) (.node 58 (sourceLit (List.headD (raw_ints% [2903493643317072740418532875]) 0) 53 false) (.node 57 (sourceLit (List.headD (raw_ints% [2788533352548048609916963618342275]) 0) 30 false) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [7232141599960115871933855464592225]) 0) 29 false) .empty .empty))) (.node 64 (sourceLit (List.headD (raw_ints% [168123321346386760710657525]) 0) 57 false) (.node 62 (sourceLit (List.headD (raw_ints% [344190663382661775486303525]) 0) 56 false) (.node 61 (sourceLit (List.headD (raw_ints% [135717180536110288094070600584307375]) 0) 25 false) .empty .empty) (.node 63 (sourceLit (List.headD (raw_ints% [302466939381683115631763441087478375]) 0) 24 false) .empty .empty)) (.node 66 (sourceLit (List.headD (raw_ints% [20564835608788960755090375]) 0) 60 false) (.node 65 (sourceLit (List.headD (raw_ints% [1308160951860274259364296845120065825]) 0) 22 false) .empty .empty) .empty)))

#time def treeG_J003_part005 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [412306421191922891216470741425]) 0) 46 false) treeG_J003_part003 treeG_J003_part004)

#time def treeG_J003_part006 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [48159381540934600133432941042892983575]) 0) 16 false) treeG_J003_part002 treeG_J003_part005)

#time def treeG_J003_part007 : IntSourceTree :=
  (.node 83 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 38 false) (.node 71 (sourceLit (List.headD (raw_ints% [48159381540934600133432941042892983575]) 0) 17 false) (.node 69 (sourceLit (List.headD (raw_ints% [23228764209513386927820352865695003875]) 0) 18 false) (.node 68 (sourceLit (List.headD (raw_ints% [10076467348591616515848525]) 0) 61 false) .empty .empty) (.node 70 (sourceLit (List.headD (raw_ints% [2471753826752411630663487]) 0) 63 false) .empty .empty)) (.node 73 (sourceLit (List.headD (raw_ints% [198297574365996166009357310450762436075]) 0) 15 false) (.node 72 (sourceLit (List.headD (raw_ints% [1213974169562333931240203]) 0) 64 false) .empty .empty) (.node 74 (sourceLit (List.headD (raw_ints% [37300634875283502525803]) 0) 69 false) .empty .empty))) (.node 87 (sourceLit (List.headD (raw_ints% [23952027664087479299018686885875]) 0) 41 false) (.node 85 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 42 true) (.node 84 (sourceLit (List.headD (raw_ints% [182243688748491690318620443696875]) 0) 39 false) .empty .empty) (.node 86 (sourceLit (List.headD (raw_ints% [425929535417903436230375779840125]) 0) 38 true) .empty .empty)) (.node 89 (sourceLit (List.headD (raw_ints% [5564011395260072830952167015725]) 0) 43 false) (.node 88 (sourceLit (List.headD (raw_ints% [462527043525763808327013028125375]) 0) 36 true) .empty .empty) .empty)))

#time def treeG_J003_part008 : IntSourceTree :=
  (.node 98 (sourceLit (List.headD (raw_ints% [15076125220424273007401853482145975]) 0) 28 false) (.node 94 (sourceLit (List.headD (raw_ints% [394185339469831639186014173691075]) 0) 31 true) (.node 92 (sourceLit (List.headD (raw_ints% [1257627968626418908836956142879375]) 0) 32 true) (.node 91 (sourceLit (List.headD (raw_ints% [1313429733487671890576179990725]) 0) 45 false) .empty .empty) (.node 93 (sourceLit (List.headD (raw_ints% [156584558792767133631830552325]) 0) 48 false) .empty .empty)) (.node 96 (sourceLit (List.headD (raw_ints% [3825999015794912461346153974586925]) 0) 29 false) (.node 95 (sourceLit (List.headD (raw_ints% [150374872423566258005012994675]) 0) 48 false) .empty .empty) (.node 97 (sourceLit (List.headD (raw_ints% [36285760215942698938932147375]) 0) 50 false) .empty .empty))) (.node 102 (sourceLit (List.headD (raw_ints% [783270504907199189120801363586980625]) 0) 23 false) (.node 100 (sourceLit (List.headD (raw_ints% [327139881861337127709696149149595025]) 0) 24 false) (.node 99 (sourceLit (List.headD (raw_ints% [4394906213204963983936300425]) 0) 53 false) .empty .empty) (.node 101 (sourceLit (List.headD (raw_ints% [133486301255814965176807725]) 0) 58 false) .empty .empty)) (.node 104 (sourceLit (List.headD (raw_ints% [3531310078246655590743918212279588175]) 0) 21 false) (.node 103 (sourceLit (List.headD (raw_ints% [520258005418936790261949525]) 0) 56 false) .empty .empty) .empty)))

#time def treeG_J003_part009 : IntSourceTree :=
  (.node 90 (sourceLit (List.headD (raw_ints% [392803335667157191568378920958625]) 0) 35 true) treeG_J003_part007 treeG_J003_part008)

#time def treeG_J003_part010 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [915569090560065911033779]) 0) 65 false) (.node 109 (sourceLit (List.headD (raw_ints% [3802356760919602442592519]) 0) 63 false) (.node 107 (sourceLit (List.headD (raw_ints% [31053203868986304994332225]) 0) 60 false) (.node 106 (sourceLit (List.headD (raw_ints% [7690734672382609974009713623498324425]) 0) 20 false) .empty .empty) (.node 108 (sourceLit (List.headD (raw_ints% [65556929950473304301128803533095465725]) 0) 17 false) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [3729533483942489330086771]) 0) 63 false) (.node 110 (sourceLit (List.headD (raw_ints% [137670732135172495289129881882667047425]) 0) 16 false) .empty .empty) (.node 112 (sourceLit (List.headD (raw_ints% [572252530288957436125569746235525301125]) 0) 14 false) .empty .empty))) (.node 126 (sourceLit (List.headD (raw_ints% [78104438035067867279408761584375]) 0) 41 true) (.node 124 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 41 false) (.node 114 (sourceLit (List.headD (raw_ints% [1180306690494189696652242620937362836455]) 0) 13 false) .empty .empty) (.node 125 (sourceLit (List.headD (raw_ints% [119760138320437396495093434429375]) 0) 41 false) .empty .empty)) (.node 128 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 46 false) (.node 127 (sourceLit (List.headD (raw_ints% [196823183848371025544110079192625]) 0) 40 true) .empty .empty) .empty)))

#time def treeG_J003_part011 : IntSourceTree :=
  (.node 136 (sourceLit (List.headD (raw_ints% [12809392204294408513050839475]) 0) 52 false) (.node 133 (sourceLit (List.headD (raw_ints% [630015417660184668653973738681375]) 0) 34 true) (.node 131 (sourceLit (List.headD (raw_ints% [176788775615883775778471260348125]) 0) 37 true) (.node 130 (sourceLit (List.headD (raw_ints% [3838275240580478049159516283575]) 0) 44 false) .empty .empty) (.node 132 (sourceLit (List.headD (raw_ints% [225280828073937249839927312325]) 0) 48 false) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [403796806245633353069979511624575]) 0) 33 true) (.node 134 (sourceLit (List.headD (raw_ints% [214031813979145643310851467875]) 0) 48 false) .empty .empty) .empty)) (.node 140 (sourceLit (List.headD (raw_ints% [745706284943945621758883775]) 0) 56 false) (.node 138 (sourceLit (List.headD (raw_ints% [24671785642674407977258015875]) 0) 51 false) (.node 137 (sourceLit (List.headD (raw_ints% [518732831623431925714595178122325]) 0) 31 false) .empty .empty) (.node 139 (sourceLit (List.headD (raw_ints% [3921991810232078567733999008776875]) 0) 30 false) .empty .empty)) (.node 142 (sourceLit (List.headD (raw_ints% [723699746663857945928158275]) 0) 56 false) (.node 141 (sourceLit (List.headD (raw_ints% [95711350662613419807812774282643825]) 0) 26 false) .empty .empty) .empty)))

#time def treeG_J003_part012 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [204261701756472727189768056486375]) 0) 38 true) treeG_J003_part010 treeG_J003_part011)

#time def treeG_J003_part013 : IntSourceTree :=
  (.node 105 (sourceLit (List.headD (raw_ints% [126993650128808839200476775]) 0) 58 false) treeG_J003_part009 treeG_J003_part012)

#time def treeG_J003_part014 : IntSourceTree :=
  (.node 67 (sourceLit (List.headD (raw_ints% [2774552942499584100904661137462202175]) 0) 21 false) treeG_J003_part006 treeG_J003_part013)

#time def treeG_J003_part015 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [44755675297118947577848470419887031925]) 0) 18 false) (.node 147 (sourceLit (List.headD (raw_ints% [2458090864941512936552526243018061125]) 0) 22 false) (.node 145 (sourceLit (List.headD (raw_ints% [1111574563193190665689810683579761175]) 0) 23 false) (.node 144 (sourceLit (List.headD (raw_ints% [11004208877267188423477875]) 0) 62 false) .empty .empty) (.node 146 (sourceLit (List.headD (raw_ints% [85863978911230917690296025]) 0) 59 false) .empty .empty)) (.node 149 (sourceLit (List.headD (raw_ints% [21164082870479958686654225333700230925]) 0) 19 false) (.node 148 (sourceLit (List.headD (raw_ints% [5244184130098672119620925]) 0) 63 false) .empty .empty) (.node 150 (sourceLit (List.headD (raw_ints% [5132959695086793254521551]) 0) 63 false) .empty .empty))) (.node 165 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 44 false) (.node 153 (sourceLit (List.headD (raw_ints% [186977477961480635058106217892381432525]) 0) 16 false) (.node 152 (sourceLit (List.headD (raw_ints% [314444914297519424855821]) 0) 67 false) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [617164011557797890827355]) 0) 66 false) .empty .empty)) (.node 167 (sourceLit (List.headD (raw_ints% [180160903734223213857836210054625]) 0) 41 true) (.node 166 (sourceLit (List.headD (raw_ints% [2342091748544901780151870730710125]) 0) 38 false) .empty .empty) .empty)))

#time def treeG_J003_part016 : IntSourceTree :=
  (.node 176 (sourceLit (List.headD (raw_ints% [16747496815655179759585498346573325]) 0) 29 true) (.node 172 (sourceLit (List.headD (raw_ints% [10056853670790142740985204519400625]) 0) 32 true) (.node 170 (sourceLit (List.headD (raw_ints% [2875383892436406443467909982823375]) 0) 35 true) (.node 169 (sourceLit (List.headD (raw_ints% [11098268718887738855321702122275]) 0) 43 false) .empty .empty) (.node 171 (sourceLit (List.headD (raw_ints% [1262422753546403079291668146425]) 0) 46 false) .empty .empty)) (.node 174 (sourceLit (List.headD (raw_ints% [9686061343093123059277565645210925]) 0) 31 true) (.node 173 (sourceLit (List.headD (raw_ints% [293977097355107366048024072325]) 0) 48 false) .empty .empty) (.node 175 (sourceLit (List.headD (raw_ints% [277688755534725028616689941075]) 0) 48 false) .empty .empty))) (.node 180 (sourceLit (List.headD (raw_ints% [174875069848368928960255723973844975]) 0) 24 false) (.node 178 (sourceLit (List.headD (raw_ints% [6776399914449362195968330632188775]) 0) 28 true) (.node 177 (sourceLit (List.headD (raw_ints% [66189377418412569165474568425]) 0) 50 false) .empty .empty) (.node 179 (sourceLit (List.headD (raw_ints% [15881973216264480009385415025]) 0) 52 false) .empty .empty)) (.node 182 (sourceLit (List.headD (raw_ints% [748111105694615527804203024935320575]) 0) 23 false) (.node 181 (sourceLit (List.headD (raw_ints% [478733682432315691405268325]) 0) 57 false) .empty .empty) .empty)))

#time def treeG_J003_part017 : IntSourceTree :=
  (.node 168 (sourceLit (List.headD (raw_ints% [5835814839622109009084509506038625]) 0) 36 true) treeG_J003_part015 treeG_J003_part016)

#time def treeG_J003_part018 : IntSourceTree :=
  (.node 191 (sourceLit (List.headD (raw_ints% [6536385906231097178956331]) 0) 63 false) (.node 187 (sourceLit (List.headD (raw_ints% [6851346880280576586995475]) 0) 63 false) (.node 185 (sourceLit (List.headD (raw_ints% [225141033943741190350815225]) 0) 58 false) (.node 184 (sourceLit (List.headD (raw_ints% [4161546970161601585080688547712447825]) 0) 21 false) .empty .empty) (.node 186 (sourceLit (List.headD (raw_ints% [10094458338708440677027257313777854375]) 0) 20 false) .empty .empty)) (.node 189 (sourceLit (List.headD (raw_ints% [6686011499277741796649331]) 0) 63 false) (.node 188 (sourceLit (List.headD (raw_ints% [91760885405783523638232876020060446275]) 0) 17 false) .empty .empty) (.node 190 (sourceLit (List.headD (raw_ints% [200954593792506843697337723456536647375]) 0) 16 false) .empty .empty))) (.node 206 (sourceLit (List.headD (raw_ints% [328038639747285042573516798654375]) 0) 41 false) (.node 193 (sourceLit (List.headD (raw_ints% [1599990223820089487812789]) 0) 65 false) (.node 192 (sourceLit (List.headD (raw_ints% [859929079218848886365581307200859720475]) 0) 14 false) .empty .empty) (.node 194 (sourceLit (List.headD (raw_ints% [1811332956889500464277456865340740083945]) 0) 13 false) .empty .empty)) (.node 208 (sourceLit (List.headD (raw_ints% [196823183848371025544110079192625]) 0) 42 true) (.node 207 (sourceLit (List.headD (raw_ints% [2735738116241643831240090889095375]) 0) 39 false) .empty .empty) .empty)))

#time def treeG_J003_part019 : IntSourceTree :=
  (.node 216 (sourceLit (List.headD (raw_ints% [175213617900369760512283225275]) 0) 49 false) (.node 213 (sourceLit (List.headD (raw_ints% [8796822835469773403677257042037875]) 0) 33 true) (.node 211 (sourceLit (List.headD (raw_ints% [2521806341204638891910967462127125]) 0) 36 true) (.node 210 (sourceLit (List.headD (raw_ints% [1814998369576815201540546459675]) 0) 46 false) .empty .empty) (.node 212 (sourceLit (List.headD (raw_ints% [811861097398528579611813521775]) 0) 47 false) .empty .empty)) (.node 215 (sourceLit (List.headD (raw_ints% [8878467730601856353137606621961775]) 0) 32 true) (.node 214 (sourceLit (List.headD (raw_ints% [373922380731069088785196676775]) 0) 48 false) .empty .empty) .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [9916322936712915035314344825]) 0) 53 false) (.node 218 (sourceLit (List.headD (raw_ints% [20758795887869080594108276275]) 0) 52 false) (.node 217 (sourceLit (List.headD (raw_ints% [17784962478902043611014688702817975]) 0) 30 true) .empty .empty) (.node 219 (sourceLit (List.headD (raw_ints% [14620383534913519331436328649742525]) 0) 29 true) .empty .empty)) (.node 222 (sourceLit (List.headD (raw_ints% [1191234983065404819692915025]) 0) 56 false) (.node 221 (sourceLit (List.headD (raw_ints% [16547631476857910655369824591442675]) 0) 25 true) .empty .empty) .empty)))

#time def treeG_J003_part020 : IntSourceTree :=
  (.node 209 (sourceLit (List.headD (raw_ints% [5427291436109163554704973393065875]) 0) 37 true) treeG_J003_part018 treeG_J003_part019)

#time def treeG_J003_part021 : IntSourceTree :=
  (.node 183 (sourceLit (List.headD (raw_ints% [927141487908779101594367025]) 0) 56 false) treeG_J003_part017 treeG_J003_part020)

#time def treeG_J003_part022 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [111443243198268948541640782616762583525]) 0) 17 false) (.node 227 (sourceLit (List.headD (raw_ints% [5178276608825414803922204827741732125]) 0) 21 false) (.node 225 (sourceLit (List.headD (raw_ints% [1938397843775220253701067180552925475]) 0) 22 false) (.node 224 (sourceLit (List.headD (raw_ints% [575006803836229072043075025]) 0) 57 false) .empty .empty) (.node 226 (sourceLit (List.headD (raw_ints% [4352407969765946020641225]) 0) 64 false) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [49432719664823606264924425352659984425]) 0) 18 false) (.node 228 (sourceLit (List.headD (raw_ints% [8458509630462481054370025]) 0) 63 false) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [8239063303468690338777111]) 0) 63 false) .empty .empty))) (.node 247 (sourceLit (List.headD (raw_ints% [836238183228793299004869807363375]) 0) 41 false) (.node 233 (sourceLit (List.headD (raw_ints% [485974123295887616249368871416096855425]) 0) 15 false) (.node 232 (sourceLit (List.headD (raw_ints% [4020826591850941780109763]) 0) 64 false) .empty .empty) (.node 234 (sourceLit (List.headD (raw_ints% [491413106131145798492717]) 0) 67 false) .empty .empty)) (.node 249 (sourceLit (List.headD (raw_ints% [51980363141814691099857945328725]) 0) 45 true) (.node 248 (sourceLit (List.headD (raw_ints% [49607624699488410308925963731564625]) 0) 36 false) .empty .empty) .empty)))

#time def treeG_J003_part023 : IntSourceTree :=
  (.node 258 (sourceLit (List.headD (raw_ints% [135503299916766986692149178990355025]) 0) 28 true) (.node 254 (sourceLit (List.headD (raw_ints% [60688521340665064170140490691092075]) 0) 31 true) (.node 252 (sourceLit (List.headD (raw_ints% [70640949247758301800165754268667375]) 0) 32 true) (.node 251 (sourceLit (List.headD (raw_ints% [2367573985607227323789424772925]) 0) 46 false) .empty .empty) (.node 253 (sourceLit (List.headD (raw_ints% [258942000021710606781894724725]) 0) 49 false) .empty .empty)) (.node 256 (sourceLit (List.headD (raw_ints% [125307986873974521890616207604815075]) 0) 29 true) (.node 255 (sourceLit (List.headD (raw_ints% [470156005927413148953703412475]) 0) 48 false) .empty .empty) (.node 257 (sourceLit (List.headD (raw_ints% [54512120240978595673404328425]) 0) 51 false) .empty .empty))) (.node 262 (sourceLit (List.headD (raw_ints% [880492157509478813047161621666861975]) 0) 23 true) (.node 260 (sourceLit (List.headD (raw_ints% [1110579616082834166172180757557366575]) 0) 24 true) (.node 259 (sourceLit (List.headD (raw_ints% [25635618559473681178831137525]) 0) 52 false) .empty .empty) (.node 261 (sourceLit (List.headD (raw_ints% [6086453477254389504072198225]) 0) 54 false) .empty .empty)) (.node 264 (sourceLit (List.headD (raw_ints% [115373672543989683961953091260645375]) 0) 21 false) (.node 263 (sourceLit (List.headD (raw_ints% [1455328478222030537791463025]) 0) 56 false) .empty .empty) .empty)))

#time def treeG_J003_part024 : IntSourceTree :=
  (.node 250 (sourceLit (List.headD (raw_ints% [40542947596436901994171877161703625]) 0) 35 true) treeG_J003_part022 treeG_J003_part023)

#time def treeG_J003_part025 : IntSourceTree :=
  (.node 273 (sourceLit (List.headD (raw_ints% [1210418184015426146148487]) 0) 66 false) (.node 269 (sourceLit (List.headD (raw_ints% [10231007761647220312090719]) 0) 63 false) (.node 267 (sourceLit (List.headD (raw_ints% [10558284998783207495569425]) 0) 63 false) (.node 266 (sourceLit (List.headD (raw_ints% [5412724411493321352581280130645549425]) 0) 20 false) .empty .empty) (.node 268 (sourceLit (List.headD (raw_ints% [73943966076629750087277678467674981725]) 0) 17 false) .empty .empty)) (.node 271 (sourceLit (List.headD (raw_ints% [9941740700706283498597891]) 0) 63 false) (.node 270 (sourceLit (List.headD (raw_ints% [194507163526082006422057679364743228025]) 0) 16 false) .empty .empty) (.node 272 (sourceLit (List.headD (raw_ints% [923162811953454290300671214667341615925]) 0) 14 false) .empty .empty))) (.node 290 (sourceLit (List.headD (raw_ints% [3362210094461969143837405736775]) 0) 50 true) (.node 288 (sourceLit (List.headD (raw_ints% [32283167721161385142155621454875]) 0) 47 false) (.node 274 (sourceLit (List.headD (raw_ints% [2076460029477600465717494105988034759455]) 0) 13 false) .empty .empty) (.node 289 (sourceLit (List.headD (raw_ints% [13758729033899393465907734281157625]) 0) 39 false) .empty .empty)) (.node 292 (sourceLit (List.headD (raw_ints% [777856444104349372088805625575]) 0) 48 false) (.node 291 (sourceLit (List.headD (raw_ints% [9505285313808065775565227424894125]) 0) 38 true) .empty .empty) .empty)))

#time def treeG_J003_part026 : IntSourceTree :=
  (.node 300 (sourceLit (List.headD (raw_ints% [3929823905690191535879198175]) 0) 55 false) (.node 297 (sourceLit (List.headD (raw_ints% [26880756098768119569900379725499275]) 0) 32 true) (.node 295 (sourceLit (List.headD (raw_ints% [12952513402515801954250721017282575]) 0) 34 true) (.node 294 (sourceLit (List.headD (raw_ints% [661845619355773338342382222125]) 0) 48 false) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [4608474812922552944397190425]) 0) 55 false) .empty .empty)) (.node 299 (sourceLit (List.headD (raw_ints% [30220729095463366840178212585153125]) 0) 31 true) (.node 298 (sourceLit (List.headD (raw_ints% [16876662176554757539648026075]) 0) 53 false) .empty .empty) .empty)) (.node 304 (sourceLit (List.headD (raw_ints% [27510052324556295804637125]) 0) 62 false) (.node 302 (sourceLit (List.headD (raw_ints% [3703983511123579864686368175]) 0) 55 false) (.node 301 (sourceLit (List.headD (raw_ints% [273507996151494063879202733241480975]) 0) 27 true) .empty .empty) (.node 303 (sourceLit (List.headD (raw_ints% [286949924419644566840581681025670075]) 0) 26 true) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [26323589357497201128967575]) 0) 62 false) (.node 305 (sourceLit (List.headD (raw_ints% [455756042807807642434778522323070025]) 0) 24 true) .empty .empty) .empty)))

#time def treeG_J003_part027 : IntSourceTree :=
  (.node 293 (sourceLit (List.headD (raw_ints% [15461031603072132099122124306657375]) 0) 35 true) treeG_J003_part025 treeG_J003_part026)

#time def treeG_J003_part028 : IntSourceTree :=
  (.node 265 (sourceLit (List.headD (raw_ints% [43733221236560985211532475]) 0) 61 false) treeG_J003_part024 treeG_J003_part027)

#time def treeG_J003_part029 : IntSourceTree :=
  (.node 223 (sourceLit (List.headD (raw_ints% [267307540169099454315165102435818325]) 0) 24 false) treeG_J003_part021 treeG_J003_part028)

#time def treeG_J003_part030 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [240401782762758036744518961249751125]) 0) 25 false) treeG_J003_part014 treeG_J003_part029)

#time def treeG_J003_part031 : IntSourceTree :=
  (.node 330 (sourceLit (List.headD (raw_ints% [480822276681217492903219374158747625]) 0) 35 false) (.node 311 (sourceLit (List.headD (raw_ints% [20765980081953264470104224186995161125]) 0) 19 false) (.node 309 (sourceLit (List.headD (raw_ints% [6127811602951535955588313278753749325]) 0) 20 false) (.node 308 (sourceLit (List.headD (raw_ints% [12658060367103933936768825]) 0) 63 false) .empty .empty) (.node 310 (sourceLit (List.headD (raw_ints% [12222952219825750285404327]) 0) 63 false) .empty .empty)) (.node 313 (sourceLit (List.headD (raw_ints% [109297172164391668512825585812811190125]) 0) 17 false) (.node 312 (sourceLit (List.headD (raw_ints% [92514282950864714351377]) 0) 70 false) .empty .empty) (.node 314 (sourceLit (List.headD (raw_ints% [359502538942140173827885]) 0) 68 false) .empty .empty))) (.node 334 (sourceLit (List.headD (raw_ints% [434064489957643163001767487121943925]) 0) 31 true) (.node 332 (sourceLit (List.headD (raw_ints% [1146035570919674117472183356117780625]) 0) 32 true) (.node 331 (sourceLit (List.headD (raw_ints% [109958297008390239926586408349725]) 0) 46 true) .empty .empty) (.node 333 (sourceLit (List.headD (raw_ints% [259457222041319382653455450425]) 0) 50 false) .empty .empty)) (.node 336 (sourceLit (List.headD (raw_ints% [703652870887036803181429937501269725]) 0) 29 true) (.node 335 (sourceLit (List.headD (raw_ints% [853535232784133527731061031775]) 0) 48 false) .empty .empty) .empty)))

#time def treeG_J003_part032 : IntSourceTree :=
  (.node 345 (sourceLit (List.headD (raw_ints% [66306988061664198007016025]) 0) 61 false) (.node 341 (sourceLit (List.headD (raw_ints% [9632842145506376639444594475]) 0) 54 false) (.node 339 (sourceLit (List.headD (raw_ints% [41871030146745348979760966775]) 0) 52 false) (.node 338 (sourceLit (List.headD (raw_ints% [724680895243812839544662972225621775]) 0) 28 true) .empty .empty) (.node 340 (sourceLit (List.headD (raw_ints% [6625927032355787744913441664241833425]) 0) 24 true) .empty .empty)) (.node 343 (sourceLit (List.headD (raw_ints% [1124327516450774663447452575]) 0) 57 false) (.node 342 (sourceLit (List.headD (raw_ints% [7871763719338331231087325842060529225]) 0) 23 true) .empty .empty) (.node 344 (sourceLit (List.headD (raw_ints% [18480168835401241961759180676903530175]) 0) 21 true) .empty .empty))) (.node 349 (sourceLit (List.headD (raw_ints% [15085112972560647561446931]) 0) 63 false) (.node 347 (sourceLit (List.headD (raw_ints% [7882652179356996816699075]) 0) 64 false) (.node 346 (sourceLit (List.headD (raw_ints% [19996917781343165910494192844983790225]) 0) 20 true) .empty .empty) (.node 348 (sourceLit (List.headD (raw_ints% [66441636391256740530187268774752828125]) 0) 17 true) .empty .empty)) (.node 351 (sourceLit (List.headD (raw_ints% [14504163738945217072210763]) 0) 63 false) (.node 350 (sourceLit (List.headD (raw_ints% [1582807768367144156768345555376750375]) 0) 16 false) .empty .empty) .empty)))

#time def treeG_J003_part033 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [92959073772543098547305765175]) 0) 51 false) treeG_J003_part031 treeG_J003_part032)

#time def treeG_J003_part034 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [558592844757090139289640844575]) 0) 49 false) (.node 372 (sourceLit (List.headD (raw_ints% [111514009896598938670764019600875]) 0) 47 true) (.node 354 (sourceLit (List.headD (raw_ints% [1421049479782932926692924640021923324545]) 0) 13 false) (.node 353 (sourceLit (List.headD (raw_ints% [1750038870412244713095577]) 0) 66 false) .empty .empty) (.node 371 (sourceLit (List.headD (raw_ints% [518843417936449756005480283858324125]) 0) 36 false) .empty .empty)) (.node 374 (sourceLit (List.headD (raw_ints% [1413812156974781722885261381275]) 0) 48 false) (.node 373 (sourceLit (List.headD (raw_ints% [1084191444507385589075694858891151125]) 0) 33 true) .empty .empty) (.node 375 (sourceLit (List.headD (raw_ints% [382254436347579955184764603052813625]) 0) 32 true) .empty .empty))) (.node 380 (sourceLit (List.headD (raw_ints% [26151734523984582836244174075]) 0) 53 false) (.node 378 (sourceLit (List.headD (raw_ints% [59205749419433583468009713025]) 0) 52 false) (.node 377 (sourceLit (List.headD (raw_ints% [596129846491964324901828418599272625]) 0) 30 true) .empty .empty) (.node 379 (sourceLit (List.headD (raw_ints% [603797978861959372183950121885009275]) 0) 29 true) .empty .empty)) (.node 382 (sourceLit (List.headD (raw_ints% [1482214658595699193689556575]) 0) 57 false) (.node 381 (sourceLit (List.headD (raw_ints% [5531895047749811489396630731275909525]) 0) 25 true) .empty .empty) .empty)))

#time def treeG_J003_part035 : IntSourceTree :=
  (.node 390 (sourceLit (List.headD (raw_ints% [17947273725295544837489535]) 0) 63 false) (.node 387 (sourceLit (List.headD (raw_ints% [20231365584011072459153268147887607525]) 0) 21 true) (.node 385 (sourceLit (List.headD (raw_ints% [16657144664170011392020066587611250075]) 0) 22 true) (.node 384 (sourceLit (List.headD (raw_ints% [684166679257873930573258575]) 0) 58 false) .empty .empty) (.node 386 (sourceLit (List.headD (raw_ints% [19991699352083498439024225]) 0) 63 false) .empty .empty)) (.node 389 (sourceLit (List.headD (raw_ints% [90952882803062884352540521889767825425]) 0) 18 true) (.node 388 (sourceLit (List.headD (raw_ints% [18872548350324053330027475]) 0) 63 false) .empty .empty) .empty)) (.node 394 (sourceLit (List.headD (raw_ints% [1031033792527964365439807]) 0) 67 false) (.node 392 (sourceLit (List.headD (raw_ints% [8583249630089875353722635]) 0) 64 false) (.node 391 (sourceLit (List.headD (raw_ints% [81481112559445913723648551192603894125]) 0) 17 true) .empty .empty) (.node 393 (sourceLit (List.headD (raw_ints% [31328775366012038265303209950896064425]) 0) 15 true) .empty .empty)) (.node 413 (sourceLit (List.headD (raw_ints% [112551838784764216201377841402575]) 0) 48 true) (.node 412 (sourceLit (List.headD (raw_ints% [17749024944886066309647552439584152625]) 0) 32 false) .empty .empty) .empty)))

#time def treeG_J003_part036 : IntSourceTree :=
  (.node 383 (sourceLit (List.headD (raw_ints% [6723964021659752963724999117957848925]) 0) 24 true) treeG_J003_part034 treeG_J003_part035)

#time def treeG_J003_part037 : IntSourceTree :=
  (.node 352 (sourceLit (List.headD (raw_ints% [405859913291554635785999133300348696075]) 0) 14 false) treeG_J003_part033 treeG_J003_part036)

#time def treeG_J003_part038 : IntSourceTree :=
  (.node 422 (sourceLit (List.headD (raw_ints% [36383396662660160684085720008146746975]) 0) 23 true) (.node 418 (sourceLit (List.headD (raw_ints% [4044357876691901759669964376568559225]) 0) 28 true) (.node 416 (sourceLit (List.headD (raw_ints% [5412418110674242479774803711343748275]) 0) 29 true) (.node 415 (sourceLit (List.headD (raw_ints% [1974089081165429918039461730775]) 0) 48 false) .empty .empty) (.node 417 (sourceLit (List.headD (raw_ints% [372674697212003942195029314225]) 0) 50 false) .empty .empty)) (.node 420 (sourceLit (List.headD (raw_ints% [32017143614809612074859366136398760175]) 0) 24 true) (.node 419 (sourceLit (List.headD (raw_ints% [76540468692121817956258459275]) 0) 52 false) .empty .empty) (.node 421 (sourceLit (List.headD (raw_ints% [1032430773654887887299973725]) 0) 58 false) .empty .empty))) (.node 426 (sourceLit (List.headD (raw_ints% [113260239532016925225666339855906210375]) 0) 20 true) (.node 424 (sourceLit (List.headD (raw_ints% [89103255511154805457840805210422052625]) 0) 21 true) (.node 423 (sourceLit (List.headD (raw_ints% [1840101800740623723931660575]) 0) 57 false) .empty .empty) (.node 425 (sourceLit (List.headD (raw_ints% [418938727011217138545194475]) 0) 59 false) .empty .empty)) (.node 428 (sourceLit (List.headD (raw_ints% [580962062297097578162717311957650612675]) 0) 17 true) (.node 427 (sourceLit (List.headD (raw_ints% [6054523586363250811162575]) 0) 65 false) .empty .empty) .empty)))

#time def treeG_J003_part039 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [176937029551042472343727610775]) 0) 52 false) (.node 433 (sourceLit (List.headD (raw_ints% [5083171889265385927531481]) 0) 65 false) (.node 431 (sourceLit (List.headD (raw_ints% [21390383711645872602768307]) 0) 63 false) (.node 430 (sourceLit (List.headD (raw_ints% [729205870192870218977092520673519353775]) 0) 16 true) .empty .empty) (.node 432 (sourceLit (List.headD (raw_ints% [1709557714242689255364375952382011002075]) 0) 14 true) .empty .empty)) (.node 454 (sourceLit (List.headD (raw_ints% [226517489726503214125640944186425]) 0) 48 true) (.node 434 (sourceLit (List.headD (raw_ints% [1671679682711029232815350319629091839945]) 0) 13 true) .empty .empty) (.node 455 (sourceLit (List.headD (raw_ints% [3928606314876930797209513390477225725]) 0) 33 true) .empty .empty))) (.node 460 (sourceLit (List.headD (raw_ints% [3149295885508577195000892825]) 0) 57 false) (.node 458 (sourceLit (List.headD (raw_ints% [254263198373136775259009888175]) 0) 51 false) (.node 457 (sourceLit (List.headD (raw_ints% [2408144132091139077436487646372237825]) 0) 31 true) .empty .empty) (.node 459 (sourceLit (List.headD (raw_ints% [1720279948914971193743007127341774975]) 0) 30 true) .empty .empty)) (.node 462 (sourceLit (List.headD (raw_ints% [2647508436023852355510338325]) 0) 57 false) (.node 461 (sourceLit (List.headD (raw_ints% [13242624283529900292731367702561425325]) 0) 26 true) .empty .empty) .empty)))

#time def treeG_J003_part040 : IntSourceTree :=
  (.node 429 (sourceLit (List.headD (raw_ints% [22659983728087459098608019]) 0) 63 false) treeG_J003_part038 treeG_J003_part039)

#time def treeG_J003_part041 : IntSourceTree :=
  (.node 471 (sourceLit (List.headD (raw_ints% [323862378816712152626721984740457729825]) 0) 18 true) (.node 467 (sourceLit (List.headD (raw_ints% [46514436974002926383256535854009301425]) 0) 22 true) (.node 465 (sourceLit (List.headD (raw_ints% [36223055423492397032910369311405401275]) 0) 23 true) (.node 464 (sourceLit (List.headD (raw_ints% [72245945092671862084900125]) 0) 62 false) .empty .empty) (.node 466 (sourceLit (List.headD (raw_ints% [259005132194549151033000675]) 0) 60 false) .empty .empty)) (.node 469 (sourceLit (List.headD (raw_ints% [245004589747017346905088395033941393625]) 0) 19 true) (.node 468 (sourceLit (List.headD (raw_ints% [29563640340581953159273125]) 0) 63 false) .empty .empty) (.node 470 (sourceLit (List.headD (raw_ints% [27372693730879373359726503]) 0) 63 false) .empty .empty))) (.node 495 (sourceLit (List.headD (raw_ints% [455009068534171858169321350103625]) 0) 48 true) (.node 473 (sourceLit (List.headD (raw_ints% [839114469438338608549536371215557468825]) 0) 16 true) (.node 472 (sourceLit (List.headD (raw_ints% [1600891760194499656130709]) 0) 67 false) .empty .empty) (.node 474 (sourceLit (List.headD (raw_ints% [3021104304209457196651867]) 0) 66 false) .empty .empty)) (.node 497 (sourceLit (List.headD (raw_ints% [1042821539196335836554791571975]) 0) 50 false) (.node 496 (sourceLit (List.headD (raw_ints% [120302983965387543030929624783927474925]) 0) 29 true) .empty .empty) .empty)))

#time def treeG_J003_part042 : IntSourceTree :=
  (.node 505 (sourceLit (List.headD (raw_ints% [736996394471532654813207525]) 0) 59 false) (.node 502 (sourceLit (List.headD (raw_ints% [175498591873818243999616163232836058225]) 0) 23 true) (.node 500 (sourceLit (List.headD (raw_ints% [188178689846306700724245546163348436625]) 0) 24 true) (.node 499 (sourceLit (List.headD (raw_ints% [44430682420253739325687857225]) 0) 54 false) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [529216277963422326925229775]) 0) 60 false) .empty .empty)) (.node 504 (sourceLit (List.headD (raw_ints% [385447666744851718067930729032600316175]) 0) 21 true) (.node 503 (sourceLit (List.headD (raw_ints% [3454915071307080987089016075]) 0) 57 false) .empty .empty) .empty)) (.node 509 (sourceLit (List.headD (raw_ints% [36467296953076447219938231]) 0) 63 false) (.node 507 (sourceLit (List.headD (raw_ints% [162132754812737138054399475]) 0) 61 false) (.node 506 (sourceLit (List.headD (raw_ints% [466308647243861427300899569126580210025]) 0) 20 true) .empty .empty) (.node 508 (sourceLit (List.headD (raw_ints% [2395961904039089710365700982698944678525]) 0) 17 true) .empty .empty)) (.node 511 (sourceLit (List.headD (raw_ints% [33355003750112874116684699]) 0) 63 false) (.node 510 (sourceLit (List.headD (raw_ints% [3190867565759407331504321799869542944225]) 0) 16 true) .empty .empty) .empty)))

#time def treeG_J003_part043 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [34485948236766323479313837965387245975]) 0) 28 true) treeG_J003_part041 treeG_J003_part042)

#time def treeG_J003_part044 : IntSourceTree :=
  (.node 463 (sourceLit (List.headD (raw_ints% [14829716320500203860180360445094449025]) 0) 25 true) treeG_J003_part040 treeG_J003_part043)

#time def treeG_J003_part045 : IntSourceTree :=
  (.node 414 (sourceLit (List.headD (raw_ints% [8239467066101441549603791384007265075]) 0) 31 true) treeG_J003_part037 treeG_J003_part044)

#time def treeG_J003_part046 : IntSourceTree :=
  (.node 542 (sourceLit (List.headD (raw_ints% [5819952011390904875293338075]) 0) 57 false) (.node 538 (sourceLit (List.headD (raw_ints% [98569792602899882661972710475]) 0) 54 false) (.node 514 (sourceLit (List.headD (raw_ints% [11754151828302388503977231619819827661255]) 0) 13 true) (.node 513 (sourceLit (List.headD (raw_ints% [7723962192290611321514191]) 0) 65 false) .empty .empty) (.node 537 (sourceLit (List.headD (raw_ints% [115486695701205264876056649491182999275]) 0) 30 true) .empty .empty)) (.node 540 (sourceLit (List.headD (raw_ints% [31833498878219430545684285925]) 0) 55 false) (.node 539 (sourceLit (List.headD (raw_ints% [31045388338936381091827823710703696025]) 0) 29 true) .empty .empty) (.node 541 (sourceLit (List.headD (raw_ints% [161693441279246900138782810758225585975]) 0) 25 true) .empty .empty))) (.node 546 (sourceLit (List.headD (raw_ints% [238995631138491751890103425]) 0) 61 false) (.node 544 (sourceLit (List.headD (raw_ints% [2298979949824331193730614075]) 0) 58 false) (.node 543 (sourceLit (List.headD (raw_ints% [145839159232817836279255442342647160175]) 0) 24 true) .empty .empty) (.node 545 (sourceLit (List.headD (raw_ints% [313001555897866924002109990409789513625]) 0) 22 true) .empty .empty)) (.node 548 (sourceLit (List.headD (raw_ints% [103005474131573231735853225]) 0) 62 false) (.node 547 (sourceLit (List.headD (raw_ints% [373279773295855574534386497418561607175]) 0) 21 true) .empty .empty) .empty)))

#time def treeG_J003_part047 : IntSourceTree :=
  (.node 582 (sourceLit (List.headD (raw_ints% [1118048938360156957110646322832968629575]) 0) 23 true) (.node 553 (sourceLit (List.headD (raw_ints% [6975809469015422411591654816881521414675]) 0) 15 true) (.node 551 (sourceLit (List.headD (raw_ints% [2543142808125983026250877830388627484575]) 0) 17 true) (.node 550 (sourceLit (List.headD (raw_ints% [45561900175273521080149959]) 0) 63 false) .empty .empty) (.node 552 (sourceLit (List.headD (raw_ints% [20547869668556876867639027]) 0) 64 false) .empty .empty)) (.node 580 (sourceLit (List.headD (raw_ints% [1798726163845621689152735171321688108975]) 0) 24 true) (.node 554 (sourceLit (List.headD (raw_ints% [1175714472020288531215581]) 0) 68 false) .empty .empty) (.node 581 (sourceLit (List.headD (raw_ints% [23366038430804673314880609525]) 0) 56 false) .empty .empty))) (.node 586 (sourceLit (List.headD (raw_ints% [2037703799939073964715980354151735898975]) 0) 20 true) (.node 584 (sourceLit (List.headD (raw_ints% [1947978880980233662400156348449754246625]) 0) 21 true) (.node 583 (sourceLit (List.headD (raw_ints% [8184988951474728763497660075]) 0) 57 false) .empty .empty) (.node 585 (sourceLit (List.headD (raw_ints% [780991777676399269458703275]) 0) 60 false) .empty .empty)) (.node 588 (sourceLit (List.headD (raw_ints% [9548990841428288674734666934695026751075]) 0) 17 true) (.node 587 (sourceLit (List.headD (raw_ints% [315858507464246365725807375]) 0) 61 false) .empty .empty) .empty)))

#time def treeG_J003_part048 : IntSourceTree :=
  (.node 549 (sourceLit (List.headD (raw_ints% [1905952724545055016555524192631061891275]) 0) 18 true) treeG_J003_part046 treeG_J003_part047)

#time def treeG_J003_part049 : IntSourceTree :=
  (.node 623 (sourceLit (List.headD (raw_ints% [121526222390917390103923860061290183675]) 0) 27 true) (.node 593 (sourceLit (List.headD (raw_ints% [3205976869066566386531209]) 0) 67 false) (.node 591 (sourceLit (List.headD (raw_ints% [57768796600434168043615219]) 0) 63 false) (.node 590 (sourceLit (List.headD (raw_ints% [12056754230601032800939871741178952185975]) 0) 16 true) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [32036246522123628791323317726905403400875]) 0) 14 true) .empty .empty)) (.node 621 (sourceLit (List.headD (raw_ints% [204629090320796848626744045070432815375]) 0) 28 true) (.node 594 (sourceLit (List.headD (raw_ints% [44052323923820990788756006915232343656145]) 0) 13 true) .empty .empty) (.node 622 (sourceLit (List.headD (raw_ints% [8773043209706884219793635725]) 0) 58 false) .empty .empty))) (.node 627 (sourceLit (List.headD (raw_ints% [208053003330402298772699232091646786475]) 0) 24 true) (.node 625 (sourceLit (List.headD (raw_ints% [204372165635295842299755794754995591625]) 0) 25 true) (.node 624 (sourceLit (List.headD (raw_ints% [367875562603149848110440375]) 0) 62 false) .empty .empty) (.node 626 (sourceLit (List.headD (raw_ints% [270998073268953758784299925]) 0) 62 false) .empty .empty)) (.node 629 (sourceLit (List.headD (raw_ints% [955379764610404207272392842757995607475]) 0) 21 true) (.node 628 (sourceLit (List.headD (raw_ints% [106426516666336566994977075]) 0) 63 false) .empty .empty) .empty)))

#time def treeG_J003_part050 : IntSourceTree :=
  (.node 665 (sourceLit (List.headD (raw_ints% [2162012723148799515424819725]) 0) 60 false) (.node 634 (sourceLit (List.headD (raw_ints% [507565599261569463828907]) 0) 70 false) (.node 632 (sourceLit (List.headD (raw_ints% [145394245827645668656157]) 0) 72 false) (.node 631 (sourceLit (List.headD (raw_ints% [1189201427809381221836124238848790587675]) 0) 20 true) .empty .empty) (.node 633 (sourceLit (List.headD (raw_ints% [3132554631638525797466457863752985248275]) 0) 18 true) .empty .empty)) (.node 664 (sourceLit (List.headD (raw_ints% [13607377585057192270902097739395389263775]) 0) 21 true) (.node 663 (sourceLit (List.headD (raw_ints% [26907183887352808115676882825]) 0) 57 false) .empty .empty) .empty)) (.node 669 (sourceLit (List.headD (raw_ints% [36578714038544087368509789]) 0) 65 false) (.node 667 (sourceLit (List.headD (raw_ints% [768133785611568669411392325]) 0) 61 false) (.node 666 (sourceLit (List.headD (raw_ints% [11042114800719859942468390510167981965025]) 0) 20 true) .empty .empty) (.node 668 (sourceLit (List.headD (raw_ints% [43712578011154699811076336480766550586525]) 0) 17 true) .empty .empty)) (.node 671 (sourceLit (List.headD (raw_ints% [117260111763005927859744839]) 0) 63 false) (.node 670 (sourceLit (List.headD (raw_ints% [49087550704464836464493270195332766692425]) 0) 16 true) .empty .empty) .empty)))

#time def treeG_J003_part051 : IntSourceTree :=
  (.node 630 (sourceLit (List.headD (raw_ints% [87514454181720047951680029]) 0) 63 false) treeG_J003_part049 treeG_J003_part050)

#time def treeG_J003_part052 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [33269088589248392257957497]) 0) 64 false) treeG_J003_part048 treeG_J003_part051)

#time def treeG_J003_part053 : IntSourceTree :=
  (.node 709 (sourceLit (List.headD (raw_ints% [36069539894271466152897193738702585726725]) 0) 18 true) (.node 705 (sourceLit (List.headD (raw_ints% [11972400259974825532504051381355424530775]) 0) 22 true) (.node 674 (sourceLit (List.headD (raw_ints% [156431172501044660249097296364958712233455]) 0) 13 true) (.node 673 (sourceLit (List.headD (raw_ints% [6099254863902756407462839]) 0) 67 false) .empty .empty) (.node 704 (sourceLit (List.headD (raw_ints% [21021174885702410545909836825]) 0) 58 false) .empty .empty)) (.node 707 (sourceLit (List.headD (raw_ints% [9377690774076641552286796653434807673225]) 0) 21 true) (.node 706 (sourceLit (List.headD (raw_ints% [1620016576610891997856219875]) 0) 61 false) .empty .empty) (.node 708 (sourceLit (List.headD (raw_ints% [555280752278895535421438175]) 0) 62 false) .empty .empty))) (.node 713 (sourceLit (List.headD (raw_ints% [95121099184368961223968921935715909835325]) 0) 15 true) (.node 711 (sourceLit (List.headD (raw_ints% [39573939281989786689804276284542441991025]) 0) 17 true) (.node 710 (sourceLit (List.headD (raw_ints% [205115258126632650996398283]) 0) 63 false) .empty .empty) (.node 712 (sourceLit (List.headD (raw_ints% [80039184831128636683768647]) 0) 64 false) .empty .empty)) (.node 745 (sourceLit (List.headD (raw_ints% [16697149439404811515060197375]) 0) 59 false) (.node 714 (sourceLit (List.headD (raw_ints% [4068992466856478552147211]) 0) 68 false) .empty .empty) .empty)))

#time def treeG_J003_part054 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [604537620973907029542654079120768566449145]) 0) 13 true) (.node 750 (sourceLit (List.headD (raw_ints% [239468768449706892758684279714287919121375]) 0) 16 true) (.node 748 (sourceLit (List.headD (raw_ints% [256373526759297829862101156429147294956675]) 0) 17 true) (.node 747 (sourceLit (List.headD (raw_ints% [2471899367610215326301047425]) 0) 61 false) .empty .empty) (.node 749 (sourceLit (List.headD (raw_ints% [408965896124719185947399019]) 0) 63 false) .empty .empty)) (.node 752 (sourceLit (List.headD (raw_ints% [513001492274359419433167835706939280034875]) 0) 14 true) (.node 751 (sourceLit (List.headD (raw_ints% [292970404490259374133051727]) 0) 63 false) .empty .empty) (.node 753 (sourceLit (List.headD (raw_ints% [55642165375517611053917291]) 0) 65 false) .empty .empty))) (.node 789 (sourceLit (List.headD (raw_ints% [110151993432513181854601981345222354614975]) 0) 19 true) (.node 787 (sourceLit (List.headD (raw_ints% [37679698252501051382638611943620303303975]) 0) 22 true) (.node 786 (sourceLit (List.headD (raw_ints% [13457116286183027519347757625]) 0) 60 false) .empty .empty) (.node 788 (sourceLit (List.headD (raw_ints% [958309307665659895439804625]) 0) 63 false) .empty .empty)) (.node 791 (sourceLit (List.headD (raw_ints% [99947414583858553034440001714872738565175]) 0) 18 true) (.node 790 (sourceLit (List.headD (raw_ints% [612816534122805720898399755]) 0) 63 false) .empty .empty) .empty)))

#time def treeG_J003_part055 : IntSourceTree :=
  (.node 746 (sourceLit (List.headD (raw_ints% [84737087279078744317564020540675414281175]) 0) 20 true) treeG_J003_part053 treeG_J003_part054)

#time def treeG_J003_part056 : IntSourceTree :=
  (.node 832 (sourceLit (List.headD (raw_ints% [2685315774409114277668912219168988354050725]) 0) 14 true) (.node 828 (sourceLit (List.headD (raw_ints% [2155127161400769458626770007962552116497725]) 0) 17 true) (.node 794 (sourceLit (List.headD (raw_ints% [39366195508091696845328447]) 0) 66 false) (.node 793 (sourceLit (List.headD (raw_ints% [208940196544995229104599456885611685099775]) 0) 16 true) .empty .empty) (.node 827 (sourceLit (List.headD (raw_ints% [1373152114821601524130838775]) 0) 64 false) .empty .empty)) (.node 830 (sourceLit (List.headD (raw_ints% [1522963126470504016914947421809269754718225]) 0) 16 true) (.node 829 (sourceLit (List.headD (raw_ints% [1507652719206600604932210231]) 0) 63 false) .empty .empty) (.node 831 (sourceLit (List.headD (raw_ints% [932662663755352067663747783]) 0) 63 false) .empty .empty))) (.node 869 (sourceLit (List.headD (raw_ints% [1934823174535743094917566045272107407267775]) 0) 18 true) (.node 834 (sourceLit (List.headD (raw_ints% [2738505523746016636130937231049018395147255]) 0) 13 true) (.node 833 (sourceLit (List.headD (raw_ints% [157289054283613126395365789]) 0) 65 false) .empty .empty) (.node 868 (sourceLit (List.headD (raw_ints% [4534299151620746201083550475]) 0) 63 false) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [1323068297302786910846067418379524277587875]) 0) 17 true) (.node 870 (sourceLit (List.headD (raw_ints% [2402488904290395488966020707]) 0) 63 false) .empty .empty) .empty)))

#time def treeG_J003_part057 : IntSourceTree :=
  (.node 913 (sourceLit (List.headD (raw_ints% [281221194906304101909549457]) 0) 66 false) (.node 910 (sourceLit (List.headD (raw_ints% [13955622269815440742425580940367589503423975]) 0) 16 true) (.node 874 (sourceLit (List.headD (raw_ints% [58961429387760714775018671]) 0) 67 false) (.node 873 (sourceLit (List.headD (raw_ints% [2267435381319123819459713305397764983851175]) 0) 15 true) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [7560945584034891797234890719]) 0) 63 false) .empty .empty)) (.node 912 (sourceLit (List.headD (raw_ints% [18483776982435476295868166474903400087355275]) 0) 14 true) (.node 911 (sourceLit (List.headD (raw_ints% [3872315144825438910268293631]) 0) 63 false) .empty .empty) .empty)) (.node 952 (sourceLit (List.headD (raw_ints% [49259120323894024688341077]) 0) 70 false) (.node 950 (sourceLit (List.headD (raw_ints% [12719402263779388105503760731]) 0) 63 false) (.node 914 (sourceLit (List.headD (raw_ints% [15400977526806973919546769212133101475662145]) 0) 13 true) .empty .empty) (.node 951 (sourceLit (List.headD (raw_ints% [3158138493128163457894878380497016306459025]) 0) 19 true) .empty .empty)) (.node 954 (sourceLit (List.headD (raw_ints% [111129882759271693567265393]) 0) 68 false) (.node 953 (sourceLit (List.headD (raw_ints% [4054085400279088119102113292376408775876025]) 0) 17 true) .empty .empty) .empty)))

#time def treeG_J003_part058 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [719731444096221330214464703]) 0) 64 false) treeG_J003_part056 treeG_J003_part057)

#time def treeG_J003_part059 : IntSourceTree :=
  (.node 792 (sourceLit (List.headD (raw_ints% [26616402457391342181160385]) 0) 67 false) treeG_J003_part055 treeG_J003_part058)

#time def treeG_J003_part060 : IntSourceTree :=
  (.node 672 (sourceLit (List.headD (raw_ints% [120181536237477167603700584845739791821525]) 0) 14 true) treeG_J003_part052 treeG_J003_part059)

#time def treeG_J003_part061 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [8654038407892099628690727559312636352325]) 0) 14 true) treeG_J003_part045 treeG_J003_part060)

#time def treeG_J003_part062 : IntSourceTree :=
  (.node 307 (sourceLit (List.headD (raw_ints% [58611950666976637164768825725954325]) 0) 23 false) treeG_J003_part030 treeG_J003_part061)

#time def treeG_J003 : IntSourceTree := treeG_J003_part062

#time def treeG_J004_part000 : IntSourceTree :=
  (.node 5 (sourceLit (List.headD (raw_ints% [57276587892383102671566425161875]) 0) 39 true) (.node 3 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 false) (.node 2 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 1 (sourceLit (List.headD (raw_ints% [36448737749698338063724088739375]) 0) 39 false) .empty .empty) .empty) (.node 4 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 true) .empty .empty)) (.node 8 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 44 false) (.node 7 (sourceLit (List.headD (raw_ints% [32283167721161385142155621454875]) 0) 38 true) (.node 6 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 42 false) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [54003640012818353947476915152625]) 0) 36 true) .empty .empty)))

#time def treeG_J004_part001 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [413408273021435066953944849558075]) 0) 31 false) (.node 13 (sourceLit (List.headD (raw_ints% [2402866693950428470991334483375]) 0) 32 false) (.node 12 (sourceLit (List.headD (raw_ints% [86170882779567764518531373325]) 0) 47 false) (.node 11 (sourceLit (List.headD (raw_ints% [39225784435389640011436400262375]) 0) 35 true) .empty .empty) .empty) (.node 14 (sourceLit (List.headD (raw_ints% [20883005320424934845374798725]) 0) 49 false) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [154694584012997881570478625]) 0) 56 false) (.node 17 (sourceLit (List.headD (raw_ints% [2788533352548048609916963618342275]) 0) 29 false) (.node 16 (sourceLit (List.headD (raw_ints% [2538579356522261068791337875]) 0) 52 false) .empty .empty) .empty) (.node 19 (sourceLit (List.headD (raw_ints% [7232141599960115871933855464592225]) 0) 28 false) .empty .empty)))

#time def treeG_J004_part002 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 47 false) treeG_J004_part000 treeG_J004_part001)

#time def treeG_J004_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [1308160951860274259364296845120065825]) 0) 21 false) (.node 23 (sourceLit (List.headD (raw_ints% [302466939381683115631763441087478375]) 0) 23 false) (.node 22 (sourceLit (List.headD (raw_ints% [73969273953491384605855725]) 0) 57 false) (.node 21 (sourceLit (List.headD (raw_ints% [135717180536110288094070600584307375]) 0) 24 false) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [18127104063648026568768675]) 0) 59 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [2185356442832756211088125]) 0) 62 false) (.node 27 (sourceLit (List.headD (raw_ints% [2774552942499584100904661137462202175]) 0) 20 false) (.node 26 (sourceLit (List.headD (raw_ints% [2224007118540581871978675]) 0) 62 false) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [23228764209513386927820352865695003875]) 0) 17 false) .empty .empty)))

#time def treeG_J004_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [406073904433779631422615862668736652145]) 0) 13 false) (.node 33 (sourceLit (List.headD (raw_ints% [198297574365996166009357310450762436075]) 0) 14 false) (.node 32 (sourceLit (List.headD (raw_ints% [33063939544778089497979]) 0) 68 false) (.node 31 (sourceLit (List.headD (raw_ints% [48159381540934600133432941042892983575]) 0) 16 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [1017985650336098973529]) 0) 73 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [13249792919524619564975822134536775109295]) 0) 8 false) (.node 36 (sourceLit (List.headD (raw_ints% [4014623346090873170655]) 0) 71 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [990158821981380165205]) 0) 73 false) .empty .empty)))

#time def treeG_J004_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [537375602887894789558353]) 0) 64 false) treeG_J004_part003 treeG_J004_part004)

#time def treeG_J004_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [302291022410164325309166675]) 0) 55 false) treeG_J004_part002 treeG_J004_part005)

#time def treeG_J004_part007 : IntSourceTree :=
  (.node 46 (sourceLit (List.headD (raw_ints% [57276587892383102671566425161875]) 0) 40 true) (.node 44 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 41 false) (.node 43 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 42 (sourceLit (List.headD (raw_ints% [36448737749698338063724088739375]) 0) 40 false) .empty .empty) .empty) (.node 45 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 41 true) .empty .empty)) (.node 49 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 45 false) (.node 48 (sourceLit (List.headD (raw_ints% [32283167721161385142155621454875]) 0) 39 true) (.node 47 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 43 false) .empty .empty) .empty) (.node 50 (sourceLit (List.headD (raw_ints% [54003640012818353947476915152625]) 0) 37 true) .empty .empty)))

#time def treeG_J004_part008 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [413408273021435066953944849558075]) 0) 32 false) (.node 54 (sourceLit (List.headD (raw_ints% [2402866693950428470991334483375]) 0) 33 false) (.node 53 (sourceLit (List.headD (raw_ints% [86170882779567764518531373325]) 0) 48 false) (.node 52 (sourceLit (List.headD (raw_ints% [39225784435389640011436400262375]) 0) 36 true) .empty .empty) .empty) (.node 55 (sourceLit (List.headD (raw_ints% [20883005320424934845374798725]) 0) 50 false) .empty .empty)) (.node 58 (sourceLit (List.headD (raw_ints% [2788533352548048609916963618342275]) 0) 30 false) (.node 57 (sourceLit (List.headD (raw_ints% [2538579356522261068791337875]) 0) 53 false) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [154694584012997881570478625]) 0) 57 false) .empty .empty)))

#time def treeG_J004_part009 : IntSourceTree :=
  (.node 51 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 48 false) treeG_J004_part007 treeG_J004_part008)

#time def treeG_J004_part010 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [18127104063648026568768675]) 0) 60 false) (.node 63 (sourceLit (List.headD (raw_ints% [73969273953491384605855725]) 0) 58 false) (.node 62 (sourceLit (List.headD (raw_ints% [135717180536110288094070600584307375]) 0) 25 false) (.node 61 (sourceLit (List.headD (raw_ints% [302291022410164325309166675]) 0) 56 false) .empty .empty) .empty) (.node 64 (sourceLit (List.headD (raw_ints% [302466939381683115631763441087478375]) 0) 24 false) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [2774552942499584100904661137462202175]) 0) 21 false) (.node 67 (sourceLit (List.headD (raw_ints% [2224007118540581871978675]) 0) 63 false) (.node 66 (sourceLit (List.headD (raw_ints% [1308160951860274259364296845120065825]) 0) 22 false) .empty .empty) .empty) (.node 69 (sourceLit (List.headD (raw_ints% [2185356442832756211088125]) 0) 63 false) .empty .empty)))

#time def treeG_J004_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [1017985650336098973529]) 0) 74 false) (.node 73 (sourceLit (List.headD (raw_ints% [33063939544778089497979]) 0) 69 false) (.node 72 (sourceLit (List.headD (raw_ints% [48159381540934600133432941042892983575]) 0) 17 false) (.node 71 (sourceLit (List.headD (raw_ints% [537375602887894789558353]) 0) 65 false) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [198297574365996166009357310450762436075]) 0) 15 false) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [4014623346090873170655]) 0) 72 false) (.node 76 (sourceLit (List.headD (raw_ints% [406073904433779631422615862668736652145]) 0) 14 false) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [13249792919524619564975822134536775109295]) 0) 9 false) .empty .empty)))

#time def treeG_J004_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [23228764209513386927820352865695003875]) 0) 18 false) treeG_J004_part010 treeG_J004_part011)

#time def treeG_J004_part013 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [7232141599960115871933855464592225]) 0) 29 false) treeG_J004_part009 treeG_J004_part012)

#time def treeG_J004_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [26931712754996476995744305624212788573855]) 0) 7 false) treeG_J004_part006 treeG_J004_part013)

#time def treeG_J004_part015 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [425929535417903436230375779840125]) 0) 38 true) (.node 85 (sourceLit (List.headD (raw_ints% [182243688748491690318620443696875]) 0) 39 false) (.node 84 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 false) (.node 83 (sourceLit (List.headD (raw_ints% [57276587892383102671566425161875]) 0) 40 false) .empty .empty) .empty) (.node 86 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 43 true) .empty .empty)) (.node 90 (sourceLit (List.headD (raw_ints% [565327361015729325070006274325]) 0) 46 false) (.node 89 (sourceLit (List.headD (raw_ints% [462527043525763808327013028125375]) 0) 36 true) (.node 88 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 48 false) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [392803335667157191568378920958625]) 0) 35 true) .empty .empty)))

#time def treeG_J004_part016 : IntSourceTree :=
  (.node 97 (sourceLit (List.headD (raw_ints% [3825999015794912461346153974586925]) 0) 29 false) (.node 95 (sourceLit (List.headD (raw_ints% [394185339469831639186014173691075]) 0) 31 true) (.node 94 (sourceLit (List.headD (raw_ints% [8160984682392853709144571825]) 0) 52 false) (.node 93 (sourceLit (List.headD (raw_ints% [1257627968626418908836956142879375]) 0) 32 true) .empty .empty) .empty) (.node 96 (sourceLit (List.headD (raw_ints% [15805846607380412707792122975]) 0) 51 false) .empty .empty)) (.node 99 (sourceLit (List.headD (raw_ints% [15076125220424273007401853482145975]) 0) 28 false) (.node 98 (sourceLit (List.headD (raw_ints% [1919801020470269542509423375]) 0) 54 false) .empty .empty) (.node 100 (sourceLit (List.headD (raw_ints% [935265649693818727254662325]) 0) 55 false) .empty .empty)))

#time def treeG_J004_part017 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [270877976809313914473051536775]) 0) 47 false) treeG_J004_part015 treeG_J004_part016)

#time def treeG_J004_part018 : IntSourceTree :=
  (.node 106 (sourceLit (List.headD (raw_ints% [13679089826566862824811325]) 0) 61 false) (.node 104 (sourceLit (List.headD (raw_ints% [27921084944921679018543525]) 0) 60 false) (.node 103 (sourceLit (List.headD (raw_ints% [783270504907199189120801363586980625]) 0) 23 false) (.node 102 (sourceLit (List.headD (raw_ints% [114160874228336470351655475]) 0) 58 false) .empty .empty) .empty) (.node 105 (sourceLit (List.headD (raw_ints% [3531310078246655590743918212279588175]) 0) 21 false) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [65556929950473304301128803533095465725]) 0) 17 false) (.node 108 (sourceLit (List.headD (raw_ints% [6710672031329571276826575]) 0) 62 false) (.node 107 (sourceLit (List.headD (raw_ints% [7690734672382609974009713623498324425]) 0) 20 false) .empty .empty) .empty) (.node 110 (sourceLit (List.headD (raw_ints% [411995209986215355382443]) 0) 66 false) .empty .empty)))

#time def treeG_J004_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [12273147059286710405809]) 0) 71 false) (.node 114 (sourceLit (List.headD (raw_ints% [24920054342089297709747]) 0) 70 false) (.node 113 (sourceLit (List.headD (raw_ints% [572252530288957436125569746235525301125]) 0) 14 false) (.node 112 (sourceLit (List.headD (raw_ints% [405119844708782431566437]) 0) 66 false) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [1180306690494189696652242620937362836455]) 0) 13 false) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [1512232262054746502725]) 0) 74 false) (.node 117 (sourceLit (List.headD (raw_ints% [38727666847999173257119008287061516365265]) 0) 8 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [79066630601200479524062271452081412300505]) 0) 7 false) .empty .empty)))

#time def treeG_J004_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [137670732135172495289129881882667047425]) 0) 16 false) treeG_J004_part018 treeG_J004_part019)

#time def treeG_J004_part021 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [327139881861337127709696149149595025]) 0) 24 false) treeG_J004_part017 treeG_J004_part020)

#time def treeG_J004_part022 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [1636473939782374362044755004625]) 0) 45 false) (.node 127 (sourceLit (List.headD (raw_ints% [21869242649819002838234453243625]) 0) 43 true) (.node 126 (sourceLit (List.headD (raw_ints% [119760138320437396495093434429375]) 0) 41 false) (.node 125 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 42 false) .empty .empty) .empty) (.node 128 (sourceLit (List.headD (raw_ints% [196823183848371025544110079192625]) 0) 40 true) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [176788775615883775778471260348125]) 0) 37 true) (.node 131 (sourceLit (List.headD (raw_ints% [386802931221288485574214819275]) 0) 47 false) (.node 130 (sourceLit (List.headD (raw_ints% [204261701756472727189768056486375]) 0) 38 true) .empty .empty) .empty) (.node 133 (sourceLit (List.headD (raw_ints% [92353547014873074977260081725]) 0) 49 false) .empty .empty)))

#time def treeG_J004_part023 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [1301022684418278016227508875]) 0) 55 false) (.node 137 (sourceLit (List.headD (raw_ints% [10728687894335890570209447225]) 0) 52 false) (.node 136 (sourceLit (List.headD (raw_ints% [403796806245633353069979511624575]) 0) 33 true) (.node 135 (sourceLit (List.headD (raw_ints% [44404872138717894827781775875]) 0) 50 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [518732831623431925714595178122325]) 0) 31 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [316487313641827200972747825]) 0) 57 false) (.node 140 (sourceLit (List.headD (raw_ints% [3921991810232078567733999008776875]) 0) 30 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [95711350662613419807812774282643825]) 0) 26 false) .empty .empty)))

#time def treeG_J004_part024 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [630015417660184668653973738681375]) 0) 34 true) treeG_J004_part022 treeG_J004_part023)

#time def treeG_J004_part025 : IntSourceTree :=
  (.node 148 (sourceLit (List.headD (raw_ints% [2458090864941512936552526243018061125]) 0) 22 false) (.node 146 (sourceLit (List.headD (raw_ints% [1111574563193190665689810683579761175]) 0) 23 false) (.node 145 (sourceLit (List.headD (raw_ints% [37715065826195331468318375]) 0) 60 false) (.node 144 (sourceLit (List.headD (raw_ints% [240401782762758036744518961249751125]) 0) 25 false) .empty .empty) .empty) (.node 147 (sourceLit (List.headD (raw_ints% [9231075589485699080853975]) 0) 62 false) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [1110605237056966631971419]) 0) 65 false) (.node 150 (sourceLit (List.headD (raw_ints% [21164082870479958686654225333700230925]) 0) 19 false) (.node 149 (sourceLit (List.headD (raw_ints% [2262657794248407532869225]) 0) 64 false) .empty .empty) .empty) (.node 152 (sourceLit (List.headD (raw_ints% [44755675297118947577848470419887031925]) 0) 18 false) .empty .empty)))

#time def treeG_J004_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [12738936964237276846071593076262370627985]) 0) 10 false) (.node 156 (sourceLit (List.headD (raw_ints% [387116393030205032614813379134313092155]) 0) 15 false) (.node 155 (sourceLit (List.headD (raw_ints% [16776169139400505921515]) 0) 71 false) (.node 154 (sourceLit (List.headD (raw_ints% [186977477961480635058106217892381432525]) 0) 16 false) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [4129261856597918617577]) 0) 73 false) .empty .empty)) (.node 165 (sourceLit (List.headD (raw_ints% [151001913534464543406856939063125]) 0) 39 false) (.node 159 (sourceLit (List.headD (raw_ints% [2034305702128112840245]) 0) 74 false) .empty .empty) (.node 166 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 46 false) .empty .empty)))

#time def treeG_J004_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [272864086529670073574521]) 0) 67 false) treeG_J004_part025 treeG_J004_part026)

#time def treeG_J004_part028 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [154352474503181556097455225]) 0) 58 false) treeG_J004_part024 treeG_J004_part027)

#time def treeG_J004_part029 : IntSourceTree :=
  (.node 124 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 44 false) treeG_J004_part021 treeG_J004_part028)

#time def treeG_J004_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [990158821981380165205]) 0) 74 false) treeG_J004_part014 treeG_J004_part029)

#time def treeG_J004_part031 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [502727885633263056675378101775]) 0) 47 false) (.node 170 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 48 false) (.node 169 (sourceLit (List.headD (raw_ints% [5835814839622109009084509506038625]) 0) 36 true) (.node 168 (sourceLit (List.headD (raw_ints% [24249568380411547364845005977625]) 0) 44 true) .empty .empty) .empty) (.node 171 (sourceLit (List.headD (raw_ints% [2875383892436406443467909982823375]) 0) 35 true) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [9686061343093123059277565645210925]) 0) 31 true) (.node 174 (sourceLit (List.headD (raw_ints% [59709608285301660140681794425]) 0) 50 false) (.node 173 (sourceLit (List.headD (raw_ints% [10056853670790142740985204519400625]) 0) 32 true) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [7149756382834370529997413225]) 0) 53 false) .empty .empty)))

#time def treeG_J004_part032 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [101163219706745365310546175]) 0) 59 false) (.node 180 (sourceLit (List.headD (raw_ints% [1666779719142737305200355425]) 0) 55 false) (.node 179 (sourceLit (List.headD (raw_ints% [6776399914449362195968330632188775]) 0) 28 true) (.node 178 (sourceLit (List.headD (raw_ints% [6889085853395351485190600475]) 0) 53 false) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [174875069848368928960255723973844975]) 0) 24 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [4161546970161601585080688547712447825]) 0) 21 false) (.node 184 (sourceLit (List.headD (raw_ints% [98510304613338198060368175]) 0) 59 false) (.node 183 (sourceLit (List.headD (raw_ints% [748111105694615527804203024935320575]) 0) 23 false) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [12017987999814234321753525]) 0) 62 false) .empty .empty)))

#time def treeG_J004_part033 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [16747496815655179759585498346573325]) 0) 29 true) treeG_J004_part031 treeG_J004_part032)

#time def treeG_J004_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [352742696174092100202491]) 0) 67 false) (.node 190 (sourceLit (List.headD (raw_ints% [1438667374275976822104339]) 0) 65 false) (.node 189 (sourceLit (List.headD (raw_ints% [91760885405783523638232876020060446275]) 0) 17 false) (.node 188 (sourceLit (List.headD (raw_ints% [11751479147641826884881375]) 0) 62 false) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [200954593792506843697337723456536647375]) 0) 16 false) .empty .empty)) (.node 195 (sourceLit (List.headD (raw_ints% [1811332956889500464277456865340740083945]) 0) 13 false) (.node 194 (sourceLit (List.headD (raw_ints% [173183869161312882735533]) 0) 68 false) (.node 193 (sourceLit (List.headD (raw_ints% [859929079218848886365581307200859720475]) 0) 14 false) .empty .empty) .empty) (.node 196 (sourceLit (List.headD (raw_ints% [21279191219514301437221]) 0) 71 false) .empty .empty)))

#time def treeG_J004_part035 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [2735738116241643831240090889095375]) 0) 39 false) (.node 206 (sourceLit (List.headD (raw_ints% [88518363106410249583329929795625]) 0) 40 true) (.node 199 (sourceLit (List.headD (raw_ints% [124756360826595950013083217768116517747255]) 0) 7 false) (.node 198 (sourceLit (List.headD (raw_ints% [654257398635793028713]) 0) 76 false) .empty .empty) .empty) (.node 207 (sourceLit (List.headD (raw_ints% [71856082992262437897056060657625]) 0) 43 false) .empty .empty)) (.node 210 (sourceLit (List.headD (raw_ints% [5427291436109163554704973393065875]) 0) 37 true) (.node 209 (sourceLit (List.headD (raw_ints% [12943021160096960863444880491125]) 0) 46 true) .empty .empty) (.node 211 (sourceLit (List.headD (raw_ints% [684343647545356551400533911025]) 0) 47 false) .empty .empty)))

#time def treeG_J004_part036 : IntSourceTree :=
  (.node 197 (sourceLit (List.headD (raw_ints% [60374129767733315092273216771322635226415]) 0) 8 false) treeG_J004_part034 treeG_J004_part035)

#time def treeG_J004_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [10094458338708440677027257313777854375]) 0) 20 false) treeG_J004_part033 treeG_J004_part036)

#time def treeG_J004_part038 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [17870337637001591549780205675]) 0) 52 false) (.node 215 (sourceLit (List.headD (raw_ints% [75014344431885425453581812975]) 0) 50 false) (.node 214 (sourceLit (List.headD (raw_ints% [8796822835469773403677257042037875]) 0) 33 true) (.node 213 (sourceLit (List.headD (raw_ints% [318020791603516906720857938325]) 0) 48 false) .empty .empty) .empty) (.node 216 (sourceLit (List.headD (raw_ints% [8878467730601856353137606621961775]) 0) 32 true) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [14620383534913519331436328649742525]) 0) 29 true) (.node 219 (sourceLit (List.headD (raw_ints% [4287040484558795452735582725]) 0) 54 false) (.node 218 (sourceLit (List.headD (raw_ints% [17784962478902043611014688702817975]) 0) 30 true) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [1033805091859082903254859775]) 0) 56 false) .empty .empty)))

#time def treeG_J004_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [14804900410142769562653075]) 0) 62 false) (.node 225 (sourceLit (List.headD (raw_ints% [7599404848392858324006225]) 0) 63 false) (.node 224 (sourceLit (List.headD (raw_ints% [267307540169099454315165102435818325]) 0) 24 false) (.node 223 (sourceLit (List.headD (raw_ints% [250300404323799905144729475]) 0) 58 false) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [1938397843775220253701067180552925475]) 0) 22 false) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [7226163559145011819142925]) 0) 63 false) (.node 228 (sourceLit (List.headD (raw_ints% [5178276608825414803922204827741732125]) 0) 21 false) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [49432719664823606264924425352659984425]) 0) 18 false) .empty .empty)))

#time def treeG_J004_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [16547631476857910655369824591442675]) 0) 25 true) treeG_J004_part038 treeG_J004_part039)

#time def treeG_J004_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [1037100170829090399047830107072113899635]) 0) 14 false) (.node 234 (sourceLit (List.headD (raw_ints% [485974123295887616249368871416096855425]) 0) 15 false) (.node 233 (sourceLit (List.headD (raw_ints% [432621305818514126830461]) 0) 67 false) (.node 232 (sourceLit (List.headD (raw_ints% [111443243198268948541640782616762583525]) 0) 17 false) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [106079192603710859049473]) 0) 69 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [3199753486958231389459]) 0) 74 false) (.node 238 (sourceLit (List.headD (raw_ints% [34896255839258761400130030618797893970445]) 0) 9 false) (.node 237 (sourceLit (List.headD (raw_ints% [13020667506318464202067]) 0) 72 false) .empty .empty) .empty) (.node 247 (sourceLit (List.headD (raw_ints% [3050238653396183776818510169075125]) 0) 38 true) .empty .empty)))

#time def treeG_J004_part042 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [70640949247758301800165754268667375]) 0) 32 true) (.node 251 (sourceLit (List.headD (raw_ints% [40542947596436901994171877161703625]) 0) 35 true) (.node 250 (sourceLit (List.headD (raw_ints% [13478594449480283381932254856275]) 0) 47 true) (.node 249 (sourceLit (List.headD (raw_ints% [49607624699488410308925963731564625]) 0) 36 false) .empty .empty) .empty) (.node 252 (sourceLit (List.headD (raw_ints% [865959409457450046125689720275]) 0) 47 false) .empty .empty)) (.node 255 (sourceLit (List.headD (raw_ints% [60688521340665064170140490691092075]) 0) 31 true) (.node 254 (sourceLit (List.headD (raw_ints% [198601575032913586439494349475]) 0) 49 false) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [46415318900547943333592160075]) 0) 51 false) .empty .empty)))

#time def treeG_J004_part043 : IntSourceTree :=
  (.node 248 (sourceLit (List.headD (raw_ints% [48052825686336992630950533317625]) 0) 45 false) treeG_J004_part041 treeG_J004_part042)

#time def treeG_J004_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [1766729511494987012237259]) 0) 65 false) treeG_J004_part040 treeG_J004_part043)

#time def treeG_J004_part045 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [2521806341204638891910967462127125]) 0) 36 true) treeG_J004_part037 treeG_J004_part044)

#time def treeG_J004_part046 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [629152213032101442012675075]) 0) 57 false) (.node 260 (sourceLit (List.headD (raw_ints% [655065191354014536883806825]) 0) 57 false) (.node 259 (sourceLit (List.headD (raw_ints% [135503299916766986692149178990355025]) 0) 28 true) (.node 258 (sourceLit (List.headD (raw_ints% [686328236475390004036850325]) 0) 57 false) .empty .empty) .empty) (.node 261 (sourceLit (List.headD (raw_ints% [1110579616082834166172180757557366575]) 0) 24 true) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [115373672543989683961953091260645375]) 0) 21 false) (.node 264 (sourceLit (List.headD (raw_ints% [37947524927615426771090325]) 0) 61 false) (.node 263 (sourceLit (List.headD (raw_ints% [880492157509478813047161621666861975]) 0) 23 true) .empty .empty) .empty) (.node 266 (sourceLit (List.headD (raw_ints% [18379631393757198974271375]) 0) 62 false) .empty .empty)))

#time def treeG_J004_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [1061244119146802811832277]) 0) 66 false) (.node 270 (sourceLit (List.headD (raw_ints% [4348828810593058174934247]) 0) 64 false) (.node 269 (sourceLit (List.headD (raw_ints% [73943966076629750087277678467674981725]) 0) 17 false) (.node 268 (sourceLit (List.headD (raw_ints% [17858321672643712240424775]) 0) 62 false) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [194507163526082006422057679364743228025]) 0) 16 false) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [16214839791075077755933]) 0) 72 false) (.node 273 (sourceLit (List.headD (raw_ints% [923162811953454290300671214667341615925]) 0) 14 false) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [2076460029477600465717494105988034759455]) 0) 13 false) .empty .empty)))

#time def treeG_J004_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [5412724411493321352581280130645549425]) 0) 20 false) treeG_J004_part046 treeG_J004_part047)

#time def treeG_J004_part049 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [30497923423216976747197706904375]) 0) 47 false) (.node 279 (sourceLit (List.headD (raw_ints% [154413685887474141187957027182266634016305]) 0) 7 false) (.node 278 (sourceLit (List.headD (raw_ints% [7786608317232119972363]) 0) 73 false) (.node 277 (sourceLit (List.headD (raw_ints% [72374692098390255985849036933907943926865]) 0) 8 false) .empty .empty) .empty) (.node 288 (sourceLit (List.headD (raw_ints% [1446494192409456902014650264542625]) 0) 41 true) .empty .empty)) (.node 292 (sourceLit (List.headD (raw_ints% [9505285313808065775565227424894125]) 0) 38 true) (.node 291 (sourceLit (List.headD (raw_ints% [27641532546505923315265043623575]) 0) 47 true) (.node 290 (sourceLit (List.headD (raw_ints% [13758729033899393465907734281157625]) 0) 39 false) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [273969308926966569702415890975]) 0) 49 false) .empty .empty)))

#time def treeG_J004_part050 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [6694211299047444611854022475]) 0) 54 false) (.node 297 (sourceLit (List.headD (raw_ints% [892030664485823493244123575]) 0) 57 false) (.node 296 (sourceLit (List.headD (raw_ints% [12952513402515801954250721017282575]) 0) 34 true) (.node 295 (sourceLit (List.headD (raw_ints% [30896807650257040246478134125]) 0) 52 false) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [26880756098768119569900379725499275]) 0) 32 true) .empty .empty)) (.node 301 (sourceLit (List.headD (raw_ints% [1586455673556975244280367525]) 0) 56 false) (.node 300 (sourceLit (List.headD (raw_ints% [30220729095463366840178212585153125]) 0) 31 true) .empty .empty) (.node 302 (sourceLit (List.headD (raw_ints% [273507996151494063879202733241480975]) 0) 27 true) .empty .empty)))

#time def treeG_J004_part051 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [15461031603072132099122124306657375]) 0) 35 true) treeG_J004_part049 treeG_J004_part050)

#time def treeG_J004_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [63520810164682256175031]) 0) 70 false) treeG_J004_part048 treeG_J004_part051)

#time def treeG_J004_part053 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [58611950666976637164768825725954325]) 0) 23 false) (.node 306 (sourceLit (List.headD (raw_ints% [455756042807807642434778522323070025]) 0) 24 true) (.node 305 (sourceLit (List.headD (raw_ints% [22748715230829710123077875]) 0) 62 false) (.node 304 (sourceLit (List.headD (raw_ints% [286949924419644566840581681025670075]) 0) 26 true) .empty .empty) .empty) (.node 307 (sourceLit (List.headD (raw_ints% [21954362377371628385889675]) 0) 62 false) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [645524824774517790674247]) 0) 67 false) (.node 310 (sourceLit (List.headD (raw_ints% [6127811602951535955588313278753749325]) 0) 20 false) (.node 309 (sourceLit (List.headD (raw_ints% [5316079056749350210640925]) 0) 64 false) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [20765980081953264470104224186995161125]) 0) 19 false) .empty .empty)))

#time def treeG_J004_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [9369609064782873646429751578777512489105]) 0) 11 false) (.node 316 (sourceLit (List.headD (raw_ints% [259839964662127516667415999728980214955]) 0) 16 false) (.node 315 (sourceLit (List.headD (raw_ints% [153358244053490385045455]) 0) 69 false) (.node 314 (sourceLit (List.headD (raw_ints% [109297172164391668512825585812811190125]) 0) 17 false) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [37479475152045327770897]) 0) 71 false) .empty .empty)) (.node 330 (sourceLit (List.headD (raw_ints% [74474441295914236876327668665025]) 0) 47 false) (.node 319 (sourceLit (List.headD (raw_ints% [573356853784236072863]) 0) 77 false) .empty .empty) (.node 331 (sourceLit (List.headD (raw_ints% [480822276681217492903219374158747625]) 0) 35 false) .empty .empty)))

#time def treeG_J004_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [78577851666036085625227]) 0) 70 false) treeG_J004_part053 treeG_J004_part054)

#time def treeG_J004_part056 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [703652870887036803181429937501269725]) 0) 29 true) (.node 335 (sourceLit (List.headD (raw_ints% [434064489957643163001767487121943925]) 0) 31 true) (.node 334 (sourceLit (List.headD (raw_ints% [349337042821019552965337432475]) 0) 49 false) (.node 333 (sourceLit (List.headD (raw_ints% [1146035570919674117472183356117780625]) 0) 32 true) .empty .empty) .empty) (.node 336 (sourceLit (List.headD (raw_ints% [77171911700480217652320376425]) 0) 51 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [4073950533631386464318795175]) 0) 55 false) (.node 339 (sourceLit (List.headD (raw_ints% [724680895243812839544662972225621775]) 0) 28 true) (.node 338 (sourceLit (List.headD (raw_ints% [1097733092496256982451396825]) 0) 57 false) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [6625927032355787744913441664241833425]) 0) 24 true) .empty .empty)))

#time def treeG_J004_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [19996917781343165910494192844983790225]) 0) 20 true) (.node 345 (sourceLit (List.headD (raw_ints% [18480168835401241961759180676903530175]) 0) 21 true) (.node 344 (sourceLit (List.headD (raw_ints% [56765427249459957445896075]) 0) 61 false) (.node 343 (sourceLit (List.headD (raw_ints% [7871763719338331231087325842060529225]) 0) 23 true) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [27117799067902221271884375]) 0) 62 false) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [66441636391256740530187268774752828125]) 0) 17 true) (.node 348 (sourceLit (List.headD (raw_ints% [26050403082099544531354575]) 0) 62 false) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [6283329302905642246347603]) 0) 64 false) .empty .empty)))

#time def treeG_J004_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [478651730262436901133846225]) 0) 58 false) treeG_J004_part056 treeG_J004_part057)

#time def treeG_J004_part059 : IntSourceTree :=
  (.node 332 (sourceLit (List.headD (raw_ints% [56149024502469296676655776967425]) 0) 47 true) treeG_J004_part055 treeG_J004_part058)

#time def treeG_J004_part060 : IntSourceTree :=
  (.node 303 (sourceLit (List.headD (raw_ints% [2959779755533605756780825]) 0) 65 false) treeG_J004_part052 treeG_J004_part059)

#time def treeG_J004_part061 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [125307986873974521890616207604815075]) 0) 29 true) treeG_J004_part045 treeG_J004_part060)

#time def treeG_J004_part062 : IntSourceTree :=
  (.node 167 (sourceLit (List.headD (raw_ints% [2342091748544901780151870730710125]) 0) 38 false) treeG_J004_part030 treeG_J004_part061)

#time def treeG_J004_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [11229679236101016108803]) 0) 73 false) (.node 354 (sourceLit (List.headD (raw_ints% [46148172083885930113361]) 0) 71 false) (.node 353 (sourceLit (List.headD (raw_ints% [405859913291554635785999133300348696075]) 0) 14 false) (.node 352 (sourceLit (List.headD (raw_ints% [1520855179951268350864711]) 0) 66 false) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [1421049479782932926692924640021923324545]) 0) 13 false) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [145413804185577815497795023338613765635055]) 0) 7 false) (.node 358 (sourceLit (List.headD (raw_ints% [21906258517581087826171]) 0) 72 false) (.node 357 (sourceLit (List.headD (raw_ints% [60663369808619032547867954927329926130095]) 0) 8 false) .empty .empty) .empty) (.node 371 (sourceLit (List.headD (raw_ints% [176590415138334397067920380953625]) 0) 47 false) .empty .empty)))

#time def treeG_J004_part064 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [48626930436933865868508422025]) 0) 52 false) (.node 375 (sourceLit (List.headD (raw_ints% [225749812219991391979424895975]) 0) 50 false) (.node 374 (sourceLit (List.headD (raw_ints% [1084191444507385589075694858891151125]) 0) 33 true) (.node 373 (sourceLit (List.headD (raw_ints% [56696963120323229816060608749375]) 0) 48 true) .empty .empty) .empty) (.node 376 (sourceLit (List.headD (raw_ints% [382254436347579955184764603052813625]) 0) 32 true) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [603797978861959372183950121885009275]) 0) 29 true) (.node 379 (sourceLit (List.headD (raw_ints% [10869518180892667107368326725]) 0) 54 false) (.node 378 (sourceLit (List.headD (raw_ints% [596129846491964324901828418599272625]) 0) 30 true) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [1243747430037205610019213825]) 0) 57 false) .empty .empty)))

#time def treeG_J004_part065 : IntSourceTree :=
  (.node 372 (sourceLit (List.headD (raw_ints% [518843417936449756005480283858324125]) 0) 36 false) treeG_J004_part063 treeG_J004_part064)

#time def treeG_J004_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [32281235758432814157879075]) 0) 62 false) (.node 385 (sourceLit (List.headD (raw_ints% [4252089002328780915352275]) 0) 65 false) (.node 384 (sourceLit (List.headD (raw_ints% [6723964021659752963724999117957848925]) 0) 24 true) (.node 383 (sourceLit (List.headD (raw_ints% [289225825908286132699873425]) 0) 59 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [16657144664170011392020066587611250075]) 0) 22 true) .empty .empty)) (.node 390 (sourceLit (List.headD (raw_ints% [90952882803062884352540521889767825425]) 0) 18 true) (.node 389 (sourceLit (List.headD (raw_ints% [15418244968600844110072725]) 0) 63 false) (.node 388 (sourceLit (List.headD (raw_ints% [20231365584011072459153268147887607525]) 0) 21 true) .empty .empty) .empty) (.node 391 (sourceLit (List.headD (raw_ints% [3701230003807571083650615]) 0) 65 false) .empty .empty)))

#time def treeG_J004_part067 : IntSourceTree :=
  (.node 397 (sourceLit (List.headD (raw_ints% [52357958736762801099527]) 0) 71 false) (.node 395 (sourceLit (List.headD (raw_ints% [215827132617597055861433]) 0) 69 false) (.node 394 (sourceLit (List.headD (raw_ints% [31328775366012038265303209950896064425]) 0) 15 true) (.node 393 (sourceLit (List.headD (raw_ints% [892232366622979665862895]) 0) 67 false) .empty .empty) .empty) (.node 396 (sourceLit (List.headD (raw_ints% [381689621134422860023260641106002464725]) 0) 14 false) .empty .empty)) (.node 399 (sourceLit (List.headD (raw_ints% [12732548857033310660363]) 0) 73 false) (.node 398 (sourceLit (List.headD (raw_ints% [23184933549487537962148948612219876173675]) 0) 9 false) .empty .empty) (.node 412 (sourceLit (List.headD (raw_ints% [409329854779138090812496538874675]) 0) 47 false) .empty .empty)))

#time def treeG_J004_part068 : IntSourceTree :=
  (.node 392 (sourceLit (List.headD (raw_ints% [81481112559445913723648551192603894125]) 0) 17 true) treeG_J004_part066 treeG_J004_part067)

#time def treeG_J004_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [5531895047749811489396630731275909525]) 0) 25 true) treeG_J004_part065 treeG_J004_part068)

#time def treeG_J004_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [31063200956993754149286072825]) 0) 53 false) (.node 416 (sourceLit (List.headD (raw_ints% [74288950259755587163552259775]) 0) 52 false) (.node 415 (sourceLit (List.headD (raw_ints% [8239467066101441549603791384007265075]) 0) 31 true) (.node 414 (sourceLit (List.headD (raw_ints% [28523150081572124684512973090925]) 0) 50 true) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [5412418110674242479774803711343748275]) 0) 29 true) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [32017143614809612074859366136398760175]) 0) 24 true) (.node 420 (sourceLit (List.headD (raw_ints% [3397783823630640321524765775]) 0) 56 false) (.node 419 (sourceLit (List.headD (raw_ints% [4044357876691901759669964376568559225]) 0) 28 true) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [47818481235923044305335475]) 0) 62 false) .empty .empty)))

#time def treeG_J004_part071 : IntSourceTree :=
  (.node 428 (sourceLit (List.headD (raw_ints% [38512068434766083784403575]) 0) 62 false) (.node 426 (sourceLit (List.headD (raw_ints% [40915624969358273373752025]) 0) 62 false) (.node 425 (sourceLit (List.headD (raw_ints% [89103255511154805457840805210422052625]) 0) 21 true) (.node 424 (sourceLit (List.headD (raw_ints% [175694971409366217808081275]) 0) 60 false) .empty .empty) .empty) (.node 427 (sourceLit (List.headD (raw_ints% [113260239532016925225666339855906210375]) 0) 20 true) .empty .empty)) (.node 430 (sourceLit (List.headD (raw_ints% [4567457832847600931862561]) 0) 65 false) (.node 429 (sourceLit (List.headD (raw_ints% [580962062297097578162717311957650612675]) 0) 17 true) .empty .empty) (.node 431 (sourceLit (List.headD (raw_ints% [729205870192870218977092520673519353775]) 0) 16 true) .empty .empty)))

#time def treeG_J004_part072 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [36383396662660160684085720008146746975]) 0) 23 true) treeG_J004_part070 treeG_J004_part071)

#time def treeG_J004_part073 : IntSourceTree :=
  (.node 437 (sourceLit (List.headD (raw_ints% [11807098303412906464890592865761610645295]) 0) 8 true) (.node 435 (sourceLit (List.headD (raw_ints% [1671679682711029232815350319629091839945]) 0) 13 true) (.node 434 (sourceLit (List.headD (raw_ints% [523046989951892224956007]) 0) 68 false) (.node 433 (sourceLit (List.headD (raw_ints% [1709557714242689255364375952382011002075]) 0) 14 true) .empty .empty) .empty) (.node 436 (sourceLit (List.headD (raw_ints% [125989698728788926991009]) 0) 70 false) .empty .empty)) (.node 454 (sourceLit (List.headD (raw_ints% [9416608194696725949361623649237651875]) 0) 34 false) (.node 439 (sourceLit (List.headD (raw_ints% [40065664210322488199396565559145243754345]) 0) 7 false) (.node 438 (sourceLit (List.headD (raw_ints% [7612925054795428318339]) 0) 74 false) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [57272049975364240761005371077825]) 0) 50 true) .empty .empty)))

#time def treeG_J004_part074 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [1077018196796717355752775975]) 0) 58 false) (.node 459 (sourceLit (List.headD (raw_ints% [5048420694025271760479436525]) 0) 56 false) (.node 458 (sourceLit (List.headD (raw_ints% [2408144132091139077436487646372237825]) 0) 31 true) (.node 457 (sourceLit (List.headD (raw_ints% [99950970082577308458596097525]) 0) 52 false) .empty .empty) .empty) (.node 460 (sourceLit (List.headD (raw_ints% [1720279948914971193743007127341774975]) 0) 30 true) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [475869873866482576185494175]) 0) 59 false) (.node 462 (sourceLit (List.headD (raw_ints% [13242624283529900292731367702561425325]) 0) 26 true) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [14829716320500203860180360445094449025]) 0) 25 true) .empty .empty)))

#time def treeG_J004_part075 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [3928606314876930797209513390477225725]) 0) 33 true) treeG_J004_part073 treeG_J004_part074)

#time def treeG_J004_part076 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [136273426491018920799119]) 0) 70 false) treeG_J004_part072 treeG_J004_part075)

#time def treeG_J004_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [17749024944886066309647552439584152625]) 0) 32 false) treeG_J004_part069 treeG_J004_part076)

#time def treeG_J004_part078 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [245004589747017346905088395033941393625]) 0) 19 true) (.node 468 (sourceLit (List.headD (raw_ints% [46514436974002926383256535854009301425]) 0) 22 true) (.node 467 (sourceLit (List.headD (raw_ints% [49550014180283732589624975]) 0) 62 false) (.node 466 (sourceLit (List.headD (raw_ints% [36223055423492397032910369311405401275]) 0) 23 true) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [11546911733082619837165425]) 0) 64 false) .empty .empty)) (.node 473 (sourceLit (List.headD (raw_ints% [1288142457233323066923009]) 0) 67 false) (.node 472 (sourceLit (List.headD (raw_ints% [323862378816712152626721984740457729825]) 0) 18 true) (.node 471 (sourceLit (List.headD (raw_ints% [5433685661887630780074507]) 0) 65 false) .empty .empty) .empty) (.node 474 (sourceLit (List.headD (raw_ints% [839114469438338608549536371215557468825]) 0) 16 true) .empty .empty)))

#time def treeG_J004_part079 : IntSourceTree :=
  (.node 495 (sourceLit (List.headD (raw_ints% [158905198181249056739389769771809695075]) 0) 31 false) (.node 478 (sourceLit (List.headD (raw_ints% [17496015926450222213519770738990743409485]) 0) 10 true) (.node 477 (sourceLit (List.headD (raw_ints% [36815869996013062945741]) 0) 72 false) (.node 476 (sourceLit (List.headD (raw_ints% [1026684651922726046419305480367547152335]) 0) 15 true) .empty .empty) .empty) (.node 479 (sourceLit (List.headD (raw_ints% [17719151362148402612993]) 0) 73 false) .empty .empty)) (.node 497 (sourceLit (List.headD (raw_ints% [120302983965387543030929624783927474925]) 0) 29 true) (.node 496 (sourceLit (List.headD (raw_ints% [57420627875883751935332475597375]) 0) 51 true) .empty .empty) (.node 498 (sourceLit (List.headD (raw_ints% [17221942281395888577327506175]) 0) 55 false) .empty .empty)))

#time def treeG_J004_part080 : IntSourceTree :=
  (.node 475 (sourceLit (List.headD (raw_ints% [153609928667147584547287]) 0) 70 false) treeG_J004_part078 treeG_J004_part079)

#time def treeG_J004_part081 : IntSourceTree :=
  (.node 504 (sourceLit (List.headD (raw_ints% [75043725614279089594353225]) 0) 62 false) (.node 502 (sourceLit (List.headD (raw_ints% [694470346909333001310092175]) 0) 59 false) (.node 501 (sourceLit (List.headD (raw_ints% [188178689846306700724245546163348436625]) 0) 24 true) (.node 500 (sourceLit (List.headD (raw_ints% [6699057564419903199434107275]) 0) 56 false) .empty .empty) .empty) (.node 503 (sourceLit (List.headD (raw_ints% [175498591873818243999616163232836058225]) 0) 23 true) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [466308647243861427300899569126580210025]) 0) 20 true) (.node 506 (sourceLit (List.headD (raw_ints% [33372961201373724894346425]) 0) 63 false) (.node 505 (sourceLit (List.headD (raw_ints% [385447666744851718067930729032600316175]) 0) 21 true) .empty .empty) .empty) (.node 508 (sourceLit (List.headD (raw_ints% [60587959925801381394846375]) 0) 62 false) .empty .empty)))

#time def treeG_J004_part082 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [382547733640715420983501]) 0) 69 false) (.node 512 (sourceLit (List.headD (raw_ints% [3253310838031328047288603]) 0) 66 false) (.node 511 (sourceLit (List.headD (raw_ints% [3190867565759407331504321799869542944225]) 0) 16 true) (.node 510 (sourceLit (List.headD (raw_ints% [436215868764688681581429]) 0) 69 false) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [8654038407892099628690727559312636352325]) 0) 14 true) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [181230158605506242103565]) 0) 70 false) (.node 515 (sourceLit (List.headD (raw_ints% [11754151828302388503977231619819827661255]) 0) 13 true) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [251024172588804961418451610108330460352465]) 0) 8 true) .empty .empty)))

#time def treeG_J004_part083 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [2395961904039089710365700982698944678525]) 0) 17 true) treeG_J004_part081 treeG_J004_part082)

#time def treeG_J004_part084 : IntSourceTree :=
  (.node 499 (sourceLit (List.headD (raw_ints% [34485948236766323479313837965387245975]) 0) 28 true) treeG_J004_part080 treeG_J004_part083)

#time def treeG_J004_part085 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [31045388338936381091827823710703696025]) 0) 29 true) (.node 538 (sourceLit (List.headD (raw_ints% [115486695701205264876056649491182999275]) 0) 30 true) (.node 537 (sourceLit (List.headD (raw_ints% [14380144711491582310947767923725]) 0) 54 true) (.node 519 (sourceLit (List.headD (raw_ints% [320001919033526043615712897382997138306105]) 0) 7 true) .empty .empty) .empty) (.node 539 (sourceLit (List.headD (raw_ints% [6086760793685308408424034825]) 0) 57 false) .empty .empty)) (.node 543 (sourceLit (List.headD (raw_ints% [913070819952183426434690175]) 0) 59 false) (.node 542 (sourceLit (List.headD (raw_ints% [161693441279246900138782810758225585975]) 0) 25 true) (.node 541 (sourceLit (List.headD (raw_ints% [4545021170826468487928555325]) 0) 57 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [145839159232817836279255442342647160175]) 0) 24 true) .empty .empty)))

#time def treeG_J004_part086 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [1905952724545055016555524192631061891275]) 0) 18 true) (.node 548 (sourceLit (List.headD (raw_ints% [373279773295855574534386497418561607175]) 0) 21 true) (.node 547 (sourceLit (List.headD (raw_ints% [83941830625211166987760725]) 0) 62 false) (.node 546 (sourceLit (List.headD (raw_ints% [313001555897866924002109990409789513625]) 0) 22 true) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [37494136459636141720515525]) 0) 63 false) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [2543142808125983026250877830388627484575]) 0) 17 true) (.node 551 (sourceLit (List.headD (raw_ints% [8525222138582407030531221]) 0) 65 false) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [982584190399002490182797]) 0) 68 false) .empty .empty)))

#time def treeG_J004_part087 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [192513355085010635214968025]) 0) 61 false) treeG_J004_part085 treeG_J004_part086)

#time def treeG_J004_part088 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [25460888410696010005133]) 0) 73 false) (.node 557 (sourceLit (List.headD (raw_ints% [107598418613480116212083]) 0) 71 false) (.node 556 (sourceLit (List.headD (raw_ints% [9700782524456936411138620659084733356585]) 0) 14 true) (.node 555 (sourceLit (List.headD (raw_ints% [114468902486783918218107]) 0) 71 false) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [216032140735904516991412068630348973533495]) 0) 9 true) .empty .empty)) (.node 582 (sourceLit (List.headD (raw_ints% [3156080477007802485308370975]) 0) 58 false) (.node 581 (sourceLit (List.headD (raw_ints% [1798726163845621689152735171321688108975]) 0) 24 true) (.node 580 (sourceLit (List.headD (raw_ints% [17647985610321330434262032025]) 0) 56 false) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [1118048938360156957110646322832968629575]) 0) 23 true) .empty .empty)))

#time def treeG_J004_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [9548990841428288674734666934695026751075]) 0) 17 true) (.node 587 (sourceLit (List.headD (raw_ints% [2037703799939073964715980354151735898975]) 0) 20 true) (.node 586 (sourceLit (List.headD (raw_ints% [125767432682263185426275175]) 0) 62 false) (.node 585 (sourceLit (List.headD (raw_ints% [1947978880980233662400156348449754246625]) 0) 21 true) .empty .empty) .empty) (.node 588 (sourceLit (List.headD (raw_ints% [107295701324620952580675075]) 0) 62 false) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [12056754230601032800939871741178952185975]) 0) 16 true) (.node 590 (sourceLit (List.headD (raw_ints% [23535228659166103909909797]) 0) 64 false) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [2635955650275539491621309]) 0) 67 false) .empty .empty)))

#time def treeG_J004_part090 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [612895917495067068057277275]) 0) 60 false) treeG_J004_part088 treeG_J004_part089)

#time def treeG_J004_part091 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [6975809469015422411591654816881521414675]) 0) 15 true) treeG_J004_part087 treeG_J004_part090)

#time def treeG_J004_part092 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [21590019886422206309063]) 0) 73 false) treeG_J004_part084 treeG_J004_part091)

#time def treeG_J004_part093 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [107661547372105723162444875]) 0) 61 false) treeG_J004_part077 treeG_J004_part092)

#time def treeG_J004_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [64418378840635703593957]) 0) 72 false) (.node 596 (sourceLit (List.headD (raw_ints% [276645451341629430768863]) 0) 70 false) (.node 595 (sourceLit (List.headD (raw_ints% [44052323923820990788756006915232343656145]) 0) 13 true) (.node 594 (sourceLit (List.headD (raw_ints% [9375569636848235456239]) 0) 75 false) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [990675990541682899207291834254515409290415]) 0) 8 true) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [204629090320796848626744045070432815375]) 0) 28 true) (.node 621 (sourceLit (List.headD (raw_ints% [3275741109873715486583369175]) 0) 59 false) (.node 599 (sourceLit (List.headD (raw_ints% [1408255206853710092315583651659794649961855]) 0) 7 true) .empty .empty) .empty) (.node 623 (sourceLit (List.headD (raw_ints% [70094051782988095589802525]) 0) 64 false) .empty .empty)))

#time def treeG_J004_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [34900782432492405430079775]) 0) 64 false) (.node 627 (sourceLit (List.headD (raw_ints% [167593034739315203864789625]) 0) 62 false) (.node 626 (sourceLit (List.headD (raw_ints% [204372165635295842299755794754995591625]) 0) 25 true) (.node 625 (sourceLit (List.headD (raw_ints% [210191281205028216421154625]) 0) 62 false) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [208053003330402298772699232091646786475]) 0) 24 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [938125407536481054961161]) 0) 69 false) (.node 630 (sourceLit (List.headD (raw_ints% [955379764610404207272392842757995607475]) 0) 21 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [1189201427809381221836124238848790587675]) 0) 20 true) .empty .empty)))

#time def treeG_J004_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [121526222390917390103923860061290183675]) 0) 27 true) treeG_J004_part094 treeG_J004_part095)

#time def treeG_J004_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [96830481225722297776984970703020804469615]) 0) 12 true) (.node 636 (sourceLit (List.headD (raw_ints% [4293942674920506797202173282018451287445]) 0) 17 true) (.node 635 (sourceLit (List.headD (raw_ints% [185549325892359616381541]) 0) 71 false) (.node 634 (sourceLit (List.headD (raw_ints% [3132554631638525797466457863752985248275]) 0) 18 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [42261758182037328639195]) 0) 73 false) .empty .empty)) (.node 664 (sourceLit (List.headD (raw_ints% [1630113739560551990816403525]) 0) 60 false) (.node 663 (sourceLit (List.headD (raw_ints% [11978212842170841355000972561674731554425]) 0) 23 true) (.node 639 (sourceLit (List.headD (raw_ints% [4869686303742461698603]) 0) 76 false) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [13607377585057192270902097739395389263775]) 0) 21 true) .empty .empty)))

#time def treeG_J004_part098 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [49087550704464836464493270195332766692425]) 0) 16 true) (.node 669 (sourceLit (List.headD (raw_ints% [43712578011154699811076336480766550586525]) 0) 17 true) (.node 668 (sourceLit (List.headD (raw_ints% [227890368154009455148904175]) 0) 62 false) (.node 667 (sourceLit (List.headD (raw_ints% [11042114800719859942468390510167981965025]) 0) 20 true) .empty .empty) .empty) (.node 670 (sourceLit (List.headD (raw_ints% [46266336205818706950249753]) 0) 64 false) .empty .empty)) (.node 673 (sourceLit (List.headD (raw_ints% [120181536237477167603700584845739791821525]) 0) 14 true) (.node 672 (sourceLit (List.headD (raw_ints% [4869047610016308948067979]) 0) 67 false) .empty .empty) (.node 674 (sourceLit (List.headD (raw_ints% [65833437694890620764951]) 0) 73 false) .empty .empty)))

#time def treeG_J004_part099 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [294615129727793247416034075]) 0) 62 false) treeG_J004_part097 treeG_J004_part098)

#time def treeG_J004_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [103335716242283562589907]) 0) 72 false) treeG_J004_part096 treeG_J004_part099)

#time def treeG_J004_part101 : IntSourceTree :=
  (.node 704 (sourceLit (List.headD (raw_ints% [11006003063043502234169581681184410085025]) 0) 24 true) (.node 678 (sourceLit (List.headD (raw_ints% [104628653887513610962823]) 0) 72 false) (.node 677 (sourceLit (List.headD (raw_ints% [3406321308576916061127733606532378709053265]) 0) 8 true) (.node 676 (sourceLit (List.headD (raw_ints% [465551852227809034757301]) 0) 70 false) .empty .empty) .empty) (.node 679 (sourceLit (List.headD (raw_ints% [4788895591592516965411454473333536836093505]) 0) 7 true) .empty .empty)) (.node 707 (sourceLit (List.headD (raw_ints% [421637224716271290967278525]) 0) 62 false) (.node 706 (sourceLit (List.headD (raw_ints% [11972400259974825532504051381355424530775]) 0) 22 true) (.node 705 (sourceLit (List.headD (raw_ints% [1209731177150495557974094275]) 0) 61 false) .empty .empty) .empty) (.node 708 (sourceLit (List.headD (raw_ints% [9377690774076641552286796653434807673225]) 0) 21 true) .empty .empty)))

#time def treeG_J004_part102 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [95121099184368961223968921935715909835325]) 0) 15 true) (.node 712 (sourceLit (List.headD (raw_ints% [39573939281989786689804276284542441991025]) 0) 17 true) (.node 711 (sourceLit (List.headD (raw_ints% [31256329685235010070871177]) 0) 65 false) (.node 710 (sourceLit (List.headD (raw_ints% [36069539894271466152897193738702585726725]) 0) 18 true) .empty .empty) .empty) (.node 713 (sourceLit (List.headD (raw_ints% [3215676150139771946629467]) 0) 68 false) .empty .empty)) (.node 716 (sourceLit (List.headD (raw_ints% [122079631101680605871479910108811101933895]) 0) 14 true) (.node 715 (sourceLit (List.headD (raw_ints% [341118175666765349738067]) 0) 71 false) .empty .empty) (.node 717 (sourceLit (List.headD (raw_ints% [296504819499659720200521]) 0) 71 false) .empty .empty)))

#time def treeG_J004_part103 : IntSourceTree :=
  (.node 709 (sourceLit (List.headD (raw_ints% [158088803289024644288744625]) 0) 63 false) treeG_J004_part101 treeG_J004_part102)

#time def treeG_J004_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [615384081278533126785652875]) 0) 62 false) (.node 746 (sourceLit (List.headD (raw_ints% [114389505927837788819757525]) 0) 65 false) (.node 745 (sourceLit (List.headD (raw_ints% [162488671423638843475811209159555172096625]) 0) 21 true) (.node 719 (sourceLit (List.headD (raw_ints% [65671163457573917373999]) 0) 73 false) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [84737087279078744317564020540675414281175]) 0) 20 true) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [239468768449706892758684279714287919121375]) 0) 16 true) (.node 750 (sourceLit (List.headD (raw_ints% [13977808385400742167311859]) 0) 67 false) (.node 749 (sourceLit (List.headD (raw_ints% [256373526759297829862101156429147294956675]) 0) 17 true) .empty .empty) .empty) (.node 752 (sourceLit (List.headD (raw_ints% [21518234465202392174735219]) 0) 66 false) .empty .empty)))

#time def treeG_J004_part105 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [95938082806073054618849]) 0) 73 false) (.node 756 (sourceLit (List.headD (raw_ints% [898920850439252364194967]) 0) 70 false) (.node 755 (sourceLit (List.headD (raw_ints% [604537620973907029542654079120768566449145]) 0) 13 true) (.node 754 (sourceLit (List.headD (raw_ints% [2162341147021522014390251]) 0) 69 false) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [12219871472438201490421694887395442338485295]) 0) 8 true) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [75258135581832008971653578889099873782925]) 0) 23 true) (.node 759 (sourceLit (List.headD (raw_ints% [16264524078576584465883376253932161350277255]) 0) 7 true) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [1408594870129133330148841875]) 0) 62 false) .empty .empty)))

#time def treeG_J004_part106 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [513001492274359419433167835706939280034875]) 0) 14 true) treeG_J004_part104 treeG_J004_part105)

#time def treeG_J004_part107 : IntSourceTree :=
  (.node 718 (sourceLit (List.headD (raw_ints% [2631677458771137678911853840908212273296345]) 0) 9 true) treeG_J004_part103 treeG_J004_part106)

#time def treeG_J004_part108 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [156431172501044660249097296364958712233455]) 0) 13 true) treeG_J004_part100 treeG_J004_part107)

#time def treeG_J004_part109 : IntSourceTree :=
  (.node 793 (sourceLit (List.headD (raw_ints% [15086882164922848281476285]) 0) 67 false) (.node 791 (sourceLit (List.headD (raw_ints% [80566137397970927267623695]) 0) 65 false) (.node 790 (sourceLit (List.headD (raw_ints% [110151993432513181854601981345222354614975]) 0) 19 true) (.node 789 (sourceLit (List.headD (raw_ints% [228647638994754241248454125]) 0) 64 false) .empty .empty) .empty) (.node 792 (sourceLit (List.headD (raw_ints% [99947414583858553034440001714872738565175]) 0) 18 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [241228994936113211835587084505978732257625]) 0) 15 true) (.node 795 (sourceLit (List.headD (raw_ints% [1480104795687991314914117]) 0) 70 false) (.node 794 (sourceLit (List.headD (raw_ints% [208940196544995229104599456885611685099775]) 0) 16 true) .empty .empty) .empty) (.node 797 (sourceLit (List.headD (raw_ints% [301208015469796321997223]) 0) 72 false) .empty .empty)))

#time def treeG_J004_part110 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [172736405453151272579206689]) 0) 65 false) (.node 828 (sourceLit (List.headD (raw_ints% [2201805658979733533512030875]) 0) 62 false) (.node 827 (sourceLit (List.headD (raw_ints% [1119393082030233399228893241684922566245625]) 0) 20 true) (.node 799 (sourceLit (List.headD (raw_ints% [126205002154572191863699]) 0) 73 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [2155127161400769458626770007962552116497725]) 0) 17 true) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [14761975733192133773222119]) 0) 68 false) (.node 831 (sourceLit (List.headD (raw_ints% [1522963126470504016914947421809269754718225]) 0) 16 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [2685315774409114277668912219168988354050725]) 0) 14 true) .empty .empty)))

#time def treeG_J004_part111 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [4794097006833531905754920523243615032594475]) 0) 10 true) treeG_J004_part109 treeG_J004_part110)

#time def treeG_J004_part112 : IntSourceTree :=
  (.node 839 (sourceLit (List.headD (raw_ints% [60441028030759926026195352117965679171234345]) 0) 7 true) (.node 837 (sourceLit (List.headD (raw_ints% [49534751231206780739488598746135113119466705]) 0) 8 true) (.node 836 (sourceLit (List.headD (raw_ints% [2061288740936730265633267]) 0) 70 false) (.node 835 (sourceLit (List.headD (raw_ints% [2738505523746016636130937231049018395147255]) 0) 13 true) .empty .empty) .empty) (.node 838 (sourceLit (List.headD (raw_ints% [102634966331861633689187]) 0) 74 false) .empty .empty)) (.node 870 (sourceLit (List.headD (raw_ints% [1934823174535743094917566045272107407267775]) 0) 18 true) (.node 869 (sourceLit (List.headD (raw_ints% [1744510380990225051015122625]) 0) 63 false) (.node 868 (sourceLit (List.headD (raw_ints% [1044033685525231296463616017797681959637675]) 0) 21 true) .empty .empty) .empty) (.node 871 (sourceLit (List.headD (raw_ints% [264906673508331617890789683]) 0) 65 false) .empty .empty)))

#time def treeG_J004_part113 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [1458872709997137621638821]) 0) 71 false) (.node 875 (sourceLit (List.headD (raw_ints% [7801990279503821622867549]) 0) 69 false) (.node 874 (sourceLit (List.headD (raw_ints% [2267435381319123819459713305397764983851175]) 0) 15 true) (.node 873 (sourceLit (List.headD (raw_ints% [43961020767845686811412191]) 0) 67 false) .empty .empty) .empty) (.node 876 (sourceLit (List.headD (raw_ints% [2256047533873790212459763062037060930632005]) 0) 14 true) .empty .empty)) (.node 879 (sourceLit (List.headD (raw_ints% [284334863172874342893049]) 0) 73 false) (.node 878 (sourceLit (List.headD (raw_ints% [39946557217539716927978757699647883054277755]) 0) 9 true) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [31253950775406632028208942561563270591907875]) 0) 17 true) .empty .empty)))

#time def treeG_J004_part114 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [1323068297302786910846067418379524277587875]) 0) 17 true) treeG_J004_part112 treeG_J004_part113)

#time def treeG_J004_part115 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [10762199870879804252695783]) 0) 68 false) treeG_J004_part111 treeG_J004_part114)

#time def treeG_J004_part116 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [15400977526806973919546769212133101475662145]) 0) 13 true) (.node 913 (sourceLit (List.headD (raw_ints% [18483776982435476295868166474903400087355275]) 0) 14 true) (.node 912 (sourceLit (List.headD (raw_ints% [205858770575563082797901207]) 0) 66 false) (.node 911 (sourceLit (List.headD (raw_ints% [13955622269815440742425580940367589503423975]) 0) 16 true) .empty .empty) .empty) (.node 914 (sourceLit (List.headD (raw_ints% [4149852612120735319839551]) 0) 71 false) .empty .empty)) (.node 918 (sourceLit (List.headD (raw_ints% [1048332844669691086882073]) 0) 72 false) (.node 917 (sourceLit (List.headD (raw_ints% [239239333104638366455361073194608686001429935]) 0) 8 true) (.node 916 (sourceLit (List.headD (raw_ints% [2870350769283545678617141]) 0) 71 false) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [259131429709557809397634709479217385262987695]) 0) 7 true) .empty .empty)))

#time def treeG_J004_part117 : IntSourceTree :=
  (.node 955 (sourceLit (List.headD (raw_ints% [25396830617462060935848859]) 0) 69 false) (.node 953 (sourceLit (List.headD (raw_ints% [20237218725964674498311127]) 0) 70 false) (.node 952 (sourceLit (List.headD (raw_ints% [3158138493128163457894878380497016306459025]) 0) 19 true) (.node 951 (sourceLit (List.headD (raw_ints% [283532724143897721991479891]) 0) 67 false) .empty .empty) .empty) (.node 954 (sourceLit (List.headD (raw_ints% [4054085400279088119102113292376408775876025]) 0) 17 true) .empty .empty)) (.node 957 (sourceLit (List.headD (raw_ints% [4281828828569953735595461]) 0) 71 false) (.node 956 (sourceLit (List.headD (raw_ints% [3286232498233295926771751537524010136257535]) 0) 16 true) .empty .empty) (.node 958 (sourceLit (List.headD (raw_ints% [49823193971774662381845578873740200736788045]) 0) 11 true) .empty .empty)))

#time def treeG_J004_part118 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [7329781900217722233322844129072790796160025]) 0) 20 true) treeG_J004_part116 treeG_J004_part117)

#time def treeG_J004_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [1443311705990809148051775714017684503762427985]) 0) 8 true) (.node 995 (sourceLit (List.headD (raw_ints% [114329755282123845891720856143911979352370655]) 0) 13 true) (.node 994 (sourceLit (List.headD (raw_ints% [2010920764230492397308947]) 0) 74 false) (.node 993 (sourceLit (List.headD (raw_ints% [183637086577766985009404049876905643526022325]) 0) 14 true) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [19656129078894969578614577]) 0) 70 false) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [167420744976650632532995596707400008422518225]) 0) 15 true) (.node 999 (sourceLit (List.headD (raw_ints% [1335210777387231386821423814480469038314229745]) 0) 7 true) (.node 998 (sourceLit (List.headD (raw_ints% [808373995975065662178347]) 0) 74 false) .empty .empty) .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [103302098293289452491923749]) 0) 69 false) .empty .empty)))

#time def treeG_J004_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [20911492303598620728327293]) 0) 72 false) (.node 1039 (sourceLit (List.headD (raw_ints% [617374500600861476181091]) 0) 75 false) (.node 1038 (sourceLit (List.headD (raw_ints% [1244018930103710498524393398522723700815275805]) 0) 9 true) (.node 1037 (sourceLit (List.headD (raw_ints% [3843575062581253960754779]) 0) 73 false) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [1225036204531081214372243917515288088027775145]) 0) 13 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [189700066662886768661027]) 0) 78 false) (.node 1077 (sourceLit (List.headD (raw_ints% [11508345931025595611581357085190755663577157935]) 0) 8 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [8616940663442452601373723373701320568207976695]) 0) 7 true) .empty .empty)))

#time def treeG_J004_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [101184825289190662184633849993815938807340515]) 0) 14 true) treeG_J004_part119 treeG_J004_part120)

#time def treeG_J004_part122 : IntSourceTree :=
  (.node 959 (sourceLit (List.headD (raw_ints% [23874936921775523249657]) 0) 78 false) treeG_J004_part118 treeG_J004_part121)

#time def treeG_J004_part123 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [1399037570083922505856709247]) 0) 64 false) treeG_J004_part115 treeG_J004_part122)

#time def treeG_J004_part124 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [37679698252501051382638611943620303303975]) 0) 22 true) treeG_J004_part108 treeG_J004_part123)

#time def treeG_J004_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [32036246522123628791323317726905403400875]) 0) 14 true) treeG_J004_part093 treeG_J004_part124)

#time def treeG_J004_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [1582807768367144156768345555376750375]) 0) 16 false) treeG_J004_part062 treeG_J004_part125)

#time def treeG_J004 : IntSourceTree := treeG_J004_part126

#time def treeG_J005_part000 : IntSourceTree :=
  (.node 5 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 true) (.node 3 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 2 (sourceLit (List.headD (raw_ints% [13538102592745096995097518674625]) 0) 40 false) (.node 1 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 37 false) .empty .empty) .empty) (.node 4 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 42 false) .empty .empty)) (.node 8 (sourceLit (List.headD (raw_ints% [40852340351294545437953611297275]) 0) 38 true) (.node 7 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 42 false) (.node 6 (sourceLit (List.headD (raw_ints% [62275271926627446177448585903275]) 0) 39 true) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 44 false) .empty .empty)))

#time def treeG_J005_part001 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [20883005320424934845374798725]) 0) 49 false) (.node 13 (sourceLit (List.headD (raw_ints% [86170882779567764518531373325]) 0) 47 false) (.node 12 (sourceLit (List.headD (raw_ints% [94622455983725221721645627526375]) 0) 35 true) (.node 11 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 47 false) .empty .empty) .empty) (.node 14 (sourceLit (List.headD (raw_ints% [406680246278373867235169113004625]) 0) 32 true) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [86278170771187225006328624396925]) 0) 29 true) (.node 17 (sourceLit (List.headD (raw_ints% [2538579356522261068791337875]) 0) 52 false) (.node 16 (sourceLit (List.headD (raw_ints% [350213537860236951697554652419525]) 0) 31 true) .empty .empty) .empty) (.node 19 (sourceLit (List.headD (raw_ints% [154694584012997881570478625]) 0) 56 false) .empty .empty)))

#time def treeG_J005_part002 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [84471809364402923888091990147825]) 0) 36 true) treeG_J005_part000 treeG_J005_part001)

#time def treeG_J005_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [18127104063648026568768675]) 0) 59 false) (.node 23 (sourceLit (List.headD (raw_ints% [73969273953491384605855725]) 0) 57 false) (.node 22 (sourceLit (List.headD (raw_ints% [52715103471855659476736448613491375]) 0) 24 false) (.node 21 (sourceLit (List.headD (raw_ints% [302291022410164325309166675]) 0) 55 false) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [143680357171804695668167672099830375]) 0) 23 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [1600237952289638808373890650371329855]) 0) 20 false) (.node 27 (sourceLit (List.headD (raw_ints% [2224007118540581871978675]) 0) 62 false) (.node 26 (sourceLit (List.headD (raw_ints% [698420476174341126704089092207497505]) 0) 21 false) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [2185356442832756211088125]) 0) 62 false) .empty .empty)))

#time def treeG_J005_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [1017985650336098973529]) 0) 73 false) (.node 33 (sourceLit (List.headD (raw_ints% [33063939544778089497979]) 0) 68 false) (.node 32 (sourceLit (List.headD (raw_ints% [30603437749586808440870588043447684375]) 0) 16 false) (.node 31 (sourceLit (List.headD (raw_ints% [537375602887894789558353]) 0) 64 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [130201792387435034595782123058974608875]) 0) 14 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [4014623346090873170655]) 0) 71 false) (.node 36 (sourceLit (List.headD (raw_ints% [273773528018289433247669784307548873585]) 0) 13 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [9130602821399086908285609100156009679535]) 0) 8 false) .empty .empty)))

#time def treeG_J005_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [14158193250650361219996470482648265955]) 0) 17 false) treeG_J005_part003 treeG_J005_part004)

#time def treeG_J005_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [1785130292618405868921301741507425]) 0) 28 false) treeG_J005_part002 treeG_J005_part005)

#time def treeG_J005_part007 : IntSourceTree :=
  (.node 46 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 41 true) (.node 44 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) (.node 43 (sourceLit (List.headD (raw_ints% [13538102592745096995097518674625]) 0) 41 false) (.node 42 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 38 false) .empty .empty) .empty) (.node 45 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 43 false) .empty .empty)) (.node 49 (sourceLit (List.headD (raw_ints% [40852340351294545437953611297275]) 0) 39 true) (.node 48 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 43 false) (.node 47 (sourceLit (List.headD (raw_ints% [62275271926627446177448585903275]) 0) 40 true) .empty .empty) .empty) (.node 50 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 45 false) .empty .empty)))

#time def treeG_J005_part008 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [20883005320424934845374798725]) 0) 50 false) (.node 54 (sourceLit (List.headD (raw_ints% [86170882779567764518531373325]) 0) 48 false) (.node 53 (sourceLit (List.headD (raw_ints% [94622455983725221721645627526375]) 0) 36 true) (.node 52 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 48 false) .empty .empty) .empty) (.node 55 (sourceLit (List.headD (raw_ints% [406680246278373867235169113004625]) 0) 33 true) .empty .empty)) (.node 58 (sourceLit (List.headD (raw_ints% [2538579356522261068791337875]) 0) 53 false) (.node 57 (sourceLit (List.headD (raw_ints% [350213537860236951697554652419525]) 0) 32 true) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [86278170771187225006328624396925]) 0) 30 true) .empty .empty)))

#time def treeG_J005_part009 : IntSourceTree :=
  (.node 51 (sourceLit (List.headD (raw_ints% [84471809364402923888091990147825]) 0) 37 true) treeG_J005_part007 treeG_J005_part008)

#time def treeG_J005_part010 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [143680357171804695668167672099830375]) 0) 24 false) (.node 63 (sourceLit (List.headD (raw_ints% [52715103471855659476736448613491375]) 0) 25 false) (.node 62 (sourceLit (List.headD (raw_ints% [302291022410164325309166675]) 0) 56 false) (.node 61 (sourceLit (List.headD (raw_ints% [1785130292618405868921301741507425]) 0) 29 false) .empty .empty) .empty) (.node 64 (sourceLit (List.headD (raw_ints% [73969273953491384605855725]) 0) 58 false) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [2224007118540581871978675]) 0) 63 false) (.node 67 (sourceLit (List.headD (raw_ints% [698420476174341126704089092207497505]) 0) 22 false) (.node 66 (sourceLit (List.headD (raw_ints% [18127104063648026568768675]) 0) 60 false) .empty .empty) .empty) (.node 69 (sourceLit (List.headD (raw_ints% [1600237952289638808373890650371329855]) 0) 21 false) .empty .empty)))

#time def treeG_J005_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [130201792387435034595782123058974608875]) 0) 15 false) (.node 73 (sourceLit (List.headD (raw_ints% [30603437749586808440870588043447684375]) 0) 17 false) (.node 72 (sourceLit (List.headD (raw_ints% [537375602887894789558353]) 0) 65 false) (.node 71 (sourceLit (List.headD (raw_ints% [14158193250650361219996470482648265955]) 0) 18 false) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [33063939544778089497979]) 0) 69 false) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [273773528018289433247669784307548873585]) 0) 14 false) (.node 76 (sourceLit (List.headD (raw_ints% [1017985650336098973529]) 0) 74 false) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [4014623346090873170655]) 0) 72 false) .empty .empty)))

#time def treeG_J005_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [2185356442832756211088125]) 0) 63 false) treeG_J005_part010 treeG_J005_part011)

#time def treeG_J005_part013 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [154694584012997881570478625]) 0) 57 false) treeG_J005_part009 treeG_J005_part012)

#time def treeG_J005_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [990158821981380165205]) 0) 73 false) treeG_J005_part006 treeG_J005_part013)

#time def treeG_J005_part015 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 43 true) (.node 85 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 40 false) (.node 84 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 43 false) (.node 83 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 39 false) .empty .empty) .empty) (.node 86 (sourceLit (List.headD (raw_ints% [162248952611514316295091800731275]) 0) 39 false) .empty .empty)) (.node 90 (sourceLit (List.headD (raw_ints% [569165636256309803119165790608575]) 0) 36 true) (.node 89 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 48 false) (.node 88 (sourceLit (List.headD (raw_ints% [457349835061725023981635075928925]) 0) 38 true) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [565327361015729325070006274325]) 0) 46 false) .empty .empty)))

#time def treeG_J005_part016 : IntSourceTree :=
  (.node 97 (sourceLit (List.headD (raw_ints% [15805846607380412707792122975]) 0) 51 false) (.node 95 (sourceLit (List.headD (raw_ints% [8160984682392853709144571825]) 0) 52 false) (.node 94 (sourceLit (List.headD (raw_ints% [2621238345200833227857490967839375]) 0) 32 true) (.node 93 (sourceLit (List.headD (raw_ints% [270877976809313914473051536775]) 0) 47 false) .empty .empty) .empty) (.node 96 (sourceLit (List.headD (raw_ints% [2903228432366753986183798251617475]) 0) 31 true) .empty .empty)) (.node 99 (sourceLit (List.headD (raw_ints% [1919801020470269542509423375]) 0) 54 false) (.node 98 (sourceLit (List.headD (raw_ints% [5517138434992604002154545814315475]) 0) 29 true) .empty .empty) (.node 100 (sourceLit (List.headD (raw_ints% [2475355658787903668971930736682825]) 0) 28 true) .empty .empty)))

#time def treeG_J005_part017 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [581152018931498169383090293656225]) 0) 35 true) treeG_J005_part015 treeG_J005_part016)

#time def treeG_J005_part018 : IntSourceTree :=
  (.node 106 (sourceLit (List.headD (raw_ints% [1600465238574534003986593661389788495]) 0) 21 false) (.node 104 (sourceLit (List.headD (raw_ints% [278040470603040580145723916808100625]) 0) 23 false) (.node 103 (sourceLit (List.headD (raw_ints% [114160874228336470351655475]) 0) 58 false) (.node 102 (sourceLit (List.headD (raw_ints% [61533235255722316134226862842983825]) 0) 24 false) .empty .empty) .empty) (.node 105 (sourceLit (List.headD (raw_ints% [27921084944921679018543525]) 0) 60 false) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [6710672031329571276826575]) 0) 62 false) (.node 108 (sourceLit (List.headD (raw_ints% [3987125857105090205258822087288650185]) 0) 20 false) (.node 107 (sourceLit (List.headD (raw_ints% [13679089826566862824811325]) 0) 61 false) .empty .empty) .empty) (.node 110 (sourceLit (List.headD (raw_ints% [37049421222618080647968030329234289405]) 0) 17 false) .empty .empty)))

#time def treeG_J005_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [767840811081190843518587200164247997415]) 0) 13 false) (.node 114 (sourceLit (List.headD (raw_ints% [359453211605953900458147285636188341125]) 0) 14 false) (.node 113 (sourceLit (List.headD (raw_ints% [405119844708782431566437]) 0) 66 false) (.node 112 (sourceLit (List.headD (raw_ints% [82662108255616081319101175817738443265]) 0) 16 false) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [24920054342089297709747]) 0) 70 false) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [25912408764941960547416123291210246139345]) 0) 8 false) (.node 117 (sourceLit (List.headD (raw_ints% [12273147059286710405809]) 0) 71 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [1512232262054746502725]) 0) 74 false) .empty .empty)))

#time def treeG_J005_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [411995209986215355382443]) 0) 66 false) treeG_J005_part018 treeG_J005_part019)

#time def treeG_J005_part021 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [935265649693818727254662325]) 0) 55 false) treeG_J005_part017 treeG_J005_part020)

#time def treeG_J005_part022 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [208248747355215239271840732315825]) 0) 40 true) (.node 127 (sourceLit (List.headD (raw_ints% [112262112269070881236270193317275]) 0) 41 false) (.node 126 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 42 false) (.node 125 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 43 false) .empty .empty) .empty) (.node 128 (sourceLit (List.headD (raw_ints% [21869242649819002838234453243625]) 0) 43 true) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [386802931221288485574214819275]) 0) 47 false) (.node 131 (sourceLit (List.headD (raw_ints% [242346913445953439615536900230375]) 0) 38 true) (.node 130 (sourceLit (List.headD (raw_ints% [1636473939782374362044755004625]) 0) 45 false) .empty .empty) .empty) (.node 133 (sourceLit (List.headD (raw_ints% [243264781473886473830722333064925]) 0) 37 true) .empty .empty)))

#time def treeG_J005_part023 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [2715430132110708388574108594959275]) 0) 31 true) (.node 137 (sourceLit (List.headD (raw_ints% [1276507447253258517243121799598975]) 0) 33 true) (.node 136 (sourceLit (List.headD (raw_ints% [44404872138717894827781775875]) 0) 50 false) (.node 135 (sourceLit (List.headD (raw_ints% [1107279049461229680311160927417375]) 0) 34 true) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [10728687894335890570209447225]) 0) 52 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [2130242975703154768946616239095125]) 0) 30 true) (.node 140 (sourceLit (List.headD (raw_ints% [1301022684418278016227508875]) 0) 55 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [316487313641827200972747825]) 0) 57 false) .empty .empty)))

#time def treeG_J005_part024 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [92353547014873074977260081725]) 0) 49 false) treeG_J005_part022 treeG_J005_part023)

#time def treeG_J005_part025 : IntSourceTree :=
  (.node 148 (sourceLit (List.headD (raw_ints% [9231075589485699080853975]) 0) 62 false) (.node 146 (sourceLit (List.headD (raw_ints% [37715065826195331468318375]) 0) 60 false) (.node 145 (sourceLit (List.headD (raw_ints% [67180056715617942238778122354135125]) 0) 25 false) (.node 144 (sourceLit (List.headD (raw_ints% [154352474503181556097455225]) 0) 58 false) .empty .empty) .empty) (.node 147 (sourceLit (List.headD (raw_ints% [451022381200096438641252284591145495]) 0) 23 false) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [11445613985983859713985779923293011725]) 0) 19 false) (.node 150 (sourceLit (List.headD (raw_ints% [2262657794248407532869225]) 0) 64 false) (.node 149 (sourceLit (List.headD (raw_ints% [1193443952407725698442465718458660165]) 0) 22 false) .empty .empty) .empty) (.node 152 (sourceLit (List.headD (raw_ints% [1110605237056966631971419]) 0) 65 false) .empty .empty)))

#time def treeG_J005_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [4129261856597918617577]) 0) 73 false) (.node 156 (sourceLit (List.headD (raw_ints% [16776169139400505921515]) 0) 71 false) (.node 155 (sourceLit (List.headD (raw_ints% [114625709609259432931182581288606866125]) 0) 16 false) (.node 154 (sourceLit (List.headD (raw_ints% [272864086529670073574521]) 0) 67 false) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [247033641531450705135458707928349561915]) 0) 15 false) .empty .empty)) (.node 165 (sourceLit (List.headD (raw_ints% [78104438035067867279408761584375]) 0) 40 false) (.node 159 (sourceLit (List.headD (raw_ints% [8390902971771436819565257095527118229905]) 0) 10 false) .empty .empty) (.node 166 (sourceLit (List.headD (raw_ints% [71022968986555047312742367200725]) 0) 39 false) .empty .empty)))

#time def treeG_J005_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [26029335253014636439115293887145379445]) 0) 18 false) treeG_J005_part025 treeG_J005_part026)

#time def treeG_J005_part028 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [4409065891933328328745207114746225]) 0) 26 false) treeG_J005_part024 treeG_J005_part027)

#time def treeG_J005_part029 : IntSourceTree :=
  (.node 124 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 40 false) treeG_J005_part021 treeG_J005_part028)

#time def treeG_J005_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [9130602821399086908285609100156009679535]) 0) 9 false) treeG_J005_part014 treeG_J005_part029)

#time def treeG_J005_part031 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [3296398596203756864465500110029775]) 0) 35 true) (.node 170 (sourceLit (List.headD (raw_ints% [6094794279110577853579737643497825]) 0) 36 true) (.node 169 (sourceLit (List.headD (raw_ints% [24249568380411547364845005977625]) 0) 44 true) (.node 168 (sourceLit (List.headD (raw_ints% [2253543631366859123761958169005325]) 0) 38 false) .empty .empty) .empty) (.node 171 (sourceLit (List.headD (raw_ints% [267786644691661259243687182575]) 0) 48 false) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [59709608285301660140681794425]) 0) 50 false) (.node 174 (sourceLit (List.headD (raw_ints% [12947707669127901097308738348315825]) 0) 32 true) (.node 173 (sourceLit (List.headD (raw_ints% [502727885633263056675378101775]) 0) 47 false) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [14813236359012920898794776587060525]) 0) 31 true) .empty .empty)))

#time def treeG_J005_part032 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [334204336145726126559393741447159825]) 0) 24 true) (.node 180 (sourceLit (List.headD (raw_ints% [40971526454983430548213806782665575]) 0) 28 true) (.node 179 (sourceLit (List.headD (raw_ints% [6889085853395351485190600475]) 0) 53 false) (.node 178 (sourceLit (List.headD (raw_ints% [35331099877111668549625351772851725]) 0) 29 true) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [1666779719142737305200355425]) 0) 55 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [98510304613338198060368175]) 0) 59 false) (.node 184 (sourceLit (List.headD (raw_ints% [207495416332107326885800602972161025]) 0) 23 true) (.node 183 (sourceLit (List.headD (raw_ints% [101163219706745365310546175]) 0) 59 false) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [549296576325240147654306253942535505]) 0) 21 false) .empty .empty)))

#time def treeG_J005_part033 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [7149756382834370529997413225]) 0) 53 false) treeG_J005_part031 treeG_J005_part032)

#time def treeG_J005_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [100467715520125674104671302954949744335]) 0) 16 false) (.node 190 (sourceLit (List.headD (raw_ints% [39330991731476364052349775652119961155]) 0) 17 false) (.node 189 (sourceLit (List.headD (raw_ints% [11751479147641826884881375]) 0) 62 false) (.node 188 (sourceLit (List.headD (raw_ints% [3229232242096452813001214466169677735]) 0) 20 false) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [1438667374275976822104339]) 0) 65 false) .empty .empty)) (.node 195 (sourceLit (List.headD (raw_ints% [173183869161312882735533]) 0) 68 false) (.node 194 (sourceLit (List.headD (raw_ints% [473485516490514465593542118752463801115]) 0) 14 false) (.node 193 (sourceLit (List.headD (raw_ints% [352742696174092100202491]) 0) 67 false) .empty .empty) .empty) (.node 196 (sourceLit (List.headD (raw_ints% [1066170542666960083380334100453461860585]) 0) 13 false) .empty .empty)))

#time def treeG_J005_part035 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [71856082992262437897056060657625]) 0) 43 false) (.node 206 (sourceLit (List.headD (raw_ints% [46862662821040720367645256950625]) 0) 41 false) (.node 199 (sourceLit (List.headD (raw_ints% [654257398635793028713]) 0) 76 false) (.node 198 (sourceLit (List.headD (raw_ints% [37328203467109419967261305938447241710895]) 0) 8 false) .empty .empty) .empty) (.node 207 (sourceLit (List.headD (raw_ints% [153501255551586715159798019433825]) 0) 40 true) .empty .empty)) (.node 210 (sourceLit (List.headD (raw_ints% [12943021160096960863444880491125]) 0) 46 true) (.node 209 (sourceLit (List.headD (raw_ints% [2670041126077289602305639633636975]) 0) 39 false) .empty .empty) (.node 211 (sourceLit (List.headD (raw_ints% [5610100452218670974348663843037075]) 0) 37 true) .empty .empty)))

#time def treeG_J005_part036 : IntSourceTree :=
  (.node 197 (sourceLit (List.headD (raw_ints% [21279191219514301437221]) 0) 71 false) treeG_J005_part034 treeG_J005_part035)

#time def treeG_J005_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [12017987999814234321753525]) 0) 62 false) treeG_J005_part033 treeG_J005_part036)

#time def treeG_J005_part038 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [12260221464506403864308532987862575]) 0) 32 true) (.node 215 (sourceLit (List.headD (raw_ints% [10733149570205441736686416493481075]) 0) 33 true) (.node 214 (sourceLit (List.headD (raw_ints% [318020791603516906720857938325]) 0) 48 false) (.node 213 (sourceLit (List.headD (raw_ints% [2809869033255983916804055443899925]) 0) 36 true) .empty .empty) .empty) (.node 216 (sourceLit (List.headD (raw_ints% [75014344431885425453581812975]) 0) 50 false) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [4287040484558795452735582725]) 0) 54 false) (.node 219 (sourceLit (List.headD (raw_ints% [29900239612890251772477134582933175]) 0) 30 true) (.node 218 (sourceLit (List.headD (raw_ints% [17870337637001591549780205675]) 0) 52 false) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [36711040503577121010320574304475325]) 0) 29 true) .empty .empty)))

#time def treeG_J005_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [352748186074952729628198315239755485]) 0) 22 true) (.node 225 (sourceLit (List.headD (raw_ints% [341855529763343211363356847680431275]) 0) 24 true) (.node 224 (sourceLit (List.headD (raw_ints% [250300404323799905144729475]) 0) 58 false) (.node 223 (sourceLit (List.headD (raw_ints% [343022467929592783216884155676652275]) 0) 25 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [7599404848392858324006225]) 0) 63 false) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [842344337281001416116283029252357405]) 0) 21 false) (.node 228 (sourceLit (List.headD (raw_ints% [14804900410142769562653075]) 0) 62 false) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [7226163559145011819142925]) 0) 63 false) .empty .empty)))

#time def treeG_J005_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [1033805091859082903254859775]) 0) 56 false) treeG_J005_part038 treeG_J005_part039)

#time def treeG_J005_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [106079192603710859049473]) 0) 69 false) (.node 234 (sourceLit (List.headD (raw_ints% [432621305818514126830461]) 0) 67 false) (.node 233 (sourceLit (List.headD (raw_ints% [48409045014096401226440715180658985445]) 0) 17 false) (.node 232 (sourceLit (List.headD (raw_ints% [1766729511494987012237259]) 0) 65 false) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [244234097271995599731176956175250068865]) 0) 15 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [20546397523566546328130791747393005251085]) 0) 9 false) (.node 238 (sourceLit (List.headD (raw_ints% [13020667506318464202067]) 0) 72 false) (.node 237 (sourceLit (List.headD (raw_ints% [572103259604058673109416684596762736755]) 0) 14 false) .empty .empty) .empty) (.node 247 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 42 true) .empty .empty)))

#time def treeG_J005_part042 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [865959409457450046125689720275]) 0) 47 false) (.node 251 (sourceLit (List.headD (raw_ints% [13478594449480283381932254856275]) 0) 47 true) (.node 250 (sourceLit (List.headD (raw_ints% [48815452296347211490469971781689425]) 0) 36 false) (.node 249 (sourceLit (List.headD (raw_ints% [48052825686336992630950533317625]) 0) 45 false) .empty .empty) .empty) (.node 252 (sourceLit (List.headD (raw_ints% [41584405021545610930323810634266825]) 0) 35 true) .empty .empty)) (.node 255 (sourceLit (List.headD (raw_ints% [198601575032913586439494349475]) 0) 49 false) (.node 254 (sourceLit (List.headD (raw_ints% [76968101395063584240421035856481775]) 0) 32 true) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [71051960202630612994696555360788075]) 0) 31 true) .empty .empty)))

#time def treeG_J005_part043 : IntSourceTree :=
  (.node 248 (sourceLit (List.headD (raw_ints% [3481553675779552845040342324475925]) 0) 38 true) treeG_J005_part041 treeG_J005_part042)

#time def treeG_J005_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [16439763759508644624378215805533937705]) 0) 18 false) treeG_J005_part040 treeG_J005_part043)

#time def treeG_J005_part045 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [684343647545356551400533911025]) 0) 47 false) treeG_J005_part037 treeG_J005_part044)

#time def treeG_J005_part046 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [2015302256083209618101123014039260975]) 0) 24 true) (.node 260 (sourceLit (List.headD (raw_ints% [198230390448138583631603269880799825]) 0) 28 true) (.node 259 (sourceLit (List.headD (raw_ints% [686328236475390004036850325]) 0) 57 false) (.node 258 (sourceLit (List.headD (raw_ints% [160832443554990793279311176032949475]) 0) 29 true) .empty .empty) .empty) (.node 261 (sourceLit (List.headD (raw_ints% [655065191354014536883806825]) 0) 57 false) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [37947524927615426771090325]) 0) 61 false) (.node 264 (sourceLit (List.headD (raw_ints% [2536684327104634938849272642441057175]) 0) 23 true) (.node 263 (sourceLit (List.headD (raw_ints% [629152213032101442012675075]) 0) 57 false) .empty .empty) .empty) (.node 266 (sourceLit (List.headD (raw_ints% [6018985052538731529468015816829435905]) 0) 21 true) .empty .empty)))

#time def treeG_J005_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [31050394555943482890354423489321757305]) 0) 16 false) (.node 270 (sourceLit (List.headD (raw_ints% [12375972938484318736628718716044524195]) 0) 17 true) (.node 269 (sourceLit (List.headD (raw_ints% [17858321672643712240424775]) 0) 62 false) (.node 268 (sourceLit (List.headD (raw_ints% [6051217730696074650026800988087721615]) 0) 20 true) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [4348828810593058174934247]) 0) 64 false) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [301059203735027954029509324138079966005]) 0) 14 false) (.node 273 (sourceLit (List.headD (raw_ints% [1061244119146802811832277]) 0) 66 false) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [16214839791075077755933]) 0) 72 false) .empty .empty)))

#time def treeG_J005_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [18379631393757198974271375]) 0) 62 false) treeG_J005_part046 treeG_J005_part047)

#time def treeG_J005_part049 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [1537898700464210611836495489528225]) 0) 41 true) (.node 279 (sourceLit (List.headD (raw_ints% [7786608317232119972363]) 0) 73 false) (.node 278 (sourceLit (List.headD (raw_ints% [35901013762210090190744029689938388593745]) 0) 8 false) (.node 277 (sourceLit (List.headD (raw_ints% [63520810164682256175031]) 0) 70 false) .empty .empty) .empty) (.node 288 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 46 true) .empty .empty)) (.node 292 (sourceLit (List.headD (raw_ints% [27641532546505923315265043623575]) 0) 47 true) (.node 291 (sourceLit (List.headD (raw_ints% [13606388187141470616204658906181625]) 0) 39 false) (.node 290 (sourceLit (List.headD (raw_ints% [30497923423216976747197706904375]) 0) 47 false) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [9693633997072406753379938797591725]) 0) 38 true) .empty .empty)))

#time def treeG_J005_part050 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [32733050985525135376708510362504075]) 0) 32 true) (.node 297 (sourceLit (List.headD (raw_ints% [14697934684531052282597005593231375]) 0) 34 true) (.node 296 (sourceLit (List.headD (raw_ints% [30896807650257040246478134125]) 0) 52 false) (.node 295 (sourceLit (List.headD (raw_ints% [16558737956214535625933654840750175]) 0) 35 true) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [892030664485823493244123575]) 0) 57 false) .empty .empty)) (.node 301 (sourceLit (List.headD (raw_ints% [40379837486140365655320673894081125]) 0) 31 true) (.node 300 (sourceLit (List.headD (raw_ints% [6694211299047444611854022475]) 0) 54 false) .empty .empty) (.node 302 (sourceLit (List.headD (raw_ints% [1586455673556975244280367525]) 0) 56 false) .empty .empty)))

#time def treeG_J005_part051 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [273969308926966569702415890975]) 0) 49 false) treeG_J005_part049 treeG_J005_part050)

#time def treeG_J005_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [887702235509004714469081548948538690335]) 0) 13 false) treeG_J005_part048 treeG_J005_part051)

#time def treeG_J005_part053 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [21954362377371628385889675]) 0) 62 false) (.node 306 (sourceLit (List.headD (raw_ints% [22748715230829710123077875]) 0) 62 false) (.node 305 (sourceLit (List.headD (raw_ints% [548707199335322931871478948690156475]) 0) 26 true) (.node 304 (sourceLit (List.headD (raw_ints% [2959779755533605756780825]) 0) 65 false) .empty .empty) .empty) (.node 307 (sourceLit (List.headD (raw_ints% [1416559216615944699959954375397420105]) 0) 24 true) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [7203934174498240840251733630394615475]) 0) 20 true) (.node 310 (sourceLit (List.headD (raw_ints% [5316079056749350210640925]) 0) 64 false) (.node 309 (sourceLit (List.headD (raw_ints% [1723390516994269016535771004335019755]) 0) 23 true) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [645524824774517790674247]) 0) 67 false) .empty .empty)))

#time def treeG_J005_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [37479475152045327770897]) 0) 71 false) (.node 316 (sourceLit (List.headD (raw_ints% [153358244053490385045455]) 0) 69 false) (.node 315 (sourceLit (List.headD (raw_ints% [14206276615758088574583091990707474285]) 0) 17 false) (.node 314 (sourceLit (List.headD (raw_ints% [78577851666036085625227]) 0) 70 false) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [78899743976236510339916216087943988395]) 0) 16 false) .empty .empty)) (.node 330 (sourceLit (List.headD (raw_ints% [147240969126056690648005683111495825]) 0) 36 true) (.node 319 (sourceLit (List.headD (raw_ints% [3838654059660885965653309485636345835665]) 0) 11 false) .empty .empty) (.node 331 (sourceLit (List.headD (raw_ints% [74474441295914236876327668665025]) 0) 47 false) .empty .empty)))

#time def treeG_J005_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [4339662614538229584021572922834307035]) 0) 19 true) treeG_J005_part053 treeG_J005_part054)

#time def treeG_J005_part056 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [77171911700480217652320376425]) 0) 51 false) (.node 335 (sourceLit (List.headD (raw_ints% [349337042821019552965337432475]) 0) 49 false) (.node 334 (sourceLit (List.headD (raw_ints% [1163817050230204480192211130235259025]) 0) 32 true) (.node 333 (sourceLit (List.headD (raw_ints% [56149024502469296676655776967425]) 0) 47 true) .empty .empty) .empty) (.node 336 (sourceLit (List.headD (raw_ints% [458827654396234527035180399543217525]) 0) 31 true) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [849227241088665748423069061719330575]) 0) 28 true) (.node 339 (sourceLit (List.headD (raw_ints% [1097733092496256982451396825]) 0) 57 false) (.node 338 (sourceLit (List.headD (raw_ints% [779835376254996552806897181933858525]) 0) 29 true) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [4073950533631386464318795175]) 0) 55 false) .empty .empty)))

#time def treeG_J005_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [27117799067902221271884375]) 0) 62 false) (.node 345 (sourceLit (List.headD (raw_ints% [56765427249459957445896075]) 0) 61 false) (.node 344 (sourceLit (List.headD (raw_ints% [10841553978124299740224638224459812425]) 0) 23 true) (.node 343 (sourceLit (List.headD (raw_ints% [478651730262436901133846225]) 0) 58 false) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [29098275704921936110306636899340578495]) 0) 21 true) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [26050403082099544531354575]) 0) 62 false) (.node 348 (sourceLit (List.headD (raw_ints% [39278677201014155748691739024629721745]) 0) 20 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [208218013236782115379949969838838004445]) 0) 17 true) .empty .empty)))

#time def treeG_J005_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [8321936140368723989660969502845507025]) 0) 24 true) treeG_J005_part056 treeG_J005_part057)

#time def treeG_J005_part059 : IntSourceTree :=
  (.node 332 (sourceLit (List.headD (raw_ints% [476988827010072670648872895632078825]) 0) 35 false) treeG_J005_part055 treeG_J005_part058)

#time def treeG_J005_part060 : IntSourceTree :=
  (.node 303 (sourceLit (List.headD (raw_ints% [418069947038404208721059714590652175]) 0) 27 true) treeG_J005_part052 treeG_J005_part059)

#time def treeG_J005_part061 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [46415318900547943333592160075]) 0) 51 false) treeG_J005_part045 treeG_J005_part060)

#time def treeG_J005_part062 : IntSourceTree :=
  (.node 167 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 46 false) treeG_J005_part030 treeG_J005_part061)

#time def treeG_J005_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [433101383804745880082422605245899513215]) 0) 13 true) (.node 354 (sourceLit (List.headD (raw_ints% [578797611065474647406889991199475616245]) 0) 14 true) (.node 353 (sourceLit (List.headD (raw_ints% [1520855179951268350864711]) 0) 66 false) (.node 352 (sourceLit (List.headD (raw_ints% [261576288139887189778409899661949452505]) 0) 16 true) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [46148172083885930113361]) 0) 71 false) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [21906258517581087826171]) 0) 72 false) (.node 358 (sourceLit (List.headD (raw_ints% [4495655153623003103293072947088933464495]) 0) 8 false) (.node 357 (sourceLit (List.headD (raw_ints% [11229679236101016108803]) 0) 73 false) .empty .empty) .empty) (.node 371 (sourceLit (List.headD (raw_ints% [201666521874622573112824318736222325]) 0) 37 true) .empty .empty)))

#time def treeG_J005_part064 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [400035915658110317904792377170292025]) 0) 32 true) (.node 375 (sourceLit (List.headD (raw_ints% [1097582098405346337688476510872258325]) 0) 33 true) (.node 374 (sourceLit (List.headD (raw_ints% [56696963120323229816060608749375]) 0) 48 true) (.node 373 (sourceLit (List.headD (raw_ints% [515763362998362297662392650822445725]) 0) 36 false) .empty .empty) .empty) (.node 376 (sourceLit (List.headD (raw_ints% [225749812219991391979424895975]) 0) 50 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [10869518180892667107368326725]) 0) 54 false) (.node 379 (sourceLit (List.headD (raw_ints% [648903172312896011300063140483842225]) 0) 30 true) (.node 378 (sourceLit (List.headD (raw_ints% [48626930436933865868508422025]) 0) 52 false) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [687707891144104285801786366143006075]) 0) 29 true) .empty .empty)))

#time def treeG_J005_part065 : IntSourceTree :=
  (.node 372 (sourceLit (List.headD (raw_ints% [176590415138334397067920380953625]) 0) 47 false) treeG_J005_part063 treeG_J005_part064)

#time def treeG_J005_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [23432038838458157310466819397750898075]) 0) 22 true) (.node 385 (sourceLit (List.headD (raw_ints% [8646725180783008012738722429699186525]) 0) 24 true) (.node 384 (sourceLit (List.headD (raw_ints% [289225825908286132699873425]) 0) 59 false) (.node 383 (sourceLit (List.headD (raw_ints% [6649656352215107154776730644482898325]) 0) 25 true) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [4252089002328780915352275]) 0) 65 false) .empty .empty)) (.node 390 (sourceLit (List.headD (raw_ints% [15418244968600844110072725]) 0) 63 false) (.node 389 (sourceLit (List.headD (raw_ints% [32385115133037079682548655007289642725]) 0) 21 true) (.node 388 (sourceLit (List.headD (raw_ints% [32281235758432814157879075]) 0) 62 false) .empty .empty) .empty) (.node 391 (sourceLit (List.headD (raw_ints% [179402276538789152018943035317259542545]) 0) 18 true) .empty .empty)))

#time def treeG_J005_part067 : IntSourceTree :=
  (.node 397 (sourceLit (List.headD (raw_ints% [748700359709691921442087469597675466795]) 0) 14 true) (.node 395 (sourceLit (List.headD (raw_ints% [635622717528507001705222359162305513385]) 0) 15 true) (.node 394 (sourceLit (List.headD (raw_ints% [892232366622979665862895]) 0) 67 false) (.node 393 (sourceLit (List.headD (raw_ints% [244217637681734271442323607970612224365]) 0) 17 true) .empty .empty) .empty) (.node 396 (sourceLit (List.headD (raw_ints% [215827132617597055861433]) 0) 69 false) .empty .empty)) (.node 399 (sourceLit (List.headD (raw_ints% [10858961085020540759320164995456449878165]) 0) 9 true) (.node 398 (sourceLit (List.headD (raw_ints% [52357958736762801099527]) 0) 71 false) .empty .empty) (.node 412 (sourceLit (List.headD (raw_ints% [2090321002007053255551467445521857425]) 0) 35 true) .empty .empty)))

#time def treeG_J005_part068 : IntSourceTree :=
  (.node 392 (sourceLit (List.headD (raw_ints% [3701230003807571083650615]) 0) 65 false) treeG_J005_part066 treeG_J005_part067)

#time def treeG_J005_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [1243747430037205610019213825]) 0) 57 false) treeG_J005_part065 treeG_J005_part068)

#time def treeG_J005_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [5620739274274768533669780852790813875]) 0) 29 true) (.node 416 (sourceLit (List.headD (raw_ints% [8321829132846536174472631687434849075]) 0) 31 true) (.node 415 (sourceLit (List.headD (raw_ints% [28523150081572124684512973090925]) 0) 50 true) (.node 414 (sourceLit (List.headD (raw_ints% [17668244666177798005388775956553522225]) 0) 32 false) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [74288950259755587163552259775]) 0) 52 false) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [3397783823630640321524765775]) 0) 56 false) (.node 420 (sourceLit (List.headD (raw_ints% [4341998137414502341977436062151407225]) 0) 28 true) (.node 419 (sourceLit (List.headD (raw_ints% [31063200956993754149286072825]) 0) 53 false) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [35691368892853950301653357930306881775]) 0) 24 true) .empty .empty)))

#time def treeG_J005_part071 : IntSourceTree :=
  (.node 428 (sourceLit (List.headD (raw_ints% [148177633506651102735042816157377462855]) 0) 20 true) (.node 426 (sourceLit (List.headD (raw_ints% [109249327187606192093512921975846405905]) 0) 21 true) (.node 425 (sourceLit (List.headD (raw_ints% [175694971409366217808081275]) 0) 60 false) (.node 424 (sourceLit (List.headD (raw_ints% [42355696839596557497989206931403374175]) 0) 23 true) .empty .empty) .empty) (.node 427 (sourceLit (List.headD (raw_ints% [40915624969358273373752025]) 0) 62 false) .empty .empty)) (.node 430 (sourceLit (List.headD (raw_ints% [828105671020404434461606990394430562755]) 0) 17 true) (.node 429 (sourceLit (List.headD (raw_ints% [38512068434766083784403575]) 0) 62 false) .empty .empty) (.node 431 (sourceLit (List.headD (raw_ints% [4567457832847600931862561]) 0) 65 false) .empty .empty)))

#time def treeG_J005_part072 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [47818481235923044305335475]) 0) 62 false) treeG_J005_part070 treeG_J005_part071)

#time def treeG_J005_part073 : IntSourceTree :=
  (.node 437 (sourceLit (List.headD (raw_ints% [125989698728788926991009]) 0) 70 false) (.node 435 (sourceLit (List.headD (raw_ints% [523046989951892224956007]) 0) 68 false) (.node 434 (sourceLit (List.headD (raw_ints% [3328684591842273695670287736330319973595]) 0) 14 true) (.node 433 (sourceLit (List.headD (raw_ints% [136273426491018920799119]) 0) 70 false) .empty .empty) .empty) (.node 436 (sourceLit (List.headD (raw_ints% [4651880356423310133559356268052544593865]) 0) 13 true) .empty .empty)) (.node 454 (sourceLit (List.headD (raw_ints% [233013408949730660314278573812025]) 0) 49 false) (.node 439 (sourceLit (List.headD (raw_ints% [7612925054795428318339]) 0) 74 false) (.node 438 (sourceLit (List.headD (raw_ints% [100329301196463569047880269055591393214255]) 0) 8 true) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [9382913382291572171538626233712890275]) 0) 34 false) .empty .empty)))

#time def treeG_J005_part074 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [1827145123135199028087824848004200575]) 0) 30 true) (.node 459 (sourceLit (List.headD (raw_ints% [2485918050980936261184858856153485825]) 0) 31 true) (.node 458 (sourceLit (List.headD (raw_ints% [99950970082577308458596097525]) 0) 52 false) (.node 457 (sourceLit (List.headD (raw_ints% [3960896608594212928283919655132278525]) 0) 33 true) .empty .empty) .empty) (.node 460 (sourceLit (List.headD (raw_ints% [5048420694025271760479436525]) 0) 56 false) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [14520856270319421573438313642911991725]) 0) 26 true) (.node 462 (sourceLit (List.headD (raw_ints% [1077018196796717355752775975]) 0) 58 false) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [475869873866482576185494175]) 0) 59 false) .empty .empty)))

#time def treeG_J005_part075 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [57272049975364240761005371077825]) 0) 50 true) treeG_J005_part073 treeG_J005_part074)

#time def treeG_J005_part076 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [1173641924170426026373134382876126887855]) 0) 16 true) treeG_J005_part072 treeG_J005_part075)

#time def treeG_J005_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [409329854779138090812496538874675]) 0) 47 false) treeG_J005_part069 treeG_J005_part076)

#time def treeG_J005_part078 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [11546911733082619837165425]) 0) 64 false) (.node 468 (sourceLit (List.headD (raw_ints% [49550014180283732589624975]) 0) 62 false) (.node 467 (sourceLit (List.headD (raw_ints% [42908644174574017391523051289047753915]) 0) 23 true) (.node 466 (sourceLit (List.headD (raw_ints% [107661547372105723162444875]) 0) 61 false) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [57896259186807011526247080575043910065]) 0) 22 true) .empty .empty)) (.node 473 (sourceLit (List.headD (raw_ints% [464712143244345877465405387452757331745]) 0) 18 true) (.node 472 (sourceLit (List.headD (raw_ints% [5433685661887630780074507]) 0) 65 false) (.node 471 (sourceLit (List.headD (raw_ints% [324351697240807641221331977538585510105]) 0) 19 true) .empty .empty) .empty) (.node 474 (sourceLit (List.headD (raw_ints% [1288142457233323066923009]) 0) 67 false) .empty .empty)))

#time def treeG_J005_part079 : IntSourceTree :=
  (.node 495 (sourceLit (List.headD (raw_ints% [130768279515651392499395773451475]) 0) 51 false) (.node 478 (sourceLit (List.headD (raw_ints% [36815869996013062945741]) 0) 72 false) (.node 477 (sourceLit (List.headD (raw_ints% [1951589998356809106058634399227434563535]) 0) 15 true) (.node 476 (sourceLit (List.headD (raw_ints% [153609928667147584547287]) 0) 70 false) .empty .empty) .empty) (.node 479 (sourceLit (List.headD (raw_ints% [44735170055721514144280052030067471668045]) 0) 10 true) .empty .empty)) (.node 497 (sourceLit (List.headD (raw_ints% [57420627875883751935332475597375]) 0) 51 true) (.node 496 (sourceLit (List.headD (raw_ints% [158448443249511690919090651426841093475]) 0) 31 false) .empty .empty) (.node 498 (sourceLit (List.headD (raw_ints% [121127952200740045171415648111442098925]) 0) 29 true) .empty .empty)))

#time def treeG_J005_part080 : IntSourceTree :=
  (.node 475 (sourceLit (List.headD (raw_ints% [1346530937156883346982532688584007230105]) 0) 16 true) treeG_J005_part078 treeG_J005_part079)

#time def treeG_J005_part081 : IntSourceTree :=
  (.node 504 (sourceLit (List.headD (raw_ints% [189978003485514187677023811355188493425]) 0) 23 true) (.node 502 (sourceLit (List.headD (raw_ints% [198183206868451525293588222614230791825]) 0) 24 true) (.node 501 (sourceLit (List.headD (raw_ints% [6699057564419903199434107275]) 0) 56 false) (.node 500 (sourceLit (List.headD (raw_ints% [35432690678280477836980305636304365975]) 0) 28 true) .empty .empty) .empty) (.node 503 (sourceLit (List.headD (raw_ints% [694470346909333001310092175]) 0) 59 false) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [33372961201373724894346425]) 0) 63 false) (.node 506 (sourceLit (List.headD (raw_ints% [430094219353410599670494830051420596495]) 0) 21 true) (.node 505 (sourceLit (List.headD (raw_ints% [75043725614279089594353225]) 0) 62 false) .empty .empty) .empty) (.node 508 (sourceLit (List.headD (raw_ints% [538360673286533175529326004467386599785]) 0) 20 true) .empty .empty)))

#time def treeG_J005_part082 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [11542103991976794383222684662157914642245]) 0) 14 true) (.node 512 (sourceLit (List.headD (raw_ints% [4015985231682496233168177257741241273825]) 0) 16 true) (.node 511 (sourceLit (List.headD (raw_ints% [436215868764688681581429]) 0) 69 false) (.node 510 (sourceLit (List.headD (raw_ints% [2877254916935244303218206166408379681405]) 0) 17 true) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [3253310838031328047288603]) 0) 66 false) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [16892614638086823418161166749291571087815]) 0) 13 true) (.node 515 (sourceLit (List.headD (raw_ints% [382547733640715420983501]) 0) 69 false) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [181230158605506242103565]) 0) 70 false) .empty .empty)))

#time def treeG_J005_part083 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [60587959925801381394846375]) 0) 62 false) treeG_J005_part081 treeG_J005_part082)

#time def treeG_J005_part084 : IntSourceTree :=
  (.node 499 (sourceLit (List.headD (raw_ints% [17221942281395888577327506175]) 0) 55 false) treeG_J005_part080 treeG_J005_part083)

#time def treeG_J005_part085 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [6086760793685308408424034825]) 0) 57 false) (.node 538 (sourceLit (List.headD (raw_ints% [14380144711491582310947767923725]) 0) 54 true) (.node 537 (sourceLit (List.headD (raw_ints% [166370236466700116775658490737105650525]) 0) 32 false) (.node 519 (sourceLit (List.headD (raw_ints% [21590019886422206309063]) 0) 73 false) .empty .empty) .empty) (.node 539 (sourceLit (List.headD (raw_ints% [116156116098778172649045930399135127275]) 0) 30 true) .empty .empty)) (.node 543 (sourceLit (List.headD (raw_ints% [169141494327812682146711595328406808375]) 0) 25 true) (.node 542 (sourceLit (List.headD (raw_ints% [4545021170826468487928555325]) 0) 57 false) (.node 541 (sourceLit (List.headD (raw_ints% [31778400432010079780804655940295964825]) 0) 29 true) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [913070819952183426434690175]) 0) 59 false) .empty .empty)))

#time def treeG_J005_part086 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [37494136459636141720515525]) 0) 63 false) (.node 548 (sourceLit (List.headD (raw_ints% [83941830625211166987760725]) 0) 62 false) (.node 547 (sourceLit (List.headD (raw_ints% [344276931004262564887448727473325088665]) 0) 22 true) (.node 546 (sourceLit (List.headD (raw_ints% [192513355085010635214968025]) 0) 61 false) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [422568154912919152476831843317298779655]) 0) 21 true) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [8525222138582407030531221]) 0) 65 false) (.node 551 (sourceLit (List.headD (raw_ints% [2228551522453629020775542211331208661195]) 0) 18 true) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [3086560945193804478237366482835726610335]) 0) 17 true) .empty .empty)))

#time def treeG_J005_part087 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [156269031826700638191773326853484305775]) 0) 24 true) treeG_J005_part085 treeG_J005_part086)

#time def treeG_J005_part088 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [309807398271436533814570033086496911714615]) 0) 9 true) (.node 557 (sourceLit (List.headD (raw_ints% [12989434641373205206043897950836701960745]) 0) 14 true) (.node 556 (sourceLit (List.headD (raw_ints% [114468902486783918218107]) 0) 71 false) (.node 555 (sourceLit (List.headD (raw_ints% [8849042117663027689257619284989900182035]) 0) 15 true) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [107598418613480116212083]) 0) 71 false) .empty .empty)) (.node 582 (sourceLit (List.headD (raw_ints% [1835634420780193580677909757564710956975]) 0) 24 true) (.node 581 (sourceLit (List.headD (raw_ints% [17647985610321330434262032025]) 0) 56 false) (.node 580 (sourceLit (List.headD (raw_ints% [893816238111944903355387137556776652225]) 0) 28 true) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [3156080477007802485308370975]) 0) 58 false) .empty .empty)))

#time def treeG_J005_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [107295701324620952580675075]) 0) 62 false) (.node 587 (sourceLit (List.headD (raw_ints% [125767432682263185426275175]) 0) 62 false) (.node 586 (sourceLit (List.headD (raw_ints% [2070210289873799611397878399604328295905]) 0) 21 true) (.node 585 (sourceLit (List.headD (raw_ints% [612895917495067068057277275]) 0) 60 false) .empty .empty) .empty) (.node 588 (sourceLit (List.headD (raw_ints% [2215854774747567343570263815319214109535]) 0) 20 true) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [23535228659166103909909797]) 0) 64 false) (.node 590 (sourceLit (List.headD (raw_ints% [10644926040278168576040412819745181267555]) 0) 17 true) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [13812426947946535933036160432908428015735]) 0) 16 true) .empty .empty)))

#time def treeG_J005_part090 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [1163153951136987269496668951272065973575]) 0) 23 true) treeG_J005_part088 treeG_J005_part089)

#time def treeG_J005_part091 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [982584190399002490182797]) 0) 68 false) treeG_J005_part087 treeG_J005_part090)

#time def treeG_J005_part092 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [399277738382879562103130137146631855050705]) 0) 8 true) treeG_J005_part084 treeG_J005_part091)

#time def treeG_J005_part093 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [16854485829406774742625242250852093825]) 0) 25 true) treeG_J005_part077 treeG_J005_part092)

#time def treeG_J005_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [1263369895712890704270488800560465995924655]) 0) 8 true) (.node 596 (sourceLit (List.headD (raw_ints% [53899722303217398095899787530627630368465]) 0) 13 true) (.node 595 (sourceLit (List.headD (raw_ints% [9375569636848235456239]) 0) 75 false) (.node 594 (sourceLit (List.headD (raw_ints% [37842871131124077268575179063213711123115]) 0) 14 true) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [276645451341629430768863]) 0) 70 false) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [3275741109873715486583369175]) 0) 59 false) (.node 621 (sourceLit (List.headD (raw_ints% [107754729709991852946822810202060085925]) 0) 32 true) (.node 599 (sourceLit (List.headD (raw_ints% [64418378840635703593957]) 0) 72 false) .empty .empty) .empty) (.node 623 (sourceLit (List.headD (raw_ints% [208311615806547612316399770279538018575]) 0) 28 true) .empty .empty)))

#time def treeG_J005_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [224160827479331023886678996500239416235]) 0) 24 true) (.node 627 (sourceLit (List.headD (raw_ints% [215741669858692130813803709016375400905]) 0) 25 true) (.node 626 (sourceLit (List.headD (raw_ints% [210191281205028216421154625]) 0) 62 false) (.node 625 (sourceLit (List.headD (raw_ints% [125860614913785828913111953052322708475]) 0) 27 true) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [167593034739315203864789625]) 0) 62 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [1052046814728067444408108826051746575795]) 0) 21 true) (.node 630 (sourceLit (List.headD (raw_ints% [34900782432492405430079775]) 0) 64 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [938125407536481054961161]) 0) 69 false) .empty .empty)))

#time def treeG_J005_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [70094051782988095589802525]) 0) 64 false) treeG_J005_part094 treeG_J005_part095)

#time def treeG_J005_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [42261758182037328639195]) 0) 73 false) (.node 636 (sourceLit (List.headD (raw_ints% [185549325892359616381541]) 0) 71 false) (.node 635 (sourceLit (List.headD (raw_ints% [3624228626682631197414694972277976367635]) 0) 18 true) (.node 634 (sourceLit (List.headD (raw_ints% [103335716242283562589907]) 0) 72 false) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [5113785957730524111231986197473866050965]) 0) 17 true) .empty .empty)) (.node 664 (sourceLit (List.headD (raw_ints% [12168789460482059918752916346618367215225]) 0) 23 true) (.node 663 (sourceLit (List.headD (raw_ints% [9946883962487059461025105725]) 0) 58 false) (.node 639 (sourceLit (List.headD (raw_ints% [119195312180181771306989845934246135526255]) 0) 12 true) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [1630113739560551990816403525]) 0) 60 false) .empty .empty)))

#time def treeG_J005_part098 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [46266336205818706950249753]) 0) 64 false) (.node 669 (sourceLit (List.headD (raw_ints% [227890368154009455148904175]) 0) 62 false) (.node 668 (sourceLit (List.headD (raw_ints% [11591612096208729028513173561728811548385]) 0) 20 true) (.node 667 (sourceLit (List.headD (raw_ints% [294615129727793247416034075]) 0) 62 false) .empty .empty) .empty) (.node 670 (sourceLit (List.headD (raw_ints% [46740245794430573538949410284316109288605]) 0) 17 true) .empty .empty)) (.node 673 (sourceLit (List.headD (raw_ints% [4869047610016308948067979]) 0) 67 false) (.node 672 (sourceLit (List.headD (raw_ints% [53518569194649780509082804434403352835145]) 0) 16 true) .empty .empty) (.node 674 (sourceLit (List.headD (raw_ints% [133770984912919626008205524137949511363285]) 0) 14 true) .empty .empty)))

#time def treeG_J005_part099 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [14039948419090786489480451591092978388895]) 0) 21 true) treeG_J005_part097 treeG_J005_part098)

#time def treeG_J005_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [1340733250344091431849849243759087675675]) 0) 20 true) treeG_J005_part096 treeG_J005_part099)

#time def treeG_J005_part101 : IntSourceTree :=
  (.node 704 (sourceLit (List.headD (raw_ints% [7703874305431440402151424925]) 0) 59 false) (.node 678 (sourceLit (List.headD (raw_ints% [3973146925003165985631065065652772840263505]) 0) 8 true) (.node 677 (sourceLit (List.headD (raw_ints% [465551852227809034757301]) 0) 70 false) (.node 676 (sourceLit (List.headD (raw_ints% [178050909804470998538640690695162857160175]) 0) 13 true) .empty .empty) .empty) (.node 679 (sourceLit (List.headD (raw_ints% [104628653887513610962823]) 0) 72 false) .empty .empty)) (.node 707 (sourceLit (List.headD (raw_ints% [12314015060221249442970021918961975181655]) 0) 22 true) (.node 706 (sourceLit (List.headD (raw_ints% [1209731177150495557974094275]) 0) 61 false) (.node 705 (sourceLit (List.headD (raw_ints% [11161904541171773287448020722199785547425]) 0) 24 true) .empty .empty) .empty) (.node 708 (sourceLit (List.headD (raw_ints% [421637224716271290967278525]) 0) 62 false) .empty .empty)))

#time def treeG_J005_part102 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [3215676150139771946629467]) 0) 68 false) (.node 712 (sourceLit (List.headD (raw_ints% [31256329685235010070871177]) 0) 65 false) (.node 711 (sourceLit (List.headD (raw_ints% [38323871276606033983684539675902136682245]) 0) 18 true) (.node 710 (sourceLit (List.headD (raw_ints% [158088803289024644288744625]) 0) 63 false) .empty .empty) .empty) (.node 713 (sourceLit (List.headD (raw_ints% [42792703191897049054284010484330651429745]) 0) 17 true) .empty .empty)) (.node 716 (sourceLit (List.headD (raw_ints% [341118175666765349738067]) 0) 71 false) (.node 715 (sourceLit (List.headD (raw_ints% [104777155899458576428887964359725700422205]) 0) 15 true) .empty .empty) (.node 717 (sourceLit (List.headD (raw_ints% [137140622142626805648784801115371928752455]) 0) 14 true) .empty .empty)))

#time def treeG_J005_part103 : IntSourceTree :=
  (.node 709 (sourceLit (List.headD (raw_ints% [9798325476374080837419741589726896218505]) 0) 21 true) treeG_J005_part101 treeG_J005_part102)

#time def treeG_J005_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [86920508385561266515247001789966989904855]) 0) 20 true) (.node 746 (sourceLit (List.headD (raw_ints% [164550524239657586109687879964103590369905]) 0) 21 true) (.node 745 (sourceLit (List.headD (raw_ints% [759220070733861051416877675]) 0) 63 false) (.node 719 (sourceLit (List.headD (raw_ints% [3019584427561711815175146298178803756053465]) 0) 9 true) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [114389505927837788819757525]) 0) 65 false) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [13977808385400742167311859]) 0) 67 false) (.node 750 (sourceLit (List.headD (raw_ints% [266806169449540013258482320586944569703555]) 0) 17 true) (.node 749 (sourceLit (List.headD (raw_ints% [615384081278533126785652875]) 0) 62 false) .empty .empty) .empty) (.node 752 (sourceLit (List.headD (raw_ints% [253072401018198491360393512972813740622815]) 0) 16 true) .empty .empty)))

#time def treeG_J005_part105 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [13580852709253065137413389477114834040050735]) 0) 8 true) (.node 756 (sourceLit (List.headD (raw_ints% [660166337391197612892463024182642746217465]) 0) 13 true) (.node 755 (sourceLit (List.headD (raw_ints% [2162341147021522014390251]) 0) 69 false) (.node 754 (sourceLit (List.headD (raw_ints% [550912266157433158860338643611340911512635]) 0) 14 true) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [898920850439252364194967]) 0) 70 false) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [4864029388720392853360927125]) 0) 61 false) (.node 759 (sourceLit (List.headD (raw_ints% [95938082806073054618849]) 0) 73 false) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [76118254589718168333358929022570807594125]) 0) 23 true) .empty .empty)))

#time def treeG_J005_part106 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [21518234465202392174735219]) 0) 66 false) treeG_J005_part104 treeG_J005_part105)

#time def treeG_J005_part107 : IntSourceTree :=
  (.node 718 (sourceLit (List.headD (raw_ints% [296504819499659720200521]) 0) 71 false) treeG_J005_part103 treeG_J005_part106)

#time def treeG_J005_part108 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [65833437694890620764951]) 0) 73 false) treeG_J005_part100 treeG_J005_part107)

#time def treeG_J005_part109 : IntSourceTree :=
  (.node 793 (sourceLit (List.headD (raw_ints% [105139848913150721153054751244241544596535]) 0) 18 true) (.node 791 (sourceLit (List.headD (raw_ints% [114241149086466989637398890455521216510655]) 0) 19 true) (.node 790 (sourceLit (List.headD (raw_ints% [228647638994754241248454125]) 0) 64 false) (.node 789 (sourceLit (List.headD (raw_ints% [38561091454593592838913630100120046843175]) 0) 22 true) .empty .empty) .empty) (.node 792 (sourceLit (List.headD (raw_ints% [80566137397970927267623695]) 0) 65 false) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [1480104795687991314914117]) 0) 70 false) (.node 795 (sourceLit (List.headD (raw_ints% [223067555128987291215725339625807605545215]) 0) 16 true) (.node 794 (sourceLit (List.headD (raw_ints% [15086882164922848281476285]) 0) 67 false) .empty .empty) .empty) (.node 797 (sourceLit (List.headD (raw_ints% [261512857624285403621839111533635408732505]) 0) 15 true) .empty .empty)))

#time def treeG_J005_part110 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [2201103683644449928431990005820738428259645]) 0) 17 true) (.node 828 (sourceLit (List.headD (raw_ints% [1130971565049929426818495862571165931601145]) 0) 20 true) (.node 827 (sourceLit (List.headD (raw_ints% [3948913341297690542802866925]) 0) 62 false) (.node 799 (sourceLit (List.headD (raw_ints% [5280634140845676661119121589468015141998635]) 0) 10 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [2201805658979733533512030875]) 0) 62 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [1574785984365273342837988734315525723547665]) 0) 16 true) (.node 831 (sourceLit (List.headD (raw_ints% [172736405453151272579206689]) 0) 65 false) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [14761975733192133773222119]) 0) 68 false) .empty .empty)))

#time def treeG_J005_part111 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [301208015469796321997223]) 0) 72 false) treeG_J005_part109 treeG_J005_part110)

#time def treeG_J005_part112 : IntSourceTree :=
  (.node 839 (sourceLit (List.headD (raw_ints% [102634966331861633689187]) 0) 74 false) (.node 837 (sourceLit (List.headD (raw_ints% [2061288740936730265633267]) 0) 70 false) (.node 836 (sourceLit (List.headD (raw_ints% [2908914544672599046559142409830278942505975]) 0) 13 true) (.node 835 (sourceLit (List.headD (raw_ints% [10762199870879804252695783]) 0) 68 false) .empty .empty) .empty) (.node 838 (sourceLit (List.headD (raw_ints% [53366438842563998189777423075495830595470545]) 0) 8 true) .empty .empty)) (.node 870 (sourceLit (List.headD (raw_ints% [1744510380990225051015122625]) 0) 63 false) (.node 869 (sourceLit (List.headD (raw_ints% [1053849382140742241140668602370925837914795]) 0) 21 true) (.node 868 (sourceLit (List.headD (raw_ints% [6489231812466247755456891975]) 0) 62 false) .empty .empty) .empty) (.node 871 (sourceLit (List.headD (raw_ints% [1972621385471515949157192224909695995238335]) 0) 18 true) .empty .empty)))

#time def treeG_J005_part113 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [2385888829424028239315464186763008125040965]) 0) 14 true) (.node 875 (sourceLit (List.headD (raw_ints% [2367427788805415335605962716952773304486055]) 0) 15 true) (.node 874 (sourceLit (List.headD (raw_ints% [43961020767845686811412191]) 0) 67 false) (.node 873 (sourceLit (List.headD (raw_ints% [1364506286538971900531879231827042634354595]) 0) 17 true) .empty .empty) .empty) (.node 876 (sourceLit (List.headD (raw_ints% [7801990279503821622867549]) 0) 69 false) .empty .empty)) (.node 879 (sourceLit (List.headD (raw_ints% [42805170560872644867539179896559800311473275]) 0) 9 true) (.node 878 (sourceLit (List.headD (raw_ints% [1458872709997137621638821]) 0) 71 false) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [10776657965952761977401753075]) 0) 62 false) .empty .empty)))

#time def treeG_J005_part114 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [264906673508331617890789683]) 0) 65 false) treeG_J005_part112 treeG_J005_part113)

#time def treeG_J005_part115 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [2813562899063389918037413396204388515576485]) 0) 14 true) treeG_J005_part111 treeG_J005_part114)

#time def treeG_J005_part116 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [4149852612120735319839551]) 0) 71 false) (.node 913 (sourceLit (List.headD (raw_ints% [205858770575563082797901207]) 0) 66 false) (.node 912 (sourceLit (List.headD (raw_ints% [14206185099406854250419549064962042238359015]) 0) 16 true) (.node 911 (sourceLit (List.headD (raw_ints% [1399037570083922505856709247]) 0) 64 false) .empty .empty) .empty) (.node 914 (sourceLit (List.headD (raw_ints% [19018537685560160490472654313028293634097035]) 0) 14 true) .empty .empty)) (.node 918 (sourceLit (List.headD (raw_ints% [252027331323711616442601992830169209409772975]) 0) 8 true) (.node 917 (sourceLit (List.headD (raw_ints% [2870350769283545678617141]) 0) 71 false) (.node 916 (sourceLit (List.headD (raw_ints% [16030507765770723638288559325791907493382465]) 0) 13 true) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [1048332844669691086882073]) 0) 72 false) .empty .empty)))

#time def treeG_J005_part117 : IntSourceTree :=
  (.node 955 (sourceLit (List.headD (raw_ints% [4162777474188686288716672899018880082402745]) 0) 17 true) (.node 953 (sourceLit (List.headD (raw_ints% [3210419703216970587471917458283749901001105]) 0) 19 true) (.node 952 (sourceLit (List.headD (raw_ints% [283532724143897721991479891]) 0) 67 false) (.node 951 (sourceLit (List.headD (raw_ints% [7387363789846946459728053261284798097443865]) 0) 20 true) .empty .empty) .empty) (.node 954 (sourceLit (List.headD (raw_ints% [20237218725964674498311127]) 0) 70 false) .empty .empty)) (.node 957 (sourceLit (List.headD (raw_ints% [3411154734086673849743273784757224842085375]) 0) 16 true) (.node 956 (sourceLit (List.headD (raw_ints% [25396830617462060935848859]) 0) 69 false) .empty .empty) (.node 958 (sourceLit (List.headD (raw_ints% [4281828828569953735595461]) 0) 71 false) .empty .empty)))

#time def treeG_J005_part118 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [4516073792481268463193315225]) 0) 64 false) treeG_J005_part116 treeG_J005_part117)

#time def treeG_J005_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [19656129078894969578614577]) 0) 70 false) (.node 995 (sourceLit (List.headD (raw_ints% [2010920764230492397308947]) 0) 74 false) (.node 994 (sourceLit (List.headD (raw_ints% [186448323320325957107730063017131700029973685]) 0) 14 true) (.node 993 (sourceLit (List.headD (raw_ints% [928272126000027805168018357]) 0) 66 false) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [117178371408267237600644973442812255143505375]) 0) 13 true) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [766374376192310409181529341]) 0) 67 false) (.node 999 (sourceLit (List.headD (raw_ints% [808373995975065662178347]) 0) 74 false) (.node 998 (sourceLit (List.headD (raw_ints% [1494483892528665394625954184965529909737939025]) 0) 8 true) .empty .empty) .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [169797213423571211952863371421056179700362705]) 0) 15 true) .empty .empty)))

#time def treeG_J005_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [1241199335980302458022261997925637182459396265]) 0) 13 true) (.node 1039 (sourceLit (List.headD (raw_ints% [1285261731765826423050891372031920500639639325]) 0) 9 true) (.node 1038 (sourceLit (List.headD (raw_ints% [3843575062581253960754779]) 0) 73 false) (.node 1037 (sourceLit (List.headD (raw_ints% [103533752471920542201671878303783355775163875]) 0) 14 true) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [637675447281558895753756733]) 0) 68 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [11757836423877164007188046237918739629483036975]) 0) 8 true) (.node 1077 (sourceLit (List.headD (raw_ints% [20911492303598620728327293]) 0) 72 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [189700066662886768661027]) 0) 78 false) .empty .empty)))

#time def treeG_J005_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [103302098293289452491923749]) 0) 69 false) treeG_J005_part119 treeG_J005_part120)

#time def treeG_J005_part122 : IntSourceTree :=
  (.node 959 (sourceLit (List.headD (raw_ints% [52305540190709742893765703233402352274574925]) 0) 11 true) treeG_J005_part118 treeG_J005_part121)

#time def treeG_J005_part123 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [31522076544859301788069405270048888385013795]) 0) 17 true) treeG_J005_part115 treeG_J005_part122)

#time def treeG_J005_part124 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [1408594870129133330148841875]) 0) 62 false) treeG_J005_part108 treeG_J005_part123)

#time def treeG_J005_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [2635955650275539491621309]) 0) 67 false) treeG_J005_part093 treeG_J005_part124)

#time def treeG_J005_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [6283329302905642246347603]) 0) 64 false) treeG_J005_part062 treeG_J005_part125)

#time def treeG_J005 : IntSourceTree := treeG_J005_part126

#time def treeG_J007_part000 : IntSourceTree :=
  (.node 5 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 39 true) (.node 3 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 37 false) (.node 2 (sourceLit (List.headD (raw_ints% [12169415297654383892296450852575]) 0) 40 false) (.node 1 (sourceLit (List.headD (raw_ints% [88518363106410249583329929795625]) 0) 36 false) .empty .empty) .empty) (.node 4 (sourceLit (List.headD (raw_ints% [2826636805078646625350031371625]) 0) 42 false) .empty .empty)) (.node 8 (sourceLit (List.headD (raw_ints% [65335690723103574854519296561275]) 0) 39 true) (.node 7 (sourceLit (List.headD (raw_ints% [17703672621282049916665985959125]) 0) 40 true) (.node 6 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 43 false) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 43 false) .empty .empty)))

#time def treeG_J007_part001 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [75767361229775174804324412075]) 0) 47 false) (.node 13 (sourceLit (List.headD (raw_ints% [155983466436556895115009705675]) 0) 46 false) (.node 12 (sourceLit (List.headD (raw_ints% [104256334917379917356023857027825]) 0) 36 true) (.node 11 (sourceLit (List.headD (raw_ints% [644671552035480809290358032125]) 0) 44 false) .empty .empty) .empty) (.node 14 (sourceLit (List.headD (raw_ints% [131147733927682748123981381766375]) 0) 35 true) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [863572738452957636505285410051525]) 0) 31 true) (.node 17 (sourceLit (List.headD (raw_ints% [4613879239701665978014960275]) 0) 51 false) (.node 16 (sourceLit (List.headD (raw_ints% [679402321593256731039276077996625]) 0) 32 true) .empty .empty) .empty) (.node 19 (sourceLit (List.headD (raw_ints% [2252992490449523311930754625]) 0) 52 false) .empty .empty)))

#time def treeG_J007_part002 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [46293084878363218641634874689275]) 0) 38 true) treeG_J007_part000 treeG_J007_part001)

#time def treeG_J007_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [33133555503878600942843175]) 0) 58 false) (.node 23 (sourceLit (List.headD (raw_ints% [270081977364366833933912925]) 0) 55 false) (.node 22 (sourceLit (List.headD (raw_ints% [1920319576321532908638258614332575]) 0) 28 true) (.node 21 (sourceLit (List.headD (raw_ints% [551139341455816794393881625]) 0) 54 false) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [3994390174529490510262040310668625]) 0) 24 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [279022265385074950800242489675043105]) 0) 21 false) (.node 27 (sourceLit (List.headD (raw_ints% [16278584956671822715928025]) 0) 59 false) (.node 26 (sourceLit (List.headD (raw_ints% [34798129370745207693130573365443175]) 0) 23 false) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [4003000377994299853458675]) 0) 61 false) .empty .empty)))

#time def treeG_J007_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [29913876835092532582729]) 0) 68 false) (.node 33 (sourceLit (List.headD (raw_ints% [60674946022260387557091]) 0) 67 false) (.node 32 (sourceLit (List.headD (raw_ints% [7888213325169007044081344411417801955]) 0) 17 false) (.node 31 (sourceLit (List.headD (raw_ints% [1970522166032201229468075]) 0) 62 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [18443476681986606402732161723485572375]) 0) 16 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [7378869973193727965957]) 0) 70 false) (.node 36 (sourceLit (List.headD (raw_ints% [82951657953331392390444237929978973675]) 0) 14 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [181827320470844507875120386218692502385]) 0) 13 false) .empty .empty)))

#time def treeG_J007_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [790365545248297227318186866170728255]) 0) 20 false) treeG_J007_part003 treeG_J007_part004)

#time def treeG_J007_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [2031639351964655083225097811212925]) 0) 29 true) treeG_J007_part002 treeG_J007_part005)

#time def treeG_J007_part007 : IntSourceTree :=
  (.node 46 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 40 true) (.node 44 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 38 false) (.node 43 (sourceLit (List.headD (raw_ints% [12169415297654383892296450852575]) 0) 41 false) (.node 42 (sourceLit (List.headD (raw_ints% [88518363106410249583329929795625]) 0) 37 false) .empty .empty) .empty) (.node 45 (sourceLit (List.headD (raw_ints% [2826636805078646625350031371625]) 0) 43 false) .empty .empty)) (.node 49 (sourceLit (List.headD (raw_ints% [65335690723103574854519296561275]) 0) 40 true) (.node 48 (sourceLit (List.headD (raw_ints% [17703672621282049916665985959125]) 0) 41 true) (.node 47 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 44 false) .empty .empty) .empty) (.node 50 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 44 false) .empty .empty)))

#time def treeG_J007_part008 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [75767361229775174804324412075]) 0) 48 false) (.node 54 (sourceLit (List.headD (raw_ints% [155983466436556895115009705675]) 0) 47 false) (.node 53 (sourceLit (List.headD (raw_ints% [104256334917379917356023857027825]) 0) 37 true) (.node 52 (sourceLit (List.headD (raw_ints% [644671552035480809290358032125]) 0) 45 false) .empty .empty) .empty) (.node 55 (sourceLit (List.headD (raw_ints% [131147733927682748123981381766375]) 0) 36 true) .empty .empty)) (.node 58 (sourceLit (List.headD (raw_ints% [4613879239701665978014960275]) 0) 52 false) (.node 57 (sourceLit (List.headD (raw_ints% [679402321593256731039276077996625]) 0) 33 true) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [863572738452957636505285410051525]) 0) 32 true) .empty .empty)))

#time def treeG_J007_part009 : IntSourceTree :=
  (.node 51 (sourceLit (List.headD (raw_ints% [46293084878363218641634874689275]) 0) 39 true) treeG_J007_part007 treeG_J007_part008)

#time def treeG_J007_part010 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [3994390174529490510262040310668625]) 0) 25 true) (.node 63 (sourceLit (List.headD (raw_ints% [1920319576321532908638258614332575]) 0) 29 true) (.node 62 (sourceLit (List.headD (raw_ints% [551139341455816794393881625]) 0) 55 false) (.node 61 (sourceLit (List.headD (raw_ints% [2031639351964655083225097811212925]) 0) 30 true) .empty .empty) .empty) (.node 64 (sourceLit (List.headD (raw_ints% [270081977364366833933912925]) 0) 56 false) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [16278584956671822715928025]) 0) 60 false) (.node 67 (sourceLit (List.headD (raw_ints% [34798129370745207693130573365443175]) 0) 24 false) (.node 66 (sourceLit (List.headD (raw_ints% [33133555503878600942843175]) 0) 59 false) .empty .empty) .empty) (.node 69 (sourceLit (List.headD (raw_ints% [279022265385074950800242489675043105]) 0) 22 false) .empty .empty)))

#time def treeG_J007_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [18443476681986606402732161723485572375]) 0) 17 false) (.node 73 (sourceLit (List.headD (raw_ints% [7888213325169007044081344411417801955]) 0) 18 false) (.node 72 (sourceLit (List.headD (raw_ints% [1970522166032201229468075]) 0) 63 false) (.node 71 (sourceLit (List.headD (raw_ints% [790365545248297227318186866170728255]) 0) 21 false) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [60674946022260387557091]) 0) 68 false) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [82951657953331392390444237929978973675]) 0) 15 false) (.node 76 (sourceLit (List.headD (raw_ints% [29913876835092532582729]) 0) 69 false) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [7378869973193727965957]) 0) 71 false) .empty .empty)))

#time def treeG_J007_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [4003000377994299853458675]) 0) 62 false) treeG_J007_part010 treeG_J007_part011)

#time def treeG_J007_part013 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [2252992490449523311930754625]) 0) 53 false) treeG_J007_part009 treeG_J007_part012)

#time def treeG_J007_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [3642453774985166446305]) 0) 71 false) treeG_J007_part006 treeG_J007_part013)

#time def treeG_J007_part015 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 40 false) (.node 85 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 41 false) (.node 84 (sourceLit (List.headD (raw_ints% [4671389246287868633473209740475]) 0) 43 false) (.node 83 (sourceLit (List.headD (raw_ints% [161415838605806925710778107274375]) 0) 37 false) .empty .empty) .empty) (.node 86 (sourceLit (List.headD (raw_ints% [4314340386698986954481626830375]) 0) 43 false) .empty .empty)) (.node 90 (sourceLit (List.headD (raw_ints% [476392440906465380194519497800925]) 0) 38 true) (.node 89 (sourceLit (List.headD (raw_ints% [20381539068198662509102857784875]) 0) 42 true) (.node 88 (sourceLit (List.headD (raw_ints% [151027417024435177812499194985275]) 0) 39 false) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [2033194894881131783146513793625]) 0) 44 false) .empty .empty)))

#time def treeG_J007_part016 : IntSourceTree :=
  (.node 97 (sourceLit (List.headD (raw_ints% [57311844270968510892264570975]) 0) 49 false) (.node 95 (sourceLit (List.headD (raw_ints% [236199571643338615425694999275]) 0) 47 false) (.node 94 (sourceLit (List.headD (raw_ints% [702902945411356590724209474456225]) 0) 35 true) (.node 93 (sourceLit (List.headD (raw_ints% [244344042799461957087674163225]) 0) 47 false) .empty .empty) .empty) (.node 96 (sourceLit (List.headD (raw_ints% [3517325164092591208928128138527375]) 0) 32 true) .empty .empty)) (.node 99 (sourceLit (List.headD (raw_ints% [6974765988953808644099165925]) 0) 52 false) (.node 98 (sourceLit (List.headD (raw_ints% [4571645834293096211808923213921475]) 0) 31 true) .empty .empty) (.node 100 (sourceLit (List.headD (raw_ints% [11785524463282667100859468749611475]) 0) 29 true) .empty .empty)))

#time def treeG_J007_part017 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [636433023136431580910134138000575]) 0) 36 true) treeG_J007_part015 treeG_J007_part016)

#time def treeG_J007_part018 : IntSourceTree :=
  (.node 106 (sourceLit (List.headD (raw_ints% [66753250766981131775226895850792175]) 0) 23 true) (.node 104 (sourceLit (List.headD (raw_ints% [118906062710048615642586511006616175]) 0) 24 true) (.node 103 (sourceLit (List.headD (raw_ints% [832196705547266754853850325]) 0) 55 false) (.node 102 (sourceLit (List.headD (raw_ints% [14332795239395707757162523875370825]) 0) 28 true) .empty .empty) .empty) (.node 105 (sourceLit (List.headD (raw_ints% [203814866356609632048226575]) 0) 57 false) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [6137792289338761431234675]) 0) 62 false) (.node 108 (sourceLit (List.headD (raw_ints% [277747804546848372289846684172047695]) 0) 21 false) (.node 107 (sourceLit (List.headD (raw_ints% [49988526051085379169758325]) 0) 59 false) .empty .empty) .empty) (.node 110 (sourceLit (List.headD (raw_ints% [1441812577832302379083753051229616585]) 0) 20 false) .empty .empty)))

#time def treeG_J007_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [212143968958454310053270349645790184325]) 0) 14 false) (.node 114 (sourceLit (List.headD (raw_ints% [44662229919365449949918593567856843265]) 0) 16 false) (.node 113 (sourceLit (List.headD (raw_ints% [1485122597854118129011347]) 0) 64 false) (.node 112 (sourceLit (List.headD (raw_ints% [17403484122776504230100635306045502205]) 0) 17 false) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [91436015209428242531453]) 0) 68 false) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [481785943155806631248433517221139287015]) 0) 13 false) (.node 117 (sourceLit (List.headD (raw_ints% [5633751715474701154193]) 0) 72 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [11115286171402289485609]) 0) 71 false) .empty .empty)))

#time def treeG_J007_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [6035478589956398477449275]) 0) 62 false) treeG_J007_part018 treeG_J007_part019)

#time def treeG_J007_part021 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [212731643624213314692109125]) 0) 57 false) treeG_J007_part017 treeG_J007_part020)

#time def treeG_J007_part022 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [108181553873769376333509245773275]) 0) 41 false) (.node 127 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 46 false) (.node 126 (sourceLit (List.headD (raw_ints% [26034812678355955759802920528125]) 0) 40 false) (.node 125 (sourceLit (List.headD (raw_ints% [6516141687497090641596388109325]) 0) 43 false) .empty .empty) .empty) (.node 128 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 44 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [347130835711412743464038940375]) 0) 47 false) (.node 131 (sourceLit (List.headD (raw_ints% [215049678014051080776442311555825]) 0) 40 true) (.node 130 (sourceLit (List.headD (raw_ints% [23059405515115275101539729610625]) 0) 43 true) .empty .empty) .empty) (.node 133 (sourceLit (List.headD (raw_ints% [266088344109525831777055140486375]) 0) 38 true) .empty .empty)))

#time def treeG_J007_part023 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [1854036547920069287651818901934975]) 0) 33 true) (.node 137 (sourceLit (List.headD (raw_ints% [1418961421249667238944426030265375]) 0) 34 true) (.node 136 (sourceLit (List.headD (raw_ints% [2506753287711928759708915425]) 0) 54 false) (.node 135 (sourceLit (List.headD (raw_ints% [285877605741836921300114046344925]) 0) 37 true) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [38856327312161846980204729875]) 0) 50 false) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [4876942555659006008817185469199275]) 0) 31 true) (.node 140 (sourceLit (List.headD (raw_ints% [1180443374626071333042102825]) 0) 55 false) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [1150713807537889723142991375]) 0) 55 false) .empty .empty)))

#time def treeG_J007_part024 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [332704619162367019060338620775]) 0) 47 false) treeG_J007_part022 treeG_J007_part023)

#time def treeG_J007_part025 : IntSourceTree :=
  (.node 148 (sourceLit (List.headD (raw_ints% [8427485273603389113457575]) 0) 62 false) (.node 146 (sourceLit (List.headD (raw_ints% [137547755348852430162540225]) 0) 58 false) (.node 145 (sourceLit (List.headD (raw_ints% [57455836267759562566162235347973775]) 0) 26 true) (.node 144 (sourceLit (List.headD (raw_ints% [70264341022862490114992175]) 0) 59 false) .empty .empty) .empty) (.node 147 (sourceLit (List.headD (raw_ints% [50775690068863169734178734608117675]) 0) 25 true) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [325723516292002575882783092529444165]) 0) 22 false) (.node 150 (sourceLit (List.headD (raw_ints% [8272584200683223009010675]) 0) 62 false) (.node 149 (sourceLit (List.headD (raw_ints% [637230419113289255197902751497705]) 0) 23 true) .empty .empty) .empty) (.node 152 (sourceLit (List.headD (raw_ints% [254059776495262327998825]) 0) 67 false) .empty .empty)))

#time def treeG_J007_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [15156136888705076650815]) 0) 71 false) (.node 156 (sourceLit (List.headD (raw_ints% [15380534593583927487181]) 0) 71 false) (.node 155 (sourceLit (List.headD (raw_ints% [13109376618689421773593215922185635445]) 0) 18 false) (.node 154 (sourceLit (List.headD (raw_ints% [999723029676035028554619]) 0) 65 false) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [64596155502561458831413055857905605325]) 0) 16 false) .empty .empty)) (.node 165 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 42 false) (.node 159 (sourceLit (List.headD (raw_ints% [149979311342481061686656565501223392315]) 0) 15 false) .empty .empty) (.node 166 (sourceLit (List.headD (raw_ints% [8717942988295194328711149388275]) 0) 43 false) .empty .empty)))

#time def treeG_J007_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [4757635398803748593009645447313850125]) 0) 19 false) treeG_J007_part025 treeG_J007_part026)

#time def treeG_J007_part028 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [6206237831537087424262132630519125]) 0) 30 true) treeG_J007_part024 treeG_J007_part027)

#time def treeG_J007_part029 : IntSourceTree :=
  (.node 124 (sourceLit (List.headD (raw_ints% [36448737749698338063724088739375]) 0) 40 false) treeG_J007_part021 treeG_J007_part028)

#time def treeG_J007_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [181827320470844507875120386218692502385]) 0) 14 false) treeG_J007_part014 treeG_J007_part029)

#time def treeG_J007_part031 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [6245156673313203003936019831785825]) 0) 36 true) (.node 170 (sourceLit (List.headD (raw_ints% [2207297302886775401530667430173325]) 0) 38 false) (.node 169 (sourceLit (List.headD (raw_ints% [45374959239420380038513661491875]) 0) 42 false) (.node 168 (sourceLit (List.headD (raw_ints% [39398641422968384316345023734725]) 0) 39 false) .empty .empty) .empty) (.node 171 (sourceLit (List.headD (raw_ints% [12546300204998203442343121702125]) 0) 45 true) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [429209666681395422694982242275]) 0) 47 false) (.node 174 (sourceLit (List.headD (raw_ints% [3554510560341056717708672773325775]) 0) 35 true) (.node 173 (sourceLit (List.headD (raw_ints% [449917628623363529840403717525]) 0) 47 false) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [14778841603384971754279170827547825]) 0) 32 true) .empty .empty)))

#time def treeG_J007_part032 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [63698285651148388383912443631817575]) 0) 28 true) (.node 180 (sourceLit (List.headD (raw_ints% [47543645070159550103998736112307725]) 0) 29 true) (.node 179 (sourceLit (List.headD (raw_ints% [24906795334254229692006398025]) 0) 51 false) (.node 178 (sourceLit (List.headD (raw_ints% [18131736905701579611301893270324525]) 0) 31 true) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [754980087377644703657884575]) 0) 56 false) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [358299861826290288871710825]) 0) 57 false) (.node 184 (sourceLit (List.headD (raw_ints% [675492379726698574662966465699831825]) 0) 24 true) (.node 183 (sourceLit (List.headD (raw_ints% [1469230909528512691432132425]) 0) 55 false) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [852540129517171869283368869716788225]) 0) 23 true) .empty .empty)))

#time def treeG_J007_part033 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [103120366142594929729106016225]) 0) 49 false) treeG_J007_part031 treeG_J007_part032)

#time def treeG_J007_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [3442820919911660626397482615838924355]) 0) 17 false) (.node 190 (sourceLit (List.headD (raw_ints% [1452008264538115007166919495253579865]) 0) 20 true) (.node 189 (sourceLit (List.headD (raw_ints% [10717178257868016795680475]) 0) 62 false) (.node 188 (sourceLit (List.headD (raw_ints% [1902569886750469803783566191631813295]) 0) 21 true) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [10509689811410047540572075]) 0) 62 false) .empty .empty)) (.node 195 (sourceLit (List.headD (raw_ints% [633978968838322058428807]) 0) 66 false) (.node 194 (sourceLit (List.headD (raw_ints% [31459936461494527538235733589164758735]) 0) 16 false) (.node 193 (sourceLit (List.headD (raw_ints% [2579833826070079118969853]) 0) 64 false) .empty .empty) .empty) (.node 196 (sourceLit (List.headD (raw_ints% [207356082839607186701712559864150149915]) 0) 14 false) .empty .empty)))

#time def treeG_J007_part035 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [19786457635550526377450219601375]) 0) 41 false) (.node 206 (sourceLit (List.headD (raw_ints% [98932288177752631887251098006875]) 0) 40 false) (.node 199 (sourceLit (List.headD (raw_ints% [19196987606007863816021]) 0) 71 false) (.node 198 (sourceLit (List.headD (raw_ints% [551752544885176710054175376505350398185]) 0) 13 false) .empty .empty) .empty) (.node 207 (sourceLit (List.headD (raw_ints% [5742535825054513670447958470775]) 0) 44 false) .empty .empty)) (.node 210 (sourceLit (List.headD (raw_ints% [17108591188633913785013347775625]) 0) 45 false) (.node 209 (sourceLit (List.headD (raw_ints% [176964466324570368350673467811825]) 0) 40 true) .empty .empty) (.node 211 (sourceLit (List.headD (raw_ints% [2637396658914877563083552053284975]) 0) 39 false) .empty .empty)))

#time def treeG_J007_part036 : IntSourceTree :=
  (.node 197 (sourceLit (List.headD (raw_ints% [2436695719527306583247]) 0) 74 false) treeG_J007_part034 treeG_J007_part035)

#time def treeG_J007_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [21889807324441762748195475]) 0) 61 false) treeG_J007_part033 treeG_J007_part036)

#time def treeG_J007_part038 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [11940918760885637276390318767017075]) 0) 33 true) (.node 215 (sourceLit (List.headD (raw_ints% [2982755348857382875108444680635925]) 0) 36 true) (.node 214 (sourceLit (List.headD (raw_ints% [567130638084360040620468814275]) 0) 47 false) (.node 213 (sourceLit (List.headD (raw_ints% [5712979985094151340381909550813075]) 0) 37 true) .empty .empty) .empty) (.node 216 (sourceLit (List.headD (raw_ints% [268777456267831982073611655075]) 0) 48 false) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [15463248337245659027669575425]) 0) 52 false) (.node 219 (sourceLit (List.headD (raw_ints% [14423663809861441035998255466454575]) 0) 32 true) (.node 218 (sourceLit (List.headD (raw_ints% [32132019415216541374450643175]) 0) 51 false) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [37789759958841538086364365173909175]) 0) 30 true) .empty .empty)))

#time def treeG_J007_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [750988749379445529815011400500552875]) 0) 24 true) (.node 225 (sourceLit (List.headD (raw_ints% [560580707191179449530641995003884275]) 0) 25 true) (.node 224 (sourceLit (List.headD (raw_ints% [907116181345612770512195025]) 0) 56 false) (.node 223 (sourceLit (List.headD (raw_ints% [51285809988074213535388178370779325]) 0) 29 true) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [27594013309679732338646325]) 0) 61 false) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [1901295425912243225273170386128817885]) 0) 22 true) (.node 228 (sourceLit (List.headD (raw_ints% [3365580512709593408684475]) 0) 64 false) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [13161772315052810582350275]) 0) 62 false) .empty .empty)))

#time def treeG_J007_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [1869206541972689091488546925]) 0) 55 false) treeG_J007_part038 treeG_J007_part039)

#time def treeG_J007_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [387890415340979218633911]) 0) 67 false) (.node 234 (sourceLit (List.headD (raw_ints% [790055398197022045207617]) 0) 66 false) (.node 233 (sourceLit (List.headD (raw_ints% [6072449877695836559621808278788775895]) 0) 18 true) (.node 232 (sourceLit (List.headD (raw_ints% [6444733387485850292590875]) 0) 63 false) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [5241183224115683991049301744793487845]) 0) 17 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [251793922200214586680862245502903613555]) 0) 14 false) (.node 238 (sourceLit (List.headD (raw_ints% [23830994623731828681137]) 0) 71 false) (.node 237 (sourceLit (List.headD (raw_ints% [78163771834484269038886448148338939265]) 0) 15 false) .empty .empty) .empty) (.node 247 (sourceLit (List.headD (raw_ints% [153084698548733019867641172705375]) 0) 40 false) .empty .empty)))

#time def treeG_J007_part042 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [855654969065274528694475206275]) 0) 51 true) (.node 251 (sourceLit (List.headD (raw_ints% [46763482582266031012369817253375]) 0) 45 false) (.node 250 (sourceLit (List.headD (raw_ints% [3623013033483338348336055172667925]) 0) 38 true) (.node 249 (sourceLit (List.headD (raw_ints% [6397125400967463415265860472625]) 0) 44 true) .empty .empty) .empty) (.node 252 (sourceLit (List.headD (raw_ints% [48443503215951244013272852684345425]) 0) 36 false) .empty .empty)) (.node 255 (sourceLit (List.headD (raw_ints% [705051609487324658545955386275]) 0) 47 false) (.node 254 (sourceLit (List.headD (raw_ints% [42149329320412154005346603633178825]) 0) 35 true) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [80669329560051280249191058952801775]) 0) 32 true) .empty .empty)))

#time def treeG_J007_part043 : IntSourceTree :=
  (.node 248 (sourceLit (List.headD (raw_ints% [328123651380520490592324318394875]) 0) 39 false) treeG_J007_part041 treeG_J007_part042)

#time def treeG_J007_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [2103455297122120158932485680312468195]) 0) 21 true) treeG_J007_part040 treeG_J007_part043)

#time def treeG_J007_part045 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [13240561876421028929271199582875]) 0) 46 true) treeG_J007_part037 treeG_J007_part044)

#time def treeG_J007_part046 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [238619794019583916307002477759455825]) 0) 28 true) (.node 260 (sourceLit (List.headD (raw_ints% [183234975887623506471973351350965475]) 0) 29 true) (.node 259 (sourceLit (List.headD (raw_ints% [39357243496178853056894888325]) 0) 51 false) (.node 258 (sourceLit (List.headD (raw_ints% [77395613181383518599820656865812075]) 0) 31 true) .empty .empty) .empty) (.node 261 (sourceLit (List.headD (raw_ints% [9423407638224501398406498825]) 0) 53 false) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [68602039939915310205060525]) 0) 60 false) (.node 264 (sourceLit (List.headD (raw_ints% [2606799459510051091601876950030044975]) 0) 24 true) (.node 263 (sourceLit (List.headD (raw_ints% [2269182174416865491544961425]) 0) 55 false) .empty .empty) .empty) (.node 266 (sourceLit (List.headD (raw_ints% [3632105528012263726961767090314285975]) 0) 23 true) .empty .empty)))

#time def treeG_J007_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [70753390427819505712237024385837906595]) 0) 17 true) (.node 270 (sourceLit (List.headD (raw_ints% [13758355142759830795018443593776963215]) 0) 20 true) (.node 269 (sourceLit (List.headD (raw_ints% [16207465843808730473795325]) 0) 62 false) (.node 268 (sourceLit (List.headD (raw_ints% [10113250103320658673256616216377032705]) 0) 21 true) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [15813854818695573624128475]) 0) 62 false) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [80039535483061220015210199819474965895]) 0) 16 true) (.node 273 (sourceLit (List.headD (raw_ints% [1932449780707885586810511]) 0) 65 false) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [946131827555722031986427]) 0) 66 false) .empty .empty)))

#time def treeG_J007_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [33298219294917701929097175]) 0) 61 false) treeG_J007_part046 treeG_J007_part047)

#time def treeG_J007_part049 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [126272029426272714735749446551675]) 0) 42 false) (.node 279 (sourceLit (List.headD (raw_ints% [28465001641455793546253]) 0) 71 false) (.node 278 (sourceLit (List.headD (raw_ints% [73557629790697442256916208681361115935]) 0) 13 false) (.node 277 (sourceLit (List.headD (raw_ints% [231941889291231597306103]) 0) 68 false) .empty .empty) .empty) (.node 288 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 48 false) .empty .empty)) (.node 292 (sourceLit (List.headD (raw_ints% [30002022229343529970820508418125]) 0) 47 false) (.node 291 (sourceLit (List.headD (raw_ints% [1565102423099553977854901806488225]) 0) 41 true) (.node 290 (sourceLit (List.headD (raw_ints% [11752858294800688600139604124125]) 0) 46 true) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [13539120800261348838413690558789625]) 0) 39 false) .empty .empty)))

#time def treeG_J007_part050 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [15742987342880519390955600349839375]) 0) 34 true) (.node 297 (sourceLit (List.headD (raw_ints% [17182102699791410743200185046446175]) 0) 35 true) (.node 296 (sourceLit (List.headD (raw_ints% [426048977753410816867523175]) 0) 58 false) (.node 295 (sourceLit (List.headD (raw_ints% [9791643492888692782559539738135725]) 0) 38 true) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [25348262823700992398901088125]) 0) 52 false) .empty .empty)) (.node 301 (sourceLit (List.headD (raw_ints% [36361303982195492096402246544264075]) 0) 32 true) (.node 300 (sourceLit (List.headD (raw_ints% [5973498789733298507306328225]) 0) 54 false) .empty .empty) (.node 302 (sourceLit (List.headD (raw_ints% [5684994554279123215429404975]) 0) 54 false) .empty .empty)))

#time def treeG_J007_part051 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [27948089648173144958843675415075]) 0) 47 true) treeG_J007_part049 treeG_J007_part050)

#time def treeG_J007_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [123497151253756242844923731947454344395]) 0) 14 true) treeG_J007_part048 treeG_J007_part051)

#time def treeG_J007_part053 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [19835897244079328294359275]) 0) 62 false) (.node 306 (sourceLit (List.headD (raw_ints% [5126003328779447233301775]) 0) 64 false) (.node 305 (sourceLit (List.headD (raw_ints% [511554688079717910517808738756540175]) 0) 27 true) (.node 304 (sourceLit (List.headD (raw_ints% [21282281141738323766136975]) 0) 62 false) .empty .empty) .empty) (.node 307 (sourceLit (List.headD (raw_ints% [720279194658204549286688922453433275]) 0) 26 true) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [2913724961409427659021489478366123755]) 0) 23 true) (.node 310 (sourceLit (List.headD (raw_ints% [19253159372564650365240375]) 0) 62 false) (.node 309 (sourceLit (List.headD (raw_ints% [2052988669352103861995861457562053705]) 0) 24 true) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [146392522362651927055275]) 0) 69 false) .empty .empty)))

#time def treeG_J007_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [136617910796304282581555]) 0) 69 false) (.node 316 (sourceLit (List.headD (raw_ints% [139560353053685703338129]) 0) 69 false) (.node 315 (sourceLit (List.headD (raw_ints% [21320179676794226001564875391067113435]) 0) 19 true) (.node 314 (sourceLit (List.headD (raw_ints% [571197191255431770801447]) 0) 67 false) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [50415230772060127970952545023948320915]) 0) 17 true) .empty .empty)) (.node 330 (sourceLit (List.headD (raw_ints% [7663717975124065219880037462321525]) 0) 38 false) (.node 319 (sourceLit (List.headD (raw_ints% [44559073102379286105986509205385624405]) 0) 16 true) .empty .empty) (.node 331 (sourceLit (List.headD (raw_ints% [93774915761468785412928233749875]) 0) 45 true) .empty .empty)))

#time def treeG_J007_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [16170235137530917288153804026762282675]) 0) 20 true) treeG_J007_part053 treeG_J007_part054)

#time def treeG_J007_part056 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [135308531547127812063919046175]) 0) 50 false) (.node 335 (sourceLit (List.headD (raw_ints% [56601230905833614576233306216425]) 0) 47 true) (.node 334 (sourceLit (List.headD (raw_ints% [475401194928775316834584701514446825]) 0) 35 false) (.node 333 (sourceLit (List.headD (raw_ints% [36847261981865726200376310068325]) 0) 48 false) .empty .empty) .empty) (.node 336 (sourceLit (List.headD (raw_ints% [1172661037529701395918430027528571025]) 0) 32 true) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [824316214056729734549185071038754525]) 0) 29 true) (.node 339 (sourceLit (List.headD (raw_ints% [62035807798625116538709464175]) 0) 51 false) (.node 338 (sourceLit (List.headD (raw_ints% [472431673211941625182585264620465525]) 0) 31 true) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [14470587520708692630818814075]) 0) 53 false) .empty .empty)))

#time def treeG_J007_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [48717833965553453803731225]) 0) 61 false) (.node 345 (sourceLit (List.headD (raw_ints% [101656209193991279924035275]) 0) 60 false) (.node 344 (sourceLit (List.headD (raw_ints% [9382575518506569885781438210845251025]) 0) 24 true) (.node 343 (sourceLit (List.headD (raw_ints% [1707906189931128861942221775]) 0) 56 false) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [12737644490538709409608112549894999625]) 0) 23 true) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [23464328644349926114923225]) 0) 62 false) (.node 348 (sourceLit (List.headD (raw_ints% [35984618354804432481091474820642696895]) 0) 21 true) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [51937282276507492788849123048208755345]) 0) 20 true) .empty .empty)))

#time def treeG_J007_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [924941933410671830777869411656994575]) 0) 28 true) treeG_J007_part056 treeG_J007_part057)

#time def treeG_J007_part059 : IntSourceTree :=
  (.node 332 (sourceLit (List.headD (raw_ints% [148610058294322698595986568299591825]) 0) 36 true) treeG_J007_part055 treeG_J007_part058)

#time def treeG_J007_part060 : IntSourceTree :=
  (.node 303 (sourceLit (List.headD (raw_ints% [46833496007877425692903574847169125]) 0) 31 true) treeG_J007_part052 treeG_J007_part059)

#time def treeG_J007_part061 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [82828545062618526172252819425]) 0) 50 false) treeG_J007_part045 treeG_J007_part060)

#time def treeG_J007_part062 : IntSourceTree :=
  (.node 167 (sourceLit (List.headD (raw_ints% [44779877806772243906861023308375]) 0) 40 false) treeG_J007_part030 treeG_J007_part061)

#time def treeG_J007_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [1240994348061074221255228293080840915445]) 0) 14 true) (.node 354 (sourceLit (List.headD (raw_ints% [437407988917928133205711529036918079705]) 0) 16 true) (.node 353 (sourceLit (List.headD (raw_ints% [2752110934896976078958289]) 0) 65 false) (.node 352 (sourceLit (List.headD (raw_ints% [302203404632587234642513628845025934045]) 0) 17 true) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [1338656937466005051219361]) 0) 66 false) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [79687907513392695489049]) 0) 70 false) (.node 358 (sourceLit (List.headD (raw_ints% [1686845014496621537327397649447707385215]) 0) 13 true) (.node 357 (sourceLit (List.headD (raw_ints% [326299522923511216046413]) 0) 68 false) .empty .empty) .empty) (.node 371 (sourceLit (List.headD (raw_ints% [13924127667522281131299644688274425]) 0) 39 false) .empty .empty)))

#time def treeG_J007_part064 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [1103932626730535752945629287342786325]) 0) 33 true) (.node 375 (sourceLit (List.headD (raw_ints% [514567768900330087964822860466989725]) 0) 36 false) (.node 374 (sourceLit (List.headD (raw_ints% [175337137575636049760348915688375]) 0) 47 false) (.node 373 (sourceLit (List.headD (raw_ints% [202766541495368093949641330534750325]) 0) 37 true) .empty .empty) .empty) (.node 376 (sourceLit (List.headD (raw_ints% [57037505059053107252705649947625]) 0) 48 true) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [38141812639691922509484151275]) 0) 52 false) (.node 379 (sourceLit (List.headD (raw_ints% [409459723840419547618762863221108025]) 0) 32 true) (.node 378 (sourceLit (List.headD (raw_ints% [84612005899725827266116869925]) 0) 51 false) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [678870998127947766163576084861698225]) 0) 30 true) .empty .empty)))

#time def treeG_J007_part065 : IntSourceTree :=
  (.node 372 (sourceLit (List.headD (raw_ints% [153778960220155845354569250586125]) 0) 46 true) treeG_J007_part063 treeG_J007_part064)

#time def treeG_J007_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [9856527711905891212461356860081266525]) 0) 24 true) (.node 385 (sourceLit (List.headD (raw_ints% [7336356766187698243710203255819090325]) 0) 25 true) (.node 384 (sourceLit (List.headD (raw_ints% [1026873193395502501425838575]) 0) 57 false) (.node 383 (sourceLit (List.headD (raw_ints% [737607949379162128006255112268318075]) 0) 29 true) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [60648182563755702057621075]) 0) 61 false) .empty .empty)) (.node 390 (sourceLit (List.headD (raw_ints% [27675497916135201864606075]) 0) 62 false) (.node 389 (sourceLit (List.headD (raw_ints% [27772663677396017033108028990394482075]) 0) 22 true) (.node 388 (sourceLit (List.headD (raw_ints% [14440968360737062754685975]) 0) 63 false) .empty .empty) .empty) (.node 391 (sourceLit (List.headD (raw_ints% [40282382430869782152763165134744260325]) 0) 21 true) .empty .empty)))

#time def treeG_J007_part067 : IntSourceTree :=
  (.node 397 (sourceLit (List.headD (raw_ints% [1039333424972833709371418112985047631785]) 0) 15 true) (.node 395 (sourceLit (List.headD (raw_ints% [352127270210751229199452027472649625965]) 0) 17 true) (.node 394 (sourceLit (List.headD (raw_ints% [1609716552386112537355395]) 0) 66 false) (.node 393 (sourceLit (List.headD (raw_ints% [237522464082463565489898412737976803345]) 0) 18 true) .empty .empty) .empty) (.node 396 (sourceLit (List.headD (raw_ints% [780415525251262237866845]) 0) 67 false) .empty .empty)) (.node 399 (sourceLit (List.headD (raw_ints% [1508608722087104392903451612626164887595]) 0) 14 true) (.node 398 (sourceLit (List.headD (raw_ints% [94840806063603466732429]) 0) 70 false) .empty .empty) (.node 412 (sourceLit (List.headD (raw_ints% [371396100974679196696780883311982625]) 0) 36 false) .empty .empty)))

#time def treeG_J007_part068 : IntSourceTree :=
  (.node 392 (sourceLit (List.headD (raw_ints% [13323342495224003774814675]) 0) 63 false) treeG_J007_part066 treeG_J007_part067)

#time def treeG_J007_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [2196398241607392353847352275]) 0) 56 false) treeG_J007_part065 treeG_J007_part068)

#time def treeG_J007_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [8359029340632344398382449034121825075]) 0) 31 true) (.node 416 (sourceLit (List.headD (raw_ints% [17638829642340264210792761562472242225]) 0) 32 false) (.node 415 (sourceLit (List.headD (raw_ints% [407275506057105714096931137593175]) 0) 47 false) (.node 414 (sourceLit (List.headD (raw_ints% [2097533526891720068431715345792449425]) 0) 35 true) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [57308122122147362876833488039975]) 0) 49 true) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [1479451569936451867416583575]) 0) 57 false) (.node 420 (sourceLit (List.headD (raw_ints% [5727039367389983027351020740498973875]) 0) 29 true) (.node 419 (sourceLit (List.headD (raw_ints% [107188204000826537993524275675]) 0) 51 false) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [4506026051612910298530739267236591225]) 0) 28 true) .empty .empty)))

#time def treeG_J007_part071 : IntSourceTree :=
  (.node 428 (sourceLit (List.headD (raw_ints% [121719825035689826918290234940657567505]) 0) 21 true) (.node 426 (sourceLit (List.headD (raw_ints% [45953209638962876540073513496657722975]) 0) 23 true) (.node 425 (sourceLit (List.headD (raw_ints% [620248356619537381729697475]) 0) 58 false) (.node 424 (sourceLit (List.headD (raw_ints% [37824333241759806306618888974327105775]) 0) 24 true) .empty .empty) .empty) (.node 427 (sourceLit (List.headD (raw_ints% [72578531161957950311510925]) 0) 61 false) .empty .empty)) (.node 430 (sourceLit (List.headD (raw_ints% [170244027142660643476015108874947101255]) 0) 20 true) (.node 429 (sourceLit (List.headD (raw_ints% [34299544798598324903820675]) 0) 62 false) .empty .empty) (.node 431 (sourceLit (List.headD (raw_ints% [32658531905836676622859875]) 0) 62 false) .empty .empty)))

#time def treeG_J007_part072 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [2684890293283655845752482775]) 0) 56 false) treeG_J007_part070 treeG_J007_part071)

#time def treeG_J007_part073 : IntSourceTree :=
  (.node 437 (sourceLit (List.headD (raw_ints% [28382250145484438863777]) 0) 72 false) (.node 435 (sourceLit (List.headD (raw_ints% [1880776167306220023491429]) 0) 66 false) (.node 434 (sourceLit (List.headD (raw_ints% [1462771723741780390713475772866896347055]) 0) 16 true) (.node 433 (sourceLit (List.headD (raw_ints% [7819120625430051616898097]) 0) 64 false) .empty .empty) .empty) (.node 436 (sourceLit (List.headD (raw_ints% [4393041975310945445936004146481553099995]) 0) 14 true) .empty .empty)) (.node 454 (sourceLit (List.headD (raw_ints% [630284105943410645270992657133925]) 0) 47 true) (.node 439 (sourceLit (List.headD (raw_ints% [109993704613814237975809]) 0) 70 false) (.node 438 (sourceLit (List.headD (raw_ints% [6627822385286048137643947254432673669065]) 0) 13 true) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [1306050647896025078198269103129719575]) 0) 37 true) .empty .empty)))

#time def treeG_J007_part074 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [2524084184631017630593722327818637825]) 0) 31 true) (.node 459 (sourceLit (List.headD (raw_ints% [3974784808395962425381843085450358525]) 0) 33 true) (.node 458 (sourceLit (List.headD (raw_ints% [57477346133946814531365721779825]) 0) 50 true) (.node 457 (sourceLit (List.headD (raw_ints% [9371381134535399981869195424907514275]) 0) 34 false) .empty .empty) .empty) (.node 460 (sourceLit (List.headD (raw_ints% [4315399460070913467752507775]) 0) 56 false) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [1884209051116874085262242077484136575]) 0) 30 true) (.node 462 (sourceLit (List.headD (raw_ints% [3721408038138415115818982025]) 0) 56 false) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [207252137486019168040830525]) 0) 60 false) .empty .empty)))

#time def treeG_J007_part075 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [7254890798689981583588074805325]) 0) 54 false) treeG_J007_part073 treeG_J007_part074)

#time def treeG_J007_part076 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [986832833155245794245907655466790396355]) 0) 17 true) treeG_J007_part072 treeG_J007_part075)

#time def treeG_J007_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [227473484183887297755321870722775]) 0) 47 true) treeG_J007_part069 treeG_J007_part076)

#time def treeG_J007_part078 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [40923591681061447943035275]) 0) 62 false) (.node 468 (sourceLit (List.headD (raw_ints% [43696594440483824802138975]) 0) 62 false) (.node 467 (sourceLit (List.headD (raw_ints% [18048340963528492663806078318288228225]) 0) 25 true) (.node 466 (sourceLit (List.headD (raw_ints% [377655626364514573499213175]) 0) 59 false) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [46973580679146904942591102975131542715]) 0) 23 true) .empty .empty)) (.node 473 (sourceLit (List.headD (raw_ints% [374655184536391114378004621364406796505]) 0) 19 true) (.node 472 (sourceLit (List.headD (raw_ints% [1208449338163292053002825]) 0) 67 false) (.node 471 (sourceLit (List.headD (raw_ints% [64980822355895430661625971870101420465]) 0) 22 true) .empty .empty) .empty) (.node 474 (sourceLit (List.headD (raw_ints% [4599687520657826542187307]) 0) 65 false) .empty .empty)))

#time def treeG_J007_part079 : IntSourceTree :=
  (.node 495 (sourceLit (List.headD (raw_ints% [1667843717943927004638916451861025]) 0) 47 true) (.node 478 (sourceLit (List.headD (raw_ints% [132217195100272044177787]) 0) 70 false) (.node 477 (sourceLit (List.headD (raw_ints% [1676854275169055868282293016748252734105]) 0) 16 true) (.node 476 (sourceLit (List.headD (raw_ints% [137545080256869723203073]) 0) 70 false) .empty .empty) .empty) (.node 479 (sourceLit (List.headD (raw_ints% [2559606831599471872370247820903254390735]) 0) 15 true) .empty .empty)) (.node 497 (sourceLit (List.headD (raw_ints% [521621133238306184226470275580775]) 0) 49 false) (.node 496 (sourceLit (List.headD (raw_ints% [101226071107685869215481984162774295025]) 0) 32 true) .empty .empty) (.node 498 (sourceLit (List.headD (raw_ints% [158301127493198744108289575832642053475]) 0) 31 false) .empty .empty)))

#time def treeG_J007_part080 : IntSourceTree :=
  (.node 475 (sourceLit (List.headD (raw_ints% [555322226765514580757011872697123360545]) 0) 18 true) treeG_J007_part078 treeG_J007_part079)

#time def treeG_J007_part081 : IntSourceTree :=
  (.node 504 (sourceLit (List.headD (raw_ints% [203354425301200076606948096943642375825]) 0) 24 true) (.node 502 (sourceLit (List.headD (raw_ints% [35879320902483371790968817977861613975]) 0) 28 true) (.node 501 (sourceLit (List.headD (raw_ints% [354493486266807700041990525]) 0) 60 false) (.node 500 (sourceLit (List.headD (raw_ints% [121466074501280814584867957993912498925]) 0) 29 true) .empty .empty) .empty) (.node 503 (sourceLit (List.headD (raw_ints% [4757925782993174385885481275]) 0) 56 false) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [232498564040598672876191325]) 0) 60 false) (.node 506 (sourceLit (List.headD (raw_ints% [197950602165613987963195972251406400625]) 0) 23 true) (.node 505 (sourceLit (List.headD (raw_ints% [1037768743268615962596946725]) 0) 58 false) .empty .empty) .empty) (.node 508 (sourceLit (List.headD (raw_ints% [455827085797221938323504271244565735695]) 0) 21 true) .empty .empty)))

#time def treeG_J007_part082 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [4531711228840477439334598168963612397025]) 0) 16 true) (.node 512 (sourceLit (List.headD (raw_ints% [3171939797622061768098154544219700513405]) 0) 17 true) (.node 511 (sourceLit (List.headD (raw_ints% [49188651456286219263210675]) 0) 62 false) (.node 510 (sourceLit (List.headD (raw_ints% [581333263723689835605442538727157582185]) 0) 20 true) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [11516068785182621231147103]) 0) 64 false) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [13377269281185521138288375779826394437445]) 0) 14 true) (.node 515 (sourceLit (List.headD (raw_ints% [1359455676675803259347939]) 0) 67 false) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [80780579965900845475519]) 0) 71 false) .empty .empty)))

#time def treeG_J007_part083 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [53093644082369324700457275]) 0) 62 false) treeG_J007_part081 treeG_J007_part082)

#time def treeG_J007_part084 : IntSourceTree :=
  (.node 499 (sourceLit (List.headD (raw_ints% [14396133584486910267339811513875]) 0) 53 true) treeG_J007_part080 treeG_J007_part083)

#time def treeG_J007_part085 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [14413395182327193921210821544975]) 0) 54 true) (.node 538 (sourceLit (List.headD (raw_ints% [72387309921531624844729499670075]) 0) 53 false) (.node 537 (sourceLit (List.headD (raw_ints% [119968833376756669179220375012589323575]) 0) 33 true) (.node 519 (sourceLit (List.headD (raw_ints% [154440685586729850379765]) 0) 70 false) .empty .empty) .empty) (.node 539 (sourceLit (List.headD (raw_ints% [166250697109990668959053262003542770525]) 0) 32 false) .empty .empty)) (.node 543 (sourceLit (List.headD (raw_ints% [32110902800249623620444333822893340825]) 0) 29 true) (.node 542 (sourceLit (List.headD (raw_ints% [7622383522399431285524714775]) 0) 56 false) (.node 541 (sourceLit (List.headD (raw_ints% [116417906132018779323680513338275223275]) 0) 30 true) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [3099908683105021041558837075]) 0) 57 false) .empty .empty)))

#time def treeG_J007_part086 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [65263696483677201457879275]) 0) 62 false) (.node 548 (sourceLit (List.headD (raw_ints% [145105375159631023271913375]) 0) 61 false) (.node 547 (sourceLit (List.headD (raw_ints% [161853920238557002635583815614829944175]) 0) 24 true) (.node 546 (sourceLit (List.headD (raw_ints% [330056558452050694548866775]) 0) 60 false) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [361879924438928128438322065294302650265]) 0) 22 true) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [29853462045673546415165475]) 0) 63 false) (.node 551 (sourceLit (List.headD (raw_ints% [451371619011898974282190594986954741255]) 0) 21 true) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [2422629428549279539342145301490886920395]) 0) 18 true) .empty .empty)))

#time def treeG_J007_part087 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [172866448825627968544039411225134360375]) 0) 25 true) treeG_J007_part085 treeG_J007_part086)

#time def treeG_J007_part088 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [15082632354219902010132245371732861295145]) 0) 14 true) (.node 557 (sourceLit (List.headD (raw_ints% [10023560730847409401723789746329888969235]) 0) 15 true) (.node 556 (sourceLit (List.headD (raw_ints% [809275355648324366535647]) 0) 68 false) (.node 555 (sourceLit (List.headD (raw_ints% [3421066775309448277820574423569365675935]) 0) 17 true) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [190905124763331337724289]) 0) 70 false) .empty .empty)) (.node 582 (sourceLit (List.headD (raw_ints% [895463928153666862798475288728340172225]) 0) 28 true) (.node 581 (sourceLit (List.headD (raw_ints% [14424738973887731767612165241775]) 0) 55 true) (.node 580 (sourceLit (List.headD (raw_ints% [2781477228261131517929720150050596827325]) 0) 29 false) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [10486841261805688185163948275]) 0) 56 false) .empty .empty)))

#time def treeG_J007_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [23002932769315424642864025]) 0) 64 false) (.node 587 (sourceLit (List.headD (raw_ints% [427614552863502716221542225]) 0) 60 false) (.node 586 (sourceLit (List.headD (raw_ints% [1184980988439409760389119317549668482375]) 0) 23 true) (.node 585 (sourceLit (List.headD (raw_ints% [1031069969918202539480945175]) 0) 59 false) .empty .empty) .empty) (.node 588 (sourceLit (List.headD (raw_ints% [2133835638019690103845836778592713371105]) 0) 21 true) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [81338741511068183652547875]) 0) 62 false) (.node 590 (sourceLit (List.headD (raw_ints% [2313706131787735191901133983627263619935]) 0) 20 true) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [11271952010758705408931944495362851206755]) 0) 17 true) .empty .empty)))

#time def treeG_J007_part090 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [1851743353914775835101489267721531436975]) 0) 24 true) treeG_J007_part088 treeG_J007_part089)

#time def treeG_J007_part091 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [1729095316131198672239949]) 0) 67 false) treeG_J007_part087 treeG_J007_part090)

#time def treeG_J007_part092 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [20201846017418845754872741013539370076615]) 0) 13 true) treeG_J007_part084 treeG_J007_part091)

#time def treeG_J007_part093 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [15243988237786054031454342859254007725]) 0) 26 true) treeG_J007_part077 treeG_J007_part092)

#time def treeG_J007_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [59986639829360429458917576957099741677265]) 0) 13 true) (.node 596 (sourceLit (List.headD (raw_ints% [41359799123765651306840814997283456377515]) 0) 14 true) (.node 595 (sourceLit (List.headD (raw_ints% [2098734955586594085131959]) 0) 67 false) (.node 594 (sourceLit (List.headD (raw_ints% [14849324199553758875402564242963482966135]) 0) 16 true) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [486153035784720984633571]) 0) 69 false) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [7216180678705065599448844978275]) 0) 57 true) (.node 621 (sourceLit (List.headD (raw_ints% [362236891799143787156675082923609006325]) 0) 33 false) (.node 599 (sourceLit (List.headD (raw_ints% [227369563939932825068813]) 0) 70 false) .empty .empty) .empty) (.node 623 (sourceLit (List.headD (raw_ints% [107919128169177154897253869363180853925]) 0) 32 true) .empty .empty)))

#time def treeG_J007_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [221494464197595246925939339162301340105]) 0) 25 true) (.node 627 (sourceLit (List.headD (raw_ints% [127890883525106594719191937741854817275]) 0) 27 true) (.node 626 (sourceLit (List.headD (raw_ints% [10953334554158622577063725]) 0) 66 false) (.node 625 (sourceLit (List.headD (raw_ints% [209859613136143483319681232062049634575]) 0) 28 true) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [141254588851935846474814425]) 0) 62 false) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [232791814096979527202367923580038609835]) 0) 24 true) (.node 630 (sourceLit (List.headD (raw_ints% [118759765670846195685032925]) 0) 62 false) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [201114372911697801708525]) 0) 71 false) .empty .empty)))

#time def treeG_J007_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [230841643084395848237659725]) 0) 62 false) treeG_J007_part094 treeG_J007_part095)

#time def treeG_J007_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [147623955510694823454641]) 0) 71 false) (.node 636 (sourceLit (List.headD (raw_ints% [161182449992283714824539]) 0) 71 false) (.node 635 (sourceLit (List.headD (raw_ints% [1428532178030538824697748727424264661275]) 0) 20 true) (.node 634 (sourceLit (List.headD (raw_ints% [713813249747883155941161]) 0) 69 false) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [3917029799114780238139628156369195926035]) 0) 18 true) .empty .empty)) (.node 664 (sourceLit (List.headD (raw_ints% [53402850268703927472292491846227065772625]) 0) 24 true) (.node 663 (sourceLit (List.headD (raw_ints% [28875209556082068085980543861375]) 0) 56 true) (.node 639 (sourceLit (List.headD (raw_ints% [5613000934392565931098166448170860047765]) 0) 17 true) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [2662396319432131032321610425]) 0) 59 false) .empty .empty)))

#time def treeG_J007_part098 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [156180789830624207717517975]) 0) 62 false) (.node 669 (sourceLit (List.headD (raw_ints% [95248723313304997189086375]) 0) 63 false) (.node 668 (sourceLit (List.headD (raw_ints% [14236197453193954020210731252364703240095]) 0) 21 true) (.node 667 (sourceLit (List.headD (raw_ints% [974412270068800973642614575]) 0) 60 false) .empty .empty) .empty) (.node 670 (sourceLit (List.headD (raw_ints% [11861939576858360611358983722760022146785]) 0) 20 true) .empty .empty)) (.node 673 (sourceLit (List.headD (raw_ints% [8286971551225928013341007]) 0) 66 false) (.node 672 (sourceLit (List.headD (raw_ints% [48322752398068053554874243941127032911005]) 0) 17 true) .empty .empty) (.node 674 (sourceLit (List.headD (raw_ints% [55945256458121648081315829308012231324745]) 0) 16 true) .empty .empty)))

#time def treeG_J007_part099 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [12246034252273773172070479534421508130425]) 0) 23 true) treeG_J007_part097 treeG_J007_part098)

#time def treeG_J007_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [1106165322776178233698724899233995535795]) 0) 21 true) treeG_J007_part096 treeG_J007_part099)

#time def treeG_J007_part101 : IntSourceTree :=
  (.node 704 (sourceLit (List.headD (raw_ints% [28882596488660768753124148972575]) 0) 57 true) (.node 678 (sourceLit (List.headD (raw_ints% [190703267313985505782018625050528797588975]) 0) 13 true) (.node 677 (sourceLit (List.headD (raw_ints% [803306564153548733962741]) 0) 69 false) (.node 676 (sourceLit (List.headD (raw_ints% [141492319664143318254471022113022420265685]) 0) 14 true) .empty .empty) .empty) (.node 679 (sourceLit (List.headD (raw_ints% [363126258102846468749751]) 0) 70 false) .empty .empty)) (.node 707 (sourceLit (List.headD (raw_ints% [11222907184072920414316944032486669592225]) 0) 24 true) (.node 706 (sourceLit (List.headD (raw_ints% [1961382907965979187389532025]) 0) 60 false) (.node 705 (sourceLit (List.headD (raw_ints% [51723973363614779605735041989730668696025]) 0) 25 true) .empty .empty) .empty) (.node 708 (sourceLit (List.headD (raw_ints% [691903092364929280692985725]) 0) 61 false) .empty .empty)))

#time def treeG_J007_part102 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [5431718552234395389576363]) 0) 67 false) (.node 712 (sourceLit (List.headD (raw_ints% [104695510365229570480135575]) 0) 63 false) (.node 711 (sourceLit (List.headD (raw_ints% [9999605064082524393740040334119713268105]) 0) 21 true) (.node 710 (sourceLit (List.headD (raw_ints% [262235127582373793071312575]) 0) 62 false) .empty .empty) .empty) (.node 713 (sourceLit (List.headD (raw_ints% [39473429815858627685284444747255068624645]) 0) 18 true) .empty .empty)) (.node 716 (sourceLit (List.headD (raw_ints% [2322311442458201443801017]) 0) 68 false) (.node 715 (sourceLit (List.headD (raw_ints% [44516999033877337483733839488618114034545]) 0) 17 true) .empty .empty) (.node 717 (sourceLit (List.headD (raw_ints% [110156081271225076349353996862068852857405]) 0) 15 true) .empty .empty)))

#time def treeG_J007_part103 : IntSourceTree :=
  (.node 709 (sourceLit (List.headD (raw_ints% [12464241739613192044803216539066292519255]) 0) 22 true) treeG_J007_part101 treeG_J007_part102)

#time def treeG_J007_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [165330317491972772608860373267422010235505]) 0) 21 true) (.node 746 (sourceLit (List.headD (raw_ints% [401545752656644463673809856383423841437775]) 0) 23 true) (.node 745 (sourceLit (List.headD (raw_ints% [28887921281299633015188792193425]) 0) 58 true) (.node 719 (sourceLit (List.headD (raw_ints% [145799259838844978333233293465161917206855]) 0) 14 true) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [2948353545863157401136449475]) 0) 60 false) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [368289465334123378425107175]) 0) 62 false) (.node 750 (sourceLit (List.headD (raw_ints% [87851994340047175747066748589770318007255]) 0) 20 true) (.node 749 (sourceLit (List.headD (raw_ints% [501405645738319286314812975]) 0) 62 false) .empty .empty) .empty) (.node 752 (sourceLit (List.headD (raw_ints% [271664609652572727044807046750703791668355]) 0) 17 true) .empty .empty)))

#time def treeG_J007_part105 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [690545382855815105012813349846022025270265]) 0) 13 true) (.node 756 (sourceLit (List.headD (raw_ints% [570779664877894081485270409704867404287035]) 0) 14 true) (.node 755 (sourceLit (List.headD (raw_ints% [7251666062072319616755397]) 0) 67 false) (.node 754 (sourceLit (List.headD (raw_ints% [259842182068747373400959728670028317672415]) 0) 16 true) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [379751219576163177459569]) 0) 71 false) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [28891844047115564973563571257475]) 0) 59 true) (.node 759 (sourceLit (List.headD (raw_ints% [652991048161471705357167]) 0) 70 false) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [195161422736285771629746456175468585922775]) 0) 25 true) .empty .empty)))

#time def treeG_J007_part106 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [71547624160325858426771547]) 0) 64 false) treeG_J007_part104 treeG_J007_part105)

#time def treeG_J007_part107 : IntSourceTree :=
  (.node 718 (sourceLit (List.headD (raw_ints% [508058653132159087053459]) 0) 70 false) treeG_J007_part103 treeG_J007_part106)

#time def treeG_J007_part108 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [3611771042396471162397329]) 0) 67 false) treeG_J007_part100 treeG_J007_part107)

#time def treeG_J007_part109 : IntSourceTree :=
  (.node 793 (sourceLit (List.headD (raw_ints% [116095589918357049679761301001724361521855]) 0) 19 true) (.node 791 (sourceLit (List.headD (raw_ints% [38926194637982325676663354127825302369575]) 0) 22 true) (.node 790 (sourceLit (List.headD (raw_ints% [740576163894264779558313375]) 0) 62 false) (.node 789 (sourceLit (List.headD (raw_ints% [76433037876179790282028578364177858858125]) 0) 23 true) .empty .empty) .empty) (.node 792 (sourceLit (List.headD (raw_ints% [16474622185555862996560725]) 0) 67 false) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [1232338654903529543238595]) 0) 70 false) (.node 795 (sourceLit (List.headD (raw_ints% [107662591517435017958612944590705101818935]) 0) 18 true) (.node 794 (sourceLit (List.headD (raw_ints% [49820749951388276868466095]) 0) 65 false) .empty .empty) .empty) (.node 797 (sourceLit (List.headD (raw_ints% [230311791803334502567958206421399275714815]) 0) 16 true) .empty .empty)))

#time def treeG_J007_part110 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [1135076611678829468765390505237075423722745]) 0) 20 true) (.node 828 (sourceLit (List.headD (raw_ints% [6079835210069171919543026224347572739293295]) 0) 21 true) (.node 827 (sourceLit (List.headD (raw_ints% [14447396200330714065482353853475]) 0) 61 true) (.node 799 (sourceLit (List.headD (raw_ints% [272373061508485063339790028190430054031705]) 0) 15 true) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [1755044807759908834128650775]) 0) 62 false) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [2219611847178296116261647617430115559984445]) 0) 17 true) (.node 831 (sourceLit (List.headD (raw_ints% [1112862862454406180691519575]) 0) 62 false) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [192046330808567949518200053]) 0) 64 false) .empty .empty)))

#time def treeG_J007_part111 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [1010946225172493622784817]) 0) 70 false) treeG_J007_part109 treeG_J007_part110)

#time def treeG_J007_part112 : IntSourceTree :=
  (.node 839 (sourceLit (List.headD (raw_ints% [1368901402183515540212467]) 0) 70 false) (.node 837 (sourceLit (List.headD (raw_ints% [426293717663683182889513]) 0) 72 false) (.node 836 (sourceLit (List.headD (raw_ints% [2874423263680026493190343817197695853918885]) 0) 14 true) (.node 835 (sourceLit (List.headD (raw_ints% [35317417827243637634955301]) 0) 66 false) .empty .empty) .empty) (.node 838 (sourceLit (List.headD (raw_ints% [2994443285997536936074517952896366386166775]) 0) 13 true) .empty .empty)) (.node 870 (sourceLit (List.headD (raw_ints% [2769513451625552888698988175]) 0) 62 false) (.node 869 (sourceLit (List.headD (raw_ints% [5926969134316812338978969067619217021577045]) 0) 22 true) (.node 868 (sourceLit (List.headD (raw_ints% [7224262212778731589771287792675]) 0) 63 true) .empty .empty) .empty) (.node 871 (sourceLit (List.headD (raw_ints% [1057224222402864817412063796981424818983595]) 0) 21 true) .empty .empty)))

#time def treeG_J007_part113 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [2413799680073357488054427404354897302489255]) 0) 15 true) (.node 875 (sourceLit (List.headD (raw_ints% [1382362073590095385557995198176151263039395]) 0) 17 true) (.node 874 (sourceLit (List.headD (raw_ints% [71112790428589836324866979]) 0) 66 false) (.node 873 (sourceLit (List.headD (raw_ints% [1987420667341582016902125015426666836940735]) 0) 18 true) .empty .empty) .empty) (.node 876 (sourceLit (List.headD (raw_ints% [25458708588015401289046541]) 0) 67 false) .empty .empty)) (.node 879 (sourceLit (List.headD (raw_ints% [2449697162980566809394937896515506278103365]) 0) 14 true) (.node 878 (sourceLit (List.headD (raw_ints% [2399403516136971840331287]) 0) 70 false) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [28898803895922686267919279821475]) 0) 62 true) .empty .empty)))

#time def treeG_J007_part114 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [849268907485512372746547975]) 0) 63 false) treeG_J007_part112 treeG_J007_part113)

#time def treeG_J007_part115 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [1597687256624965421475221087357561466677265]) 0) 16 true) treeG_J007_part111 treeG_J007_part114)

#time def treeG_J007_part116 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [106908163029936035014778657]) 0) 66 false) (.node 913 (sourceLit (List.headD (raw_ints% [328611288338472211614173961]) 0) 65 false) (.node 912 (sourceLit (List.headD (raw_ints% [31611563269713378040924393885975478647490595]) 0) 17 true) (.node 911 (sourceLit (List.headD (raw_ints% [4426164040796699596706456775]) 0) 62 false) .empty .empty) .empty) (.node 914 (sourceLit (List.headD (raw_ints% [14301678082107690713741779036055773228848615]) 0) 16 true) .empty .empty)) (.node 918 (sourceLit (List.headD (raw_ints% [16315954154589322968360901281942812033747265]) 0) 13 true) (.node 917 (sourceLit (List.headD (raw_ints% [18638009105396470362814333]) 0) 68 false) (.node 916 (sourceLit (List.headD (raw_ints% [19243369913761499675737579353620724354711435]) 0) 14 true) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [3429905630090428140450107]) 0) 70 false) .empty .empty)))

#time def treeG_J007_part117 : IntSourceTree :=
  (.node 955 (sourceLit (List.headD (raw_ints% [3229829002129398832045945959469905491452305]) 0) 19 true) (.node 953 (sourceLit (List.headD (raw_ints% [7406035650592949006005567217637202952637465]) 0) 20 true) (.node 952 (sourceLit (List.headD (raw_ints% [55888986457987300374373575]) 0) 69 false) (.node 951 (sourceLit (List.headD (raw_ints% [11305863060113201106413574559683808982477505]) 0) 23 true) .empty .empty) .empty) (.node 954 (sourceLit (List.headD (raw_ints% [128749248954941187644653491]) 0) 67 false) .empty .empty)) (.node 957 (sourceLit (List.headD (raw_ints% [4207392558422035546920787987316456763055545]) 0) 17 true) (.node 956 (sourceLit (List.headD (raw_ints% [20362363610480158431433029]) 0) 69 false) .empty .empty) (.node 958 (sourceLit (List.headD (raw_ints% [13839202073122526682151759]) 0) 69 false) .empty .empty)))

#time def treeG_J007_part118 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [57800377305296998088727258631125]) 0) 62 true) treeG_J007_part116 treeG_J007_part117)

#time def treeG_J007_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [62811445336524163362917783]) 0) 68 false) (.node 995 (sourceLit (List.headD (raw_ints% [408088832789828715563835307]) 0) 66 false) (.node 994 (sourceLit (List.headD (raw_ints% [222691462736866677478436371928334721255550265]) 0) 16 true) (.node 993 (sourceLit (List.headD (raw_ints% [1459836278317121400365780439]) 0) 65 false) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [187465686222520025575202962052453227098236085]) 0) 14 true) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [1202337780407239025076473457]) 0) 66 false) (.node 999 (sourceLit (List.headD (raw_ints% [2602324110758024635425413]) 0) 72 false) (.node 998 (sourceLit (List.headD (raw_ints% [118320607714915814533104314312183804384030175]) 0) 13 true) .empty .empty) .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [209772146728349082150252588090455099289741045]) 0) 17 true) .empty .empty)))

#time def treeG_J007_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [3168888661431065288828838447394828361537620635]) 0) 14 true) (.node 1039 (sourceLit (List.headD (raw_ints% [104454350723307058374138350926756498628386275]) 0) 14 true) (.node 1038 (sourceLit (List.headD (raw_ints% [6121530407925204585095753]) 0) 72 false) (.node 1037 (sourceLit (List.headD (raw_ints% [170636115988831883387519810103187400046013905]) 0) 15 true) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [1996586728024649334589111607]) 0) 66 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [1246768320195739252567054166513315395984081065]) 0) 13 true) (.node 1077 (sourceLit (List.headD (raw_ints% [1030577863325718431543693]) 0) 76 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [9640736705092384534766093]) 0) 72 false) .empty .empty)))

#time def treeG_J007_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [326639378347908081838103191]) 0) 67 false) treeG_J007_part119 treeG_J007_part120)

#time def treeG_J007_part122 : IntSourceTree :=
  (.node 959 (sourceLit (List.headD (raw_ints% [3466564247902189039741490846356826438910975]) 0) 16 true) treeG_J007_part118 treeG_J007_part121)

#time def treeG_J007_part123 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [46280676462855669243066362035716660748893615]) 0) 20 true) treeG_J007_part115 treeG_J007_part122)

#time def treeG_J007_part124 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [1128225226749114060221731875]) 0) 62 false) treeG_J007_part108 treeG_J007_part123)

#time def treeG_J007_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [4584348315122731296004593]) 0) 66 false) treeG_J007_part093 treeG_J007_part124)

#time def treeG_J007_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [22692463926433727106352275]) 0) 62 false) treeG_J007_part062 treeG_J007_part125)

#time def treeG_J007 : IntSourceTree := treeG_J007_part126

#time def treeG_J008_part000 : IntSourceTree :=
  (.node 5 (sourceLit (List.headD (raw_ints% [2826636805078646625350031371625]) 0) 42 false) (.node 3 (sourceLit (List.headD (raw_ints% [12169415297654383892296450852575]) 0) 40 false) (.node 2 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 39 false) (.node 1 (sourceLit (List.headD (raw_ints% [27556520913270475296457523883075]) 0) 39 false) .empty .empty) .empty) (.node 4 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)) (.node 8 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 true) (.node 7 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 43 false) (.node 6 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 42 true) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [65335690723103574854519296561275]) 0) 39 true) .empty .empty)))

#time def treeG_J008_part001 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [131147733927682748123981381766375]) 0) 35 true) (.node 13 (sourceLit (List.headD (raw_ints% [104256334917379917356023857027825]) 0) 36 true) (.node 12 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 51 false) (.node 11 (sourceLit (List.headD (raw_ints% [46293084878363218641634874689275]) 0) 38 true) .empty .empty) .empty) (.node 14 (sourceLit (List.headD (raw_ints% [17547273013983501317962407975]) 0) 49 false) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [523187367574069917840510675]) 0) 54 false) (.node 17 (sourceLit (List.headD (raw_ints% [679402321593256731039276077996625]) 0) 32 true) (.node 16 (sourceLit (List.headD (raw_ints% [267519125566095164079607575]) 0) 55 false) .empty .empty) .empty) (.node 19 (sourceLit (List.headD (raw_ints% [863572738452957636505285410051525]) 0) 31 true) .empty .empty)))

#time def treeG_J008_part002 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 46 false) treeG_J008_part000 treeG_J008_part001)

#time def treeG_J008_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [3994390174529490510262040310668625]) 0) 24 true) (.node 23 (sourceLit (List.headD (raw_ints% [1920319576321532908638258614332575]) 0) 28 true) (.node 22 (sourceLit (List.headD (raw_ints% [62853221735890069666375125]) 0) 57 false) (.node 21 (sourceLit (List.headD (raw_ints% [2031639351964655083225097811212925]) 0) 29 true) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [1929496004118470982604725]) 0) 62 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [116746432651650242534625]) 0) 66 false) (.node 27 (sourceLit (List.headD (raw_ints% [34798129370745207693130573365443175]) 0) 23 false) (.node 26 (sourceLit (List.headD (raw_ints% [3795097105426786895447775]) 0) 61 false) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [279022265385074950800242489675043105]) 0) 21 false) .empty .empty)))

#time def treeG_J008_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [18443476681986606402732161723485572375]) 0) 16 false) (.node 33 (sourceLit (List.headD (raw_ints% [7888213325169007044081344411417801955]) 0) 17 false) (.node 32 (sourceLit (List.headD (raw_ints% [3544129027153840160475]) 0) 71 false) (.node 31 (sourceLit (List.headD (raw_ints% [790365545248297227318186866170728255]) 0) 20 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [6993731494716506523027]) 0) 70 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [82951657953331392390444237929978973675]) 0) 14 false) (.node 36 (sourceLit (List.headD (raw_ints% [53943029583217463117]) 0) 77 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [852576952066895984929]) 0) 73 false) .empty .empty)))

#time def treeG_J008_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [460093620349183422628575]) 0) 64 false) treeG_J008_part003 treeG_J008_part004)

#time def treeG_J008_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [8008107447894527797916625]) 0) 60 false) treeG_J008_part002 treeG_J008_part005)

#time def treeG_J008_part007 : IntSourceTree :=
  (.node 46 (sourceLit (List.headD (raw_ints% [2826636805078646625350031371625]) 0) 43 false) (.node 44 (sourceLit (List.headD (raw_ints% [12169415297654383892296450852575]) 0) 41 false) (.node 43 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 40 false) (.node 42 (sourceLit (List.headD (raw_ints% [27556520913270475296457523883075]) 0) 40 false) .empty .empty) .empty) (.node 45 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)) (.node 49 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 48 true) (.node 48 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 44 false) (.node 47 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 43 true) .empty .empty) .empty) (.node 50 (sourceLit (List.headD (raw_ints% [65335690723103574854519296561275]) 0) 40 true) .empty .empty)))

#time def treeG_J008_part008 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [131147733927682748123981381766375]) 0) 36 true) (.node 54 (sourceLit (List.headD (raw_ints% [104256334917379917356023857027825]) 0) 37 true) (.node 53 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 52 false) (.node 52 (sourceLit (List.headD (raw_ints% [46293084878363218641634874689275]) 0) 39 true) .empty .empty) .empty) (.node 55 (sourceLit (List.headD (raw_ints% [17547273013983501317962407975]) 0) 50 false) .empty .empty)) (.node 58 (sourceLit (List.headD (raw_ints% [679402321593256731039276077996625]) 0) 33 true) (.node 57 (sourceLit (List.headD (raw_ints% [267519125566095164079607575]) 0) 56 false) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [523187367574069917840510675]) 0) 55 false) .empty .empty)))

#time def treeG_J008_part009 : IntSourceTree :=
  (.node 51 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 false) treeG_J008_part007 treeG_J008_part008)

#time def treeG_J008_part010 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [1929496004118470982604725]) 0) 63 false) (.node 63 (sourceLit (List.headD (raw_ints% [62853221735890069666375125]) 0) 58 false) (.node 62 (sourceLit (List.headD (raw_ints% [2031639351964655083225097811212925]) 0) 30 true) (.node 61 (sourceLit (List.headD (raw_ints% [8008107447894527797916625]) 0) 61 false) .empty .empty) .empty) (.node 64 (sourceLit (List.headD (raw_ints% [1920319576321532908638258614332575]) 0) 29 true) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [34798129370745207693130573365443175]) 0) 24 false) (.node 67 (sourceLit (List.headD (raw_ints% [3795097105426786895447775]) 0) 62 false) (.node 66 (sourceLit (List.headD (raw_ints% [3994390174529490510262040310668625]) 0) 25 true) .empty .empty) .empty) (.node 69 (sourceLit (List.headD (raw_ints% [116746432651650242534625]) 0) 67 false) .empty .empty)))

#time def treeG_J008_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [6993731494716506523027]) 0) 71 false) (.node 73 (sourceLit (List.headD (raw_ints% [3544129027153840160475]) 0) 72 false) (.node 72 (sourceLit (List.headD (raw_ints% [790365545248297227318186866170728255]) 0) 21 false) (.node 71 (sourceLit (List.headD (raw_ints% [460093620349183422628575]) 0) 65 false) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [7888213325169007044081344411417801955]) 0) 18 false) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [53943029583217463117]) 0) 78 false) (.node 76 (sourceLit (List.headD (raw_ints% [18443476681986606402732161723485572375]) 0) 17 false) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [82951657953331392390444237929978973675]) 0) 15 false) .empty .empty)))

#time def treeG_J008_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [279022265385074950800242489675043105]) 0) 22 false) treeG_J008_part010 treeG_J008_part011)

#time def treeG_J008_part013 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [863572738452957636505285410051525]) 0) 32 true) treeG_J008_part009 treeG_J008_part012)

#time def treeG_J008_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [181827320470844507875120386218692502385]) 0) 13 false) treeG_J008_part006 treeG_J008_part013)

#time def treeG_J008_part015 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [4314340386698986954481626830375]) 0) 43 false) (.node 85 (sourceLit (List.headD (raw_ints% [4671389246287868633473209740475]) 0) 43 false) (.node 84 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 41 false) (.node 83 (sourceLit (List.headD (raw_ints% [42943626528886566700618596913575]) 0) 40 false) .empty .empty) .empty) (.node 86 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 42 false) .empty .empty)) (.node 90 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 46 true) (.node 89 (sourceLit (List.headD (raw_ints% [151027417024435177812499194985275]) 0) 39 false) (.node 88 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 44 false) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [476392440906465380194519497800925]) 0) 38 true) .empty .empty)))

#time def treeG_J008_part016 : IntSourceTree :=
  (.node 97 (sourceLit (List.headD (raw_ints% [3517325164092591208928128138527375]) 0) 32 true) (.node 95 (sourceLit (List.headD (raw_ints% [702902945411356590724209474456225]) 0) 35 true) (.node 94 (sourceLit (List.headD (raw_ints% [54583809731245120700539190025]) 0) 49 false) (.node 93 (sourceLit (List.headD (raw_ints% [636433023136431580910134138000575]) 0) 36 true) .empty .empty) .empty) (.node 96 (sourceLit (List.headD (raw_ints% [13266967004925978692688686775]) 0) 51 false) .empty .empty)) (.node 99 (sourceLit (List.headD (raw_ints% [4571645834293096211808923213921475]) 0) 31 true) (.node 98 (sourceLit (List.headD (raw_ints% [1616965636954691394796349925]) 0) 54 false) .empty .empty) (.node 100 (sourceLit (List.headD (raw_ints% [395057648407757473073844675]) 0) 56 false) .empty .empty)))

#time def treeG_J008_part017 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [112704816789419721903908746875]) 0) 48 false) treeG_J008_part015 treeG_J008_part016)

#time def treeG_J008_part018 : IntSourceTree :=
  (.node 106 (sourceLit (List.headD (raw_ints% [11640870927520980965390025]) 0) 61 false) (.node 104 (sourceLit (List.headD (raw_ints% [47417253702942301805537325]) 0) 59 false) (.node 103 (sourceLit (List.headD (raw_ints% [14332795239395707757162523875370825]) 0) 28 true) (.node 102 (sourceLit (List.headD (raw_ints% [193406216596734819866956875]) 0) 57 false) .empty .empty) .empty) (.node 105 (sourceLit (List.headD (raw_ints% [118906062710048615642586511006616175]) 0) 24 true) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [277747804546848372289846684172047695]) 0) 21 false) (.node 108 (sourceLit (List.headD (raw_ints% [2861125644213584955170775]) 0) 63 false) (.node 107 (sourceLit (List.headD (raw_ints% [66753250766981131775226895850792175]) 0) 23 true) .empty .empty) .empty) (.node 110 (sourceLit (List.headD (raw_ints% [1407849302077220457925425]) 0) 64 false) .empty .empty)))

#time def treeG_J008_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [5267554548053547703283]) 0) 72 false) (.node 114 (sourceLit (List.headD (raw_ints% [21359300722514214760773]) 0) 70 false) (.node 113 (sourceLit (List.headD (raw_ints% [17403484122776504230100635306045502205]) 0) 17 false) (.node 112 (sourceLit (List.headD (raw_ints% [346681491480260537493375]) 0) 66 false) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [44662229919365449949918593567856843265]) 0) 16 false) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [2599776941259021654559]) 0) 73 false) (.node 117 (sourceLit (List.headD (raw_ints% [212143968958454310053270349645790184325]) 0) 14 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [481785943155806631248433517221139287015]) 0) 13 false) .empty .empty)))

#time def treeG_J008_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [1441812577832302379083753051229616585]) 0) 20 false) treeG_J008_part018 treeG_J008_part019)

#time def treeG_J008_part021 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [11785524463282667100859468749611475]) 0) 29 true) treeG_J008_part017 treeG_J008_part020)

#time def treeG_J008_part022 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 45 false) (.node 127 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 44 false) (.node 126 (sourceLit (List.headD (raw_ints% [6516141687497090641596388109325]) 0) 43 false) (.node 125 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 42 false) .empty .empty) .empty) (.node 128 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 46 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [215049678014051080776442311555825]) 0) 40 true) (.node 131 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 48 true) (.node 130 (sourceLit (List.headD (raw_ints% [108181553873769376333509245773275]) 0) 41 false) .empty .empty) .empty) (.node 133 (sourceLit (List.headD (raw_ints% [76639275416805410894657947875]) 0) 49 false) .empty .empty)))

#time def treeG_J008_part023 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [546889134690310738477919625]) 0) 56 false) (.node 137 (sourceLit (List.headD (raw_ints% [8986660995868456067414965575]) 0) 52 false) (.node 136 (sourceLit (List.headD (raw_ints% [285877605741836921300114046344925]) 0) 37 true) (.node 135 (sourceLit (List.headD (raw_ints% [18518268358630809691288391025]) 0) 51 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [1418961421249667238944426030265375]) 0) 34 true) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [266927929241445028307178675]) 0) 57 false) (.node 140 (sourceLit (List.headD (raw_ints% [1854036547920069287651818901934975]) 0) 33 true) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [4876942555659006008817185469199275]) 0) 31 true) .empty .empty)))

#time def treeG_J008_part024 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [266088344109525831777055140486375]) 0) 38 true) treeG_J008_part022 treeG_J008_part023)

#time def treeG_J008_part025 : IntSourceTree :=
  (.node 148 (sourceLit (List.headD (raw_ints% [50775690068863169734178734608117675]) 0) 25 true) (.node 146 (sourceLit (List.headD (raw_ints% [57455836267759562566162235347973775]) 0) 26 true) (.node 145 (sourceLit (List.headD (raw_ints% [31981285669994533944699525]) 0) 60 false) (.node 144 (sourceLit (List.headD (raw_ints% [6206237831537087424262132630519125]) 0) 30 true) .empty .empty) .empty) (.node 147 (sourceLit (List.headD (raw_ints% [3922886911047097034971125]) 0) 63 false) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [473877840864018517648425]) 0) 66 false) (.node 150 (sourceLit (List.headD (raw_ints% [637230419113289255197902751497705]) 0) 23 true) (.node 149 (sourceLit (List.headD (raw_ints% [1927154183000383014893775]) 0) 64 false) .empty .empty) .empty) (.node 152 (sourceLit (List.headD (raw_ints% [325723516292002575882783092529444165]) 0) 22 false) .empty .empty)))

#time def treeG_J008_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [64596155502561458831413055857905605325]) 0) 16 false) (.node 156 (sourceLit (List.headD (raw_ints% [13109376618689421773593215922185635445]) 0) 18 false) (.node 155 (sourceLit (List.headD (raw_ints% [7182784613898854118873]) 0) 72 false) (.node 154 (sourceLit (List.headD (raw_ints% [4757635398803748593009645447313850125]) 0) 19 false) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [3541377601390588883539]) 0) 73 false) .empty .empty)) (.node 165 (sourceLit (List.headD (raw_ints% [10715716369328222770687863290025]) 0) 43 false) (.node 159 (sourceLit (List.headD (raw_ints% [873599994596062834815]) 0) 75 false) .empty .empty) (.node 166 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 42 false) .empty .empty)))

#time def treeG_J008_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [233269362611337652358175]) 0) 67 false) treeG_J008_part025 treeG_J008_part026)

#time def treeG_J008_part028 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [65276497430422375100290875]) 0) 59 false) treeG_J008_part024 treeG_J008_part027)

#time def treeG_J008_part029 : IntSourceTree :=
  (.node 124 (sourceLit (List.headD (raw_ints% [3846776403904022851040268257625]) 0) 44 false) treeG_J008_part021 treeG_J008_part028)

#time def treeG_J008_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [852576952066895984929]) 0) 74 false) treeG_J008_part014 treeG_J008_part029)

#time def treeG_J008_part031 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [1600408398409760051035504205625]) 0) 48 true) (.node 170 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 47 false) (.node 169 (sourceLit (List.headD (raw_ints% [39398641422968384316345023734725]) 0) 39 false) (.node 168 (sourceLit (List.headD (raw_ints% [1934014656106442427871074096375]) 0) 44 false) .empty .empty) .empty) (.node 171 (sourceLit (List.headD (raw_ints% [2207297302886775401530667430173325]) 0) 38 false) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [3554510560341056717708672773325775]) 0) 35 true) (.node 174 (sourceLit (List.headD (raw_ints% [98694741102365701088776705725]) 0) 49 false) (.node 173 (sourceLit (List.headD (raw_ints% [6245156673313203003936019831785825]) 0) 36 true) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [23769569712335640689888095275]) 0) 51 false) .empty .empty)))

#time def treeG_J008_part032 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [340449641886155236747400475]) 0) 57 false) (.node 180 (sourceLit (List.headD (raw_ints% [698720620972864003881994575]) 0) 56 false) (.node 179 (sourceLit (List.headD (raw_ints% [18131736905701579611301893270324525]) 0) 31 true) (.node 178 (sourceLit (List.headD (raw_ints% [5752729721959073277822265725]) 0) 53 false) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [47543645070159550103998736112307725]) 0) 29 true) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [675492379726698574662966465699831825]) 0) 24 true) (.node 184 (sourceLit (List.headD (raw_ints% [83135741157902448395044425]) 0) 59 false) (.node 183 (sourceLit (List.headD (raw_ints% [63698285651148388383912443631817575]) 0) 28 true) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [5085103685618388244827375]) 0) 63 false) .empty .empty)))

#time def treeG_J008_part033 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [14778841603384971754279170827547825]) 0) 32 true) treeG_J008_part031 treeG_J008_part032)

#time def treeG_J008_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [601074190247776497803475]) 0) 66 false) (.node 190 (sourceLit (List.headD (raw_ints% [2446459063923545571862125]) 0) 64 false) (.node 189 (sourceLit (List.headD (raw_ints% [1902569886750469803783566191631813295]) 0) 21 true) (.node 188 (sourceLit (List.headD (raw_ints% [4984648177880609114771475]) 0) 63 false) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [1452008264538115007166919495253579865]) 0) 20 true) .empty .empty)) (.node 195 (sourceLit (List.headD (raw_ints% [31459936461494527538235733589164758735]) 0) 16 false) (.node 194 (sourceLit (List.headD (raw_ints% [147832159721280793315083]) 0) 68 false) (.node 193 (sourceLit (List.headD (raw_ints% [3442820919911660626397482615838924355]) 0) 17 false) .empty .empty) .empty) (.node 196 (sourceLit (List.headD (raw_ints% [9098014679744160534463]) 0) 72 false) .empty .empty)))

#time def treeG_J008_part035 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [5742535825054513670447958470775]) 0) 44 false) (.node 206 (sourceLit (List.headD (raw_ints% [14915291051159354899779338470725]) 0) 43 false) (.node 199 (sourceLit (List.headD (raw_ints% [551752544885176710054175376505350398185]) 0) 13 false) (.node 198 (sourceLit (List.headD (raw_ints% [4482978261522156112519]) 0) 73 false) .empty .empty) .empty) (.node 207 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 43 false) .empty .empty)) (.node 210 (sourceLit (List.headD (raw_ints% [176964466324570368350673467811825]) 0) 40 true) (.node 209 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 false) .empty .empty) (.node 211 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 49 false) .empty .empty)))

#time def treeG_J008_part036 : IntSourceTree :=
  (.node 197 (sourceLit (List.headD (raw_ints% [207356082839607186701712559864150149915]) 0) 14 false) treeG_J008_part034 treeG_J008_part035)

#time def treeG_J008_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [852540129517171869283368869716788225]) 0) 23 true) treeG_J008_part033 treeG_J008_part036)

#time def treeG_J008_part038 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [3695727179116796155618282425]) 0) 54 false) (.node 215 (sourceLit (List.headD (raw_ints% [61658204385104081706199923675]) 0) 50 false) (.node 214 (sourceLit (List.headD (raw_ints% [5712979985094151340381909550813075]) 0) 37 true) (.node 213 (sourceLit (List.headD (raw_ints% [419261918456641365482540538375]) 0) 51 true) .empty .empty) .empty) (.node 216 (sourceLit (List.headD (raw_ints% [2982755348857382875108444680635925]) 0) 36 true) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [14423663809861441035998255466454575]) 0) 32 true) (.node 219 (sourceLit (List.headD (raw_ints% [3565173183197830323910587225]) 0) 54 false) (.node 218 (sourceLit (List.headD (raw_ints% [11940918760885637276390318767017075]) 0) 33 true) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [107948172932854743893703975]) 0) 59 false) .empty .empty)))

#time def treeG_J008_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [6247320460189679454683625]) 0) 63 false) (.node 225 (sourceLit (List.headD (raw_ints% [12788613871976978612586225]) 0) 62 false) (.node 224 (sourceLit (List.headD (raw_ints% [51285809988074213535388178370779325]) 0) 29 true) (.node 223 (sourceLit (List.headD (raw_ints% [209896647025310486546818725]) 0) 58 false) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [560580707191179449530641995003884275]) 0) 25 true) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [764373498720056524969425]) 0) 66 false) (.node 228 (sourceLit (List.headD (raw_ints% [750988749379445529815011400500552875]) 0) 24 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [1901295425912243225273170386128817885]) 0) 22 true) .empty .empty)))

#time def treeG_J008_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [37789759958841538086364365173909175]) 0) 30 true) treeG_J008_part038 treeG_J008_part039)

#time def treeG_J008_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [5241183224115683991049301744793487845]) 0) 17 false) (.node 234 (sourceLit (List.headD (raw_ints% [6072449877695836559621808278788775895]) 0) 18 true) (.node 233 (sourceLit (List.headD (raw_ints% [91951206909109711361325]) 0) 69 false) (.node 232 (sourceLit (List.headD (raw_ints% [2103455297122120158932485680312468195]) 0) 21 true) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [90369882810089960364099]) 0) 69 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [2735778272330030442889]) 0) 74 false) (.node 238 (sourceLit (List.headD (raw_ints% [78163771834484269038886448148338939265]) 0) 15 false) (.node 237 (sourceLit (List.headD (raw_ints% [1389159269588392912731]) 0) 75 false) .empty .empty) .empty) (.node 247 (sourceLit (List.headD (raw_ints% [21112639114023515470847527553175]) 0) 43 false) .empty .empty)))

#time def treeG_J008_part042 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [48443503215951244013272852684345425]) 0) 36 false) (.node 251 (sourceLit (List.headD (raw_ints% [3623013033483338348336055172667925]) 0) 38 true) (.node 250 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 47 true) (.node 249 (sourceLit (List.headD (raw_ints% [328123651380520490592324318394875]) 0) 39 false) .empty .empty) .empty) (.node 252 (sourceLit (List.headD (raw_ints% [5765978426946712972603971490125]) 0) 48 false) .empty .empty)) (.node 255 (sourceLit (List.headD (raw_ints% [42149329320412154005346603633178825]) 0) 35 true) (.node 254 (sourceLit (List.headD (raw_ints% [3452790088755496624949101012725]) 0) 49 true) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [2368039667048027563519489275]) 0) 55 false) .empty .empty)))

#time def treeG_J008_part043 : IntSourceTree :=
  (.node 248 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 46 false) treeG_J008_part041 treeG_J008_part042)

#time def treeG_J008_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [1498703382195508536565275]) 0) 65 false) treeG_J008_part040 treeG_J008_part043)

#time def treeG_J008_part045 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [2637396658914877563083552053284975]) 0) 39 false) treeG_J008_part037 treeG_J008_part044)

#time def treeG_J008_part046 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [523135741576682714402231325]) 0) 57 false) (.node 260 (sourceLit (List.headD (raw_ints% [2167731941252102316146598075]) 0) 55 false) (.node 259 (sourceLit (List.headD (raw_ints% [77395613181383518599820656865812075]) 0) 31 true) (.node 258 (sourceLit (List.headD (raw_ints% [9030178994508111344650863975]) 0) 53 false) .empty .empty) .empty) (.node 261 (sourceLit (List.headD (raw_ints% [183234975887623506471973351350965475]) 0) 29 true) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [2606799459510051091601876950030044975]) 0) 24 true) (.node 264 (sourceLit (List.headD (raw_ints% [31690226466852009537943575]) 0) 61 false) (.node 263 (sourceLit (List.headD (raw_ints% [238619794019583916307002477759455825]) 0) 28 true) .empty .empty) .empty) (.node 266 (sourceLit (List.headD (raw_ints% [3851755093179295183879425]) 0) 64 false) .empty .empty)))

#time def treeG_J008_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [112203648993466504845225]) 0) 69 false) (.node 270 (sourceLit (List.headD (raw_ints% [3668528925836906627893275]) 0) 64 false) (.node 269 (sourceLit (List.headD (raw_ints% [10113250103320658673256616216377032705]) 0) 21 true) (.node 268 (sourceLit (List.headD (raw_ints% [7509992742498749794595775]) 0) 63 false) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [13758355142759830795018443593776963215]) 0) 20 true) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [219972667915158052130217]) 0) 68 false) (.node 273 (sourceLit (List.headD (raw_ints% [70753390427819505712237024385837906595]) 0) 17 true) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [80039535483061220015210199819474965895]) 0) 16 true) .empty .empty)))

#time def treeG_J008_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [3632105528012263726961767090314285975]) 0) 23 true) treeG_J008_part046 treeG_J008_part047)

#time def treeG_J008_part049 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 50 false) (.node 279 (sourceLit (List.headD (raw_ints% [73557629790697442256916208681361115935]) 0) 13 false) (.node 278 (sourceLit (List.headD (raw_ints% [6630295895184987189329]) 0) 73 false) (.node 277 (sourceLit (List.headD (raw_ints% [123497151253756242844923731947454344395]) 0) 14 true) .empty .empty) .empty) (.node 288 (sourceLit (List.headD (raw_ints% [480315727780281306262486533825]) 0) 49 false) .empty .empty)) (.node 292 (sourceLit (List.headD (raw_ints% [1565102423099553977854901806488225]) 0) 41 true) (.node 291 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 48 true) (.node 290 (sourceLit (List.headD (raw_ints% [126272029426272714735749446551675]) 0) 42 false) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [7443026100773278434534133643625]) 0) 49 false) .empty .empty)))

#time def treeG_J008_part050 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [2732502905655140510370138375]) 0) 55 false) (.node 297 (sourceLit (List.headD (raw_ints% [5776431489075314098459674675]) 0) 54 false) (.node 296 (sourceLit (List.headD (raw_ints% [9791643492888692782559539738135725]) 0) 38 true) (.node 295 (sourceLit (List.headD (raw_ints% [219653018321287544165956308525]) 0) 54 true) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [17182102699791410743200185046446175]) 0) 35 true) .empty .empty)) (.node 301 (sourceLit (List.headD (raw_ints% [1304146557789264364996966275]) 0) 56 false) (.node 300 (sourceLit (List.headD (raw_ints% [15742987342880519390955600349839375]) 0) 34 true) .empty .empty) (.node 302 (sourceLit (List.headD (raw_ints% [36361303982195492096402246544264075]) 0) 32 true) .empty .empty)))

#time def treeG_J008_part051 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [13539120800261348838413690558789625]) 0) 39 false) treeG_J008_part049 treeG_J008_part050)

#time def treeG_J008_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [53977824091113318226247]) 0) 70 false) treeG_J008_part048 treeG_J008_part051)

#time def treeG_J008_part053 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [720279194658204549286688922453433275]) 0) 26 true) (.node 306 (sourceLit (List.headD (raw_ints% [511554688079717910517808738756540175]) 0) 27 true) (.node 305 (sourceLit (List.headD (raw_ints% [9450806297437515462678675]) 0) 63 false) (.node 304 (sourceLit (List.headD (raw_ints% [46833496007877425692903574847169125]) 0) 31 true) .empty .empty) .empty) (.node 307 (sourceLit (List.headD (raw_ints% [9159699912527501280834075]) 0) 63 false) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [4237940514924605647125]) 0) 74 false) (.node 310 (sourceLit (List.headD (raw_ints% [2052988669352103861995861457562053705]) 0) 24 true) (.node 309 (sourceLit (List.headD (raw_ints% [4452498747618523694718075]) 0) 64 false) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [2913724961409427659021489478366123755]) 0) 23 true) .empty .empty)))

#time def treeG_J008_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [50415230772060127970952545023948320915]) 0) 17 true) (.node 316 (sourceLit (List.headD (raw_ints% [21320179676794226001564875391067113435]) 0) 19 true) (.node 315 (sourceLit (List.headD (raw_ints% [64801392552534045883059]) 0) 70 false) (.node 314 (sourceLit (List.headD (raw_ints% [16170235137530917288153804026762282675]) 0) 20 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [31751275777699031622551]) 0) 71 false) .empty .empty)) (.node 330 (sourceLit (List.headD (raw_ints% [3421718237726782757002669555125]) 0) 47 false) (.node 319 (sourceLit (List.headD (raw_ints% [486814702856869593305]) 0) 77 false) .empty .empty) (.node 331 (sourceLit (List.headD (raw_ints% [7663717975124065219880037462321525]) 0) 38 false) .empty .empty)))

#time def treeG_J008_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [132456091077823298329125]) 0) 69 false) treeG_J008_part053 treeG_J008_part054)

#time def treeG_J008_part056 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [1172661037529701395918430027528571025]) 0) 32 true) (.node 335 (sourceLit (List.headD (raw_ints% [475401194928775316834584701514446825]) 0) 35 false) (.node 334 (sourceLit (List.headD (raw_ints% [18338842290302053494017368299975]) 0) 49 false) (.node 333 (sourceLit (List.headD (raw_ints% [148610058294322698595986568299591825]) 0) 36 true) .empty .empty) .empty) (.node 336 (sourceLit (List.headD (raw_ints% [27752632248541946466184474725]) 0) 58 true) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [3297273870058178704593678675]) 0) 55 false) (.node 339 (sourceLit (List.headD (raw_ints% [472431673211941625182585264620465525]) 0) 31 true) (.node 338 (sourceLit (List.headD (raw_ints% [14075546961793145049187834725]) 0) 53 false) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [824316214056729734549185071038754525]) 0) 29 true) .empty .empty)))

#time def treeG_J008_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [12737644490538709409608112549894999625]) 0) 23 true) (.node 345 (sourceLit (List.headD (raw_ints% [9382575518506569885781438210845251025]) 0) 24 true) (.node 344 (sourceLit (List.headD (raw_ints% [46619547170991047425909575]) 0) 61 false) (.node 343 (sourceLit (List.headD (raw_ints% [924941933410671830777869411656994575]) 0) 28 true) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [2799525602129110139399625]) 0) 65 false) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [35984618354804432481091474820642696895]) 0) 21 true) (.node 348 (sourceLit (List.headD (raw_ints% [10809407082556252767072375]) 0) 63 false) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [5236468569400140761542875]) 0) 64 false) .empty .empty)))

#time def treeG_J008_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [390505408106290825297367475]) 0) 58 false) treeG_J008_part056 treeG_J008_part057)

#time def treeG_J008_part059 : IntSourceTree :=
  (.node 332 (sourceLit (List.headD (raw_ints% [12014333469752142354956672416875]) 0) 48 true) treeG_J008_part055 treeG_J008_part058)

#time def treeG_J008_part060 : IntSourceTree :=
  (.node 303 (sourceLit (List.headD (raw_ints% [39154886818921528481926575]) 0) 61 false) treeG_J008_part052 treeG_J008_part059)

#time def treeG_J008_part061 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [80669329560051280249191058952801775]) 0) 32 true) treeG_J008_part045 treeG_J008_part060)

#time def treeG_J008_part062 : IntSourceTree :=
  (.node 167 (sourceLit (List.headD (raw_ints% [8717942988295194328711149388275]) 0) 43 false) treeG_J008_part030 treeG_J008_part061)

#time def treeG_J008_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [75624961013954773539871]) 0) 70 false) (.node 354 (sourceLit (List.headD (raw_ints% [309851696396135141186283]) 0) 68 false) (.node 353 (sourceLit (List.headD (raw_ints% [302203404632587234642513628845025934045]) 0) 17 true) (.node 352 (sourceLit (List.headD (raw_ints% [159024543961708256570775]) 0) 69 false) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [437407988917928133205711529036918079705]) 0) 16 true) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [1686845014496621537327397649447707385215]) 0) 13 true) (.node 358 (sourceLit (List.headD (raw_ints% [18490683987329057243893]) 0) 72 false) (.node 357 (sourceLit (List.headD (raw_ints% [1240994348061074221255228293080840915445]) 0) 14 true) .empty .empty) .empty) (.node 371 (sourceLit (List.headD (raw_ints% [1636473939782374362044755004625]) 0) 50 false) .empty .empty)))

#time def treeG_J008_part064 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [893860663442417601016362865875]) 0) 54 true) (.node 375 (sourceLit (List.headD (raw_ints% [21853290583442654200672669236375]) 0) 50 false) (.node 374 (sourceLit (List.headD (raw_ints% [202766541495368093949641330534750325]) 0) 37 true) (.node 373 (sourceLit (List.headD (raw_ints% [4864339892631355197372701515125]) 0) 51 true) .empty .empty) .empty) (.node 376 (sourceLit (List.headD (raw_ints% [514567768900330087964822860466989725]) 0) 36 false) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [409459723840419547618762863221108025]) 0) 32 true) (.node 379 (sourceLit (List.headD (raw_ints% [8610541150482864028447557975]) 0) 54 false) (.node 378 (sourceLit (List.headD (raw_ints% [1103932626730535752945629287342786325]) 0) 33 true) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [124570457016807146224794525]) 0) 60 false) .empty .empty)))

#time def treeG_J008_part065 : IntSourceTree :=
  (.node 372 (sourceLit (List.headD (raw_ints% [13924127667522281131299644688274425]) 0) 39 false) treeG_J008_part063 treeG_J008_part064)

#time def treeG_J008_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [13236504904505379834362925]) 0) 63 false) (.node 385 (sourceLit (List.headD (raw_ints% [27717934576116016500552225]) 0) 62 false) (.node 384 (sourceLit (List.headD (raw_ints% [737607949379162128006255112268318075]) 0) 29 true) (.node 383 (sourceLit (List.headD (raw_ints% [233885860830604711369661175]) 0) 59 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [7336356766187698243710203255819090325]) 0) 25 true) .empty .empty)) (.node 390 (sourceLit (List.headD (raw_ints% [27772663677396017033108028990394482075]) 0) 22 true) (.node 389 (sourceLit (List.headD (raw_ints% [1589227083734432268088575]) 0) 66 false) (.node 388 (sourceLit (List.headD (raw_ints% [9856527711905891212461356860081266525]) 0) 24 true) .empty .empty) .empty) (.node 391 (sourceLit (List.headD (raw_ints% [3066643025758742670214875]) 0) 65 false) .empty .empty)))

#time def treeG_J008_part067 : IntSourceTree :=
  (.node 397 (sourceLit (List.headD (raw_ints% [5484210654531967739665]) 0) 74 false) (.node 395 (sourceLit (List.headD (raw_ints% [180248911291067049420165]) 0) 69 false) (.node 394 (sourceLit (List.headD (raw_ints% [237522464082463565489898412737976803345]) 0) 18 true) (.node 393 (sourceLit (List.headD (raw_ints% [185592996845593214812425]) 0) 69 false) .empty .empty) .empty) (.node 396 (sourceLit (List.headD (raw_ints% [352127270210751229199452027472649625965]) 0) 17 true) .empty .empty)) (.node 399 (sourceLit (List.headD (raw_ints% [10701648741619143751013]) 0) 73 false) (.node 398 (sourceLit (List.headD (raw_ints% [1039333424972833709371418112985047631785]) 0) 15 true) .empty .empty) (.node 412 (sourceLit (List.headD (raw_ints% [25106124988011137251314712453875]) 0) 48 false) .empty .empty)))

#time def treeG_J008_part068 : IntSourceTree :=
  (.node 392 (sourceLit (List.headD (raw_ints% [40282382430869782152763165134744260325]) 0) 21 true) treeG_J008_part066 treeG_J008_part067)

#time def treeG_J008_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [678870998127947766163576084861698225]) 0) 30 true) treeG_J008_part065 treeG_J008_part068)

#time def treeG_J008_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [3589518200731463549114639298225]) 0) 53 true) (.node 416 (sourceLit (List.headD (raw_ints% [25405627511256023348344282001175]) 0) 51 false) (.node 415 (sourceLit (List.headD (raw_ints% [2097533526891720068431715345792449425]) 0) 35 true) (.node 414 (sourceLit (List.headD (raw_ints% [57253561431352895072998980420975]) 0) 49 true) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [17638829642340264210792761562472242225]) 0) 32 false) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [5727039367389983027351020740498973875]) 0) 29 true) (.node 420 (sourceLit (List.headD (raw_ints% [1328316820106171330963469825]) 0) 57 false) (.node 419 (sourceLit (List.headD (raw_ints% [8359029340632344398382449034121825075]) 0) 31 true) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [606058248028166344500988725]) 0) 58 false) .empty .empty)))

#time def treeG_J008_part071 : IntSourceTree :=
  (.node 428 (sourceLit (List.headD (raw_ints% [15663602726454506901653475]) 0) 63 false) (.node 426 (sourceLit (List.headD (raw_ints% [16519832167599575942953725]) 0) 63 false) (.node 425 (sourceLit (List.headD (raw_ints% [37824333241759806306618888974327105775]) 0) 24 true) (.node 424 (sourceLit (List.headD (raw_ints% [140646766488622616517842025]) 0) 60 false) .empty .empty) .empty) (.node 427 (sourceLit (List.headD (raw_ints% [45953209638962876540073513496657722975]) 0) 23 true) .empty .empty)) (.node 430 (sourceLit (List.headD (raw_ints% [7477348100475317383165725]) 0) 64 false) (.node 429 (sourceLit (List.headD (raw_ints% [121719825035689826918290234940657567505]) 0) 21 true) .empty .empty) (.node 431 (sourceLit (List.headD (raw_ints% [170244027142660643476015108874947101255]) 0) 20 true) .empty .empty)))

#time def treeG_J008_part072 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [4506026051612910298530739267236591225]) 0) 28 true) treeG_J008_part070 treeG_J008_part071)

#time def treeG_J008_part073 : IntSourceTree :=
  (.node 437 (sourceLit (List.headD (raw_ints% [4393041975310945445936004146481553099995]) 0) 14 true) (.node 435 (sourceLit (List.headD (raw_ints% [1462771723741780390713475772866896347055]) 0) 16 true) (.node 434 (sourceLit (List.headD (raw_ints% [432520290986237718063417]) 0) 68 false) (.node 433 (sourceLit (List.headD (raw_ints% [986832833155245794245907655466790396355]) 0) 17 true) .empty .empty) .empty) (.node 436 (sourceLit (List.headD (raw_ints% [52311975138556137940147]) 0) 71 false) .empty .empty)) (.node 454 (sourceLit (List.headD (raw_ints% [287081321235023645323211106923366475]) 0) 38 false) (.node 439 (sourceLit (List.headD (raw_ints% [6627822385286048137643947254432673669065]) 0) 13 true) (.node 438 (sourceLit (List.headD (raw_ints% [25383001248926684673427]) 0) 72 false) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [39553426007397774636835824828675]) 0) 51 true) .empty .empty)))

#time def treeG_J008_part074 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [830034992038942746064291725]) 0) 58 false) (.node 459 (sourceLit (List.headD (raw_ints% [449766092735243301642885857025]) 0) 57 true) (.node 458 (sourceLit (List.headD (raw_ints% [9371381134535399981869195424907514275]) 0) 34 false) (.node 457 (sourceLit (List.headD (raw_ints% [28981070165025693752409733464675]) 0) 52 false) .empty .empty) .empty) (.node 460 (sourceLit (List.headD (raw_ints% [3974784808395962425381843085450358525]) 0) 33 true) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [186086193598780816565663775]) 0) 60 false) (.node 462 (sourceLit (List.headD (raw_ints% [2524084184631017630593722327818637825]) 0) 31 true) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [1884209051116874085262242077484136575]) 0) 30 true) .empty .empty)))

#time def treeG_J008_part075 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [1306050647896025078198269103129719575]) 0) 37 true) treeG_J008_part073 treeG_J008_part074)

#time def treeG_J008_part076 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [1794446674065076617648675]) 0) 66 false) treeG_J008_part072 treeG_J008_part075)

#time def treeG_J008_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [371396100974679196696780883311982625]) 0) 36 false) treeG_J008_part069 treeG_J008_part076)

#time def treeG_J008_part078 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [46973580679146904942591102975131542715]) 0) 23 true) (.node 468 (sourceLit (List.headD (raw_ints% [18048340963528492663806078318288228225]) 0) 25 true) (.node 467 (sourceLit (List.headD (raw_ints% [19803159430693772051544525]) 0) 63 false) (.node 466 (sourceLit (List.headD (raw_ints% [15243988237786054031454342859254007725]) 0) 26 true) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [9306694391516777829299175]) 0) 64 false) .empty .empty)) (.node 473 (sourceLit (List.headD (raw_ints% [1052074686682703758398975]) 0) 67 false) (.node 472 (sourceLit (List.headD (raw_ints% [64980822355895430661625971870101420465]) 0) 22 true) (.node 471 (sourceLit (List.headD (raw_ints% [2205352537358287356475425]) 0) 66 false) .empty .empty) .empty) (.node 474 (sourceLit (List.headD (raw_ints% [374655184536391114378004621364406796505]) 0) 19 true) .empty .empty)))

#time def treeG_J008_part079 : IntSourceTree :=
  (.node 495 (sourceLit (List.headD (raw_ints% [6690834666652098393603093056566313025]) 0) 35 false) (.node 478 (sourceLit (List.headD (raw_ints% [1676854275169055868282293016748252734105]) 0) 16 true) (.node 477 (sourceLit (List.headD (raw_ints% [30375132520428266981487]) 0) 72 false) (.node 476 (sourceLit (List.headD (raw_ints% [555322226765514580757011872697123360545]) 0) 18 true) .empty .empty) .empty) (.node 479 (sourceLit (List.headD (raw_ints% [7340676253653770461207]) 0) 74 false) .empty .empty)) (.node 497 (sourceLit (List.headD (raw_ints% [101226071107685869215481984162774295025]) 0) 32 true) (.node 496 (sourceLit (List.headD (raw_ints% [104512479526051572622015931658525]) 0) 51 true) .empty .empty) (.node 498 (sourceLit (List.headD (raw_ints% [8142647091439289325381093190725]) 0) 55 false) .empty .empty)))

#time def treeG_J008_part080 : IntSourceTree :=
  (.node 475 (sourceLit (List.headD (raw_ints% [63067844923792667160813]) 0) 71 false) treeG_J008_part078 treeG_J008_part079)

#time def treeG_J008_part081 : IntSourceTree :=
  (.node 504 (sourceLit (List.headD (raw_ints% [231525620708939016613485525]) 0) 60 false) (.node 502 (sourceLit (List.headD (raw_ints% [1054011736049719147627594725]) 0) 58 false) (.node 501 (sourceLit (List.headD (raw_ints% [121466074501280814584867957993912498925]) 0) 29 true) (.node 500 (sourceLit (List.headD (raw_ints% [900860502290592774616735183875]) 0) 57 true) .empty .empty) .empty) (.node 503 (sourceLit (List.headD (raw_ints% [35879320902483371790968817977861613975]) 0) 28 true) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [197950602165613987963195972251406400625]) 0) 23 true) (.node 506 (sourceLit (List.headD (raw_ints% [52171233001191431630830125]) 0) 62 false) (.node 505 (sourceLit (List.headD (raw_ints% [203354425301200076606948096943642375825]) 0) 24 true) .empty .empty) .empty) (.node 508 (sourceLit (List.headD (raw_ints% [23942716134933037201435575]) 0) 63 false) .empty .empty)))

#time def treeG_J008_part082 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [309777197848233020167779]) 0) 69 false) (.node 512 (sourceLit (List.headD (raw_ints% [2616258400651498095302175]) 0) 66 false) (.node 511 (sourceLit (List.headD (raw_ints% [581333263723689835605442538727157582185]) 0) 20 true) (.node 510 (sourceLit (List.headD (raw_ints% [11136040682558238275432625]) 0) 64 false) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [3171939797622061768098154544219700513405]) 0) 17 true) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [73823714709029196381479]) 0) 71 false) (.node 515 (sourceLit (List.headD (raw_ints% [4531711228840477439334598168963612397025]) 0) 16 true) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [13377269281185521138288375779826394437445]) 0) 14 true) .empty .empty)))

#time def treeG_J008_part083 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [455827085797221938323504271244565735695]) 0) 21 true) treeG_J008_part081 treeG_J008_part082)

#time def treeG_J008_part084 : IntSourceTree :=
  (.node 499 (sourceLit (List.headD (raw_ints% [158301127493198744108289575832642053475]) 0) 31 false) treeG_J008_part080 treeG_J008_part083)

#time def treeG_J008_part085 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [166250697109990668959053262003542770525]) 0) 32 false) (.node 538 (sourceLit (List.headD (raw_ints% [119968833376756669179220375012589323575]) 0) 33 true) (.node 537 (sourceLit (List.headD (raw_ints% [1042918356961541143550200508775]) 0) 59 true) (.node 519 (sourceLit (List.headD (raw_ints% [20201846017418845754872741013539370076615]) 0) 13 true) .empty .empty) .empty) (.node 539 (sourceLit (List.headD (raw_ints% [9042179276909775928666864904775]) 0) 56 false) .empty .empty)) (.node 543 (sourceLit (List.headD (raw_ints% [681839348852157514496267175]) 0) 59 false) (.node 542 (sourceLit (List.headD (raw_ints% [116417906132018779323680513338275223275]) 0) 30 true) (.node 541 (sourceLit (List.headD (raw_ints% [56355658580164482335174967225]) 0) 62 true) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [32110902800249623620444333822893340825]) 0) 29 true) .empty .empty)))

#time def treeG_J008_part086 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [361879924438928128438322065294302650265]) 0) 22 true) (.node 548 (sourceLit (List.headD (raw_ints% [161853920238557002635583815614829944175]) 0) 24 true) (.node 547 (sourceLit (List.headD (raw_ints% [1011502299078051861852675]) 0) 68 false) (.node 546 (sourceLit (List.headD (raw_ints% [172866448825627968544039411225134360375]) 0) 25 true) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [914751358963516210758525]) 0) 68 false) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [451371619011898974282190594986954741255]) 0) 21 true) (.node 551 (sourceLit (List.headD (raw_ints% [6725335607841663562481775]) 0) 65 false) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [48880741061524823028225]) 0) 72 false) .empty .empty)))

#time def treeG_J008_part087 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [73157361686274216548373975]) 0) 62 false) treeG_J008_part085 treeG_J008_part086)

#time def treeG_J008_part088 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [20685911284622308367133]) 0) 73 false) (.node 557 (sourceLit (List.headD (raw_ints% [5431072773575116174999]) 0) 75 false) (.node 556 (sourceLit (List.headD (raw_ints% [3421066775309448277820574423569365675935]) 0) 17 true) (.node 555 (sourceLit (List.headD (raw_ints% [183641508000647685846153]) 0) 70 false) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [10023560730847409401723789746329888969235]) 0) 15 true) .empty .empty)) (.node 582 (sourceLit (List.headD (raw_ints% [1804435086301313153873226545925]) 0) 58 true) (.node 581 (sourceLit (List.headD (raw_ints% [2781477228261131517929720150050596827325]) 0) 29 false) (.node 580 (sourceLit (List.headD (raw_ints% [4971519889600184351641800044325]) 0) 58 false) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [895463928153666862798475288728340172225]) 0) 28 true) .empty .empty)))

#time def treeG_J008_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [2133835638019690103845836778592713371105]) 0) 21 true) (.node 587 (sourceLit (List.headD (raw_ints% [1184980988439409760389119317549668482375]) 0) 23 true) (.node 586 (sourceLit (List.headD (raw_ints% [94143490371357001465917825]) 0) 62 false) (.node 585 (sourceLit (List.headD (raw_ints% [1851743353914775835101489267721531436975]) 0) 24 true) .empty .empty) .empty) (.node 588 (sourceLit (List.headD (raw_ints% [40793431006062281957135625]) 0) 63 false) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [2313706131787735191901133983627263619935]) 0) 20 true) (.node 590 (sourceLit (List.headD (raw_ints% [18136002804274280468840175]) 0) 64 false) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [256817325449385341698725]) 0) 70 false) .empty .empty)))

#time def treeG_J008_part090 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [225156864071609248941390825]) 0) 61 false) treeG_J008_part088 treeG_J008_part089)

#time def treeG_J008_part091 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [2422629428549279539342145301490886920395]) 0) 18 true) treeG_J008_part087 treeG_J008_part090)

#time def treeG_J008_part092 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [35367263791929849289547]) 0) 72 false) treeG_J008_part084 treeG_J008_part091)

#time def treeG_J008_part093 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [85210897336390583516737575]) 0) 61 false) treeG_J008_part077 treeG_J008_part092)

#time def treeG_J008_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [51529900585272009510437]) 0) 72 false) (.node 596 (sourceLit (List.headD (raw_ints% [54908896645809244732337]) 0) 72 false) (.node 595 (sourceLit (List.headD (raw_ints% [14849324199553758875402564242963482966135]) 0) 16 true) (.node 594 (sourceLit (List.headD (raw_ints% [472314659136164148283821]) 0) 69 false) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [41359799123765651306840814997283456377515]) 0) 14 true) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [362236891799143787156675082923609006325]) 0) 33 false) (.node 621 (sourceLit (List.headD (raw_ints% [5422365158241500210323199782125]) 0) 59 false) (.node 599 (sourceLit (List.headD (raw_ints% [59986639829360429458917576957099741677265]) 0) 13 true) .empty .empty) .empty) (.node 623 (sourceLit (List.headD (raw_ints% [451279231412541327846930703275]) 0) 61 true) .empty .empty)))

#time def treeG_J008_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [26157409262646022584999225]) 0) 64 false) (.node 627 (sourceLit (List.headD (raw_ints% [61775416800859341886632225]) 0) 63 false) (.node 626 (sourceLit (List.headD (raw_ints% [209859613136143483319681232062049634575]) 0) 28 true) (.node 625 (sourceLit (List.headD (raw_ints% [75999751192667516196508425]) 0) 63 false) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [127890883525106594719191937741854817275]) 0) 27 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [89145837472129819580925]) 0) 72 false) (.node 630 (sourceLit (List.headD (raw_ints% [221494464197595246925939339162301340105]) 0) 25 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [232791814096979527202367923580038609835]) 0) 24 true) .empty .empty)))

#time def treeG_J008_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [107919128169177154897253869363180853925]) 0) 32 true) treeG_J008_part094 treeG_J008_part095)

#time def treeG_J008_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [3917029799114780238139628156369195926035]) 0) 18 true) (.node 636 (sourceLit (List.headD (raw_ints% [1428532178030538824697748727424264661275]) 0) 20 true) (.node 635 (sourceLit (List.headD (raw_ints% [72168287783879115609417]) 0) 72 false) (.node 634 (sourceLit (List.headD (raw_ints% [1106165322776178233698724899233995535795]) 0) 21 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [33184605551508780032341]) 0) 73 false) .empty .empty)) (.node 664 (sourceLit (List.headD (raw_ints% [902783619689154264942802797375]) 0) 61 true) (.node 663 (sourceLit (List.headD (raw_ints% [24078625003298869240825680595839316577025]) 0) 28 false) (.node 639 (sourceLit (List.headD (raw_ints% [3855498662581212642913]) 0) 76 false) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [53402850268703927472292491846227065772625]) 0) 24 true) .empty .empty)))

#time def treeG_J008_part098 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [11861939576858360611358983722760022146785]) 0) 20 true) (.node 669 (sourceLit (List.headD (raw_ints% [14236197453193954020210731252364703240095]) 0) 21 true) (.node 668 (sourceLit (List.headD (raw_ints% [82757402595656401816128825]) 0) 63 false) (.node 667 (sourceLit (List.headD (raw_ints% [12246034252273773172070479534421508130425]) 0) 23 true) .empty .empty) .empty) (.node 670 (sourceLit (List.headD (raw_ints% [34178815721017764701158275]) 0) 64 false) .empty .empty)) (.node 673 (sourceLit (List.headD (raw_ints% [48322752398068053554874243941127032911005]) 0) 17 true) (.node 672 (sourceLit (List.headD (raw_ints% [456349374327653214948675]) 0) 70 false) .empty .empty) (.node 674 (sourceLit (List.headD (raw_ints% [800132087474521416854379]) 0) 69 false) .empty .empty)))

#time def treeG_J008_part099 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [209855514399313063320115875]) 0) 62 false) treeG_J008_part097 treeG_J008_part098)

#time def treeG_J008_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [159055843326335695642275]) 0) 71 false) treeG_J008_part096 treeG_J008_part099)

#time def treeG_J008_part101 : IntSourceTree :=
  (.node 704 (sourceLit (List.headD (raw_ints% [24941978028652286480003711550744763408425]) 0) 29 false) (.node 678 (sourceLit (List.headD (raw_ints% [81208521620763110618927]) 0) 72 false) (.node 677 (sourceLit (List.headD (raw_ints% [141492319664143318254471022113022420265685]) 0) 14 true) (.node 676 (sourceLit (List.headD (raw_ints% [89427678921948986486497]) 0) 72 false) .empty .empty) .empty) (.node 679 (sourceLit (List.headD (raw_ints% [190703267313985505782018625050528797588975]) 0) 13 true) .empty .empty)) (.node 707 (sourceLit (List.headD (raw_ints% [74040048799226860716741825]) 0) 64 false) (.node 706 (sourceLit (List.headD (raw_ints% [51723973363614779605735041989730668696025]) 0) 25 true) (.node 705 (sourceLit (List.headD (raw_ints% [902935619191539599975195814225]) 0) 62 true) .empty .empty) .empty) (.node 708 (sourceLit (List.headD (raw_ints% [11222907184072920414316944032486669592225]) 0) 24 true) .empty .empty)))

#time def treeG_J008_part102 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [39473429815858627685284444747255068624645]) 0) 18 true) (.node 712 (sourceLit (List.headD (raw_ints% [9999605064082524393740040334119713268105]) 0) 21 true) (.node 711 (sourceLit (List.headD (raw_ints% [22768148524585147794799875]) 0) 65 false) (.node 710 (sourceLit (List.headD (raw_ints% [12464241739613192044803216539066292519255]) 0) 22 true) .empty .empty) .empty) (.node 713 (sourceLit (List.headD (raw_ints% [9290422843791172478325]) 0) 76 false) .empty .empty)) (.node 716 (sourceLit (List.headD (raw_ints% [44516999033877337483733839488618114034545]) 0) 17 true) (.node 715 (sourceLit (List.headD (raw_ints% [511458936339004954416711]) 0) 70 false) .empty .empty) (.node 717 (sourceLit (List.headD (raw_ints% [14060768342610051613539]) 0) 75 false) .empty .empty)))

#time def treeG_J008_part103 : IntSourceTree :=
  (.node 709 (sourceLit (List.headD (raw_ints% [13818357747316987116975]) 0) 76 false) treeG_J008_part101 treeG_J008_part102)

#time def treeG_J008_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [213402792601251041050838475]) 0) 63 false) (.node 746 (sourceLit (List.headD (raw_ints% [1806081093897478513013711744325]) 0) 62 true) (.node 745 (sourceLit (List.headD (raw_ints% [1649689444102450262192530031093891923911825]) 0) 24 false) (.node 719 (sourceLit (List.headD (raw_ints% [50364532320113409475623]) 0) 73 false) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [401545752656644463673809856383423841437775]) 0) 23 true) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [87851994340047175747066748589770318007255]) 0) 20 true) (.node 750 (sourceLit (List.headD (raw_ints% [79021170945002993761100925]) 0) 64 false) (.node 749 (sourceLit (List.headD (raw_ints% [165330317491972772608860373267422010235505]) 0) 21 true) .empty .empty) .empty) (.node 752 (sourceLit (List.headD (raw_ints% [15466558535342696355621075]) 0) 66 false) .empty .empty)))

#time def treeG_J008_part105 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [143763771860997715197697]) 0) 72 false) (.node 756 (sourceLit (List.headD (raw_ints% [332603578495106981443717]) 0) 71 false) (.node 755 (sourceLit (List.headD (raw_ints% [259842182068747373400959728670028317672415]) 0) 16 true) (.node 754 (sourceLit (List.headD (raw_ints% [1578216160536018737596821]) 0) 69 false) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [570779664877894081485270409704867404287035]) 0) 14 true) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [850706708733032520899132536541811296303925]) 0) 26 false) (.node 759 (sourceLit (List.headD (raw_ints% [690545382855815105012813349846022025270265]) 0) 13 true) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [1806229173995076966735145227975]) 0) 63 true) .empty .empty)))

#time def treeG_J008_part106 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [271664609652572727044807046750703791668355]) 0) 17 true) treeG_J008_part104 treeG_J008_part105)

#time def treeG_J008_part107 : IntSourceTree :=
  (.node 718 (sourceLit (List.headD (raw_ints% [110156081271225076349353996862068852857405]) 0) 15 true) treeG_J008_part103 treeG_J008_part106)

#time def treeG_J008_part108 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [55945256458121648081315829308012231324745]) 0) 16 true) treeG_J008_part100 treeG_J008_part107)

#time def treeG_J008_part109 : IntSourceTree :=
  (.node 793 (sourceLit (List.headD (raw_ints% [10709862039321616046718675]) 0) 67 false) (.node 791 (sourceLit (List.headD (raw_ints% [28126511210208922983150525]) 0) 66 false) (.node 790 (sourceLit (List.headD (raw_ints% [76433037876179790282028578364177858858125]) 0) 23 true) (.node 789 (sourceLit (List.headD (raw_ints% [156802799268240661819708875]) 0) 64 false) .empty .empty) .empty) (.node 792 (sourceLit (List.headD (raw_ints% [38926194637982325676663354127825302369575]) 0) 22 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [107662591517435017958612944590705101818935]) 0) 18 true) (.node 795 (sourceLit (List.headD (raw_ints% [533378612098506891590055]) 0) 71 false) (.node 794 (sourceLit (List.headD (raw_ints% [116095589918357049679761301001724361521855]) 0) 19 true) .empty .empty) .empty) (.node 797 (sourceLit (List.headD (raw_ints% [220117431754226568535405]) 0) 72 false) .empty .empty)))

#time def treeG_J008_part110 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [234584427591478329878316825]) 0) 64 false) (.node 828 (sourceLit (List.headD (raw_ints% [3612671750782755184511341294425]) 0) 63 true) (.node 827 (sourceLit (List.headD (raw_ints% [14012853092385164798059930441052404582300575]) 0) 23 false) (.node 799 (sourceLit (List.headD (raw_ints% [46699619770442152861037]) 0) 74 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [6079835210069171919543026224347572739293295]) 0) 21 true) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [40786463885075149610679975]) 0) 66 false) (.node 831 (sourceLit (List.headD (raw_ints% [1135076611678829468765390505237075423722745]) 0) 20 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [2219611847178296116261647617430115559984445]) 0) 17 true) .empty .empty)))

#time def treeG_J008_part111 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [230311791803334502567958206421399275714815]) 0) 16 true) treeG_J008_part109 treeG_J008_part110)

#time def treeG_J008_part112 : IntSourceTree :=
  (.node 839 (sourceLit (List.headD (raw_ints% [2994443285997536936074517952896366386166775]) 0) 13 true) (.node 837 (sourceLit (List.headD (raw_ints% [2874423263680026493190343817197695853918885]) 0) 14 true) (.node 836 (sourceLit (List.headD (raw_ints% [734153645701906801736393]) 0) 71 false) (.node 835 (sourceLit (List.headD (raw_ints% [1597687256624965421475221087357561466677265]) 0) 16 true) .empty .empty) .empty) (.node 838 (sourceLit (List.headD (raw_ints% [296471091647455421873113]) 0) 72 false) .empty .empty)) (.node 870 (sourceLit (List.headD (raw_ints% [5926969134316812338978969067619217021577045]) 0) 22 true) (.node 869 (sourceLit (List.headD (raw_ints% [903207138395505856293290250825]) 0) 66 true) (.node 868 (sourceLit (List.headD (raw_ints% [14403175937857736341319423353403341754146125]) 0) 24 false) .empty .empty) .empty) (.node 871 (sourceLit (List.headD (raw_ints% [178331405171060483912015775]) 0) 65 false) .empty .empty)))

#time def treeG_J008_part113 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [128509053486920058300247]) 0) 74 false) (.node 875 (sourceLit (List.headD (raw_ints% [5419915269855551005164813]) 0) 69 false) (.node 874 (sourceLit (List.headD (raw_ints% [1987420667341582016902125015426666836940735]) 0) 18 true) (.node 873 (sourceLit (List.headD (raw_ints% [7519150461438383390990325]) 0) 69 false) .empty .empty) .empty) (.node 876 (sourceLit (List.headD (raw_ints% [1382362073590095385557995198176151263039395]) 0) 17 true) .empty .empty)) (.node 879 (sourceLit (List.headD (raw_ints% [203071852106571116151039]) 0) 73 false) (.node 878 (sourceLit (List.headD (raw_ints% [2413799680073357488054427404354897302489255]) 0) 15 true) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [236530650215792953380653799878801040805631295]) 0) 21 false) .empty .empty)))

#time def treeG_J008_part114 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [1057224222402864817412063796981424818983595]) 0) 21 true) treeG_J008_part112 treeG_J008_part113)

#time def treeG_J008_part115 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [7553429718249578571525033]) 0) 68 false) treeG_J008_part111 treeG_J008_part114)

#time def treeG_J008_part116 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [14301678082107690713741779036055773228848615]) 0) 16 true) (.node 913 (sourceLit (List.headD (raw_ints% [31611563269713378040924393885975478647490595]) 0) 17 true) (.node 912 (sourceLit (List.headD (raw_ints% [17193117660748166787666975]) 0) 69 false) (.node 911 (sourceLit (List.headD (raw_ints% [46280676462855669243066362035716660748893615]) 0) 20 true) .empty .empty) .empty) (.node 914 (sourceLit (List.headD (raw_ints% [22523172127503954992436267]) 0) 68 false) .empty .empty)) (.node 918 (sourceLit (List.headD (raw_ints% [731601336247905044528863]) 0) 72 false) (.node 917 (sourceLit (List.headD (raw_ints% [19243369913761499675737579353620724354711435]) 0) 14 true) (.node 916 (sourceLit (List.headD (raw_ints% [3951607978451737401692027]) 0) 70 false) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [16315954154589322968360901281942812033747265]) 0) 13 true) .empty .empty)))

#time def treeG_J008_part117 : IntSourceTree :=
  (.node 955 (sourceLit (List.headD (raw_ints% [8551628428824201993635727]) 0) 70 false) (.node 953 (sourceLit (List.headD (raw_ints% [26867084860057950184343625]) 0) 69 false) (.node 952 (sourceLit (List.headD (raw_ints% [11305863060113201106413574559683808982477505]) 0) 23 true) (.node 951 (sourceLit (List.headD (raw_ints% [28226836027331286676406688825]) 0) 73 true) .empty .empty) .empty) (.node 954 (sourceLit (List.headD (raw_ints% [7406035650592949006005567217637202952637465]) 0) 20 true) .empty .empty)) (.node 957 (sourceLit (List.headD (raw_ints% [2923535550556376935290051]) 0) 71 false) (.node 956 (sourceLit (List.headD (raw_ints% [3229829002129398832045945959469905491452305]) 0) 19 true) .empty .empty) (.node 958 (sourceLit (List.headD (raw_ints% [4207392558422035546920787987316456763055545]) 0) 17 true) .empty .empty)))

#time def treeG_J008_part118 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [60614404837527441429908192236605064456802085]) 0) 24 false) treeG_J008_part116 treeG_J008_part117)

#time def treeG_J008_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [187465686222520025575202962052453227098236085]) 0) 14 true) (.node 995 (sourceLit (List.headD (raw_ints% [222691462736866677478436371928334721255550265]) 0) 16 true) (.node 994 (sourceLit (List.headD (raw_ints% [84945167312727845744938233]) 0) 68 false) (.node 993 (sourceLit (List.headD (raw_ints% [1415538908424776363580013149753552071109630045]) 0) 17 true) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [13151648879196666585579427]) 0) 70 false) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [1385914765822404567555990880883003259299080185]) 0) 18 true) (.node 999 (sourceLit (List.headD (raw_ints% [118320607714915814533104314312183804384030175]) 0) 13 true) (.node 998 (sourceLit (List.headD (raw_ints% [547983553577117972690297]) 0) 74 false) .empty .empty) .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [67841910455079441757666779]) 0) 69 false) .empty .empty)))

#time def treeG_J008_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [6836282696985346896510919]) 0) 73 false) (.node 1039 (sourceLit (List.headD (raw_ints% [415851182541784490595841]) 0) 75 false) (.node 1038 (sourceLit (List.headD (raw_ints% [170636115988831883387519810103187400046013905]) 0) 15 true) (.node 1037 (sourceLit (List.headD (raw_ints% [319628541520009051571543]) 0) 76 false) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [10864626663842369862969490675135691353137091215]) 0) 16 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [2009044778582954439882047]) 0) 74 false) (.node 1077 (sourceLit (List.headD (raw_ints% [3168888661431065288828838447394828361537620635]) 0) 14 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [1246768320195739252567054166513315395984081065]) 0) 13 true) .empty .empty)))

#time def treeG_J008_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [209772146728349082150252588090455099289741045]) 0) 17 true) treeG_J008_part119 treeG_J008_part120)

#time def treeG_J008_part122 : IntSourceTree :=
  (.node 959 (sourceLit (List.headD (raw_ints% [16516546379416685261807]) 0) 78 false) treeG_J008_part118 treeG_J008_part121)

#time def treeG_J008_part123 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [7225891691591638328676200323425]) 0) 64 true) treeG_J008_part115 treeG_J008_part122)

#time def treeG_J008_part124 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [195161422736285771629746456175468585922775]) 0) 25 true) treeG_J008_part108 treeG_J008_part123)

#time def treeG_J008_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [11271952010758705408931944495362851206755]) 0) 17 true) treeG_J008_part093 treeG_J008_part124)

#time def treeG_J008_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [51937282276507492788849123048208755345]) 0) 20 true) treeG_J008_part062 treeG_J008_part125)

#time def treeG_J008 : IntSourceTree := treeG_J008_part126

#time def treeG_J009_part000 : IntSourceTree :=
  (.node 6 (sourceLit (List.headD (raw_ints% [1239752984683616940942996215625]) 0) 43 false) (.node 4 (sourceLit (List.headD (raw_ints% [2608440279774330043744064037675]) 0) 42 false) (.node 3 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 39 false) (.node 2 (sourceLit (List.headD (raw_ints% [11174779188799642072248469888725]) 0) 40 false) .empty .empty) .empty) (.node 5 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)) (.node 9 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 true) (.node 8 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 42 true) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [67451535816963614433728676769275]) 0) 39 true) .empty .empty)))

#time def treeG_J009_part001 : IntSourceTree :=
  (.node 16 (sourceLit (List.headD (raw_ints% [157662380138851915438269558918375]) 0) 35 true) (.node 14 (sourceLit (List.headD (raw_ints% [118460609673363399845821094787825]) 0) 36 true) (.node 13 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 51 false) (.node 12 (sourceLit (List.headD (raw_ints% [50140075958108745149288293249275]) 0) 38 true) .empty .empty) .empty) (.node 15 (sourceLit (List.headD (raw_ints% [17547273013983501317962407975]) 0) 49 false) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [879042010712648108464504705964625]) 0) 32 true) (.node 17 (sourceLit (List.headD (raw_ints% [267519125566095164079607575]) 0) 55 false) .empty .empty) (.node 19 (sourceLit (List.headD (raw_ints% [523187367574069917840510675]) 0) 54 false) .empty .empty)))

#time def treeG_J009_part002 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 46 false) treeG_J009_part000 treeG_J009_part001)

#time def treeG_J009_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [1929496004118470982604725]) 0) 62 false) (.node 23 (sourceLit (List.headD (raw_ints% [62853221735890069666375125]) 0) 57 false) (.node 22 (sourceLit (List.headD (raw_ints% [3472647634330186830053815727372925]) 0) 29 true) (.node 21 (sourceLit (List.headD (raw_ints% [8008107447894527797916625]) 0) 60 false) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [4677031073020811033006240714812575]) 0) 28 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [46751522727167659843728488238089625]) 0) 23 true) (.node 27 (sourceLit (List.headD (raw_ints% [3795097105426786895447775]) 0) 61 false) (.node 26 (sourceLit (List.headD (raw_ints% [46337478763830402500554245374041425]) 0) 24 true) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [116746432651650242534625]) 0) 66 false) .empty .empty)))

#time def treeG_J009_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [6993731494716506523027]) 0) 70 false) (.node 33 (sourceLit (List.headD (raw_ints% [3544129027153840160475]) 0) 71 false) (.node 32 (sourceLit (List.headD (raw_ints% [180784163604276682437549609245544255]) 0) 20 false) (.node 31 (sourceLit (List.headD (raw_ints% [460093620349183422628575]) 0) 64 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [3159339576657817362583067509210313955]) 0) 17 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [53943029583217463117]) 0) 77 false) (.node 36 (sourceLit (List.headD (raw_ints% [9255950542022009307249795170625309975]) 0) 16 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [47194799462658365856675027562090384875]) 0) 14 false) .empty .empty)))

#time def treeG_J009_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [35928115131002330721420093069635295]) 0) 21 true) treeG_J009_part003 treeG_J009_part004)

#time def treeG_J009_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [1241837412573909720047823863043525]) 0) 31 true) treeG_J009_part002 treeG_J009_part005)

#time def treeG_J009_part007 : IntSourceTree :=
  (.node 47 (sourceLit (List.headD (raw_ints% [1239752984683616940942996215625]) 0) 44 false) (.node 45 (sourceLit (List.headD (raw_ints% [2608440279774330043744064037675]) 0) 43 false) (.node 44 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 40 false) (.node 43 (sourceLit (List.headD (raw_ints% [11174779188799642072248469888725]) 0) 41 false) .empty .empty) .empty) (.node 46 (sourceLit (List.headD (raw_ints% [0]) 0) 0 false) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 48 true) (.node 49 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 false) (.node 48 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 43 true) .empty .empty) .empty) (.node 51 (sourceLit (List.headD (raw_ints% [67451535816963614433728676769275]) 0) 40 true) .empty .empty)))

#time def treeG_J009_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [157662380138851915438269558918375]) 0) 36 true) (.node 55 (sourceLit (List.headD (raw_ints% [118460609673363399845821094787825]) 0) 37 true) (.node 54 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 52 false) (.node 53 (sourceLit (List.headD (raw_ints% [50140075958108745149288293249275]) 0) 39 true) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [17547273013983501317962407975]) 0) 50 false) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [879042010712648108464504705964625]) 0) 33 true) (.node 58 (sourceLit (List.headD (raw_ints% [267519125566095164079607575]) 0) 56 false) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [523187367574069917840510675]) 0) 55 false) .empty .empty)))

#time def treeG_J009_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 false) treeG_J009_part007 treeG_J009_part008)

#time def treeG_J009_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [1929496004118470982604725]) 0) 63 false) (.node 64 (sourceLit (List.headD (raw_ints% [62853221735890069666375125]) 0) 58 false) (.node 63 (sourceLit (List.headD (raw_ints% [3472647634330186830053815727372925]) 0) 30 true) (.node 62 (sourceLit (List.headD (raw_ints% [8008107447894527797916625]) 0) 61 false) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [4677031073020811033006240714812575]) 0) 29 true) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [46751522727167659843728488238089625]) 0) 24 true) (.node 68 (sourceLit (List.headD (raw_ints% [3795097105426786895447775]) 0) 62 false) (.node 67 (sourceLit (List.headD (raw_ints% [46337478763830402500554245374041425]) 0) 25 true) .empty .empty) .empty) (.node 70 (sourceLit (List.headD (raw_ints% [116746432651650242534625]) 0) 67 false) .empty .empty)))

#time def treeG_J009_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [6993731494716506523027]) 0) 71 false) (.node 74 (sourceLit (List.headD (raw_ints% [3544129027153840160475]) 0) 72 false) (.node 73 (sourceLit (List.headD (raw_ints% [180784163604276682437549609245544255]) 0) 21 false) (.node 72 (sourceLit (List.headD (raw_ints% [460093620349183422628575]) 0) 65 false) .empty .empty) .empty) (.node 75 (sourceLit (List.headD (raw_ints% [3159339576657817362583067509210313955]) 0) 18 false) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [53943029583217463117]) 0) 78 false) (.node 77 (sourceLit (List.headD (raw_ints% [9255950542022009307249795170625309975]) 0) 17 false) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [47194799462658365856675027562090384875]) 0) 15 false) .empty .empty)))

#time def treeG_J009_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [35928115131002330721420093069635295]) 0) 22 true) treeG_J009_part010 treeG_J009_part011)

#time def treeG_J009_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [1241837412573909720047823863043525]) 0) 32 true) treeG_J009_part009 treeG_J009_part012)

#time def treeG_J009_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [852576952066895984929]) 0) 73 false) treeG_J009_part006 treeG_J009_part013)

#time def treeG_J009_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 44 false) (.node 87 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 42 false) (.node 86 (sourceLit (List.headD (raw_ints% [3977127574865043146545131859725]) 0) 43 false) (.node 85 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 41 false) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [942212268359548875116677123875]) 0) 45 false) .empty .empty)) (.node 92 (sourceLit (List.headD (raw_ints% [489472210577600170320541120904925]) 0) 38 true) (.node 91 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 46 true) (.node 90 (sourceLit (List.headD (raw_ints% [143621959195925039285266364257275]) 0) 39 false) .empty .empty) .empty) (.node 93 (sourceLit (List.headD (raw_ints% [112704816789419721903908746875]) 0) 48 false) .empty .empty)))

#time def treeG_J009_part016 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [1616965636954691394796349925]) 0) 54 false) (.node 97 (sourceLit (List.headD (raw_ints% [13266967004925978692688686775]) 0) 51 false) (.node 96 (sourceLit (List.headD (raw_ints% [790022497248055283328299199384225]) 0) 35 true) (.node 95 (sourceLit (List.headD (raw_ints% [54583809731245120700539190025]) 0) 49 false) .empty .empty) .empty) (.node 98 (sourceLit (List.headD (raw_ints% [4166154153730613185560121179423375]) 0) 32 true) .empty .empty)) (.node 101 (sourceLit (List.headD (raw_ints% [395057648407757473073844675]) 0) 56 false) (.node 100 (sourceLit (List.headD (raw_ints% [5790498673127275147668213784673475]) 0) 31 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [16396750966852368690711366081323475]) 0) 29 true) .empty .empty)))

#time def treeG_J009_part017 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [683780605656376522542791597200575]) 0) 36 true) treeG_J009_part015 treeG_J009_part016)

#time def treeG_J009_part018 : IntSourceTree :=
  (.node 108 (sourceLit (List.headD (raw_ints% [323948307383475560160705474754241775]) 0) 23 true) (.node 106 (sourceLit (List.headD (raw_ints% [252992509909501503611845160373963375]) 0) 24 true) (.node 105 (sourceLit (List.headD (raw_ints% [47417253702942301805537325]) 0) 59 false) (.node 104 (sourceLit (List.headD (raw_ints% [23104150001620683607424285104170825]) 0) 28 true) .empty .empty) .empty) (.node 107 (sourceLit (List.headD (raw_ints% [11640870927520980965390025]) 0) 61 false) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [1407849302077220457925425]) 0) 64 false) (.node 110 (sourceLit (List.headD (raw_ints% [712096248503680226778235718739798705]) 0) 21 true) (.node 109 (sourceLit (List.headD (raw_ints% [2861125644213584955170775]) 0) 63 false) .empty .empty) .empty) (.node 112 (sourceLit (List.headD (raw_ints% [468209084652295328208910353802626615]) 0) 20 true) .empty .empty)))

#time def treeG_J009_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [100900409209693783059321695167914574725]) 0) 14 false) (.node 116 (sourceLit (List.headD (raw_ints% [16018766071240529593414744903057201665]) 0) 16 false) (.node 115 (sourceLit (List.headD (raw_ints% [21359300722514214760773]) 0) 70 false) (.node 114 (sourceLit (List.headD (raw_ints% [2625753658679036475418519986647102205]) 0) 17 false) .empty .empty) .empty) (.node 117 (sourceLit (List.headD (raw_ints% [5267554548053547703283]) 0) 72 false) .empty .empty)) (.node 125 (sourceLit (List.headD (raw_ints% [5957898629250981984760341813375]) 0) 43 false) (.node 119 (sourceLit (List.headD (raw_ints% [2599776941259021654559]) 0) 73 false) .empty .empty) (.node 126 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 42 false) .empty .empty)))

#time def treeG_J009_part020 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [346681491480260537493375]) 0) 66 false) treeG_J009_part018 treeG_J009_part019)

#time def treeG_J009_part021 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [193406216596734819866956875]) 0) 57 false) treeG_J009_part017 treeG_J009_part020)

#time def treeG_J009_part022 : IntSourceTree :=
  (.node 132 (sourceLit (List.headD (raw_ints% [743851790810170164565797729375]) 0) 48 true) (.node 130 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 45 false) (.node 129 (sourceLit (List.headD (raw_ints% [644671552035480809290358032125]) 0) 46 false) (.node 128 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 44 false) .empty .empty) .empty) (.node 131 (sourceLit (List.headD (raw_ints% [105536747506444326859497520513275]) 0) 41 false) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [282659997991506561348485251206375]) 0) 38 true) (.node 134 (sourceLit (List.headD (raw_ints% [76639275416805410894657947875]) 0) 49 false) (.node 133 (sourceLit (List.headD (raw_ints% [219666067309745712585626413827825]) 0) 40 true) .empty .empty) .empty) (.node 136 (sourceLit (List.headD (raw_ints% [18518268358630809691288391025]) 0) 51 false) .empty .empty)))

#time def treeG_J009_part023 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [266927929241445028307178675]) 0) 57 false) (.node 140 (sourceLit (List.headD (raw_ints% [546889134690310738477919625]) 0) 56 false) (.node 139 (sourceLit (List.headD (raw_ints% [1643556071508982538547808236729375]) 0) 34 true) (.node 138 (sourceLit (List.headD (raw_ints% [8986660995868456067414965575]) 0) 52 false) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [2274330630276682713810194960814975]) 0) 33 true) .empty .empty)) (.node 144 (sourceLit (List.headD (raw_ints% [65276497430422375100290875]) 0) 59 false) (.node 143 (sourceLit (List.headD (raw_ints% [6462051666261090930328775176975275]) 0) 31 true) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [9213559464299936287209022194679125]) 0) 30 true) .empty .empty)))

#time def treeG_J009_part024 : IntSourceTree :=
  (.node 137 (sourceLit (List.headD (raw_ints% [316180058554601683945014820232925]) 0) 37 true) treeG_J009_part022 treeG_J009_part023)

#time def treeG_J009_part025 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [338084066686338948028407812835081705]) 0) 23 true) (.node 149 (sourceLit (List.headD (raw_ints% [138598392328153950158488493258076075]) 0) 25 true) (.node 148 (sourceLit (List.headD (raw_ints% [3922886911047097034971125]) 0) 63 false) (.node 147 (sourceLit (List.headD (raw_ints% [103327515572835550555645457499960975]) 0) 26 true) .empty .empty) .empty) (.node 150 (sourceLit (List.headD (raw_ints% [1927154183000383014893775]) 0) 64 false) .empty .empty)) (.node 153 (sourceLit (List.headD (raw_ints% [324496624128286005323229981524085435]) 0) 22 true) (.node 152 (sourceLit (List.headD (raw_ints% [473877840864018517648425]) 0) 66 false) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [233269362611337652358175]) 0) 67 false) .empty .empty)))

#time def treeG_J009_part026 : IntSourceTree :=
  (.node 166 (sourceLit (List.headD (raw_ints% [7938669683636920822975551767025]) 0) 43 false) (.node 158 (sourceLit (List.headD (raw_ints% [3541377601390588883539]) 0) 73 false) (.node 157 (sourceLit (List.headD (raw_ints% [3381407764609260143082474866215945845]) 0) 18 false) (.node 156 (sourceLit (List.headD (raw_ints% [7182784613898854118873]) 0) 72 false) .empty .empty) .empty) (.node 159 (sourceLit (List.headD (raw_ints% [26852804873517708601323333802912094925]) 0) 16 false) .empty .empty)) (.node 168 (sourceLit (List.headD (raw_ints% [1795162321821877330485458520225]) 0) 45 false) (.node 167 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 42 false) .empty .empty) (.node 169 (sourceLit (List.headD (raw_ints% [1934014656106442427871074096375]) 0) 44 false) .empty .empty)))

#time def treeG_J009_part027 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [266792958989390443582273761281605875]) 0) 19 true) treeG_J009_part025 treeG_J009_part026)

#time def treeG_J009_part028 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [31981285669994533944699525]) 0) 60 false) treeG_J009_part024 treeG_J009_part027)

#time def treeG_J009_part029 : IntSourceTree :=
  (.node 127 (sourceLit (List.headD (raw_ints% [684343647545356551400533911025]) 0) 46 false) treeG_J009_part021 treeG_J009_part028)

#time def treeG_J009_part030 : IntSourceTree :=
  (.node 84 (sourceLit (List.headD (raw_ints% [4283169454512656014252202925525]) 0) 43 false) treeG_J009_part014 treeG_J009_part029)

#time def treeG_J009_part031 : IntSourceTree :=
  (.node 175 (sourceLit (List.headD (raw_ints% [98694741102365701088776705725]) 0) 49 false) (.node 173 (sourceLit (List.headD (raw_ints% [1600408398409760051035504205625]) 0) 48 true) (.node 172 (sourceLit (List.headD (raw_ints% [2178060170680709400072501449117325]) 0) 38 false) (.node 171 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 47 false) .empty .empty) .empty) (.node 174 (sourceLit (List.headD (raw_ints% [6345533548255486280197253645289825]) 0) 36 true) .empty .empty)) (.node 178 (sourceLit (List.headD (raw_ints% [16069369593763894586920827315483825]) 0) 32 true) (.node 177 (sourceLit (List.headD (raw_ints% [23769569712335640689888095275]) 0) 51 false) (.node 176 (sourceLit (List.headD (raw_ints% [3732537470616049698247464819917775]) 0) 35 true) .empty .empty) .empty) (.node 179 (sourceLit (List.headD (raw_ints% [5752729721959073277822265725]) 0) 53 false) .empty .empty)))

#time def treeG_J009_part032 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [83135741157902448395044425]) 0) 59 false) (.node 183 (sourceLit (List.headD (raw_ints% [340449641886155236747400475]) 0) 57 false) (.node 182 (sourceLit (List.headD (raw_ints% [56381829202001478151214872664755725]) 0) 29 true) (.node 181 (sourceLit (List.headD (raw_ints% [698720620972864003881994575]) 0) 56 false) .empty .empty) .empty) (.node 184 (sourceLit (List.headD (raw_ints% [80288676658556771277836117727433575]) 0) 28 true) .empty .empty)) (.node 187 (sourceLit (List.headD (raw_ints% [5085103685618388244827375]) 0) 63 false) (.node 186 (sourceLit (List.headD (raw_ints% [926343101520890341150909680544964625]) 0) 24 true) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [1329291941781893248729621845245133825]) 0) 23 true) .empty .empty)))

#time def treeG_J009_part033 : IntSourceTree :=
  (.node 180 (sourceLit (List.headD (raw_ints% [20506398471016445469096718002996525]) 0) 31 true) treeG_J009_part031 treeG_J009_part032)

#time def treeG_J009_part034 : IntSourceTree :=
  (.node 194 (sourceLit (List.headD (raw_ints% [23393537602889340816105238804188570045]) 0) 17 true) (.node 192 (sourceLit (List.headD (raw_ints% [4941135982329127840245614651558680665]) 0) 20 true) (.node 191 (sourceLit (List.headD (raw_ints% [2446459063923545571862125]) 0) 64 false) (.node 190 (sourceLit (List.headD (raw_ints% [3723052305997246178293396065518635695]) 0) 21 true) .empty .empty) .empty) (.node 193 (sourceLit (List.headD (raw_ints% [601074190247776497803475]) 0) 66 false) .empty .empty)) (.node 197 (sourceLit (List.headD (raw_ints% [9098014679744160534463]) 0) 72 false) (.node 196 (sourceLit (List.headD (raw_ints% [20287453415070776690731125083562895665]) 0) 16 true) (.node 195 (sourceLit (List.headD (raw_ints% [147832159721280793315083]) 0) 68 false) .empty .empty) .empty) (.node 198 (sourceLit (List.headD (raw_ints% [7304639257802541519317500550995692315]) 0) 14 false) .empty .empty)))

#time def treeG_J009_part035 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [189659536887730605825929749059825]) 0) 40 true) (.node 209 (sourceLit (List.headD (raw_ints% [287622692446599130298775122025]) 0) 48 false) (.node 208 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 43 false) (.node 207 (sourceLit (List.headD (raw_ints% [5201295093455494617373416122925]) 0) 44 false) .empty .empty) .empty) (.node 210 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 false) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [2617392305300200825243754276772975]) 0) 39 false) (.node 212 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 49 false) .empty .empty) (.node 214 (sourceLit (List.headD (raw_ints% [419261918456641365482540538375]) 0) 51 true) .empty .empty)))

#time def treeG_J009_part036 : IntSourceTree :=
  (.node 199 (sourceLit (List.headD (raw_ints% [4482978261522156112519]) 0) 73 false) treeG_J009_part034 treeG_J009_part035)

#time def treeG_J009_part037 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [4984648177880609114771475]) 0) 63 false) treeG_J009_part033 treeG_J009_part036)

#time def treeG_J009_part038 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [3565173183197830323910587225]) 0) 54 false) (.node 218 (sourceLit (List.headD (raw_ints% [3695727179116796155618282425]) 0) 54 false) (.node 217 (sourceLit (List.headD (raw_ints% [3100177353506846330357435179451925]) 0) 36 true) (.node 216 (sourceLit (List.headD (raw_ints% [61658204385104081706199923675]) 0) 50 false) .empty .empty) .empty) (.node 219 (sourceLit (List.headD (raw_ints% [12782257450745929509825210842025075]) 0) 33 true) .empty .empty)) (.node 223 (sourceLit (List.headD (raw_ints% [43457725869479296290557322310805175]) 0) 30 true) (.node 222 (sourceLit (List.headD (raw_ints% [107948172932854743893703975]) 0) 59 false) (.node 221 (sourceLit (List.headD (raw_ints% [15957737210463080041476328081366575]) 0) 32 true) .empty .empty) .empty) (.node 224 (sourceLit (List.headD (raw_ints% [209896647025310486546818725]) 0) 58 false) .empty .empty)))

#time def treeG_J009_part039 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [764373498720056524969425]) 0) 66 false) (.node 228 (sourceLit (List.headD (raw_ints% [6247320460189679454683625]) 0) 63 false) (.node 227 (sourceLit (List.headD (raw_ints% [719688070375219240039618765545042675]) 0) 25 true) (.node 226 (sourceLit (List.headD (raw_ints% [12788613871976978612586225]) 0) 62 false) .empty .empty) .empty) (.node 229 (sourceLit (List.headD (raw_ints% [1052095157125585348412644858728981675]) 0) 24 true) .empty .empty)) (.node 232 (sourceLit (List.headD (raw_ints% [1498703382195508536565275]) 0) 65 false) (.node 231 (sourceLit (List.headD (raw_ints% [3046884172624568282236580439848472285]) 0) 22 true) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [4292142734072555829599154688510509795]) 0) 21 true) .empty .empty)))

#time def treeG_J009_part040 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [61861557729956898703418073338075325]) 0) 29 true) treeG_J009_part038 treeG_J009_part039)

#time def treeG_J009_part041 : IntSourceTree :=
  (.node 239 (sourceLit (List.headD (raw_ints% [46400970489232875683329167054828497535]) 0) 15 true) (.node 237 (sourceLit (List.headD (raw_ints% [27050268944289296976896074815994787355]) 0) 17 true) (.node 236 (sourceLit (List.headD (raw_ints% [90369882810089960364099]) 0) 69 false) (.node 235 (sourceLit (List.headD (raw_ints% [22859951684910559928940691281625358295]) 0) 18 true) .empty .empty) .empty) (.node 238 (sourceLit (List.headD (raw_ints% [1389159269588392912731]) 0) 75 false) .empty .empty)) (.node 250 (sourceLit (List.headD (raw_ints% [273111678940159461532880432986875]) 0) 39 false) (.node 249 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 46 false) (.node 248 (sourceLit (List.headD (raw_ints% [851533192908404321721989400675]) 0) 47 false) .empty .empty) .empty) (.node 251 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 47 true) .empty .empty)))

#time def treeG_J009_part042 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [2368039667048027563519489275]) 0) 55 false) (.node 255 (sourceLit (List.headD (raw_ints% [3452790088755496624949101012725]) 0) 49 true) (.node 254 (sourceLit (List.headD (raw_ints% [48223810433058699484097322073657425]) 0) 36 false) (.node 253 (sourceLit (List.headD (raw_ints% [5765978426946712972603971490125]) 0) 48 false) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [42509170947563735561754800323098825]) 0) 35 true) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [9030178994508111344650863975]) 0) 53 false) (.node 258 (sourceLit (List.headD (raw_ints% [83136305718455187984517098426977775]) 0) 32 true) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [81751661134950990609504968733204075]) 0) 31 true) .empty .empty)))

#time def treeG_J009_part043 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [3695336465782554246679939441595925]) 0) 38 true) treeG_J009_part041 treeG_J009_part042)

#time def treeG_J009_part044 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [91951206909109711361325]) 0) 69 false) treeG_J009_part040 treeG_J009_part043)

#time def treeG_J009_part045 : IntSourceTree :=
  (.node 215 (sourceLit (List.headD (raw_ints% [5780213552272473157500283142877075]) 0) 37 true) treeG_J009_part037 treeG_J009_part044)

#time def treeG_J009_part046 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [3032796593196351175867847013091856175]) 0) 24 true) (.node 264 (sourceLit (List.headD (raw_ints% [267373130297277599046622460759007825]) 0) 28 true) (.node 263 (sourceLit (List.headD (raw_ints% [523135741576682714402231325]) 0) 57 false) (.node 262 (sourceLit (List.headD (raw_ints% [198941966165407802512406376637109475]) 0) 29 true) .empty .empty) .empty) (.node 265 (sourceLit (List.headD (raw_ints% [31690226466852009537943575]) 0) 61 false) .empty .empty)) (.node 269 (sourceLit (List.headD (raw_ints% [7509992742498749794595775]) 0) 63 false) (.node 268 (sourceLit (List.headD (raw_ints% [4428212621219860671587328279115207575]) 0) 23 true) (.node 267 (sourceLit (List.headD (raw_ints% [3851755093179295183879425]) 0) 64 false) .empty .empty) .empty) (.node 270 (sourceLit (List.headD (raw_ints% [13110470208012119396308921674145071105]) 0) 21 true) .empty .empty)))

#time def treeG_J009_part047 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [162592160064213702740794405169439970695]) 0) 16 true) (.node 274 (sourceLit (List.headD (raw_ints% [113955029887432445731067711228147743395]) 0) 17 true) (.node 273 (sourceLit (List.headD (raw_ints% [112203648993466504845225]) 0) 69 false) (.node 272 (sourceLit (List.headD (raw_ints% [19433937398667418417647028867229097615]) 0) 20 true) .empty .empty) .empty) (.node 275 (sourceLit (List.headD (raw_ints% [219972667915158052130217]) 0) 68 false) .empty .empty)) (.node 278 (sourceLit (List.headD (raw_ints% [440108942366431293149654697606912289995]) 0) 14 true) (.node 277 (sourceLit (List.headD (raw_ints% [53977824091113318226247]) 0) 70 false) .empty .empty) (.node 279 (sourceLit (List.headD (raw_ints% [6630295895184987189329]) 0) 73 false) .empty .empty)))

#time def treeG_J009_part048 : IntSourceTree :=
  (.node 271 (sourceLit (List.headD (raw_ints% [3668528925836906627893275]) 0) 64 false) treeG_J009_part046 treeG_J009_part047)

#time def treeG_J009_part049 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [7443026100773278434534133643625]) 0) 49 false) (.node 292 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 48 true) (.node 291 (sourceLit (List.headD (raw_ints% [115692803956972516839702545511675]) 0) 42 false) (.node 290 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 50 false) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [1578182192770688767980923429592225]) 0) 41 true) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [9852248398514222307849341285911725]) 0) 38 true) (.node 296 (sourceLit (List.headD (raw_ints% [219653018321287544165956308525]) 0) 54 true) (.node 295 (sourceLit (List.headD (raw_ints% [13501005996332793160399401304133625]) 0) 39 false) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [5776431489075314098459674675]) 0) 54 false) .empty .empty)))

#time def treeG_J009_part050 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [39154886818921528481926575]) 0) 61 false) (.node 302 (sourceLit (List.headD (raw_ints% [1304146557789264364996966275]) 0) 56 false) (.node 301 (sourceLit (List.headD (raw_ints% [16448480981121977642007160162959375]) 0) 34 true) (.node 300 (sourceLit (List.headD (raw_ints% [2732502905655140510370138375]) 0) 55 false) .empty .empty) .empty) (.node 303 (sourceLit (List.headD (raw_ints% [38871060073982126555462263581576075]) 0) 32 true) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [9450806297437515462678675]) 0) 63 false) (.node 305 (sourceLit (List.headD (raw_ints% [51377893141830175085801096855233125]) 0) 31 true) .empty .empty) (.node 307 (sourceLit (List.headD (raw_ints% [578277130705282983957057061886703375]) 0) 27 true) .empty .empty)))

#time def treeG_J009_part051 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [17588512066927314618672971896238175]) 0) 35 true) treeG_J009_part049 treeG_J009_part050)

#time def treeG_J009_part052 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [281955250230902595711607139325]) 0) 49 false) treeG_J009_part048 treeG_J009_part051)

#time def treeG_J009_part053 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [3785448666148715647011968544679646955]) 0) 23 true) (.node 311 (sourceLit (List.headD (raw_ints% [2515896508846887778518085308574149705]) 0) 24 true) (.node 310 (sourceLit (List.headD (raw_ints% [4452498747618523694718075]) 0) 64 false) (.node 309 (sourceLit (List.headD (raw_ints% [844029366023568830793670855096556475]) 0) 26 true) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [4237940514924605647125]) 0) 74 false) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [64801392552534045883059]) 0) 70 false) (.node 315 (sourceLit (List.headD (raw_ints% [22773769550630471450531754986630596275]) 0) 20 true) (.node 314 (sourceLit (List.headD (raw_ints% [132456091077823298329125]) 0) 69 false) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [33885472779981101440974582588361295835]) 0) 19 true) .empty .empty)))

#time def treeG_J009_part054 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [12014333469752142354956672416875]) 0) 48 true) (.node 331 (sourceLit (List.headD (raw_ints% [3421718237726782757002669555125]) 0) 47 false) (.node 330 (sourceLit (List.headD (raw_ints% [304332673532729054484490988350725]) 0) 39 false) (.node 319 (sourceLit (List.headD (raw_ints% [98426992969299604366581382638020948115]) 0) 17 true) .empty .empty) .empty) (.node 332 (sourceLit (List.headD (raw_ints% [7397506192405674785550420897969525]) 0) 38 false) .empty .empty)) (.node 335 (sourceLit (List.headD (raw_ints% [18338842290302053494017368299975]) 0) 49 false) (.node 334 (sourceLit (List.headD (raw_ints% [149227470770382780634876421567559825]) 0) 36 true) .empty .empty) (.node 336 (sourceLit (List.headD (raw_ints% [474541362830213116694535642055374825]) 0) 35 false) .empty .empty)))

#time def treeG_J009_part055 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [31751275777699031622551]) 0) 71 false) treeG_J009_part053 treeG_J009_part054)

#time def treeG_J009_part056 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [853760816626398766576051873792290525]) 0) 29 true) (.node 340 (sourceLit (List.headD (raw_ints% [481080725006723077188030131946417525]) 0) 31 true) (.node 339 (sourceLit (List.headD (raw_ints% [14075546961793145049187834725]) 0) 53 false) (.node 338 (sourceLit (List.headD (raw_ints% [1177951489291365267420198586169723025]) 0) 32 true) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [3297273870058178704593678675]) 0) 55 false) .empty .empty)) (.node 344 (sourceLit (List.headD (raw_ints% [976500792070150450728169973851426575]) 0) 28 true) (.node 343 (sourceLit (List.headD (raw_ints% [390505408106290825297367475]) 0) 58 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [46619547170991047425909575]) 0) 61 false) .empty .empty)))

#time def treeG_J009_part057 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [5236468569400140761542875]) 0) 64 false) (.node 349 (sourceLit (List.headD (raw_ints% [10809407082556252767072375]) 0) 63 false) (.node 348 (sourceLit (List.headD (raw_ints% [14076655561349194815038497701259300425]) 0) 23 true) (.node 347 (sourceLit (List.headD (raw_ints% [2799525602129110139399625]) 0) 65 false) .empty .empty) .empty) (.node 350 (sourceLit (List.headD (raw_ints% [40907409217496285774486013052034543295]) 0) 21 true) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [159024543961708256570775]) 0) 69 false) (.node 352 (sourceLit (List.headD (raw_ints% [61074750884432990494931701007143692945]) 0) 20 true) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [370582399379603157086464262490847066845]) 0) 17 true) .empty .empty)))

#time def treeG_J009_part058 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [10119944051112173646097233781847823825]) 0) 24 true) treeG_J009_part056 treeG_J009_part057)

#time def treeG_J009_part059 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [27752632248541946466184474725]) 0) 58 true) treeG_J009_part055 treeG_J009_part058)

#time def treeG_J009_part060 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [9159699912527501280834075]) 0) 63 false) treeG_J009_part052 treeG_J009_part059)

#time def treeG_J009_part061 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [2167731941252102316146598075]) 0) 55 false) treeG_J009_part045 treeG_J009_part060)

#time def treeG_J009_part062 : IntSourceTree :=
  (.node 170 (sourceLit (List.headD (raw_ints% [21413958125158047893065291966725]) 0) 39 false) treeG_J009_part030 treeG_J009_part061)

#time def treeG_J009_part063 : IntSourceTree :=
  (.node 371 (sourceLit (List.headD (raw_ints% [158438542295161012874319193695975]) 0) 40 true) (.node 358 (sourceLit (List.headD (raw_ints% [1728561315552359199072718588048210643445]) 0) 14 true) (.node 357 (sourceLit (List.headD (raw_ints% [75624961013954773539871]) 0) 70 false) (.node 356 (sourceLit (List.headD (raw_ints% [566168465555961383676221754402739110105]) 0) 16 true) .empty .empty) .empty) (.node 359 (sourceLit (List.headD (raw_ints% [18490683987329057243893]) 0) 72 false) .empty .empty)) (.node 374 (sourceLit (List.headD (raw_ints% [4864339892631355197372701515125]) 0) 51 true) (.node 373 (sourceLit (List.headD (raw_ints% [13710234963488429857474114616338425]) 0) 39 false) (.node 372 (sourceLit (List.headD (raw_ints% [1636473939782374362044755004625]) 0) 50 false) .empty .empty) .empty) (.node 375 (sourceLit (List.headD (raw_ints% [203231494755713953276474026784094325]) 0) 37 true) .empty .empty)))

#time def treeG_J009_part064 : IntSourceTree :=
  (.node 381 (sourceLit (List.headD (raw_ints% [415286801082235166620001491294580025]) 0) 32 true) (.node 379 (sourceLit (List.headD (raw_ints% [1107597441023656008945506698584770325]) 0) 33 true) (.node 378 (sourceLit (List.headD (raw_ints% [893860663442417601016362865875]) 0) 54 true) (.node 377 (sourceLit (List.headD (raw_ints% [513950356424270005925933007199021725]) 0) 36 false) .empty .empty) .empty) (.node 380 (sourceLit (List.headD (raw_ints% [8610541150482864028447557975]) 0) 54 false) .empty .empty)) (.node 383 (sourceLit (List.headD (raw_ints% [698276576330470260354202819465986225]) 0) 30 true) (.node 382 (sourceLit (List.headD (raw_ints% [124570457016807146224794525]) 0) 60 false) .empty .empty) (.node 384 (sourceLit (List.headD (raw_ints% [233885860830604711369661175]) 0) 59 false) .empty .empty)))

#time def treeG_J009_part065 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [21853290583442654200672669236375]) 0) 50 false) treeG_J009_part063 treeG_J009_part064)

#time def treeG_J009_part066 : IntSourceTree :=
  (.node 390 (sourceLit (List.headD (raw_ints% [1589227083734432268088575]) 0) 66 false) (.node 388 (sourceLit (List.headD (raw_ints% [13236504904505379834362925]) 0) 63 false) (.node 387 (sourceLit (List.headD (raw_ints% [7806835528291041710269005534301010325]) 0) 25 true) (.node 386 (sourceLit (List.headD (raw_ints% [27717934576116016500552225]) 0) 62 false) .empty .empty) .empty) (.node 389 (sourceLit (List.headD (raw_ints% [10700538097254919491863814280873074525]) 0) 24 true) .empty .empty)) (.node 393 (sourceLit (List.headD (raw_ints% [45932956219838127906883826828425105125]) 0) 21 true) (.node 392 (sourceLit (List.headD (raw_ints% [3066643025758742670214875]) 0) 65 false) (.node 391 (sourceLit (List.headD (raw_ints% [30843823182108734660413671817737944475]) 0) 22 true) .empty .empty) .empty) (.node 394 (sourceLit (List.headD (raw_ints% [185592996845593214812425]) 0) 69 false) .empty .empty)))

#time def treeG_J009_part067 : IntSourceTree :=
  (.node 412 (sourceLit (List.headD (raw_ints% [8665014530766962888544974447537325]) 0) 38 true) (.node 398 (sourceLit (List.headD (raw_ints% [5484210654531967739665]) 0) 74 false) (.node 397 (sourceLit (List.headD (raw_ints% [430626574436036977912323424049293926765]) 0) 17 true) (.node 396 (sourceLit (List.headD (raw_ints% [180248911291067049420165]) 0) 69 false) .empty .empty) .empty) (.node 399 (sourceLit (List.headD (raw_ints% [1334853343675160781606393057496126850985]) 0) 15 true) .empty .empty)) (.node 414 (sourceLit (List.headD (raw_ints% [368591230186197658354462255428974625]) 0) 36 false) (.node 413 (sourceLit (List.headD (raw_ints% [25106124988011137251314712453875]) 0) 48 false) .empty .empty) (.node 415 (sourceLit (List.headD (raw_ints% [57253561431352895072998980420975]) 0) 49 true) .empty .empty)))

#time def treeG_J009_part068 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [279487321177081271284337242544324681745]) 0) 18 true) treeG_J009_part066 treeG_J009_part067)

#time def treeG_J009_part069 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [770989219502829750384965586430494075]) 0) 29 true) treeG_J009_part065 treeG_J009_part068)

#time def treeG_J009_part070 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [1328316820106171330963469825]) 0) 57 false) (.node 419 (sourceLit (List.headD (raw_ints% [3589518200731463549114639298225]) 0) 53 true) (.node 418 (sourceLit (List.headD (raw_ints% [17624362894868005457050054816538418225]) 0) 32 false) (.node 417 (sourceLit (List.headD (raw_ints% [25405627511256023348344282001175]) 0) 51 false) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [8379698803182524994376023456731745075]) 0) 31 true) .empty .empty)) (.node 424 (sourceLit (List.headD (raw_ints% [4609711818573611632105452581876463225]) 0) 28 true) (.node 423 (sourceLit (List.headD (raw_ints% [606058248028166344500988725]) 0) 58 false) (.node 422 (sourceLit (List.headD (raw_ints% [5790828000689363899343971986920989875]) 0) 29 true) .empty .empty) .empty) (.node 425 (sourceLit (List.headD (raw_ints% [140646766488622616517842025]) 0) 60 false) .empty .empty)))

#time def treeG_J009_part071 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [7477348100475317383165725]) 0) 64 false) (.node 429 (sourceLit (List.headD (raw_ints% [15663602726454506901653475]) 0) 63 false) (.node 428 (sourceLit (List.headD (raw_ints% [48378028664979138867113546573148782175]) 0) 23 true) (.node 427 (sourceLit (List.headD (raw_ints% [16519832167599575942953725]) 0) 63 false) .empty .empty) .empty) (.node 430 (sourceLit (List.headD (raw_ints% [130301200338582426095335015441934649105]) 0) 21 true) .empty .empty)) (.node 433 (sourceLit (List.headD (raw_ints% [1794446674065076617648675]) 0) 66 false) (.node 432 (sourceLit (List.headD (raw_ints% [185675834572436886788377673534759862855]) 0) 20 true) .empty .empty) (.node 434 (sourceLit (List.headD (raw_ints% [1099272199655216935933818196018756297155]) 0) 17 true) .empty .empty)))

#time def treeG_J009_part072 : IntSourceTree :=
  (.node 426 (sourceLit (List.headD (raw_ints% [39223365997068930378540563749703796975]) 0) 24 true) treeG_J009_part070 treeG_J009_part071)

#time def treeG_J009_part073 : IntSourceTree :=
  (.node 454 (sourceLit (List.headD (raw_ints% [44563484558536558040805518514375]) 0) 49 false) (.node 438 (sourceLit (List.headD (raw_ints% [5161463875424232447524456196740492184795]) 0) 14 true) (.node 437 (sourceLit (List.headD (raw_ints% [52311975138556137940147]) 0) 71 false) (.node 436 (sourceLit (List.headD (raw_ints% [1669730103860688786598476185951858343855]) 0) 16 true) .empty .empty) .empty) (.node 439 (sourceLit (List.headD (raw_ints% [25383001248926684673427]) 0) 72 false) .empty .empty)) (.node 457 (sourceLit (List.headD (raw_ints% [1307171838650097374416130431763575575]) 0) 37 true) (.node 456 (sourceLit (List.headD (raw_ints% [39553426007397774636835824828675]) 0) 51 true) (.node 455 (sourceLit (List.headD (raw_ints% [285911362470955805815468141106534475]) 0) 38 false) .empty .empty) .empty) (.node 458 (sourceLit (List.headD (raw_ints% [28981070165025693752409733464675]) 0) 52 false) .empty .empty)))

#time def treeG_J009_part074 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [186086193598780816565663775]) 0) 60 false) (.node 462 (sourceLit (List.headD (raw_ints% [830034992038942746064291725]) 0) 58 false) (.node 461 (sourceLit (List.headD (raw_ints% [3982206001050144913878010982718582525]) 0) 33 true) (.node 460 (sourceLit (List.headD (raw_ints% [449766092735243301642885857025]) 0) 57 true) .empty .empty) .empty) (.node 463 (sourceLit (List.headD (raw_ints% [2546275712179446819494884583727501825]) 0) 31 true) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [85210897336390583516737575]) 0) 61 false) (.node 465 (sourceLit (List.headD (raw_ints% [1919361299535390940860243497722984575]) 0) 30 true) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [15708265234388944334135779107701393325]) 0) 26 true) .empty .empty)))

#time def treeG_J009_part075 : IntSourceTree :=
  (.node 459 (sourceLit (List.headD (raw_ints% [9365980167945830732997780757561594275]) 0) 34 false) treeG_J009_part073 treeG_J009_part074)

#time def treeG_J009_part076 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [432520290986237718063417]) 0) 68 false) treeG_J009_part072 treeG_J009_part075)

#time def treeG_J009_part077 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [2100393320875924742906327856328129425]) 0) 35 true) treeG_J009_part069 treeG_J009_part076)

#time def treeG_J009_part078 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [69871439176299379440746923353167378865]) 0) 22 true) (.node 471 (sourceLit (List.headD (raw_ints% [49728688578236845717460671812098352315]) 0) 23 true) (.node 470 (sourceLit (List.headD (raw_ints% [9306694391516777829299175]) 0) 64 false) (.node 469 (sourceLit (List.headD (raw_ints% [18838745283862109687624866146137853825]) 0) 25 true) .empty .empty) .empty) (.node 472 (sourceLit (List.headD (raw_ints% [2205352537358287356475425]) 0) 66 false) .empty .empty)) (.node 476 (sourceLit (List.headD (raw_ints% [63067844923792667160813]) 0) 71 false) (.node 475 (sourceLit (List.headD (raw_ints% [409892439239067832324740476737215807705]) 0) 19 true) (.node 474 (sourceLit (List.headD (raw_ints% [1052074686682703758398975]) 0) 67 false) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [619551764712325904343076380951282208545]) 0) 18 true) .empty .empty)))

#time def treeG_J009_part079 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [101283360568474237419682402449407255025]) 0) 32 true) (.node 496 (sourceLit (List.headD (raw_ints% [6674975120411217635953818114032681025]) 0) 35 false) (.node 495 (sourceLit (List.headD (raw_ints% [146380530548426011154610017449725]) 0) 49 false) (.node 479 (sourceLit (List.headD (raw_ints% [1913305265874535832959031569622182666905]) 0) 16 true) .empty .empty) .empty) (.node 497 (sourceLit (List.headD (raw_ints% [104512479526051572622015931658525]) 0) 51 true) .empty .empty)) (.node 500 (sourceLit (List.headD (raw_ints% [158235381490315816722340515577717253475]) 0) 31 false) (.node 499 (sourceLit (List.headD (raw_ints% [8142647091439289325381093190725]) 0) 55 false) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [900860502290592774616735183875]) 0) 57 true) .empty .empty)))

#time def treeG_J009_part080 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [30375132520428266981487]) 0) 72 false) treeG_J009_part078 treeG_J009_part079)

#time def treeG_J009_part081 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [52171233001191431630830125]) 0) 62 false) (.node 505 (sourceLit (List.headD (raw_ints% [231525620708939016613485525]) 0) 60 false) (.node 504 (sourceLit (List.headD (raw_ints% [36130699576297537479812700757763565975]) 0) 28 true) (.node 503 (sourceLit (List.headD (raw_ints% [1054011736049719147627594725]) 0) 58 false) .empty .empty) .empty) (.node 506 (sourceLit (List.headD (raw_ints% [206454880343461110051570603958838228625]) 0) 24 true) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [472538648745005083908660701234476673295]) 0) 21 true) (.node 509 (sourceLit (List.headD (raw_ints% [23942716134933037201435575]) 0) 63 false) (.node 508 (sourceLit (List.headD (raw_ints% [202954215085243970479058919150073511025]) 0) 23 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [11136040682558238275432625]) 0) 64 false) .empty .empty)))

#time def treeG_J009_part082 : IntSourceTree :=
  (.node 517 (sourceLit (List.headD (raw_ints% [73823714709029196381479]) 0) 71 false) (.node 515 (sourceLit (List.headD (raw_ints% [309777197848233020167779]) 0) 69 false) (.node 514 (sourceLit (List.headD (raw_ints% [3372499907627943348273984898583955950205]) 0) 17 true) (.node 513 (sourceLit (List.headD (raw_ints% [2616258400651498095302175]) 0) 66 false) .empty .empty) .empty) (.node 516 (sourceLit (List.headD (raw_ints% [4888548923964396530597371441843594579425]) 0) 16 true) .empty .empty)) (.node 519 (sourceLit (List.headD (raw_ints% [35367263791929849289547]) 0) 72 false) (.node 518 (sourceLit (List.headD (raw_ints% [14664192595370196491453987993700538488645]) 0) 14 true) .empty .empty) (.node 537 (sourceLit (List.headD (raw_ints% [9289318797711412384786078977559832175]) 0) 36 false) .empty .empty)))

#time def treeG_J009_part083 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [609983182679352644690993075458813774185]) 0) 20 true) treeG_J009_part081 treeG_J009_part082)

#time def treeG_J009_part084 : IntSourceTree :=
  (.node 502 (sourceLit (List.headD (raw_ints% [121639764032915273344752379460073650925]) 0) 29 true) treeG_J009_part080 treeG_J009_part083)

#time def treeG_J009_part085 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [116547212608556379705762610292618647275]) 0) 30 true) (.node 541 (sourceLit (List.headD (raw_ints% [166199793492416106550096537543154418525]) 0) 32 false) (.node 540 (sourceLit (List.headD (raw_ints% [9042179276909775928666864904775]) 0) 56 false) (.node 539 (sourceLit (List.headD (raw_ints% [120015320904365898885677963964530443575]) 0) 33 true) .empty .empty) .empty) (.node 542 (sourceLit (List.headD (raw_ints% [56355658580164482335174967225]) 0) 62 true) .empty .empty)) (.node 546 (sourceLit (List.headD (raw_ints% [73157361686274216548373975]) 0) 62 false) (.node 545 (sourceLit (List.headD (raw_ints% [32291976977226755598092213762317596825]) 0) 29 true) (.node 544 (sourceLit (List.headD (raw_ints% [681839348852157514496267175]) 0) 59 false) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [175038349874683221383299045743435441975]) 0) 25 true) .empty .empty)))

#time def treeG_J009_part086 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [470240304326753885809499228752479016455]) 0) 21 true) (.node 551 (sourceLit (List.headD (raw_ints% [373081271588531392473739357610279968665]) 0) 22 true) (.node 550 (sourceLit (List.headD (raw_ints% [914751358963516210758525]) 0) 68 false) (.node 549 (sourceLit (List.headD (raw_ints% [165276724517519751103809186857797803375]) 0) 24 true) .empty .empty) .empty) (.node 552 (sourceLit (List.headD (raw_ints% [6725335607841663562481775]) 0) 65 false) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [2552715029149807683624503945109524334795]) 0) 18 true) (.node 554 (sourceLit (List.headD (raw_ints% [48880741061524823028225]) 0) 72 false) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [183641508000647685846153]) 0) 70 false) .empty .empty)))

#time def treeG_J009_part087 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [1011502299078051861852675]) 0) 68 false) treeG_J009_part085 treeG_J009_part086)

#time def treeG_J009_part088 : IntSourceTree :=
  (.node 582 (sourceLit (List.headD (raw_ints% [2780836459911572978146296980150544347325]) 0) 29 false) (.node 580 (sourceLit (List.headD (raw_ints% [1118357948725243007807764227293960802075]) 0) 31 true) (.node 559 (sourceLit (List.headD (raw_ints% [10837582063621124825535924854456173154835]) 0) 15 true) (.node 558 (sourceLit (List.headD (raw_ints% [5431072773575116174999]) 0) 75 false) .empty .empty) .empty) (.node 581 (sourceLit (List.headD (raw_ints% [4971519889600184351641800044325]) 0) 58 false) .empty .empty)) (.node 584 (sourceLit (List.headD (raw_ints% [896247001292153500166288181583185612225]) 0) 28 true) (.node 583 (sourceLit (List.headD (raw_ints% [1804435086301313153873226545925]) 0) 58 true) .empty .empty) (.node 585 (sourceLit (List.headD (raw_ints% [225156864071609248941390825]) 0) 61 false) .empty .empty)))

#time def treeG_J009_part089 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [18136002804274280468840175]) 0) 64 false) (.node 589 (sourceLit (List.headD (raw_ints% [40793431006062281957135625]) 0) 63 false) (.node 588 (sourceLit (List.headD (raw_ints% [1197352583912221800587333446797410024775]) 0) 23 true) (.node 587 (sourceLit (List.headD (raw_ints% [94143490371357001465917825]) 0) 62 false) .empty .empty) .empty) (.node 590 (sourceLit (List.headD (raw_ints% [2171888943535310933752286288490288180705]) 0) 21 true) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [256817325449385341698725]) 0) 70 false) (.node 592 (sourceLit (List.headD (raw_ints% [2374666990028898495098921785423425975135]) 0) 20 true) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [11675189830828180997629990421495372576355]) 0) 17 true) .empty .empty)))

#time def treeG_J009_part090 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [1860231646199051248226331076829487968175]) 0) 24 true) treeG_J009_part088 treeG_J009_part089)

#time def treeG_J009_part091 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [3649445394539744721911218679941030162335]) 0) 17 true) treeG_J009_part087 treeG_J009_part090)

#time def treeG_J009_part092 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [1042918356961541143550200508775]) 0) 59 true) treeG_J009_part084 treeG_J009_part091)

#time def treeG_J009_part093 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [19803159430693772051544525]) 0) 63 false) treeG_J009_part077 treeG_J009_part092)

#time def treeG_J009_part094 : IntSourceTree :=
  (.node 621 (sourceLit (List.headD (raw_ints% [160569717777207389294732595604639402575]) 0) 35 true) (.node 598 (sourceLit (List.headD (raw_ints% [43726933717265719059125510885355944108715]) 0) 14 true) (.node 597 (sourceLit (List.headD (raw_ints% [54908896645809244732337]) 0) 72 false) (.node 596 (sourceLit (List.headD (raw_ints% [15533171309234064938398660119032600098935]) 0) 16 true) .empty .empty) .empty) (.node 599 (sourceLit (List.headD (raw_ints% [51529900585272009510437]) 0) 72 false) .empty .empty)) (.node 624 (sourceLit (List.headD (raw_ints% [451279231412541327846930703275]) 0) 61 true) (.node 623 (sourceLit (List.headD (raw_ints% [362172959065016169731507448805395374325]) 0) 33 false) (.node 622 (sourceLit (List.headD (raw_ints% [5422365158241500210323199782125]) 0) 59 false) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [107994378039365843071024495977608501925]) 0) 32 true) .empty .empty)))

#time def treeG_J009_part095 : IntSourceTree :=
  (.node 631 (sourceLit (List.headD (raw_ints% [224850958993347442659818366360001026505]) 0) 25 true) (.node 629 (sourceLit (List.headD (raw_ints% [129009482424337756185440532492451527675]) 0) 27 true) (.node 628 (sourceLit (List.headD (raw_ints% [61775416800859341886632225]) 0) 63 false) (.node 627 (sourceLit (List.headD (raw_ints% [210649162040546003355379003885756565775]) 0) 28 true) .empty .empty) .empty) (.node 630 (sourceLit (List.headD (raw_ints% [26157409262646022584999225]) 0) 64 false) .empty .empty)) (.node 633 (sourceLit (List.headD (raw_ints% [238053335712768076161177819583868369835]) 0) 24 true) (.node 632 (sourceLit (List.headD (raw_ints% [89145837472129819580925]) 0) 72 false) .empty .empty) (.node 634 (sourceLit (List.headD (raw_ints% [159055843326335695642275]) 0) 71 false) .empty .empty)))

#time def treeG_J009_part096 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [75999751192667516196508425]) 0) 63 false) treeG_J009_part094 treeG_J009_part095)

#time def treeG_J009_part097 : IntSourceTree :=
  (.node 663 (sourceLit (List.headD (raw_ints% [23493895719267313995166025674425]) 0) 58 false) (.node 638 (sourceLit (List.headD (raw_ints% [33184605551508780032341]) 0) 73 false) (.node 637 (sourceLit (List.headD (raw_ints% [1485465739336790027060930179886446242075]) 0) 20 true) (.node 636 (sourceLit (List.headD (raw_ints% [72168287783879115609417]) 0) 72 false) .empty .empty) .empty) (.node 639 (sourceLit (List.headD (raw_ints% [4111168956705574279198698253862471369235]) 0) 18 true) .empty .empty)) (.node 666 (sourceLit (List.headD (raw_ints% [53432889909956260404138210863706065017425]) 0) 24 true) (.node 665 (sourceLit (List.headD (raw_ints% [902783619689154264942802797375]) 0) 61 true) (.node 664 (sourceLit (List.headD (raw_ints% [24075316381453188362982764905128489569025]) 0) 28 false) .empty .empty) .empty) (.node 667 (sourceLit (List.headD (raw_ints% [209855514399313063320115875]) 0) 62 false) .empty .empty)))

#time def treeG_J009_part098 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [456349374327653214948675]) 0) 70 false) (.node 671 (sourceLit (List.headD (raw_ints% [34178815721017764701158275]) 0) 64 false) (.node 670 (sourceLit (List.headD (raw_ints% [14341324806779921857984101870543507361695]) 0) 21 true) (.node 669 (sourceLit (List.headD (raw_ints% [82757402595656401816128825]) 0) 63 false) .empty .empty) .empty) (.node 672 (sourceLit (List.headD (raw_ints% [12015794385545337835129453661616639721185]) 0) 20 true) .empty .empty)) (.node 675 (sourceLit (List.headD (raw_ints% [800132087474521416854379]) 0) 69 false) (.node 674 (sourceLit (List.headD (raw_ints% [49266464111640446499631531391974930101405]) 0) 17 true) .empty .empty) (.node 676 (sourceLit (List.headD (raw_ints% [57446627104192921573645231692054185833545]) 0) 16 true) .empty .empty)))

#time def treeG_J009_part099 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [12284193786682722414156922801891010184825]) 0) 23 true) treeG_J009_part097 treeG_J009_part098)

#time def treeG_J009_part100 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [1140309350209796664250685809548231030195]) 0) 21 true) treeG_J009_part096 treeG_J009_part099)

#time def treeG_J009_part101 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [902935619191539599975195814225]) 0) 62 true) (.node 704 (sourceLit (List.headD (raw_ints% [25299012644917479306553748487525]) 0) 59 false) (.node 679 (sourceLit (List.headD (raw_ints% [81208521620763110618927]) 0) 72 false) (.node 678 (sourceLit (List.headD (raw_ints% [146412680917843404404673552140109174876885]) 0) 14 true) .empty .empty) .empty) (.node 705 (sourceLit (List.headD (raw_ints% [24939271405768115107550960872949357584425]) 0) 29 false) .empty .empty)) (.node 709 (sourceLit (List.headD (raw_ints% [11252117927288020364673398541951397963425]) 0) 24 true) (.node 708 (sourceLit (List.headD (raw_ints% [74040048799226860716741825]) 0) 64 false) (.node 707 (sourceLit (List.headD (raw_ints% [51747696613631892377295178832620012491225]) 0) 25 true) .empty .empty) .empty) (.node 710 (sourceLit (List.headD (raw_ints% [13818357747316987116975]) 0) 76 false) .empty .empty)))

#time def treeG_J009_part102 : IntSourceTree :=
  (.node 716 (sourceLit (List.headD (raw_ints% [511458936339004954416711]) 0) 70 false) (.node 714 (sourceLit (List.headD (raw_ints% [9290422843791172478325]) 0) 76 false) (.node 713 (sourceLit (List.headD (raw_ints% [10111367699843193225840031104945692762505]) 0) 21 true) (.node 712 (sourceLit (List.headD (raw_ints% [22768148524585147794799875]) 0) 65 false) .empty .empty) .empty) (.node 715 (sourceLit (List.headD (raw_ints% [40143989309962073185626044915589081859845]) 0) 18 true) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [14060768342610051613539]) 0) 75 false) (.node 717 (sourceLit (List.headD (raw_ints% [45562901189498601357157790252962615896945]) 0) 17 true) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [113523329264198810171083966109209403923005]) 0) 15 true) .empty .empty)))

#time def treeG_J009_part103 : IntSourceTree :=
  (.node 711 (sourceLit (List.headD (raw_ints% [12542517134833142316705554939663499149655]) 0) 22 true) treeG_J009_part101 treeG_J009_part102)

#time def treeG_J009_part104 : IntSourceTree :=
  (.node 750 (sourceLit (List.headD (raw_ints% [165692562029828403976790274800678860053105]) 0) 21 true) (.node 748 (sourceLit (List.headD (raw_ints% [401697379122372416604204507859069089744975]) 0) 23 true) (.node 747 (sourceLit (List.headD (raw_ints% [1806081093897478513013711744325]) 0) 62 true) (.node 746 (sourceLit (List.headD (raw_ints% [1649546259879115627287399706732464950420625]) 0) 24 false) .empty .empty) .empty) (.node 749 (sourceLit (List.headD (raw_ints% [213402792601251041050838475]) 0) 63 false) .empty .empty)) (.node 752 (sourceLit (List.headD (raw_ints% [88324342693119800698514985855691353476055]) 0) 20 true) (.node 751 (sourceLit (List.headD (raw_ints% [79021170945002993761100925]) 0) 64 false) .empty .empty) (.node 753 (sourceLit (List.headD (raw_ints% [15466558535342696355621075]) 0) 66 false) .empty .empty)))

#time def treeG_J009_part105 : IntSourceTree :=
  (.node 759 (sourceLit (List.headD (raw_ints% [143763771860997715197697]) 0) 72 false) (.node 757 (sourceLit (List.headD (raw_ints% [332603578495106981443717]) 0) 71 false) (.node 756 (sourceLit (List.headD (raw_ints% [263705287375503663911363127632658469045215]) 0) 16 true) (.node 755 (sourceLit (List.headD (raw_ints% [1578216160536018737596821]) 0) 69 false) .empty .empty) .empty) (.node 758 (sourceLit (List.headD (raw_ints% [582593738114134217309851091907292679474235]) 0) 14 true) .empty .empty)) (.node 787 (sourceLit (List.headD (raw_ints% [850646978246373759832347442782542481455925]) 0) 26 false) (.node 786 (sourceLit (List.headD (raw_ints% [28910451122678867036389745710725]) 0) 61 false) .empty .empty) (.node 788 (sourceLit (List.headD (raw_ints% [1806229173995076966735145227975]) 0) 63 true) .empty .empty)))

#time def treeG_J009_part106 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [274297302283341736727249463966287238298755]) 0) 17 true) treeG_J009_part104 treeG_J009_part105)

#time def treeG_J009_part107 : IntSourceTree :=
  (.node 745 (sourceLit (List.headD (raw_ints% [27104579884295787836439354082275]) 0) 60 false) treeG_J009_part103 treeG_J009_part106)

#time def treeG_J009_part108 : IntSourceTree :=
  (.node 677 (sourceLit (List.headD (raw_ints% [89427678921948986486497]) 0) 72 false) treeG_J009_part100 treeG_J009_part107)

#time def treeG_J009_part109 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [10709862039321616046718675]) 0) 67 false) (.node 792 (sourceLit (List.headD (raw_ints% [28126511210208922983150525]) 0) 66 false) (.node 791 (sourceLit (List.headD (raw_ints% [76575022447497630830042359930507680451725]) 0) 23 true) (.node 790 (sourceLit (List.headD (raw_ints% [156802799268240661819708875]) 0) 64 false) .empty .empty) .empty) (.node 793 (sourceLit (List.headD (raw_ints% [39106487496638303736337477375372830356775]) 0) 22 true) .empty .empty)) (.node 797 (sourceLit (List.headD (raw_ints% [109071193093002531277102668689847926574135]) 0) 18 true) (.node 796 (sourceLit (List.headD (raw_ints% [533378612098506891590055]) 0) 71 false) (.node 795 (sourceLit (List.headD (raw_ints% [117076656486689831770811709525349078219455]) 0) 19 true) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [220117431754226568535405]) 0) 72 false) .empty .empty)))

#time def treeG_J009_part110 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [234584427591478329878316825]) 0) 64 false) (.node 829 (sourceLit (List.headD (raw_ints% [3612671750782755184511341294425]) 0) 63 true) (.node 828 (sourceLit (List.headD (raw_ints% [14012049031064352573921763592379748793039775]) 0) 23 false) (.node 827 (sourceLit (List.headD (raw_ints% [15358266108288172774701728727525]) 0) 63 false) .empty .empty) .empty) (.node 830 (sourceLit (List.headD (raw_ints% [6081431617091521935855707474273204208451695]) 0) 21 true) .empty .empty)) (.node 833 (sourceLit (List.headD (raw_ints% [40786463885075149610679975]) 0) 66 false) (.node 832 (sourceLit (List.headD (raw_ints% [1136876016466842292582162773032431533751545]) 0) 20 true) .empty .empty) (.node 834 (sourceLit (List.headD (raw_ints% [2228517897501509702398349088057573904534845]) 0) 17 true) .empty .empty)))

#time def treeG_J009_part111 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [234535204424967703569383562899041637775615]) 0) 16 true) treeG_J009_part109 treeG_J009_part110)

#time def treeG_J009_part112 : IntSourceTree :=
  (.node 868 (sourceLit (List.headD (raw_ints% [32522761390571422516138602683025]) 0) 63 false) (.node 838 (sourceLit (List.headD (raw_ints% [2907684440861946783557434306167840970898085]) 0) 14 true) (.node 837 (sourceLit (List.headD (raw_ints% [734153645701906801736393]) 0) 71 false) (.node 836 (sourceLit (List.headD (raw_ints% [1609521216411533644421624224772926782466065]) 0) 16 true) .empty .empty) .empty) (.node 839 (sourceLit (List.headD (raw_ints% [296471091647455421873113]) 0) 72 false) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [5928281572196526674195622754412188847548245]) 0) 22 true) (.node 870 (sourceLit (List.headD (raw_ints% [903207138395505856293290250825]) 0) 66 true) (.node 869 (sourceLit (List.headD (raw_ints% [14402494292259436970161294701696866484821325]) 0) 24 false) .empty .empty) .empty) (.node 872 (sourceLit (List.headD (raw_ints% [178331405171060483912015775]) 0) 65 false) .empty .empty)))

#time def treeG_J009_part113 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [128509053486920058300247]) 0) 74 false) (.node 876 (sourceLit (List.headD (raw_ints% [5419915269855551005164813]) 0) 69 false) (.node 875 (sourceLit (List.headD (raw_ints% [1994364584528130038856725669006875748095935]) 0) 18 true) (.node 874 (sourceLit (List.headD (raw_ints% [7519150461438383390990325]) 0) 69 false) .empty .empty) .empty) (.node 877 (sourceLit (List.headD (raw_ints% [1391378830225528581867418887393230929317795]) 0) 17 true) .empty .empty)) (.node 909 (sourceLit (List.headD (raw_ints% [68658194531925600216788546660475]) 0) 63 false) (.node 879 (sourceLit (List.headD (raw_ints% [2438614032012011376418667180369757695346855]) 0) 15 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [236521340293242513458436422701423067965592895]) 0) 21 false) .empty .empty)))

#time def treeG_J009_part114 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [1058663041473565685109487818281685873037995]) 0) 21 true) treeG_J009_part112 treeG_J009_part113)

#time def treeG_J009_part115 : IntSourceTree :=
  (.node 835 (sourceLit (List.headD (raw_ints% [7553429718249578571525033]) 0) 68 false) treeG_J009_part111 treeG_J009_part114)

#time def treeG_J009_part116 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [14345395459813506666432181127282079202301415]) 0) 16 true) (.node 914 (sourceLit (List.headD (raw_ints% [31648699429652592221105261096956374032680995]) 0) 17 true) (.node 913 (sourceLit (List.headD (raw_ints% [17193117660748166787666975]) 0) 69 false) (.node 912 (sourceLit (List.headD (raw_ints% [46289376561105371100982819262265079246634415]) 0) 20 true) .empty .empty) .empty) (.node 915 (sourceLit (List.headD (raw_ints% [22523172127503954992436267]) 0) 68 false) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [731601336247905044528863]) 0) 72 false) (.node 918 (sourceLit (List.headD (raw_ints% [19354376842746510526321267892123853898186635]) 0) 14 true) (.node 917 (sourceLit (List.headD (raw_ints% [3951607978451737401692027]) 0) 70 false) .empty .empty) .empty) (.node 950 (sourceLit (List.headD (raw_ints% [72271023085507623641961707663775]) 0) 64 false) .empty .empty)))

#time def treeG_J009_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [8551628428824201993635727]) 0) 70 false) (.node 954 (sourceLit (List.headD (raw_ints% [26867084860057950184343625]) 0) 69 false) (.node 953 (sourceLit (List.headD (raw_ints% [11307678379907951353968332860995848343399105]) 0) 23 true) (.node 952 (sourceLit (List.headD (raw_ints% [28226836027331286676406688825]) 0) 73 true) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [7413583711281115545562133856987374571146265]) 0) 20 true) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [2923535550556376935290051]) 0) 71 false) (.node 957 (sourceLit (List.headD (raw_ints% [3238504157396994521141190559972212068245905]) 0) 19 true) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [4228940702683624787475650177938524050709945]) 0) 17 true) .empty .empty)))

#time def treeG_J009_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [60612405466359760033158011363958814203285285]) 0) 24 false) treeG_J009_part116 treeG_J009_part117)

#time def treeG_J009_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [187909889230661138826714927946097718469551285]) 0) 14 true) (.node 996 (sourceLit (List.headD (raw_ints% [222889283301182190791556102296313907074379065]) 0) 16 true) (.node 995 (sourceLit (List.headD (raw_ints% [84945167312727845744938233]) 0) 68 false) (.node 994 (sourceLit (List.headD (raw_ints% [1415734133198565181086841345110512213922404445]) 0) 17 true) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [13151648879196666585579427]) 0) 70 false) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [1806578759069383901573787762375]) 0) 69 true) (.node 999 (sourceLit (List.headD (raw_ints% [547983553577117972690297]) 0) 74 false) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [1386079798353440718904592809682562715637819385]) 0) 18 true) .empty .empty)))

#time def treeG_J009_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [10865749103526343560445186375164187818028176015]) 0) 16 true) (.node 1039 (sourceLit (List.headD (raw_ints% [170994126419926639676812327234343622266711505]) 0) 15 true) (.node 1038 (sourceLit (List.headD (raw_ints% [319628541520009051571543]) 0) 76 false) (.node 1037 (sourceLit (List.headD (raw_ints% [209935266671594212706991340056425058801395445]) 0) 17 true) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [7226399981444848334140895987733]) 0) 68 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [3171054377514846264485146512956703222352775835]) 0) 14 true) (.node 1077 (sourceLit (List.headD (raw_ints% [6836282696985346896510919]) 0) 73 false) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [2009044778582954439882047]) 0) 74 false) .empty .empty)))

#time def treeG_J009_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [67841910455079441757666779]) 0) 69 false) treeG_J009_part119 treeG_J009_part120)

#time def treeG_J009_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [903275945992261921811801709375]) 0) 69 true) treeG_J009_part118 treeG_J009_part121)

#time def treeG_J009_part123 : IntSourceTree :=
  (.node 911 (sourceLit (List.headD (raw_ints% [7225891691591638328676200323425]) 0) 64 true) treeG_J009_part115 treeG_J009_part122)

#time def treeG_J009_part124 : IntSourceTree :=
  (.node 789 (sourceLit (List.headD (raw_ints% [195222630597542198119765554658558845890775]) 0) 25 true) treeG_J009_part108 treeG_J009_part123)

#time def treeG_J009_part125 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [472314659136164148283821]) 0) 69 false) treeG_J009_part093 treeG_J009_part124)

#time def treeG_J009_part126 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [309851696396135141186283]) 0) 68 false) treeG_J009_part062 treeG_J009_part125)

#time def treeG_J009 : IntSourceTree := treeG_J009_part126

#time def treeG_J010_part000 : IntSourceTree :=
  (.node 6 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 41 true) (.node 4 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 40 false) (.node 3 (sourceLit (List.headD (raw_ints% [11174779188799642072248469888725]) 0) 40 false) (.node 2 (sourceLit (List.headD (raw_ints% [11455317578476620534313285032375]) 0) 38 false) .empty .empty) .empty) (.node 5 (sourceLit (List.headD (raw_ints% [2608440279774330043744064037675]) 0) 42 false) .empty .empty)) (.node 9 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 46 false) (.node 8 (sourceLit (List.headD (raw_ints% [327294787956474872408951000925]) 0) 44 true) (.node 7 (sourceLit (List.headD (raw_ints% [1239752984683616940942996215625]) 0) 43 false) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 45 true) .empty .empty)))

#time def treeG_J010_part001 : IntSourceTree :=
  (.node 16 (sourceLit (List.headD (raw_ints% [2011347499626567344746679175]) 0) 52 false) (.node 14 (sourceLit (List.headD (raw_ints% [32944484907676534094988710625]) 0) 48 false) (.node 13 (sourceLit (List.headD (raw_ints% [50140075958108745149288293249275]) 0) 38 true) (.node 12 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 47 false) .empty .empty) .empty) (.node 15 (sourceLit (List.headD (raw_ints% [118460609673363399845821094787825]) 0) 36 true) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [984400442442559329260255325]) 0) 53 false) (.node 17 (sourceLit (List.headD (raw_ints% [157662380138851915438269558918375]) 0) 35 true) .empty .empty) (.node 19 (sourceLit (List.headD (raw_ints% [879042010712648108464504705964625]) 0) 32 true) .empty .empty)))

#time def treeG_J010_part002 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [67451535816963614433728676769275]) 0) 39 true) treeG_J010_part000 treeG_J010_part001)

#time def treeG_J010_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [4677031073020811033006240714812575]) 0) 28 true) (.node 23 (sourceLit (List.headD (raw_ints% [3472647634330186830053815727372925]) 0) 29 true) (.node 22 (sourceLit (List.headD (raw_ints% [118467005652573197354089875]) 0) 56 false) (.node 21 (sourceLit (List.headD (raw_ints% [1241837412573909720047823863043525]) 0) 31 true) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [14557980992112390008568375]) 0) 59 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [1764044394987334280574285]) 0) 62 false) (.node 27 (sourceLit (List.headD (raw_ints% [46337478763830402500554245374041425]) 0) 24 true) (.node 26 (sourceLit (List.headD (raw_ints% [7163428284381022774566705]) 0) 60 false) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [46751522727167659843728488238089625]) 0) 23 true) .empty .empty)))

#time def treeG_J010_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [3159339576657817362583067509210313955]) 0) 17 false) (.node 33 (sourceLit (List.headD (raw_ints% [180784163604276682437549609245544255]) 0) 20 false) (.node 32 (sourceLit (List.headD (raw_ints% [26806749970206025572975]) 0) 68 false) (.node 31 (sourceLit (List.headD (raw_ints% [35928115131002330721420093069635295]) 0) 21 true) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [13231497295709693567325]) 0) 69 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [9255950542022009307249795170625309975]) 0) 16 false) (.node 36 (sourceLit (List.headD (raw_ints% [3267361178509734114831]) 0) 71 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [1614526075331246802439]) 0) 72 false) .empty .empty)))

#time def treeG_J010_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [869521178173035445790985]) 0) 63 false) treeG_J010_part003 treeG_J010_part004)

#time def treeG_J010_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [241301985408182539353845475]) 0) 55 false) treeG_J010_part002 treeG_J010_part005)

#time def treeG_J010_part007 : IntSourceTree :=
  (.node 47 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 42 true) (.node 45 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 41 false) (.node 44 (sourceLit (List.headD (raw_ints% [11174779188799642072248469888725]) 0) 41 false) (.node 43 (sourceLit (List.headD (raw_ints% [11455317578476620534313285032375]) 0) 39 false) .empty .empty) .empty) (.node 46 (sourceLit (List.headD (raw_ints% [2608440279774330043744064037675]) 0) 43 false) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 47 false) (.node 49 (sourceLit (List.headD (raw_ints% [327294787956474872408951000925]) 0) 45 true) (.node 48 (sourceLit (List.headD (raw_ints% [1239752984683616940942996215625]) 0) 44 false) .empty .empty) .empty) (.node 51 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 46 true) .empty .empty)))

#time def treeG_J010_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [2011347499626567344746679175]) 0) 53 false) (.node 55 (sourceLit (List.headD (raw_ints% [32944484907676534094988710625]) 0) 49 false) (.node 54 (sourceLit (List.headD (raw_ints% [50140075958108745149288293249275]) 0) 39 true) (.node 53 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 48 false) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [118460609673363399845821094787825]) 0) 37 true) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [984400442442559329260255325]) 0) 54 false) (.node 58 (sourceLit (List.headD (raw_ints% [157662380138851915438269558918375]) 0) 36 true) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [879042010712648108464504705964625]) 0) 33 true) .empty .empty)))

#time def treeG_J010_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [67451535816963614433728676769275]) 0) 40 true) treeG_J010_part007 treeG_J010_part008)

#time def treeG_J010_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [4677031073020811033006240714812575]) 0) 29 true) (.node 64 (sourceLit (List.headD (raw_ints% [3472647634330186830053815727372925]) 0) 30 true) (.node 63 (sourceLit (List.headD (raw_ints% [118467005652573197354089875]) 0) 57 false) (.node 62 (sourceLit (List.headD (raw_ints% [1241837412573909720047823863043525]) 0) 32 true) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [14557980992112390008568375]) 0) 60 false) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [1764044394987334280574285]) 0) 63 false) (.node 68 (sourceLit (List.headD (raw_ints% [46337478763830402500554245374041425]) 0) 25 true) (.node 67 (sourceLit (List.headD (raw_ints% [7163428284381022774566705]) 0) 61 false) .empty .empty) .empty) (.node 70 (sourceLit (List.headD (raw_ints% [46751522727167659843728488238089625]) 0) 24 true) .empty .empty)))

#time def treeG_J010_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [3159339576657817362583067509210313955]) 0) 18 false) (.node 74 (sourceLit (List.headD (raw_ints% [180784163604276682437549609245544255]) 0) 21 false) (.node 73 (sourceLit (List.headD (raw_ints% [26806749970206025572975]) 0) 69 false) (.node 72 (sourceLit (List.headD (raw_ints% [35928115131002330721420093069635295]) 0) 22 true) .empty .empty) .empty) (.node 75 (sourceLit (List.headD (raw_ints% [13231497295709693567325]) 0) 70 false) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [9255950542022009307249795170625309975]) 0) 17 false) (.node 77 (sourceLit (List.headD (raw_ints% [3267361178509734114831]) 0) 72 false) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [1614526075331246802439]) 0) 73 false) .empty .empty)))

#time def treeG_J010_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [869521178173035445790985]) 0) 64 false) treeG_J010_part010 treeG_J010_part011)

#time def treeG_J010_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [241301985408182539353845475]) 0) 56 false) treeG_J010_part009 treeG_J010_part012)

#time def treeG_J010_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [47194799462658365856675027562090384875]) 0) 14 false) treeG_J010_part006 treeG_J010_part013)

#time def treeG_J010_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [942212268359548875116677123875]) 0) 45 false) (.node 87 (sourceLit (List.headD (raw_ints% [3977127574865043146545131859725]) 0) 43 false) (.node 86 (sourceLit (List.headD (raw_ints% [2707620518549019399019503734925]) 0) 41 false) (.node 85 (sourceLit (List.headD (raw_ints% [4283169454512656014252202925525]) 0) 43 false) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 43 false) .empty .empty)) (.node 92 (sourceLit (List.headD (raw_ints% [2704915602946073325693809925]) 0) 55 true) (.node 91 (sourceLit (List.headD (raw_ints% [143621959195925039285266364257275]) 0) 39 false) (.node 90 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 45 true) .empty .empty) .empty) (.node 93 (sourceLit (List.headD (raw_ints% [489472210577600170320541120904925]) 0) 38 true) .empty .empty)))

#time def treeG_J010_part016 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [4166154153730613185560121179423375]) 0) 32 true) (.node 97 (sourceLit (List.headD (raw_ints% [790022497248055283328299199384225]) 0) 35 true) (.node 96 (sourceLit (List.headD (raw_ints% [24899094909170264716001993925]) 0) 50 false) (.node 95 (sourceLit (List.headD (raw_ints% [683780605656376522542791597200575]) 0) 36 true) .empty .empty) .empty) (.node 98 (sourceLit (List.headD (raw_ints% [3038294556810575360233103025]) 0) 53 false) .empty .empty)) (.node 101 (sourceLit (List.headD (raw_ints% [5790498673127275147668213784673475]) 0) 31 true) (.node 100 (sourceLit (List.headD (raw_ints% [371549228517188394953204925]) 0) 56 false) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [364136965163791881353601075]) 0) 56 false) .empty .empty)))

#time def treeG_J010_part017 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [102301295239627132189701785625]) 0) 48 false) treeG_J010_part015 treeG_J010_part016)

#time def treeG_J010_part018 : IntSourceTree :=
  (.node 108 (sourceLit (List.headD (raw_ints% [1349845972348422123498105]) 0) 64 false) (.node 106 (sourceLit (List.headD (raw_ints% [21952533699843757242570045]) 0) 60 false) (.node 105 (sourceLit (List.headD (raw_ints% [23104150001620683607424285104170825]) 0) 28 true) (.node 104 (sourceLit (List.headD (raw_ints% [89351043668348417336953125]) 0) 58 false) .empty .empty) .empty) (.node 107 (sourceLit (List.headD (raw_ints% [252992509909501503611845160373963375]) 0) 24 true) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [712096248503680226778235718739798705]) 0) 21 true) (.node 110 (sourceLit (List.headD (raw_ints% [2658567611801633115357585]) 0) 63 false) (.node 109 (sourceLit (List.headD (raw_ints% [323948307383475560160705474754241775]) 0) 23 true) .empty .empty) .empty) (.node 112 (sourceLit (List.headD (raw_ints% [655067178411387241207185]) 0) 65 false) .empty .empty)))

#time def treeG_J010_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [4920196281688221427223]) 0) 72 false) (.node 116 (sourceLit (List.headD (raw_ints% [4982068058599979726247]) 0) 72 false) (.node 115 (sourceLit (List.headD (raw_ints% [2625753658679036475418519986647102205]) 0) 17 false) (.node 114 (sourceLit (List.headD (raw_ints% [40382002644702357578625]) 0) 69 false) .empty .empty) .empty) (.node 117 (sourceLit (List.headD (raw_ints% [16018766071240529593414744903057201665]) 0) 16 false) .empty .empty)) (.node 125 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 41 false) (.node 119 (sourceLit (List.headD (raw_ints% [100900409209693783059321695167914574725]) 0) 14 false) .empty .empty) (.node 126 (sourceLit (List.headD (raw_ints% [5957898629250981984760341813375]) 0) 43 false) .empty .empty)))

#time def treeG_J010_part020 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [468209084652295328208910353802626615]) 0) 20 true) treeG_J010_part018 treeG_J010_part019)

#time def treeG_J010_part021 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [16396750966852368690711366081323475]) 0) 29 true) treeG_J010_part017 treeG_J010_part020)

#time def treeG_J010_part022 : IntSourceTree :=
  (.node 132 (sourceLit (List.headD (raw_ints% [105536747506444326859497520513275]) 0) 41 false) (.node 130 (sourceLit (List.headD (raw_ints% [644671552035480809290358032125]) 0) 46 false) (.node 129 (sourceLit (List.headD (raw_ints% [684343647545356551400533911025]) 0) 44 false) (.node 128 (sourceLit (List.headD (raw_ints% [684343647545356551400533911025]) 0) 46 false) .empty .empty) .empty) (.node 131 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 48 false) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [8669601291493824761839134375]) 0) 52 false) (.node 134 (sourceLit (List.headD (raw_ints% [219666067309745712585626413827825]) 0) 40 true) (.node 133 (sourceLit (List.headD (raw_ints% [760081284427846604519960588925]) 0) 48 true) .empty .empty) .empty) (.node 136 (sourceLit (List.headD (raw_ints% [282659997991506561348485251206375]) 0) 38 true) .empty .empty)))

#time def treeG_J010_part023 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [2274330630276682713810194960814975]) 0) 33 true) (.node 140 (sourceLit (List.headD (raw_ints% [1643556071508982538547808236729375]) 0) 34 true) (.node 139 (sourceLit (List.headD (raw_ints% [513473528592004007743211925]) 0) 56 false) (.node 138 (sourceLit (List.headD (raw_ints% [316180058554601683945014820232925]) 0) 37 true) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [501796471626194250552564375]) 0) 56 false) .empty .empty)) (.node 144 (sourceLit (List.headD (raw_ints% [6462051666261090930328775176975275]) 0) 31 true) (.node 143 (sourceLit (List.headD (raw_ints% [7677186234725583874984725]) 0) 62 false) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [60235081684123637319816375]) 0) 59 false) .empty .empty)))

#time def treeG_J010_part024 : IntSourceTree :=
  (.node 137 (sourceLit (List.headD (raw_ints% [16853704910663995337015277225]) 0) 51 false) treeG_J010_part022 treeG_J010_part023)

#time def treeG_J010_part025 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [223630804203574708695825]) 0) 67 false) (.node 149 (sourceLit (List.headD (raw_ints% [3635339494406354213418135]) 0) 63 false) (.node 148 (sourceLit (List.headD (raw_ints% [103327515572835550555645457499960975]) 0) 26 true) (.node 147 (sourceLit (List.headD (raw_ints% [3697276353865683617000835]) 0) 63 false) .empty .empty) .empty) (.node 150 (sourceLit (List.headD (raw_ints% [138598392328153950158488493258076075]) 0) 25 true) .empty .empty)) (.node 153 (sourceLit (List.headD (raw_ints% [440613178649739036623385]) 0) 66 false) (.node 152 (sourceLit (List.headD (raw_ints% [338084066686338948028407812835081705]) 0) 23 true) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [324496624128286005323229981524085435]) 0) 22 true) .empty .empty)))

#time def treeG_J010_part026 : IntSourceTree :=
  (.node 166 (sourceLit (List.headD (raw_ints% [16037444609867268748038599045325]) 0) 41 false) (.node 158 (sourceLit (List.headD (raw_ints% [3381407764609260143082474866215945845]) 0) 18 false) (.node 157 (sourceLit (List.headD (raw_ints% [6696774938690225337663]) 0) 72 false) (.node 156 (sourceLit (List.headD (raw_ints% [266792958989390443582273761281605875]) 0) 19 true) .empty .empty) .empty) (.node 159 (sourceLit (List.headD (raw_ints% [206604387897310914049]) 0) 77 false) .empty .empty)) (.node 168 (sourceLit (List.headD (raw_ints% [3302701951197155530672141918425]) 0) 43 false) (.node 167 (sourceLit (List.headD (raw_ints% [7938669683636920822975551767025]) 0) 43 false) .empty .empty) (.node 169 (sourceLit (List.headD (raw_ints% [1795162321821877330485458520225]) 0) 45 false) .empty .empty)))

#time def treeG_J010_part027 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [6787626337248166002825]) 0) 72 false) treeG_J010_part025 treeG_J010_part026)

#time def treeG_J010_part028 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [9213559464299936287209022194679125]) 0) 30 true) treeG_J010_part024 treeG_J010_part027)

#time def treeG_J010_part029 : IntSourceTree :=
  (.node 127 (sourceLit (List.headD (raw_ints% [208278501426847646078423364225]) 0) 46 false) treeG_J010_part021 treeG_J010_part028)

#time def treeG_J010_part030 : IntSourceTree :=
  (.node 84 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 41 false) treeG_J010_part014 treeG_J010_part029)

#time def treeG_J010_part031 : IntSourceTree :=
  (.node 175 (sourceLit (List.headD (raw_ints% [6345533548255486280197253645289825]) 0) 36 true) (.node 173 (sourceLit (List.headD (raw_ints% [2178060170680709400072501449117325]) 0) 38 false) (.node 172 (sourceLit (List.headD (raw_ints% [321884956750582725757563381075]) 0) 49 false) (.node 171 (sourceLit (List.headD (raw_ints% [21413958125158047893065291966725]) 0) 39 false) .empty .empty) .empty) (.node 174 (sourceLit (List.headD (raw_ints% [1622463864095320341229622963475]) 0) 48 true) .empty .empty)) (.node 178 (sourceLit (List.headD (raw_ints% [10777115797042844616549071175]) 0) 52 false) (.node 177 (sourceLit (List.headD (raw_ints% [3732537470616049698247464819917775]) 0) 35 true) (.node 176 (sourceLit (List.headD (raw_ints% [44457715422780333378711081075]) 0) 50 false) .empty .empty) .empty) (.node 179 (sourceLit (List.headD (raw_ints% [16069369593763894586920827315483825]) 0) 32 true) .empty .empty)))

#time def treeG_J010_part032 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [80288676658556771277836117727433575]) 0) 28 true) (.node 183 (sourceLit (List.headD (raw_ints% [56381829202001478151214872664755725]) 0) 29 true) (.node 182 (sourceLit (List.headD (raw_ints% [639455978088596619751527675]) 0) 56 false) (.node 181 (sourceLit (List.headD (raw_ints% [20506398471016445469096718002996525]) 0) 31 true) .empty .empty) .empty) (.node 184 (sourceLit (List.headD (raw_ints% [156318915842870266662558075]) 0) 58 false) .empty .empty)) (.node 187 (sourceLit (List.headD (raw_ints% [926343101520890341150909680544964625]) 0) 24 true) (.node 186 (sourceLit (List.headD (raw_ints% [19141273992139940038623165]) 0) 61 false) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [1173715190758630746751365]) 0) 65 false) .empty .empty)))

#time def treeG_J010_part033 : IntSourceTree :=
  (.node 180 (sourceLit (List.headD (raw_ints% [655397828666819620533218925]) 0) 56 false) treeG_J010_part031 treeG_J010_part032)

#time def treeG_J010_part034 : IntSourceTree :=
  (.node 194 (sourceLit (List.headD (raw_ints% [279085168070929606308885]) 0) 67 false) (.node 192 (sourceLit (List.headD (raw_ints% [1133979255217210428359415]) 0) 65 false) (.node 191 (sourceLit (List.headD (raw_ints% [3723052305997246178293396065518635695]) 0) 21 true) (.node 190 (sourceLit (List.headD (raw_ints% [4612111377011075311478685]) 0) 63 false) .empty .empty) .empty) (.node 193 (sourceLit (List.headD (raw_ints% [4941135982329127840245614651558680665]) 0) 20 true) .empty .empty)) (.node 197 (sourceLit (List.headD (raw_ints% [20287453415070776690731125083562895665]) 0) 16 true) (.node 196 (sourceLit (List.headD (raw_ints% [8593184615896352279403]) 0) 72 false) (.node 195 (sourceLit (List.headD (raw_ints% [23393537602889340816105238804188570045]) 0) 17 true) .empty .empty) .empty) (.node 198 (sourceLit (List.headD (raw_ints% [8473353595692229248103]) 0) 72 false) .empty .empty)))

#time def treeG_J010_part035 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 48 false) (.node 209 (sourceLit (List.headD (raw_ints% [327294787956474872408951000925]) 0) 47 false) (.node 208 (sourceLit (List.headD (raw_ints% [5201295093455494617373416122925]) 0) 44 false) (.node 207 (sourceLit (List.headD (raw_ints% [12704988587037706410783825217725]) 0) 42 false) .empty .empty) .empty) (.node 210 (sourceLit (List.headD (raw_ints% [287622692446599130298775122025]) 0) 48 false) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [2047621111430177507550214113225]) 0) 48 false) (.node 212 (sourceLit (List.headD (raw_ints% [189659536887730605825929749059825]) 0) 40 true) .empty .empty) (.node 214 (sourceLit (List.headD (raw_ints% [2617392305300200825243754276772975]) 0) 39 false) .empty .empty)))

#time def treeG_J010_part036 : IntSourceTree :=
  (.node 199 (sourceLit (List.headD (raw_ints% [7304639257802541519317500550995692315]) 0) 14 false) treeG_J010_part034 treeG_J010_part035)

#time def treeG_J010_part037 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [1329291941781893248729621845245133825]) 0) 23 true) treeG_J010_part033 treeG_J010_part036)

#time def treeG_J010_part038 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [12782257450745929509825210842025075]) 0) 33 true) (.node 218 (sourceLit (List.headD (raw_ints% [3100177353506846330357435179451925]) 0) 36 true) (.node 217 (sourceLit (List.headD (raw_ints% [13802005256058169020847901925]) 0) 52 false) (.node 216 (sourceLit (List.headD (raw_ints% [5780213552272473157500283142877075]) 0) 37 true) .empty .empty) .empty) (.node 219 (sourceLit (List.headD (raw_ints% [6669327568306812554603375775]) 0) 53 false) .empty .empty)) (.node 223 (sourceLit (List.headD (raw_ints% [393786018577377935752016475]) 0) 57 false) (.node 222 (sourceLit (List.headD (raw_ints% [15957737210463080041476328081366575]) 0) 32 true) (.node 221 (sourceLit (List.headD (raw_ints% [808999185707444990513873475]) 0) 56 false) .empty .empty) .empty) (.node 224 (sourceLit (List.headD (raw_ints% [43457725869479296290557322310805175]) 0) 30 true) .empty .empty)))

#time def treeG_J010_part039 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [1052095157125585348412644858728981675]) 0) 24 true) (.node 228 (sourceLit (List.headD (raw_ints% [719688070375219240039618765545042675]) 0) 25 true) (.node 227 (sourceLit (List.headD (raw_ints% [11746721284408572804621495]) 0) 62 false) (.node 226 (sourceLit (List.headD (raw_ints% [61861557729956898703418073338075325]) 0) 29 true) .empty .empty) .empty) (.node 229 (sourceLit (List.headD (raw_ints% [5754382031662691760592785]) 0) 63 false) .empty .empty)) (.node 232 (sourceLit (List.headD (raw_ints% [3046884172624568282236580439848472285]) 0) 22 true) (.node 231 (sourceLit (List.headD (raw_ints% [2823064943382477641912085]) 0) 64 false) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [346683038283735695868015]) 0) 67 false) .empty .empty)))

#time def treeG_J010_part040 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [24020958539686657335685425]) 0) 61 false) treeG_J010_part038 treeG_J010_part039)

#time def treeG_J010_part041 : IntSourceTree :=
  (.node 239 (sourceLit (List.headD (raw_ints% [5167683389335254623319]) 0) 73 false) (.node 237 (sourceLit (List.headD (raw_ints% [10489594293102479221143]) 0) 72 false) (.node 236 (sourceLit (List.headD (raw_ints% [22859951684910559928940691281625358295]) 0) 18 true) (.node 235 (sourceLit (List.headD (raw_ints% [170483146674958950263685]) 0) 68 false) .empty .empty) .empty) (.node 238 (sourceLit (List.headD (raw_ints% [27050268944289296976896074815994787355]) 0) 17 true) .empty .empty)) (.node 250 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 51 false) (.node 249 (sourceLit (List.headD (raw_ints% [851533192908404321721989400675]) 0) 47 false) (.node 248 (sourceLit (List.headD (raw_ints% [2350571658960137720027920824825]) 0) 45 false) .empty .empty) .empty) (.node 251 (sourceLit (List.headD (raw_ints% [273111678940159461532880432986875]) 0) 39 false) .empty .empty)))

#time def treeG_J010_part042 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [42509170947563735561754800323098825]) 0) 35 true) (.node 255 (sourceLit (List.headD (raw_ints% [48223810433058699484097322073657425]) 0) 36 false) (.node 254 (sourceLit (List.headD (raw_ints% [5717706086955675356330051189925]) 0) 48 false) (.node 253 (sourceLit (List.headD (raw_ints% [3695336465782554246679939441595925]) 0) 38 true) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [868139194925025636351523559775]) 0) 51 true) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [83136305718455187984517098426977775]) 0) 32 true) (.node 258 (sourceLit (List.headD (raw_ints% [16826894715073493425146732675]) 0) 52 false) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [4047736253639534072470500075]) 0) 54 false) .empty .empty)))

#time def treeG_J010_part043 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [73032721279543979793732867975]) 0) 51 true) treeG_J010_part041 treeG_J010_part042)

#time def treeG_J010_part044 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [4292142734072555829599154688510509795]) 0) 21 true) treeG_J010_part040 treeG_J010_part043)

#time def treeG_J010_part045 : IntSourceTree :=
  (.node 215 (sourceLit (List.headD (raw_ints% [1691820674427270939324336038475]) 0) 49 true) treeG_J010_part037 treeG_J010_part044)

#time def treeG_J010_part046 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [28900643087233374632747685]) 0) 61 false) (.node 264 (sourceLit (List.headD (raw_ints% [7420846960453364659045575]) 0) 63 false) (.node 263 (sourceLit (List.headD (raw_ints% [198941966165407802512406376637109475]) 0) 29 true) (.node 262 (sourceLit (List.headD (raw_ints% [978542393326293361276219275]) 0) 56 false) .empty .empty) .empty) (.node 265 (sourceLit (List.headD (raw_ints% [267373130297277599046622460759007825]) 0) 28 true) .empty .empty)) (.node 269 (sourceLit (List.headD (raw_ints% [4428212621219860671587328279115207575]) 0) 23 true) (.node 268 (sourceLit (List.headD (raw_ints% [7051860521374049817616035]) 0) 63 false) (.node 267 (sourceLit (List.headD (raw_ints% [3032796593196351175867847013091856175]) 0) 24 true) .empty .empty) .empty) (.node 270 (sourceLit (List.headD (raw_ints% [6896652686314308209706885]) 0) 63 false) .empty .empty)))

#time def treeG_J010_part047 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [101737669747788132028461]) 0) 69 false) (.node 274 (sourceLit (List.headD (raw_ints% [414280908496541785427145]) 0) 67 false) (.node 273 (sourceLit (List.headD (raw_ints% [19433937398667418417647028867229097615]) 0) 20 true) (.node 272 (sourceLit (List.headD (raw_ints% [844542844082633606776335]) 0) 66 false) .empty .empty) .empty) (.node 275 (sourceLit (List.headD (raw_ints% [113955029887432445731067711228147743395]) 0) 17 true) .empty .empty)) (.node 278 (sourceLit (List.headD (raw_ints% [12505834990512729194183]) 0) 72 false) (.node 277 (sourceLit (List.headD (raw_ints% [162592160064213702740794405169439970695]) 0) 16 true) .empty .empty) (.node 279 (sourceLit (List.headD (raw_ints% [440108942366431293149654697606912289995]) 0) 14 true) .empty .empty)))

#time def treeG_J010_part048 : IntSourceTree :=
  (.node 271 (sourceLit (List.headD (raw_ints% [13110470208012119396308921674145071105]) 0) 21 true) treeG_J010_part046 treeG_J010_part047)

#time def treeG_J010_part049 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [1578182192770688767980923429592225]) 0) 41 true) (.node 292 (sourceLit (List.headD (raw_ints% [115692803956972516839702545511675]) 0) 42 false) (.node 291 (sourceLit (List.headD (raw_ints% [446311074486102098739478637625]) 0) 48 false) (.node 290 (sourceLit (List.headD (raw_ints% [281955250230902595711607139325]) 0) 49 false) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [3216144651902881184249940000825]) 0) 48 true) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [220485300045270951343092865425]) 0) 54 true) (.node 296 (sourceLit (List.headD (raw_ints% [13501005996332793160399401304133625]) 0) 39 false) (.node 295 (sourceLit (List.headD (raw_ints% [463095422586434143478399201775]) 0) 53 false) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [9852248398514222307849341285911725]) 0) 38 true) .empty .empty)))

#time def treeG_J010_part050 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [38871060073982126555462263581576075]) 0) 32 true) (.node 302 (sourceLit (List.headD (raw_ints% [16448480981121977642007160162959375]) 0) 34 true) (.node 301 (sourceLit (List.headD (raw_ints% [2429737882224644091442753125]) 0) 55 false) (.node 300 (sourceLit (List.headD (raw_ints% [17588512066927314618672971896238175]) 0) 35 true) .empty .empty) .empty) (.node 303 (sourceLit (List.headD (raw_ints% [36547273421807214095262675]) 0) 61 false) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [51377893141830175085801096855233125]) 0) 31 true) (.node 305 (sourceLit (List.headD (raw_ints% [35345817143940259936679175]) 0) 61 false) .empty .empty) (.node 307 (sourceLit (List.headD (raw_ints% [8576960901412400914063095]) 0) 63 false) .empty .empty)))

#time def treeG_J010_part051 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [2539391786691670217635839225]) 0) 55 false) treeG_J010_part049 treeG_J010_part050)

#time def treeG_J010_part052 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [1695982083047187975210018822975]) 0) 46 false) treeG_J010_part048 treeG_J010_part051)

#time def treeG_J010_part053 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [15558118931215559715885]) 0) 72 false) (.node 311 (sourceLit (List.headD (raw_ints% [254599233933239410487175]) 0) 68 false) (.node 310 (sourceLit (List.headD (raw_ints% [844029366023568830793670855096556475]) 0) 26 true) (.node 309 (sourceLit (List.headD (raw_ints% [8349339011085407874639285]) 0) 63 false) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [2515896508846887778518085308574149705]) 0) 24 true) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [22773769550630471450531754986630596275]) 0) 20 true) (.node 315 (sourceLit (List.headD (raw_ints% [60949440455395708790865]) 0) 70 false) (.node 314 (sourceLit (List.headD (raw_ints% [3785448666148715647011968544679646955]) 0) 23 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [59779292575378215143889]) 0) 70 false) .empty .empty)))

#time def treeG_J010_part054 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [7397506192405674785550420897969525]) 0) 38 false) (.node 331 (sourceLit (List.headD (raw_ints% [304332673532729054484490988350725]) 0) 39 false) (.node 330 (sourceLit (List.headD (raw_ints% [1219916936928679069887908276175]) 0) 47 false) (.node 319 (sourceLit (List.headD (raw_ints% [458634475073592160679]) 0) 77 false) .empty .empty) .empty) (.node 332 (sourceLit (List.headD (raw_ints% [738441959604278017914410109525]) 0) 49 false) .empty .empty)) (.node 335 (sourceLit (List.headD (raw_ints% [149227470770382780634876421567559825]) 0) 36 true) (.node 334 (sourceLit (List.headD (raw_ints% [12149995390761437724829931191575]) 0) 48 true) .empty .empty) (.node 336 (sourceLit (List.headD (raw_ints% [4572902575616498784178717173975]) 0) 51 false) .empty .empty)))

#time def treeG_J010_part055 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [33885472779981101440974582588361295835]) 0) 19 true) treeG_J010_part053 treeG_J010_part054)

#time def treeG_J010_part056 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [725597744449175365083266925]) 0) 57 false) (.node 340 (sourceLit (List.headD (raw_ints% [6109830893127146798072856825]) 0) 54 false) (.node 339 (sourceLit (List.headD (raw_ints% [1177951489291365267420198586169723025]) 0) 32 true) (.node 338 (sourceLit (List.headD (raw_ints% [1780709295077241104169889656075]) 0) 52 true) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [481080725006723077188030131946417525]) 0) 31 true) .empty .empty)) (.node 344 (sourceLit (List.headD (raw_ints% [21705579500900484777171525]) 0) 62 false) (.node 343 (sourceLit (List.headD (raw_ints% [853760816626398766576051873792290525]) 0) 29 true) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [976500792070150450728169973851426575]) 0) 28 true) .empty .empty)))

#time def treeG_J010_part057 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [40907409217496285774486013052034543295]) 0) 21 true) (.node 349 (sourceLit (List.headD (raw_ints% [14076655561349194815038497701259300425]) 0) 23 true) (.node 348 (sourceLit (List.headD (raw_ints% [10102061281450752010510155]) 0) 63 false) (.node 347 (sourceLit (List.headD (raw_ints% [10119944051112173646097233781847823825]) 0) 24 true) .empty .empty) .empty) (.node 350 (sourceLit (List.headD (raw_ints% [9802025335856507539571685]) 0) 63 false) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [61074750884432990494931701007143692945]) 0) 20 true) (.node 352 (sourceLit (List.headD (raw_ints% [1192251027383281677121065]) 0) 66 false) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [581438703101254036389495]) 0) 67 false) .empty .empty)))

#time def treeG_J010_part058 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [41790991200647145240610665]) 0) 61 false) treeG_J010_part056 treeG_J010_part057)

#time def treeG_J010_part059 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [474541362830213116694535642055374825]) 0) 35 false) treeG_J010_part055 treeG_J010_part058)

#time def treeG_J010_part060 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [578277130705282983957057061886703375]) 0) 27 true) treeG_J010_part052 treeG_J010_part059)

#time def treeG_J010_part061 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [81751661134950990609504968733204075]) 0) 31 true) treeG_J010_part045 treeG_J010_part060)

#time def treeG_J010_part062 : IntSourceTree :=
  (.node 170 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 48 false) treeG_J010_part030 treeG_J010_part061)

#time def treeG_J010_part063 : IntSourceTree :=
  (.node 371 (sourceLit (List.headD (raw_ints% [386802931221288485574214819275]) 0) 49 false) (.node 358 (sourceLit (List.headD (raw_ints% [34767622594352756755523]) 0) 71 false) (.node 357 (sourceLit (List.headD (raw_ints% [566168465555961383676221754402739110105]) 0) 16 true) (.node 356 (sourceLit (List.headD (raw_ints% [142060092073794703134999]) 0) 69 false) .empty .empty) .empty) (.node 359 (sourceLit (List.headD (raw_ints% [1728561315552359199072718588048210643445]) 0) 14 true) .empty .empty)) (.node 374 (sourceLit (List.headD (raw_ints% [13710234963488429857474114616338425]) 0) 39 false) (.node 373 (sourceLit (List.headD (raw_ints% [6169912490319993255907580438925]) 0) 48 false) (.node 372 (sourceLit (List.headD (raw_ints% [158438542295161012874319193695975]) 0) 40 true) .empty .empty) .empty) (.node 375 (sourceLit (List.headD (raw_ints% [19559522152144384020484318419975]) 0) 49 true) .empty .empty)))

#time def treeG_J010_part064 : IntSourceTree :=
  (.node 381 (sourceLit (List.headD (raw_ints% [920023252725625676657525925]) 0) 57 false) (.node 379 (sourceLit (List.headD (raw_ints% [1790866862224007785040433012975]) 0) 53 true) (.node 378 (sourceLit (List.headD (raw_ints% [513950356424270005925933007199021725]) 0) 36 false) (.node 377 (sourceLit (List.headD (raw_ints% [5454843775797582589551088635675]) 0) 52 false) .empty .empty) .empty) (.node 380 (sourceLit (List.headD (raw_ints% [1107597441023656008945506698584770325]) 0) 33 true) .empty .empty)) (.node 383 (sourceLit (List.headD (raw_ints% [433219557074717652321165525]) 0) 58 false) (.node 382 (sourceLit (List.headD (raw_ints% [415286801082235166620001491294580025]) 0) 32 true) .empty .empty) (.node 384 (sourceLit (List.headD (raw_ints% [698276576330470260354202819465986225]) 0) 30 true) .empty .empty)))

#time def treeG_J010_part065 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [203231494755713953276474026784094325]) 0) 37 true) treeG_J010_part063 treeG_J010_part064)

#time def treeG_J010_part066 : IntSourceTree :=
  (.node 390 (sourceLit (List.headD (raw_ints% [10700538097254919491863814280873074525]) 0) 24 true) (.node 388 (sourceLit (List.headD (raw_ints% [7806835528291041710269005534301010325]) 0) 25 true) (.node 387 (sourceLit (List.headD (raw_ints% [24637069397822343412484475]) 0) 62 false) (.node 386 (sourceLit (List.headD (raw_ints% [770989219502829750384965586430494075]) 0) 29 true) .empty .empty) .empty) (.node 389 (sourceLit (List.headD (raw_ints% [11854783551816096146381025]) 0) 63 false) .empty .empty)) (.node 393 (sourceLit (List.headD (raw_ints% [694391221584383766212745]) 0) 67 false) (.node 392 (sourceLit (List.headD (raw_ints% [30843823182108734660413671817737944475]) 0) 22 true) (.node 391 (sourceLit (List.headD (raw_ints% [5728437592924676971776885]) 0) 64 false) .empty .empty) .empty) (.node 394 (sourceLit (List.headD (raw_ints% [45932956219838127906883826828425105125]) 0) 21 true) .empty .empty)))

#time def treeG_J010_part067 : IntSourceTree :=
  (.node 412 (sourceLit (List.headD (raw_ints% [35163902838298953234019529025]) 0) 49 false) (.node 398 (sourceLit (List.headD (raw_ints% [430626574436036977912323424049293926765]) 0) 17 true) (.node 397 (sourceLit (List.headD (raw_ints% [41140399749208243995555]) 0) 71 false) (.node 396 (sourceLit (List.headD (raw_ints% [279487321177081271284337242544324681745]) 0) 18 true) .empty .empty) .empty) (.node 399 (sourceLit (List.headD (raw_ints% [20091319391997807613795]) 0) 72 false) .empty .empty)) (.node 414 (sourceLit (List.headD (raw_ints% [24489820371401424236645092069425]) 0) 48 false) (.node 413 (sourceLit (List.headD (raw_ints% [8665014530766962888544974447537325]) 0) 38 true) .empty .empty) (.node 415 (sourceLit (List.headD (raw_ints% [368591230186197658354462255428974625]) 0) 36 false) .empty .empty)))

#time def treeG_J010_part068 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [337640941279671201226035]) 0) 68 false) treeG_J010_part066 treeG_J010_part067)

#time def treeG_J010_part069 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [51476500859661679172006925]) 0) 61 false) treeG_J010_part065 treeG_J010_part068)

#time def treeG_J010_part070 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [8379698803182524994376023456731745075]) 0) 31 true) (.node 419 (sourceLit (List.headD (raw_ints% [17624362894868005457050054816538418225]) 0) 32 false) (.node 418 (sourceLit (List.headD (raw_ints% [12690396846672406283272066927425]) 0) 52 false) (.node 417 (sourceLit (List.headD (raw_ints% [2100393320875924742906327856328129425]) 0) 35 true) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [224622086639641866479813233725]) 0) 57 true) .empty .empty)) (.node 424 (sourceLit (List.headD (raw_ints% [259574921067513774103793325]) 0) 59 false) (.node 423 (sourceLit (List.headD (raw_ints% [5790828000689363899343971986920989875]) 0) 29 true) (.node 422 (sourceLit (List.headD (raw_ints% [1114448761002075988231784925]) 0) 57 false) .empty .empty) .empty) (.node 425 (sourceLit (List.headD (raw_ints% [4609711818573611632105452581876463225]) 0) 28 true) .empty .empty)))

#time def treeG_J010_part071 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [130301200338582426095335015441934649105]) 0) 21 true) (.node 429 (sourceLit (List.headD (raw_ints% [48378028664979138867113546573148782175]) 0) 23 true) (.node 428 (sourceLit (List.headD (raw_ints% [908438007273224462623395]) 0) 67 false) (.node 427 (sourceLit (List.headD (raw_ints% [39223365997068930378540563749703796975]) 0) 24 true) .empty .empty) .empty) (.node 430 (sourceLit (List.headD (raw_ints% [13907541767775684753190365]) 0) 63 false) .empty .empty)) (.node 433 (sourceLit (List.headD (raw_ints% [185675834572436886788377673534759862855]) 0) 20 true) (.node 432 (sourceLit (List.headD (raw_ints% [3343935538158113617534755]) 0) 65 false) .empty .empty) (.node 434 (sourceLit (List.headD (raw_ints% [807343740067513496035995]) 0) 67 false) .empty .empty)))

#time def treeG_J010_part072 : IntSourceTree :=
  (.node 426 (sourceLit (List.headD (raw_ints% [61162010518676213103403185]) 0) 61 false) treeG_J010_part070 treeG_J010_part071)

#time def treeG_J010_part073 : IntSourceTree :=
  (.node 454 (sourceLit (List.headD (raw_ints% [11187624747127696373009544531937875]) 0) 40 true) (.node 438 (sourceLit (List.headD (raw_ints% [47513176904063731235587]) 0) 71 false) (.node 437 (sourceLit (List.headD (raw_ints% [1669730103860688786598476185951858343855]) 0) 16 true) (.node 436 (sourceLit (List.headD (raw_ints% [48895212301469124522759]) 0) 71 false) .empty .empty) .empty) (.node 439 (sourceLit (List.headD (raw_ints% [5161463875424232447524456196740492184795]) 0) 14 true) .empty .empty)) (.node 457 (sourceLit (List.headD (raw_ints% [39615014854972546767943930039275]) 0) 51 true) (.node 456 (sourceLit (List.headD (raw_ints% [285911362470955805815468141106534475]) 0) 38 false) (.node 455 (sourceLit (List.headD (raw_ints% [5506167815443226032141176311175]) 0) 52 false) .empty .empty) .empty) (.node 458 (sourceLit (List.headD (raw_ints% [1307171838650097374416130431763575575]) 0) 37 true) .empty .empty)))

#time def treeG_J010_part074 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [2546275712179446819494884583727501825]) 0) 31 true) (.node 462 (sourceLit (List.headD (raw_ints% [3982206001050144913878010982718582525]) 0) 33 true) (.node 461 (sourceLit (List.headD (raw_ints% [450164196532009358636283993375]) 0) 57 true) (.node 460 (sourceLit (List.headD (raw_ints% [9365980167945830732997780757561594275]) 0) 34 false) .empty .empty) .empty) (.node 463 (sourceLit (List.headD (raw_ints% [85153650490919791988827425]) 0) 61 false) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [1919361299535390940860243497722984575]) 0) 30 true) (.node 465 (sourceLit (List.headD (raw_ints% [156621919348190415759779475]) 0) 60 false) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [18262470560426934845459355]) 0) 63 false) .empty .empty)))

#time def treeG_J010_part075 : IntSourceTree :=
  (.node 459 (sourceLit (List.headD (raw_ints% [905078981806025879269531246275]) 0) 57 false) treeG_J010_part073 treeG_J010_part074)

#time def treeG_J010_part076 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [1099272199655216935933818196018756297155]) 0) 17 true) treeG_J010_part072 treeG_J010_part075)

#time def treeG_J010_part077 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [28705327303377381588841752767925]) 0) 50 true) treeG_J010_part069 treeG_J010_part076)

#time def treeG_J010_part078 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [1955153094989346085109265]) 0) 66 false) (.node 471 (sourceLit (List.headD (raw_ints% [1022388021856375972676685]) 0) 67 false) (.node 470 (sourceLit (List.headD (raw_ints% [18838745283862109687624866146137853825]) 0) 25 true) (.node 469 (sourceLit (List.headD (raw_ints% [17215232680927086657567615]) 0) 63 false) .empty .empty) .empty) (.node 472 (sourceLit (List.headD (raw_ints% [49728688578236845717460671812098352315]) 0) 23 true) .empty .empty)) (.node 476 (sourceLit (List.headD (raw_ints% [409892439239067832324740476737215807705]) 0) 19 true) (.node 475 (sourceLit (List.headD (raw_ints% [58712849848480286851245]) 0) 71 false) (.node 474 (sourceLit (List.headD (raw_ints% [69871439176299379440746923353167378865]) 0) 22 true) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [56650024853730005049963]) 0) 71 false) .empty .empty)))

#time def treeG_J010_part079 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [13076352925411238262803999241675]) 0) 54 true) (.node 496 (sourceLit (List.headD (raw_ints% [72754669826923189845971163257325]) 0) 50 false) (.node 495 (sourceLit (List.headD (raw_ints% [726595222094283942290767680450986625]) 0) 36 true) (.node 479 (sourceLit (List.headD (raw_ints% [856933047252060113181]) 0) 77 false) .empty .empty) .empty) (.node 497 (sourceLit (List.headD (raw_ints% [6674975120411217635953818114032681025]) 0) 35 false) .empty .empty)) (.node 500 (sourceLit (List.headD (raw_ints% [2034780050251693625018875726275]) 0) 57 false) (.node 499 (sourceLit (List.headD (raw_ints% [101283360568474237419682402449407255025]) 0) 32 true) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [158235381490315816722340515577717253475]) 0) 31 false) .empty .empty)))

#time def treeG_J010_part080 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [619551764712325904343076380951282208545]) 0) 18 true) treeG_J010_part078 treeG_J010_part079)

#time def treeG_J010_part081 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [206454880343461110051570603958838228625]) 0) 24 true) (.node 505 (sourceLit (List.headD (raw_ints% [36130699576297537479812700757763565975]) 0) 28 true) (.node 504 (sourceLit (List.headD (raw_ints% [421654282859844561806826075]) 0) 59 false) (.node 503 (sourceLit (List.headD (raw_ints% [121639764032915273344752379460073650925]) 0) 29 true) .empty .empty) .empty) (.node 506 (sourceLit (List.headD (raw_ints% [47729954414757101328188145]) 0) 62 false) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [20522923594078488561944865]) 0) 63 false) (.node 509 (sourceLit (List.headD (raw_ints% [202954215085243970479058919150073511025]) 0) 23 true) (.node 508 (sourceLit (List.headD (raw_ints% [10994966502241139144472195]) 0) 64 false) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [472538648745005083908660701234476673295]) 0) 21 true) .empty .empty)))

#time def treeG_J010_part082 : IntSourceTree :=
  (.node 517 (sourceLit (List.headD (raw_ints% [4888548923964396530597371441843594579425]) 0) 16 true) (.node 515 (sourceLit (List.headD (raw_ints% [3372499907627943348273984898583955950205]) 0) 17 true) (.node 514 (sourceLit (List.headD (raw_ints% [573904677460916294536635]) 0) 68 false) (.node 513 (sourceLit (List.headD (raw_ints% [609983182679352644690993075458813774185]) 0) 20 true) .empty .empty) .empty) (.node 516 (sourceLit (List.headD (raw_ints% [68530487395491449179731]) 0) 71 false) .empty .empty)) (.node 519 (sourceLit (List.headD (raw_ints% [14664192595370196491453987993700538488645]) 0) 14 true) (.node 518 (sourceLit (List.headD (raw_ints% [65786872803396278864339]) 0) 71 false) .empty .empty) (.node 537 (sourceLit (List.headD (raw_ints% [14046210585236967076739386662075]) 0) 54 false) .empty .empty)))

#time def treeG_J010_part083 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [4835168636692894163878725]) 0) 65 false) treeG_J010_part081 treeG_J010_part082)

#time def treeG_J010_part084 : IntSourceTree :=
  (.node 502 (sourceLit (List.headD (raw_ints% [901442841825020793260799771675]) 0) 57 true) treeG_J010_part080 treeG_J010_part083)

#time def treeG_J010_part085 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [902124071028948151596710391075]) 0) 58 true) (.node 541 (sourceLit (List.headD (raw_ints% [4519724297035396608674035445925]) 0) 57 false) (.node 540 (sourceLit (List.headD (raw_ints% [120015320904365898885677963964530443575]) 0) 33 true) (.node 539 (sourceLit (List.headD (raw_ints% [16696668852635341779882124226775]) 0) 55 true) .empty .empty) .empty) (.node 542 (sourceLit (List.headD (raw_ints% [166199793492416106550096537543154418525]) 0) 32 false) .empty .empty)) (.node 546 (sourceLit (List.headD (raw_ints% [32291976977226755598092213762317596825]) 0) 29 true) (.node 545 (sourceLit (List.headD (raw_ints% [33129045438956768255880825]) 0) 63 false) (.node 544 (sourceLit (List.headD (raw_ints% [116547212608556379705762610292618647275]) 0) 30 true) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [14733741927165083241364395]) 0) 64 false) .empty .empty)))

#time def treeG_J010_part086 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [720003885425887019692365]) 0) 68 false) (.node 551 (sourceLit (List.headD (raw_ints% [12343819419227480780531385]) 0) 64 false) (.node 550 (sourceLit (List.headD (raw_ints% [165276724517519751103809186857797803375]) 0) 24 true) (.node 549 (sourceLit (List.headD (raw_ints% [26764633328037469920321165]) 0) 63 false) .empty .empty) .empty) (.node 552 (sourceLit (List.headD (raw_ints% [373081271588531392473739357610279968665]) 0) 22 true) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [339053278066995147131655]) 0) 69 false) (.node 554 (sourceLit (List.headD (raw_ints% [470240304326753885809499228752479016455]) 0) 21 true) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [2552715029149807683624503945109524334795]) 0) 18 true) .empty .empty)))

#time def treeG_J010_part087 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [175038349874683221383299045743435441975]) 0) 25 true) treeG_J010_part085 treeG_J010_part086)

#time def treeG_J010_part088 : IntSourceTree :=
  (.node 582 (sourceLit (List.headD (raw_ints% [9940891435895814010608870663525]) 0) 57 false) (.node 580 (sourceLit (List.headD (raw_ints% [20766228953138729029919875679325]) 0) 56 true) (.node 559 (sourceLit (List.headD (raw_ints% [38365015291330355242547]) 0) 72 false) (.node 558 (sourceLit (List.headD (raw_ints% [3649445394539744721911218679941030162335]) 0) 17 true) .empty .empty) .empty) (.node 581 (sourceLit (List.headD (raw_ints% [1118357948725243007807764227293960802075]) 0) 31 true) .empty .empty)) (.node 584 (sourceLit (List.headD (raw_ints% [451272862655903998079258608575]) 0) 60 true) (.node 583 (sourceLit (List.headD (raw_ints% [2780836459911572978146296980150544347325]) 0) 29 false) .empty .empty) (.node 585 (sourceLit (List.headD (raw_ints% [896247001292153500166288181583185612225]) 0) 28 true) .empty .empty)))

#time def treeG_J010_part089 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [2171888943535310933752286288490288180705]) 0) 21 true) (.node 589 (sourceLit (List.headD (raw_ints% [1197352583912221800587333446797410024775]) 0) 23 true) (.node 588 (sourceLit (List.headD (raw_ints% [18472517352089027338256595]) 0) 64 false) (.node 587 (sourceLit (List.headD (raw_ints% [1860231646199051248226331076829487968175]) 0) 24 true) .empty .empty) .empty) (.node 590 (sourceLit (List.headD (raw_ints% [33006343061996451278697465]) 0) 63 false) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [2374666990028898495098921785423425975135]) 0) 20 true) (.node 592 (sourceLit (List.headD (raw_ints% [1877162695633646654163165]) 0) 67 false) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [866103093390857744848095]) 0) 68 false) .empty .empty)))

#time def treeG_J010_part090 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [84786227341069971695335155]) 0) 62 false) treeG_J010_part088 treeG_J010_part089)

#time def treeG_J010_part091 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [80410949937252893309499]) 0) 71 false) treeG_J010_part087 treeG_J010_part090)

#time def treeG_J010_part092 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [9289318797711412384786078977559832175]) 0) 36 false) treeG_J010_part084 treeG_J010_part091)

#time def treeG_J010_part093 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [15708265234388944334135779107701393325]) 0) 26 true) treeG_J010_part077 treeG_J010_part092)

#time def treeG_J010_part094 : IntSourceTree :=
  (.node 621 (sourceLit (List.headD (raw_ints% [12642976625087062819296955562625]) 0) 58 true) (.node 598 (sourceLit (List.headD (raw_ints% [95035027071109507754659]) 0) 71 false) (.node 597 (sourceLit (List.headD (raw_ints% [15533171309234064938398660119032600098935]) 0) 16 true) (.node 596 (sourceLit (List.headD (raw_ints% [201992303276012248772193]) 0) 70 false) .empty .empty) .empty) (.node 599 (sourceLit (List.headD (raw_ints% [43726933717265719059125510885355944108715]) 0) 14 true) .empty .empty)) (.node 624 (sourceLit (List.headD (raw_ints% [362172959065016169731507448805395374325]) 0) 33 false) (.node 623 (sourceLit (List.headD (raw_ints% [1355376938365595270275697631825]) 0) 61 false) (.node 622 (sourceLit (List.headD (raw_ints% [160569717777207389294732595604639402575]) 0) 35 true) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [451405378837659825152282131875]) 0) 61 true) .empty .empty)))

#time def treeG_J010_part095 : IntSourceTree :=
  (.node 631 (sourceLit (List.headD (raw_ints% [322851931918265164033845]) 0) 70 false) (.node 629 (sourceLit (List.headD (raw_ints% [47125436080318639432705215]) 0) 63 false) (.node 628 (sourceLit (List.headD (raw_ints% [210649162040546003355379003885756565775]) 0) 28 true) (.node 627 (sourceLit (List.headD (raw_ints% [55318743486739805212606365]) 0) 63 false) .empty .empty) .empty) (.node 630 (sourceLit (List.headD (raw_ints% [129009482424337756185440532492451527675]) 0) 27 true) .empty .empty)) (.node 633 (sourceLit (List.headD (raw_ints% [72322425637984977154425]) 0) 72 false) (.node 632 (sourceLit (List.headD (raw_ints% [224850958993347442659818366360001026505]) 0) 25 true) .empty .empty) (.node 634 (sourceLit (List.headD (raw_ints% [238053335712768076161177819583868369835]) 0) 24 true) .empty .empty)))

#time def treeG_J010_part096 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [107994378039365843071024495977608501925]) 0) 32 true) treeG_J010_part094 treeG_J010_part095)

#time def treeG_J010_part097 : IntSourceTree :=
  (.node 663 (sourceLit (List.headD (raw_ints% [23333760335394118807872069217544387876925]) 0) 29 true) (.node 638 (sourceLit (List.headD (raw_ints% [1485465739336790027060930179886446242075]) 0) 20 true) (.node 637 (sourceLit (List.headD (raw_ints% [60790676669379677731347]) 0) 72 false) (.node 636 (sourceLit (List.headD (raw_ints% [1140309350209796664250685809548231030195]) 0) 21 true) .empty .empty) .empty) (.node 639 (sourceLit (List.headD (raw_ints% [3541875736236197032007]) 0) 76 false) .empty .empty)) (.node 666 (sourceLit (List.headD (raw_ints% [225745082532500447561988733515]) 0) 63 true) (.node 665 (sourceLit (List.headD (raw_ints% [24075316381453188362982764905128489569025]) 0) 28 false) (.node 664 (sourceLit (List.headD (raw_ints% [5872780616118285079182049135875]) 0) 60 false) .empty .empty) .empty) (.node 667 (sourceLit (List.headD (raw_ints% [53432889909956260404138210863706065017425]) 0) 24 true) .empty .empty)))

#time def treeG_J010_part098 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [12015794385545337835129453661616639721185]) 0) 20 true) (.node 671 (sourceLit (List.headD (raw_ints% [14341324806779921857984101870543507361695]) 0) 21 true) (.node 670 (sourceLit (List.headD (raw_ints% [61244529098640827586712965]) 0) 63 false) (.node 669 (sourceLit (List.headD (raw_ints% [12284193786682722414156922801891010184825]) 0) 23 true) .empty .empty) .empty) (.node 672 (sourceLit (List.headD (raw_ints% [3288468215058595970378355]) 0) 67 false) .empty .empty)) (.node 675 (sourceLit (List.headD (raw_ints% [49266464111640446499631531391974930101405]) 0) 17 true) (.node 674 (sourceLit (List.headD (raw_ints% [1448214527024661524093505]) 0) 68 false) .empty .empty) (.node 676 (sourceLit (List.headD (raw_ints% [325057512047850348944247]) 0) 70 false) .empty .empty)))

#time def treeG_J010_part099 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [18423113067325388937174885]) 0) 65 false) treeG_J010_part097 treeG_J010_part098)

#time def treeG_J010_part100 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [65881226915482824714555]) 0) 72 false) treeG_J010_part096 treeG_J010_part099)

#time def treeG_J010_part101 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [24939271405768115107550960872949357584425]) 0) 29 false) (.node 704 (sourceLit (List.headD (raw_ints% [26231144007914248165724128807987550871525]) 0) 30 true) (.node 679 (sourceLit (List.headD (raw_ints% [146412680917843404404673552140109174876885]) 0) 14 true) (.node 678 (sourceLit (List.headD (raw_ints% [148127679606409203170729]) 0) 71 false) .empty .empty) .empty) (.node 705 (sourceLit (List.headD (raw_ints% [3162092997477972452167165633875]) 0) 62 false) .empty .empty)) (.node 709 (sourceLit (List.headD (raw_ints% [100259468458284472064693865]) 0) 63 false) (.node 708 (sourceLit (List.headD (raw_ints% [51747696613631892377295178832620012491225]) 0) 25 true) (.node 707 (sourceLit (List.headD (raw_ints% [451545483808487634929190073395]) 0) 63 true) .empty .empty) .empty) (.node 710 (sourceLit (List.headD (raw_ints% [11252117927288020364673398541951397963425]) 0) 24 true) .empty .empty)))

#time def treeG_J010_part102 : IntSourceTree :=
  (.node 716 (sourceLit (List.headD (raw_ints% [40143989309962073185626044915589081859845]) 0) 18 true) (.node 714 (sourceLit (List.headD (raw_ints% [10111367699843193225840031104945692762505]) 0) 21 true) (.node 713 (sourceLit (List.headD (raw_ints% [2131309404850836335907555]) 0) 68 false) (.node 712 (sourceLit (List.headD (raw_ints% [12542517134833142316705554939663499149655]) 0) 22 true) .empty .empty) .empty) (.node 715 (sourceLit (List.headD (raw_ints% [921164711700798926377065]) 0) 69 false) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [45562901189498601357157790252962615896945]) 0) 17 true) (.node 717 (sourceLit (List.headD (raw_ints% [203476158709090993481553]) 0) 71 false) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [91457667826630050658617]) 0) 72 false) .empty .empty)))

#time def treeG_J010_part103 : IntSourceTree :=
  (.node 711 (sourceLit (List.headD (raw_ints% [40582005455871857088546885]) 0) 64 false) treeG_J010_part101 treeG_J010_part102)

#time def treeG_J010_part104 : IntSourceTree :=
  (.node 750 (sourceLit (List.headD (raw_ints% [139274407817928116542674765]) 0) 63 false) (.node 748 (sourceLit (List.headD (raw_ints% [451582330034622285707064423165]) 0) 64 true) (.node 747 (sourceLit (List.headD (raw_ints% [1649546259879115627287399706732464950420625]) 0) 24 false) (.node 746 (sourceLit (List.headD (raw_ints% [1693919040005236449864577183695]) 0) 64 false) .empty .empty) .empty) (.node 749 (sourceLit (List.headD (raw_ints% [401697379122372416604204507859069089744975]) 0) 23 true) .empty .empty)) (.node 752 (sourceLit (List.headD (raw_ints% [27428132595637473207033465]) 0) 65 false) (.node 751 (sourceLit (List.headD (raw_ints% [165692562029828403976790274800678860053105]) 0) 21 true) .empty .empty) (.node 753 (sourceLit (List.headD (raw_ints% [88324342693119800698514985855691353476055]) 0) 20 true) .empty .empty)))

#time def treeG_J010_part105 : IntSourceTree :=
  (.node 759 (sourceLit (List.headD (raw_ints% [582593738114134217309851091907292679474235]) 0) 14 true) (.node 757 (sourceLit (List.headD (raw_ints% [263705287375503663911363127632658469045215]) 0) 16 true) (.node 756 (sourceLit (List.headD (raw_ints% [298053599826474288716409]) 0) 71 false) (.node 755 (sourceLit (List.headD (raw_ints% [274297302283341736727249463966287238298755]) 0) 17 true) .empty .empty) .empty) (.node 758 (sourceLit (List.headD (raw_ints% [258824637811772783792377]) 0) 71 false) .empty .empty)) (.node 787 (sourceLit (List.headD (raw_ints% [7227221643829433434387498808175]) 0) 63 false) (.node 786 (sourceLit (List.headD (raw_ints% [129431869925267644398163378120989127062825]) 0) 30 true) .empty .empty) (.node 788 (sourceLit (List.headD (raw_ints% [850646978246373759832347442782542481455925]) 0) 26 false) .empty .empty)))

#time def treeG_J010_part106 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [2814404282677011147721605]) 0) 68 false) treeG_J010_part104 treeG_J010_part105)

#time def treeG_J010_part107 : IntSourceTree :=
  (.node 745 (sourceLit (List.headD (raw_ints% [233924468444767173688775795369028896541225]) 0) 28 true) treeG_J010_part103 treeG_J010_part106)

#time def treeG_J010_part108 : IntSourceTree :=
  (.node 677 (sourceLit (List.headD (raw_ints% [57446627104192921573645231692054185833545]) 0) 16 true) treeG_J010_part100 treeG_J010_part107)

#time def treeG_J010_part109 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [39106487496638303736337477375372830356775]) 0) 22 true) (.node 792 (sourceLit (List.headD (raw_ints% [76575022447497630830042359930507680451725]) 0) 23 true) (.node 791 (sourceLit (List.headD (raw_ints% [12336550295257032431765985]) 0) 67 false) (.node 790 (sourceLit (List.headD (raw_ints% [195222630597542198119765554658558845890775]) 0) 25 true) .empty .empty) .empty) (.node 793 (sourceLit (List.headD (raw_ints% [18902894976234127863403245]) 0) 66 false) .empty .empty)) (.node 797 (sourceLit (List.headD (raw_ints% [392631040943857583951265]) 0) 71 false) (.node 796 (sourceLit (List.headD (raw_ints% [117076656486689831770811709525349078219455]) 0) 19 true) (.node 795 (sourceLit (List.headD (raw_ints% [473309892744053055336135]) 0) 71 false) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [109071193093002531277102668689847926574135]) 0) 18 true) .empty .empty)))

#time def treeG_J010_part110 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [6081431617091521935855707474273204208451695]) 0) 21 true) (.node 829 (sourceLit (List.headD (raw_ints% [14012049031064352573921763592379748793039775]) 0) 23 false) (.node 828 (sourceLit (List.headD (raw_ints% [1919700993466013930023640807835]) 0) 66 false) (.node 827 (sourceLit (List.headD (raw_ints% [18216825610313374110252312106219073214462225]) 0) 24 true) .empty .empty) .empty) (.node 830 (sourceLit (List.headD (raw_ints% [3612998433621712782717187447815]) 0) 63 true) .empty .empty)) (.node 833 (sourceLit (List.headD (raw_ints% [1136876016466842292582162773032431533751545]) 0) 20 true) (.node 832 (sourceLit (List.headD (raw_ints% [71264269766418786247094415]) 0) 65 false) .empty .empty) (.node 834 (sourceLit (List.headD (raw_ints% [13274086410880105567960035]) 0) 67 false) .empty .empty)))

#time def treeG_J010_part111 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [2615108906017855205215]) 0) 78 false) treeG_J010_part109 treeG_J010_part110)

#time def treeG_J010_part112 : IntSourceTree :=
  (.node 868 (sourceLit (List.headD (raw_ints% [19918119566806121629917006991784158177374075]) 0) 25 true) (.node 838 (sourceLit (List.headD (raw_ints% [526437444075942384110153]) 0) 71 false) (.node 837 (sourceLit (List.headD (raw_ints% [1609521216411533644421624224772926782466065]) 0) 16 true) (.node 836 (sourceLit (List.headD (raw_ints% [648566185661631821955861]) 0) 71 false) .empty .empty) .empty) (.node 839 (sourceLit (List.headD (raw_ints% [2907684440861946783557434306167840970898085]) 0) 14 true) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [3613097126024074838976641575695]) 0) 64 true) (.node 870 (sourceLit (List.headD (raw_ints% [14402494292259436970161294701696866484821325]) 0) 24 false) (.node 869 (sourceLit (List.headD (raw_ints% [32521645475063170307678575311885]) 0) 63 false) .empty .empty) .empty) (.node 872 (sourceLit (List.headD (raw_ints% [5928281572196526674195622754412188847548245]) 0) 22 true) .empty .empty)))

#time def treeG_J010_part113 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [1391378830225528581867418887393230929317795]) 0) 17 true) (.node 876 (sourceLit (List.headD (raw_ints% [1994364584528130038856725669006875748095935]) 0) 18 true) (.node 875 (sourceLit (List.headD (raw_ints% [9487607268927681125270955]) 0) 68 false) (.node 874 (sourceLit (List.headD (raw_ints% [1058663041473565685109487818281685873037995]) 0) 21 true) .empty .empty) .empty) (.node 877 (sourceLit (List.headD (raw_ints% [904501330379406059960457]) 0) 71 false) .empty .empty)) (.node 909 (sourceLit (List.headD (raw_ints% [173357005565513325613257819526653014212032375]) 0) 23 true) (.node 879 (sourceLit (List.headD (raw_ints% [359070474090799650976393]) 0) 72 false) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [68656289383748053398074338071585]) 0) 63 false) .empty .empty)))

#time def treeG_J010_part114 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [26180687395092329191845585]) 0) 67 false) treeG_J010_part112 treeG_J010_part113)

#time def treeG_J010_part115 : IntSourceTree :=
  (.node 835 (sourceLit (List.headD (raw_ints% [2228517897501509702398349088057573904534845]) 0) 17 true) treeG_J010_part111 treeG_J010_part114)

#time def treeG_J010_part116 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [6893342526281153837447511]) 0) 69 false) (.node 914 (sourceLit (List.headD (raw_ints% [39087288379304552815731135]) 0) 67 false) (.node 913 (sourceLit (List.headD (raw_ints% [46289376561105371100982819262265079246634415]) 0) 20 true) (.node 912 (sourceLit (List.headD (raw_ints% [1806584195146920628881444335055]) 0) 66 true) .empty .empty) .empty) (.node 915 (sourceLit (List.headD (raw_ints% [31648699429652592221105261096956374032680995]) 0) 17 true) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [19354376842746510526321267892123853898186635]) 0) 14 true) (.node 918 (sourceLit (List.headD (raw_ints% [1282565216682869735810761]) 0) 71 false) (.node 917 (sourceLit (List.headD (raw_ints% [14345395459813506666432181127282079202301415]) 0) 16 true) .empty .empty) .empty) (.node 950 (sourceLit (List.headD (raw_ints% [46939874964443190645854778557087470174213425]) 0) 26 true) .empty .empty)))

#time def treeG_J010_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [7413583711281115545562133856987374571146265]) 0) 20 true) (.node 954 (sourceLit (List.headD (raw_ints% [11307678379907951353968332860995848343399105]) 0) 23 true) (.node 953 (sourceLit (List.headD (raw_ints% [56456574244822366287832380645]) 0) 72 true) (.node 952 (sourceLit (List.headD (raw_ints% [60612405466359760033158011363958814203285285]) 0) 24 false) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [7399920277594217922615045]) 0) 70 false) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [3238504157396994521141190559972212068245905]) 0) 19 true) (.node 957 (sourceLit (List.headD (raw_ints% [5084339865522341717526597]) 0) 70 false) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [14429605353001095075537]) 0) 78 false) .empty .empty)))

#time def treeG_J010_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [4516836656860758014815686227955]) 0) 68 false) treeG_J010_part116 treeG_J010_part117)

#time def treeG_J010_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [950443662209867995428959]) 0) 73 false) (.node 996 (sourceLit (List.headD (raw_ints% [22706338584095717853012669]) 0) 69 false) (.node 995 (sourceLit (List.headD (raw_ints% [1415734133198565181086841345110512213922404445]) 0) 17 true) (.node 994 (sourceLit (List.headD (raw_ints% [3613259838957010746974088092415]) 0) 67 true) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [222889283301182190791556102296313907074379065]) 0) 16 true) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [2031117065004249497577912514352930527125359955]) 0) 21 false) (.node 999 (sourceLit (List.headD (raw_ints% [187909889230661138826714927946097718469551285]) 0) 14 true) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [3613289438638121123845778552595]) 0) 68 true) .empty .empty)))

#time def treeG_J010_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [225832009061044076222726972829]) 0) 73 true) (.node 1039 (sourceLit (List.headD (raw_ints% [719569976561850474220367]) 0) 74 false) (.node 1038 (sourceLit (List.headD (raw_ints% [209935266671594212706991340056425058801395445]) 0) 17 true) (.node 1037 (sourceLit (List.headD (raw_ints% [2202749839821672016935759]) 0) 73 false) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [66411480213334549103580041804404289081933923005]) 0) 17 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [3455056017433476038442559]) 0) 73 false) (.node 1077 (sourceLit (List.headD (raw_ints% [10865749103526343560445186375164187818028176015]) 0) 16 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [3171054377514846264485146512956703222352775835]) 0) 14 true) .empty .empty)))

#time def treeG_J010_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [1386079798353440718904592809682562715637819385]) 0) 18 true) treeG_J010_part119 treeG_J010_part120)

#time def treeG_J010_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [1985886351484617692162039182908947133751763535]) 0) 20 false) treeG_J010_part118 treeG_J010_part121)

#time def treeG_J010_part123 : IntSourceTree :=
  (.node 911 (sourceLit (List.headD (raw_ints% [236521340293242513458436422701423067965592895]) 0) 21 false) treeG_J010_part115 treeG_J010_part122)

#time def treeG_J010_part124 : IntSourceTree :=
  (.node 789 (sourceLit (List.headD (raw_ints% [1806429579606947427300322386525]) 0) 63 true) treeG_J010_part108 treeG_J010_part123)

#time def treeG_J010_part125 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [11675189830828180997629990421495372576355]) 0) 17 true) treeG_J010_part093 treeG_J010_part124)

#time def treeG_J010_part126 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [370582399379603157086464262490847066845]) 0) 17 true) treeG_J010_part062 treeG_J010_part125)

#time def treeG_J010 : IntSourceTree := treeG_J010_part126

#time def treeG_J011_part000 : IntSourceTree :=
  (.node 6 (sourceLit (List.headD (raw_ints% [1162212070732496172273106997775]) 0) 43 false) (.node 4 (sourceLit (List.headD (raw_ints% [2438674624313238394064804919525]) 0) 42 false) (.node 3 (sourceLit (List.headD (raw_ints% [11455317578476620534313285032375]) 0) 38 false) (.node 2 (sourceLit (List.headD (raw_ints% [10406497287226355785106167749075]) 0) 40 false) .empty .empty) .empty) (.node 5 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 40 false) .empty .empty)) (.node 9 (sourceLit (List.headD (raw_ints% [327294787956474872408951000925]) 0) 44 true) (.node 8 (sourceLit (List.headD (raw_ints% [139753972818880455160846846125]) 0) 46 false) (.node 7 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 41 true) .empty .empty) .empty) (.node 10 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 47 false) .empty .empty)))

#time def treeG_J011_part001 : IntSourceTree :=
  (.node 16 (sourceLit (List.headD (raw_ints% [129307510396114422838029894531825]) 0) 36 true) (.node 14 (sourceLit (List.headD (raw_ints% [53045495794559912022201364609275]) 0) 38 true) (.node 13 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 47 false) (.node 12 (sourceLit (List.headD (raw_ints% [69025304895041329823223257089275]) 0) 39 true) .empty .empty) .empty) (.node 15 (sourceLit (List.headD (raw_ints% [32944484907676534094988710625]) 0) 48 false) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [178080075616971488129486123142375]) 0) 35 true) (.node 17 (sourceLit (List.headD (raw_ints% [2011347499626567344746679175]) 0) 52 false) .empty .empty) (.node 19 (sourceLit (List.headD (raw_ints% [984400442442559329260255325]) 0) 53 false) .empty .empty)))

#time def treeG_J011_part002 : IntSourceTree :=
  (.node 11 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 45 true) treeG_J011_part000 treeG_J011_part001)

#time def treeG_J011_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [14557980992112390008568375]) 0) 59 false) (.node 23 (sourceLit (List.headD (raw_ints% [118467005652573197354089875]) 0) 56 false) (.node 22 (sourceLit (List.headD (raw_ints% [1536589106694132122808243436803525]) 0) 31 true) (.node 21 (sourceLit (List.headD (raw_ints% [241301985408182539353845475]) 0) 55 false) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [4600393246616255153658899313932925]) 0) 29 true) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [79698700076612939220178406939123025]) 0) 24 true) (.node 27 (sourceLit (List.headD (raw_ints% [7163428284381022774566705]) 0) 60 false) (.node 26 (sourceLit (List.headD (raw_ints% [6842302648610062214328001201007775]) 0) 28 true) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [1764044394987334280574285]) 0) 62 false) .empty .empty)))

#time def treeG_J011_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [13231497295709693567325]) 0) 69 false) (.node 33 (sourceLit (List.headD (raw_ints% [26806749970206025572975]) 0) 68 false) (.node 32 (sourceLit (List.headD (raw_ints% [285302316712647099081680789084483295]) 0) 21 true) (.node 31 (sourceLit (List.headD (raw_ints% [869521178173035445790985]) 0) 63 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [302850651584367716806592346662039745]) 0) 20 true) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [3267361178509734114831]) 0) 71 false) (.node 36 (sourceLit (List.headD (raw_ints% [599193844236790540114264262414338845]) 0) 17 true) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [1942047668929799334433365777193553175]) 0) 16 false) .empty .empty)))

#time def treeG_J011_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [111173191469092558336795834708592025]) 0) 23 true) treeG_J011_part003 treeG_J011_part004)

#time def treeG_J011_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [1033786650125764869913724982188625]) 0) 32 true) treeG_J011_part002 treeG_J011_part005)

#time def treeG_J011_part007 : IntSourceTree :=
  (.node 47 (sourceLit (List.headD (raw_ints% [1162212070732496172273106997775]) 0) 44 false) (.node 45 (sourceLit (List.headD (raw_ints% [2438674624313238394064804919525]) 0) 43 false) (.node 44 (sourceLit (List.headD (raw_ints% [11455317578476620534313285032375]) 0) 39 false) (.node 43 (sourceLit (List.headD (raw_ints% [10406497287226355785106167749075]) 0) 41 false) .empty .empty) .empty) (.node 46 (sourceLit (List.headD (raw_ints% [1041392507134238230392116821125]) 0) 41 false) .empty .empty)) (.node 50 (sourceLit (List.headD (raw_ints% [327294787956474872408951000925]) 0) 45 true) (.node 49 (sourceLit (List.headD (raw_ints% [139753972818880455160846846125]) 0) 47 false) (.node 48 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 42 true) .empty .empty) .empty) (.node 51 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 48 false) .empty .empty)))

#time def treeG_J011_part008 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [129307510396114422838029894531825]) 0) 37 true) (.node 55 (sourceLit (List.headD (raw_ints% [53045495794559912022201364609275]) 0) 39 true) (.node 54 (sourceLit (List.headD (raw_ints% [67622890073651833142345248125]) 0) 48 false) (.node 53 (sourceLit (List.headD (raw_ints% [69025304895041329823223257089275]) 0) 40 true) .empty .empty) .empty) (.node 56 (sourceLit (List.headD (raw_ints% [32944484907676534094988710625]) 0) 49 false) .empty .empty)) (.node 59 (sourceLit (List.headD (raw_ints% [178080075616971488129486123142375]) 0) 36 true) (.node 58 (sourceLit (List.headD (raw_ints% [2011347499626567344746679175]) 0) 53 false) .empty .empty) (.node 60 (sourceLit (List.headD (raw_ints% [984400442442559329260255325]) 0) 54 false) .empty .empty)))

#time def treeG_J011_part009 : IntSourceTree :=
  (.node 52 (sourceLit (List.headD (raw_ints% [624835504280542938235270092675]) 0) 46 true) treeG_J011_part007 treeG_J011_part008)

#time def treeG_J011_part010 : IntSourceTree :=
  (.node 66 (sourceLit (List.headD (raw_ints% [14557980992112390008568375]) 0) 60 false) (.node 64 (sourceLit (List.headD (raw_ints% [118467005652573197354089875]) 0) 57 false) (.node 63 (sourceLit (List.headD (raw_ints% [1536589106694132122808243436803525]) 0) 32 true) (.node 62 (sourceLit (List.headD (raw_ints% [241301985408182539353845475]) 0) 56 false) .empty .empty) .empty) (.node 65 (sourceLit (List.headD (raw_ints% [4600393246616255153658899313932925]) 0) 30 true) .empty .empty)) (.node 69 (sourceLit (List.headD (raw_ints% [79698700076612939220178406939123025]) 0) 25 true) (.node 68 (sourceLit (List.headD (raw_ints% [7163428284381022774566705]) 0) 61 false) (.node 67 (sourceLit (List.headD (raw_ints% [6842302648610062214328001201007775]) 0) 29 true) .empty .empty) .empty) (.node 70 (sourceLit (List.headD (raw_ints% [1764044394987334280574285]) 0) 63 false) .empty .empty)))

#time def treeG_J011_part011 : IntSourceTree :=
  (.node 76 (sourceLit (List.headD (raw_ints% [13231497295709693567325]) 0) 70 false) (.node 74 (sourceLit (List.headD (raw_ints% [26806749970206025572975]) 0) 69 false) (.node 73 (sourceLit (List.headD (raw_ints% [285302316712647099081680789084483295]) 0) 22 true) (.node 72 (sourceLit (List.headD (raw_ints% [869521178173035445790985]) 0) 64 false) .empty .empty) .empty) (.node 75 (sourceLit (List.headD (raw_ints% [302850651584367716806592346662039745]) 0) 21 true) .empty .empty)) (.node 78 (sourceLit (List.headD (raw_ints% [3267361178509734114831]) 0) 72 false) (.node 77 (sourceLit (List.headD (raw_ints% [599193844236790540114264262414338845]) 0) 18 true) .empty .empty) (.node 79 (sourceLit (List.headD (raw_ints% [1942047668929799334433365777193553175]) 0) 17 false) .empty .empty)))

#time def treeG_J011_part012 : IntSourceTree :=
  (.node 71 (sourceLit (List.headD (raw_ints% [111173191469092558336795834708592025]) 0) 24 true) treeG_J011_part010 treeG_J011_part011)

#time def treeG_J011_part013 : IntSourceTree :=
  (.node 61 (sourceLit (List.headD (raw_ints% [1033786650125764869913724982188625]) 0) 33 true) treeG_J011_part009 treeG_J011_part012)

#time def treeG_J011_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [1614526075331246802439]) 0) 72 false) treeG_J011_part006 treeG_J011_part013)

#time def treeG_J011_part015 : IntSourceTree :=
  (.node 89 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 43 false) (.node 87 (sourceLit (List.headD (raw_ints% [2707620518549019399019503734925]) 0) 41 false) (.node 86 (sourceLit (List.headD (raw_ints% [3715137177893980615856502841275]) 0) 43 false) (.node 85 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 41 false) .empty .empty) .empty) (.node 88 (sourceLit (List.headD (raw_ints% [882704125094735261951413305525]) 0) 45 false) .empty .empty)) (.node 92 (sourceLit (List.headD (raw_ints% [138271144330460806960984791169275]) 0) 39 false) (.node 91 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 45 true) (.node 90 (sourceLit (List.headD (raw_ints% [211885055564109077179348444125]) 0) 47 false) .empty .empty) .empty) (.node 93 (sourceLit (List.headD (raw_ints% [2704915602946073325693809925]) 0) 55 true) .empty .empty)))

#time def treeG_J011_part016 : IntSourceTree :=
  (.node 99 (sourceLit (List.headD (raw_ints% [3038294556810575360233103025]) 0) 53 false) (.node 97 (sourceLit (List.headD (raw_ints% [24899094909170264716001993925]) 0) 50 false) (.node 96 (sourceLit (List.headD (raw_ints% [719420422316844169517191939216575]) 0) 36 true) (.node 95 (sourceLit (List.headD (raw_ints% [102301295239627132189701785625]) 0) 48 false) .empty .empty) .empty) (.node 98 (sourceLit (List.headD (raw_ints% [856380007551943894574753033112225]) 0) 35 true) .empty .empty)) (.node 101 (sourceLit (List.headD (raw_ints% [371549228517188394953204925]) 0) 56 false) (.node 100 (sourceLit (List.headD (raw_ints% [4664775769617322750229830958367375]) 0) 32 true) .empty .empty) (.node 102 (sourceLit (List.headD (raw_ints% [6733704094311986836501556420705475]) 0) 31 true) .empty .empty)))

#time def treeG_J011_part017 : IntSourceTree :=
  (.node 94 (sourceLit (List.headD (raw_ints% [499156943365770726563584692104925]) 0) 38 true) treeG_J011_part015 treeG_J011_part016)

#time def treeG_J011_part018 : IntSourceTree :=
  (.node 108 (sourceLit (List.headD (raw_ints% [358208669434431042496813669925374575]) 0) 24 true) (.node 106 (sourceLit (List.headD (raw_ints% [29960843324319979014943193310455625]) 0) 28 true) (.node 105 (sourceLit (List.headD (raw_ints% [89351043668348417336953125]) 0) 58 false) (.node 104 (sourceLit (List.headD (raw_ints% [19985032460489858811272995674923475]) 0) 29 true) .empty .empty) .empty) (.node 107 (sourceLit (List.headD (raw_ints% [21952533699843757242570045]) 0) 60 false) .empty .empty)) (.node 111 (sourceLit (List.headD (raw_ints% [2658567611801633115357585]) 0) 63 false) (.node 110 (sourceLit (List.headD (raw_ints% [526416409143810955424631420804392175]) 0) 23 true) (.node 109 (sourceLit (List.headD (raw_ints% [1349845972348422123498105]) 0) 64 false) .empty .empty) .empty) (.node 112 (sourceLit (List.headD (raw_ints% [1493468746792833834307052566252989105]) 0) 21 true) .empty .empty)))

#time def treeG_J011_part019 : IntSourceTree :=
  (.node 118 (sourceLit (List.headD (raw_ints% [6735598422824123655347479876508263935]) 0) 16 true) (.node 116 (sourceLit (List.headD (raw_ints% [9092027006462976397696690830770932995]) 0) 17 true) (.node 115 (sourceLit (List.headD (raw_ints% [40382002644702357578625]) 0) 69 false) (.node 114 (sourceLit (List.headD (raw_ints% [1979567882116809075846853966013826615]) 0) 20 true) .empty .empty) .empty) (.node 117 (sourceLit (List.headD (raw_ints% [4982068058599979726247]) 0) 72 false) .empty .empty)) (.node 125 (sourceLit (List.headD (raw_ints% [5529148038599878996976557910025]) 0) 43 false) (.node 119 (sourceLit (List.headD (raw_ints% [4920196281688221427223]) 0) 72 false) .empty .empty) (.node 126 (sourceLit (List.headD (raw_ints% [9372532564208144073529051390125]) 0) 41 false) .empty .empty)))

#time def treeG_J011_part020 : IntSourceTree :=
  (.node 113 (sourceLit (List.headD (raw_ints% [655067178411387241207185]) 0) 65 false) treeG_J011_part018 treeG_J011_part019)

#time def treeG_J011_part021 : IntSourceTree :=
  (.node 103 (sourceLit (List.headD (raw_ints% [364136965163791881353601075]) 0) 56 false) treeG_J011_part017 treeG_J011_part020)

#time def treeG_J011_part022 : IntSourceTree :=
  (.node 132 (sourceLit (List.headD (raw_ints% [148770358162034032913159545875]) 0) 48 false) (.node 130 (sourceLit (List.headD (raw_ints% [684343647545356551400533911025]) 0) 44 false) (.node 129 (sourceLit (List.headD (raw_ints% [603196179456974351629719613275]) 0) 46 false) (.node 128 (sourceLit (List.headD (raw_ints% [208278501426847646078423364225]) 0) 46 false) .empty .empty) .empty) (.node 131 (sourceLit (List.headD (raw_ints% [4508192671576788876156349875]) 0) 53 false) .empty .empty)) (.node 135 (sourceLit (List.headD (raw_ints% [223055723785605407270691663747825]) 0) 40 true) (.node 134 (sourceLit (List.headD (raw_ints% [760081284427846604519960588925]) 0) 48 true) (.node 133 (sourceLit (List.headD (raw_ints% [103648224612751068392104024129275]) 0) 41 false) .empty .empty) .empty) (.node 136 (sourceLit (List.headD (raw_ints% [8669601291493824761839134375]) 0) 52 false) .empty .empty)))

#time def treeG_J011_part023 : IntSourceTree :=
  (.node 142 (sourceLit (List.headD (raw_ints% [501796471626194250552564375]) 0) 56 false) (.node 140 (sourceLit (List.headD (raw_ints% [513473528592004007743211925]) 0) 56 false) (.node 139 (sourceLit (List.headD (raw_ints% [339149965967486203222633454984925]) 0) 37 true) (.node 138 (sourceLit (List.headD (raw_ints% [16853704910663995337015277225]) 0) 51 false) .empty .empty) .empty) (.node 141 (sourceLit (List.headD (raw_ints% [1815494559745778940158052988089375]) 0) 34 true) .empty .empty)) (.node 144 (sourceLit (List.headD (raw_ints% [7677186234725583874984725]) 0) 62 false) (.node 143 (sourceLit (List.headD (raw_ints% [2598557493808927356846656491950975]) 0) 33 true) .empty .empty) (.node 145 (sourceLit (List.headD (raw_ints% [7692319606936801828807048180495275]) 0) 31 true) .empty .empty)))

#time def treeG_J011_part024 : IntSourceTree :=
  (.node 137 (sourceLit (List.headD (raw_ints% [295056455960364873339581022342375]) 0) 38 true) treeG_J011_part022 treeG_J011_part023)

#time def treeG_J011_part025 : IntSourceTree :=
  (.node 151 (sourceLit (List.headD (raw_ints% [207621608837359198543917793047900075]) 0) 25 true) (.node 149 (sourceLit (List.headD (raw_ints% [139254984678909051638317631493125775]) 0) 26 true) (.node 148 (sourceLit (List.headD (raw_ints% [3697276353865683617000835]) 0) 63 false) (.node 147 (sourceLit (List.headD (raw_ints% [11559270337854958400307596054723925]) 0) 30 true) .empty .empty) .empty) (.node 150 (sourceLit (List.headD (raw_ints% [3635339494406354213418135]) 0) 63 false) .empty .empty)) (.node 153 (sourceLit (List.headD (raw_ints% [604083215040093367612685888584252905]) 0) 23 true) (.node 152 (sourceLit (List.headD (raw_ints% [223630804203574708695825]) 0) 67 false) .empty .empty) (.node 154 (sourceLit (List.headD (raw_ints% [440613178649739036623385]) 0) 66 false) .empty .empty)))

#time def treeG_J011_part026 : IntSourceTree :=
  (.node 166 (sourceLit (List.headD (raw_ints% [7343158899305777378096612978775]) 0) 43 false) (.node 158 (sourceLit (List.headD (raw_ints% [6696774938690225337663]) 0) 72 false) (.node 157 (sourceLit (List.headD (raw_ints% [4246416581113092928791213284178297075]) 0) 19 true) (.node 156 (sourceLit (List.headD (raw_ints% [6787626337248166002825]) 0) 72 false) .empty .empty) .empty) (.node 159 (sourceLit (List.headD (raw_ints% [4338823045876961494890422826850908555]) 0) 18 true) .empty .empty)) (.node 168 (sourceLit (List.headD (raw_ints% [1670220982066749181631982537975]) 0) 45 false) (.node 167 (sourceLit (List.headD (raw_ints% [16037444609867268748038599045325]) 0) 41 false) .empty .empty) (.node 169 (sourceLit (List.headD (raw_ints% [3302701951197155530672141918425]) 0) 43 false) .empty .empty)))

#time def treeG_J011_part027 : IntSourceTree :=
  (.node 155 (sourceLit (List.headD (raw_ints% [838358615266220679520130809675893435]) 0) 22 true) treeG_J011_part025 treeG_J011_part026)

#time def treeG_J011_part028 : IntSourceTree :=
  (.node 146 (sourceLit (List.headD (raw_ints% [60235081684123637319816375]) 0) 59 false) treeG_J011_part024 treeG_J011_part027)

#time def treeG_J011_part029 : IntSourceTree :=
  (.node 127 (sourceLit (List.headD (raw_ints% [638231276790371110895848960875]) 0) 46 false) treeG_J011_part021 treeG_J011_part028)

#time def treeG_J011_part030 : IntSourceTree :=
  (.node 84 (sourceLit (List.headD (raw_ints% [3983911331456558695520681414775]) 0) 43 false) treeG_J011_part014 treeG_J011_part029)

#time def treeG_J011_part031 : IntSourceTree :=
  (.node 175 (sourceLit (List.headD (raw_ints% [1622463864095320341229622963475]) 0) 48 true) (.node 173 (sourceLit (List.headD (raw_ints% [321884956750582725757563381075]) 0) 49 false) (.node 172 (sourceLit (List.headD (raw_ints% [9453313131767410932906481534725]) 0) 39 false) (.node 171 (sourceLit (List.headD (raw_ints% [89262214897220419747895727525]) 0) 48 false) .empty .empty) .empty) (.node 174 (sourceLit (List.headD (raw_ints% [2157528537169787820837249078173325]) 0) 38 false) .empty .empty)) (.node 178 (sourceLit (List.headD (raw_ints% [3864523287813894078858543324365775]) 0) 35 true) (.node 177 (sourceLit (List.headD (raw_ints% [44457715422780333378711081075]) 0) 50 false) (.node 176 (sourceLit (List.headD (raw_ints% [6418362738822528863144941300713825]) 0) 36 true) .empty .empty) .empty) (.node 179 (sourceLit (List.headD (raw_ints% [10777115797042844616549071175]) 0) 52 false) .empty .empty)))

#time def treeG_J011_part032 : IntSourceTree :=
  (.node 185 (sourceLit (List.headD (raw_ints% [156318915842870266662558075]) 0) 58 false) (.node 183 (sourceLit (List.headD (raw_ints% [639455978088596619751527675]) 0) 56 false) (.node 182 (sourceLit (List.headD (raw_ints% [22314208861620476206027291388724525]) 0) 31 true) (.node 181 (sourceLit (List.headD (raw_ints% [655397828666819620533218925]) 0) 56 false) .empty .empty) .empty) (.node 184 (sourceLit (List.headD (raw_ints% [63168807341395816607820012067507725]) 0) 29 true) .empty .empty)) (.node 187 (sourceLit (List.headD (raw_ints% [19141273992139940038623165]) 0) 61 false) (.node 186 (sourceLit (List.headD (raw_ints% [93116270386668850245969577577468775]) 0) 28 true) .empty .empty) (.node 188 (sourceLit (List.headD (raw_ints% [1121377933811003632742558625079287825]) 0) 24 true) .empty .empty)))

#time def treeG_J011_part033 : IntSourceTree :=
  (.node 180 (sourceLit (List.headD (raw_ints% [17040822052301794256018710160667825]) 0) 32 true) treeG_J011_part031 treeG_J011_part032)

#time def treeG_J011_part034 : IntSourceTree :=
  (.node 194 (sourceLit (List.headD (raw_ints% [7685763558524684805956120251334219865]) 0) 20 true) (.node 192 (sourceLit (List.headD (raw_ints% [5150422736002660519098316811279813295]) 0) 21 true) (.node 191 (sourceLit (List.headD (raw_ints% [4612111377011075311478685]) 0) 63 false) (.node 190 (sourceLit (List.headD (raw_ints% [1701663345718733870788450683085620225]) 0) 23 true) .empty .empty) .empty) (.node 193 (sourceLit (List.headD (raw_ints% [1133979255217210428359415]) 0) 65 false) .empty .empty)) (.node 197 (sourceLit (List.headD (raw_ints% [8593184615896352279403]) 0) 72 false) (.node 196 (sourceLit (List.headD (raw_ints% [44562924370575147091591680988486246845]) 0) 17 true) (.node 195 (sourceLit (List.headD (raw_ints% [279085168070929606308885]) 0) 67 false) .empty .empty) .empty) (.node 198 (sourceLit (List.headD (raw_ints% [61207066874985363205311932670344489265]) 0) 16 true) .empty .empty)))

#time def treeG_J011_part035 : IntSourceTree :=
  (.node 211 (sourceLit (List.headD (raw_ints% [123524479201204015206683986575]) 0) 49 false) (.node 209 (sourceLit (List.headD (raw_ints% [266756200652443707500565731175]) 0) 48 false) (.node 208 (sourceLit (List.headD (raw_ints% [12704988587037706410783825217725]) 0) 42 false) (.node 207 (sourceLit (List.headD (raw_ints% [4790233792144292934513217135275]) 0) 44 false) .empty .empty) .empty) (.node 210 (sourceLit (List.headD (raw_ints% [327294787956474872408951000925]) 0) 47 false) .empty .empty)) (.node 213 (sourceLit (List.headD (raw_ints% [197843136093734725851301566723825]) 0) 40 true) (.node 212 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 48 false) .empty .empty) (.node 214 (sourceLit (List.headD (raw_ints% [2047621111430177507550214113225]) 0) 48 false) .empty .empty)))

#time def treeG_J011_part036 : IntSourceTree :=
  (.node 199 (sourceLit (List.headD (raw_ints% [8473353595692229248103]) 0) 72 false) treeG_J011_part034 treeG_J011_part035)

#time def treeG_J011_part037 : IntSourceTree :=
  (.node 189 (sourceLit (List.headD (raw_ints% [1173715190758630746751365]) 0) 65 false) treeG_J011_part033 treeG_J011_part036)

#time def treeG_J011_part038 : IntSourceTree :=
  (.node 220 (sourceLit (List.headD (raw_ints% [6669327568306812554603375775]) 0) 53 false) (.node 218 (sourceLit (List.headD (raw_ints% [13802005256058169020847901925]) 0) 52 false) (.node 217 (sourceLit (List.headD (raw_ints% [5828249826901799116465779256029075]) 0) 37 true) (.node 216 (sourceLit (List.headD (raw_ints% [1691820674427270939324336038475]) 0) 49 true) .empty .empty) .empty) (.node 219 (sourceLit (List.headD (raw_ints% [3186223355878921672413276414395925]) 0) 36 true) .empty .empty)) (.node 223 (sourceLit (List.headD (raw_ints% [17117093874002621492333978404822575]) 0) 32 true) (.node 222 (sourceLit (List.headD (raw_ints% [808999185707444990513873475]) 0) 56 false) (.node 221 (sourceLit (List.headD (raw_ints% [13409832932810236375702604184489075]) 0) 33 true) .empty .empty) .empty) (.node 224 (sourceLit (List.headD (raw_ints% [393786018577377935752016475]) 0) 57 false) .empty .empty)))

#time def treeG_J011_part039 : IntSourceTree :=
  (.node 230 (sourceLit (List.headD (raw_ints% [5754382031662691760592785]) 0) 63 false) (.node 228 (sourceLit (List.headD (raw_ints% [11746721284408572804621495]) 0) 62 false) (.node 227 (sourceLit (List.headD (raw_ints% [69997729710958933445354385468020925]) 0) 29 true) (.node 226 (sourceLit (List.headD (raw_ints% [24020958539686657335685425]) 0) 61 false) .empty .empty) .empty) (.node 229 (sourceLit (List.headD (raw_ints% [842867964453185529465923362093036275]) 0) 25 true) .empty .empty)) (.node 232 (sourceLit (List.headD (raw_ints% [2823064943382477641912085]) 0) 64 false) (.node 231 (sourceLit (List.headD (raw_ints% [1286420128044015473700615096989820075]) 0) 24 true) .empty .empty) (.node 233 (sourceLit (List.headD (raw_ints% [3942256305922473783872945034111307485]) 0) 22 true) .empty .empty)))

#time def treeG_J011_part040 : IntSourceTree :=
  (.node 225 (sourceLit (List.headD (raw_ints% [47784168127522212950205915706517175]) 0) 30 true) treeG_J011_part038 treeG_J011_part039)

#time def treeG_J011_part041 : IntSourceTree :=
  (.node 239 (sourceLit (List.headD (raw_ints% [52529420783231440215531087016642672155]) 0) 17 true) (.node 237 (sourceLit (List.headD (raw_ints% [36070091208348961234009254420129652695]) 0) 18 true) (.node 236 (sourceLit (List.headD (raw_ints% [170483146674958950263685]) 0) 68 false) (.node 235 (sourceLit (List.headD (raw_ints% [6009046327992243446915858631982432995]) 0) 21 true) .empty .empty) .empty) (.node 238 (sourceLit (List.headD (raw_ints% [10489594293102479221143]) 0) 72 false) .empty .empty)) (.node 250 (sourceLit (List.headD (raw_ints% [337856839358454777775945877775]) 0) 48 false) (.node 249 (sourceLit (List.headD (raw_ints% [2350571658960137720027920824825]) 0) 45 false) (.node 248 (sourceLit (List.headD (raw_ints% [780003202519385938220308649325]) 0) 47 false) .empty .empty) .empty) (.node 251 (sourceLit (List.headD (raw_ints% [29754071632406806582631909175]) 0) 51 false) .empty .empty)))

#time def treeG_J011_part042 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [868139194925025636351523559775]) 0) 51 true) (.node 255 (sourceLit (List.headD (raw_ints% [5717706086955675356330051189925]) 0) 48 false) (.node 254 (sourceLit (List.headD (raw_ints% [3740273625919665627647661611963925]) 0) 38 true) (.node 253 (sourceLit (List.headD (raw_ints% [73032721279543979793732867975]) 0) 51 true) .empty .empty) .empty) (.node 256 (sourceLit (List.headD (raw_ints% [48076602494678507029203059791417425]) 0) 36 false) .empty .empty)) (.node 259 (sourceLit (List.headD (raw_ints% [16826894715073493425146732675]) 0) 52 false) (.node 258 (sourceLit (List.headD (raw_ints% [42761475327400498852867690723866825]) 0) 35 true) .empty .empty) (.node 260 (sourceLit (List.headD (raw_ints% [84918325335823699261206135100001775]) 0) 32 true) .empty .empty)))

#time def treeG_J011_part043 : IntSourceTree :=
  (.node 252 (sourceLit (List.headD (raw_ints% [243524820272298412210382322970875]) 0) 39 false) treeG_J011_part041 treeG_J011_part042)

#time def treeG_J011_part044 : IntSourceTree :=
  (.node 234 (sourceLit (List.headD (raw_ints% [346683038283735695868015]) 0) 67 false) treeG_J011_part040 treeG_J011_part043)

#time def treeG_J011_part045 : IntSourceTree :=
  (.node 215 (sourceLit (List.headD (raw_ints% [2603639984740998635378632405668975]) 0) 39 false) treeG_J011_part037 treeG_J011_part044)

#time def treeG_J011_part046 : IntSourceTree :=
  (.node 266 (sourceLit (List.headD (raw_ints% [289157074633508853355677748074668625]) 0) 28 true) (.node 264 (sourceLit (List.headD (raw_ints% [210704694642646127269523642409653475]) 0) 29 true) (.node 263 (sourceLit (List.headD (raw_ints% [978542393326293361276219275]) 0) 56 false) (.node 262 (sourceLit (List.headD (raw_ints% [84964454600861414799593542087188075]) 0) 31 true) .empty .empty) .empty) (.node 265 (sourceLit (List.headD (raw_ints% [7420846960453364659045575]) 0) 63 false) .empty .empty)) (.node 269 (sourceLit (List.headD (raw_ints% [7051860521374049817616035]) 0) 63 false) (.node 268 (sourceLit (List.headD (raw_ints% [3358476767690368107760122044874051375]) 0) 24 true) (.node 267 (sourceLit (List.headD (raw_ints% [28900643087233374632747685]) 0) 61 false) .empty .empty) .empty) (.node 270 (sourceLit (List.headD (raw_ints% [5041280369906750364938936213658669975]) 0) 23 true) .empty .empty)))

#time def treeG_J011_part047 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [147726558125176643209715795234951608995]) 0) 17 true) (.node 274 (sourceLit (List.headD (raw_ints% [23852286888855105465027440021556240015]) 0) 20 true) (.node 273 (sourceLit (List.headD (raw_ints% [844542844082633606776335]) 0) 66 false) (.node 272 (sourceLit (List.headD (raw_ints% [15432299312701587060111524740557307905]) 0) 21 true) .empty .empty) .empty) (.node 275 (sourceLit (List.headD (raw_ints% [414280908496541785427145]) 0) 67 false) .empty .empty)) (.node 278 (sourceLit (List.headD (raw_ints% [227353662791806326666762102690692732295]) 0) 16 true) (.node 277 (sourceLit (List.headD (raw_ints% [101737669747788132028461]) 0) 69 false) .empty .empty) (.node 279 (sourceLit (List.headD (raw_ints% [12505834990512729194183]) 0) 72 false) .empty .empty)))

#time def treeG_J011_part048 : IntSourceTree :=
  (.node 271 (sourceLit (List.headD (raw_ints% [6896652686314308209706885]) 0) 63 false) treeG_J011_part046 treeG_J011_part047)

#time def treeG_J011_part049 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [3216144651902881184249940000825]) 0) 48 true) (.node 292 (sourceLit (List.headD (raw_ints% [446311074486102098739478637625]) 0) 48 false) (.node 291 (sourceLit (List.headD (raw_ints% [1674471563728521582572358525]) 0) 56 false) (.node 290 (sourceLit (List.headD (raw_ints% [1695982083047187975210018822975]) 0) 46 false) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [110341989091508284515420972423675]) 0) 42 false) .empty .empty)) (.node 297 (sourceLit (List.headD (raw_ints% [13476213080395076536417209761861625]) 0) 39 false) (.node 296 (sourceLit (List.headD (raw_ints% [463095422586434143478399201775]) 0) 53 false) (.node 295 (sourceLit (List.headD (raw_ints% [1585978402665166065756573504408225]) 0) 41 true) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [220485300045270951343092865425]) 0) 54 true) .empty .empty)))

#time def treeG_J011_part050 : IntSourceTree :=
  (.node 304 (sourceLit (List.headD (raw_ints% [36547273421807214095262675]) 0) 61 false) (.node 302 (sourceLit (List.headD (raw_ints% [2429737882224644091442753125]) 0) 55 false) (.node 301 (sourceLit (List.headD (raw_ints% [17877123100753365721375882728878175]) 0) 35 true) (.node 300 (sourceLit (List.headD (raw_ints% [2539391786691670217635839225]) 0) 55 false) .empty .empty) .empty) (.node 303 (sourceLit (List.headD (raw_ints% [16961840181714698326814890920591375]) 0) 34 true) .empty .empty)) (.node 306 (sourceLit (List.headD (raw_ints% [35345817143940259936679175]) 0) 61 false) (.node 305 (sourceLit (List.headD (raw_ints% [40730131628780978579829431675784075]) 0) 32 true) .empty .empty) (.node 307 (sourceLit (List.headD (raw_ints% [54789836230637479977580840651661925]) 0) 31 true) .empty .empty)))

#time def treeG_J011_part051 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [9893812992880394295113603577367725]) 0) 38 true) treeG_J011_part049 treeG_J011_part050)

#time def treeG_J011_part052 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [256623500933471115359871459075]) 0) 49 false) treeG_J011_part048 treeG_J011_part051)

#time def treeG_J011_part053 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [2872510751694778319059644926611500105]) 0) 24 true) (.node 311 (sourceLit (List.headD (raw_ints% [938715060465683722809580279167212475]) 0) 26 true) (.node 310 (sourceLit (List.headD (raw_ints% [8349339011085407874639285]) 0) 63 false) (.node 309 (sourceLit (List.headD (raw_ints% [628902200809295644573549670695253775]) 0) 27 true) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [254599233933239410487175]) 0) 68 false) .empty .empty)) (.node 316 (sourceLit (List.headD (raw_ints% [60949440455395708790865]) 0) 70 false) (.node 315 (sourceLit (List.headD (raw_ints% [4460810140215715504527895347393451755]) 0) 23 true) (.node 314 (sourceLit (List.headD (raw_ints% [15558118931215559715885]) 0) 72 false) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [27914116729206920493926635203705489075]) 0) 20 true) .empty .empty)))

#time def treeG_J011_part054 : IntSourceTree :=
  (.node 333 (sourceLit (List.headD (raw_ints% [738441959604278017914410109525]) 0) 49 false) (.node 331 (sourceLit (List.headD (raw_ints% [1219916936928679069887908276175]) 0) 47 false) (.node 330 (sourceLit (List.headD (raw_ints% [688637164375429683663539958525]) 0) 48 false) (.node 319 (sourceLit (List.headD (raw_ints% [43706060502143721612807753918512515035]) 0) 19 true) .empty .empty) .empty) (.node 332 (sourceLit (List.headD (raw_ints% [195427853329751149531466030206725]) 0) 39 false) .empty .empty)) (.node 335 (sourceLit (List.headD (raw_ints% [12149995390761437724829931191575]) 0) 48 true) (.node 334 (sourceLit (List.headD (raw_ints% [7271217276847930732141132729521525]) 0) 38 false) .empty .empty) (.node 336 (sourceLit (List.headD (raw_ints% [149579220265249135237623764073543825]) 0) 36 true) .empty .empty)))

#time def treeG_J011_part055 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [59779292575378215143889]) 0) 70 false) treeG_J011_part053 treeG_J011_part054)

#time def treeG_J011_part056 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [487103484623246288284434705236913525]) 0) 31 true) (.node 340 (sourceLit (List.headD (raw_ints% [1181489737752866770513335122803067025]) 0) 32 true) (.node 339 (sourceLit (List.headD (raw_ints% [1780709295077241104169889656075]) 0) 52 true) (.node 338 (sourceLit (List.headD (raw_ints% [474000293900042948018218403103438825]) 0) 35 false) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [6109830893127146798072856825]) 0) 54 false) .empty .empty)) (.node 344 (sourceLit (List.headD (raw_ints% [874853076987094565646629376508194525]) 0) 29 true) (.node 343 (sourceLit (List.headD (raw_ints% [725597744449175365083266925]) 0) 57 false) .empty .empty) (.node 345 (sourceLit (List.headD (raw_ints% [21705579500900484777171525]) 0) 62 false) .empty .empty)))

#time def treeG_J011_part057 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [9802025335856507539571685]) 0) 63 false) (.node 349 (sourceLit (List.headD (raw_ints% [10102061281450752010510155]) 0) 63 false) (.node 348 (sourceLit (List.headD (raw_ints% [10667721307352826766500573161951401425]) 0) 24 true) (.node 347 (sourceLit (List.headD (raw_ints% [41790991200647145240610665]) 0) 61 false) .empty .empty) .empty) (.node 350 (sourceLit (List.headD (raw_ints% [15083590055990710261414653248589450825]) 0) 23 true) .empty .empty)) (.node 353 (sourceLit (List.headD (raw_ints% [1192251027383281677121065]) 0) 66 false) (.node 352 (sourceLit (List.headD (raw_ints% [44645464557102171199701613126144290495]) 0) 21 true) .empty .empty) (.node 354 (sourceLit (List.headD (raw_ints% [68068057165377800744881197630011763345]) 0) 20 true) .empty .empty)))

#time def treeG_J011_part058 : IntSourceTree :=
  (.node 346 (sourceLit (List.headD (raw_ints% [1014207137487482461198864065550421775]) 0) 28 true) treeG_J011_part056 treeG_J011_part057)

#time def treeG_J011_part059 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [4572902575616498784178717173975]) 0) 51 false) treeG_J011_part055 treeG_J011_part058)

#time def treeG_J011_part060 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [8576960901412400914063095]) 0) 63 false) treeG_J011_part052 treeG_J011_part059)

#time def treeG_J011_part061 : IntSourceTree :=
  (.node 261 (sourceLit (List.headD (raw_ints% [4047736253639534072470500075]) 0) 54 false) treeG_J011_part045 treeG_J011_part060)

#time def treeG_J011_part062 : IntSourceTree :=
  (.node 170 (sourceLit (List.headD (raw_ints% [195655561946432637225185584575]) 0) 48 false) treeG_J011_part030 treeG_J011_part061)

#time def treeG_J011_part063 : IntSourceTree :=
  (.node 371 (sourceLit (List.headD (raw_ints% [474304804218178921094278067325]) 0) 49 false) (.node 358 (sourceLit (List.headD (raw_ints% [665898072542815129138890223827882918105]) 0) 16 true) (.node 357 (sourceLit (List.headD (raw_ints% [142060092073794703134999]) 0) 69 false) (.node 356 (sourceLit (List.headD (raw_ints% [423257139822434941369854809231410215645]) 0) 17 true) .empty .empty) .empty) (.node 359 (sourceLit (List.headD (raw_ints% [34767622594352756755523]) 0) 71 false) .empty .empty)) (.node 374 (sourceLit (List.headD (raw_ints% [6169912490319993255907580438925]) 0) 48 false) (.node 373 (sourceLit (List.headD (raw_ints% [245940103036281988530217859487975]) 0) 40 true) (.node 372 (sourceLit (List.headD (raw_ints% [386802931221288485574214819275]) 0) 49 false) .empty .empty) .empty) (.node 375 (sourceLit (List.headD (raw_ints% [13615130887508594995167426747154425]) 0) 39 false) .empty .empty)))

#time def treeG_J011_part064 : IntSourceTree :=
  (.node 381 (sourceLit (List.headD (raw_ints% [1109981245349853307627831591887554325]) 0) 33 true) (.node 379 (sourceLit (List.headD (raw_ints% [513575545871564525198672817412909725]) 0) 36 false) (.node 378 (sourceLit (List.headD (raw_ints% [5454843775797582589551088635675]) 0) 52 false) (.node 377 (sourceLit (List.headD (raw_ints% [203484072586829441383292603120990325]) 0) 37 true) .empty .empty) .empty) (.node 380 (sourceLit (List.headD (raw_ints% [1790866862224007785040433012975]) 0) 53 true) .empty .empty)) (.node 383 (sourceLit (List.headD (raw_ints% [419256123896387494977175141554548025]) 0) 32 true) (.node 382 (sourceLit (List.headD (raw_ints% [920023252725625676657525925]) 0) 57 false) .empty .empty) (.node 384 (sourceLit (List.headD (raw_ints% [433219557074717652321165525]) 0) 58 false) .empty .empty)))

#time def treeG_J011_part065 : IntSourceTree :=
  (.node 376 (sourceLit (List.headD (raw_ints% [19559522152144384020484318419975]) 0) 49 true) treeG_J011_part063 treeG_J011_part064)

#time def treeG_J011_part066 : IntSourceTree :=
  (.node 390 (sourceLit (List.headD (raw_ints% [11854783551816096146381025]) 0) 63 false) (.node 388 (sourceLit (List.headD (raw_ints% [24637069397822343412484475]) 0) 62 false) (.node 387 (sourceLit (List.headD (raw_ints% [795047792564932541288540702943774075]) 0) 29 true) (.node 386 (sourceLit (List.headD (raw_ints% [51476500859661679172006925]) 0) 61 false) .empty .empty) .empty) (.node 389 (sourceLit (List.headD (raw_ints% [8152112504115644188206374479170386325]) 0) 25 true) .empty .empty)) (.node 393 (sourceLit (List.headD (raw_ints% [33155421550323057923463033419698290075]) 0) 22 true) (.node 392 (sourceLit (List.headD (raw_ints% [5728437592924676971776885]) 0) 64 false) (.node 391 (sourceLit (List.headD (raw_ints% [11328729814127975370176332131920600925]) 0) 24 true) .empty .empty) .empty) (.node 394 (sourceLit (List.headD (raw_ints% [694391221584383766212745]) 0) 67 false) .empty .empty)))

#time def treeG_J011_part067 : IntSourceTree :=
  (.node 412 (sourceLit (List.headD (raw_ints% [775948385709079280869615451674875]) 0) 39 false) (.node 398 (sourceLit (List.headD (raw_ints% [41140399749208243995555]) 0) 71 false) (.node 397 (sourceLit (List.headD (raw_ints% [311600672905607259394148268416588259345]) 0) 18 true) (.node 396 (sourceLit (List.headD (raw_ints% [337640941279671201226035]) 0) 68 false) .empty .empty) .empty) (.node 399 (sourceLit (List.headD (raw_ints% [491073830534240242687659208153832857965]) 0) 17 true) .empty .empty)) (.node 414 (sourceLit (List.headD (raw_ints% [9238738101138186640382875605425325]) 0) 38 true) (.node 413 (sourceLit (List.headD (raw_ints% [35163902838298953234019529025]) 0) 49 false) .empty .empty) (.node 415 (sourceLit (List.headD (raw_ints% [24489820371401424236645092069425]) 0) 48 false) .empty .empty)))

#time def treeG_J011_part068 : IntSourceTree :=
  (.node 395 (sourceLit (List.headD (raw_ints% [50224816604514938726769616240437956325]) 0) 21 true) treeG_J011_part066 treeG_J011_part067)

#time def treeG_J011_part069 : IntSourceTree :=
  (.node 385 (sourceLit (List.headD (raw_ints% [711932550471970651327311649805058225]) 0) 30 true) treeG_J011_part065 treeG_J011_part068)

#time def treeG_J011_part070 : IntSourceTree :=
  (.node 421 (sourceLit (List.headD (raw_ints% [224622086639641866479813233725]) 0) 57 true) (.node 419 (sourceLit (List.headD (raw_ints% [12690396846672406283272066927425]) 0) 52 false) (.node 418 (sourceLit (List.headD (raw_ints% [2101872874594678479084559228071361425]) 0) 35 true) (.node 417 (sourceLit (List.headD (raw_ints% [28705327303377381588841752767925]) 0) 50 true) .empty .empty) .empty) (.node 420 (sourceLit (List.headD (raw_ints% [17615907205642931576870865280016178225]) 0) 32 false) .empty .empty)) (.node 424 (sourceLit (List.headD (raw_ints% [5833244905355105353988172888364573875]) 0) 29 true) (.node 423 (sourceLit (List.headD (raw_ints% [1114448761002075988231784925]) 0) 57 false) (.node 422 (sourceLit (List.headD (raw_ints% [8392746478175580172738218029863521075]) 0) 31 true) .empty .empty) .empty) (.node 425 (sourceLit (List.headD (raw_ints% [259574921067513774103793325]) 0) 59 false) .empty .empty)))

#time def treeG_J011_part071 : IntSourceTree :=
  (.node 431 (sourceLit (List.headD (raw_ints% [13907541767775684753190365]) 0) 63 false) (.node 429 (sourceLit (List.headD (raw_ints% [908438007273224462623395]) 0) 67 false) (.node 428 (sourceLit (List.headD (raw_ints% [40215337416802855875966031826450139375]) 0) 24 true) (.node 427 (sourceLit (List.headD (raw_ints% [61162010518676213103403185]) 0) 61 false) .empty .empty) .empty) (.node 430 (sourceLit (List.headD (raw_ints% [50133309976934443244236342584773639775]) 0) 23 true) .empty .empty)) (.node 433 (sourceLit (List.headD (raw_ints% [3343935538158113617534755]) 0) 65 false) (.node 432 (sourceLit (List.headD (raw_ints% [136614212468945434723119700984585324305]) 0) 21 true) .empty .empty) (.node 434 (sourceLit (List.headD (raw_ints% [197175315237206662642823069727574557255]) 0) 20 true) .empty .empty)))

#time def treeG_J011_part072 : IntSourceTree :=
  (.node 426 (sourceLit (List.headD (raw_ints% [4681253266288282749419629132890044025]) 0) 28 true) treeG_J011_part070 treeG_J011_part071)

#time def treeG_J011_part073 : IntSourceTree :=
  (.node 454 (sourceLit (List.headD (raw_ints% [6029256878966797442971502322825]) 0) 48 true) (.node 438 (sourceLit (List.headD (raw_ints% [1826907310702042946014295923504823156655]) 0) 16 true) (.node 437 (sourceLit (List.headD (raw_ints% [48895212301469124522759]) 0) 71 false) (.node 436 (sourceLit (List.headD (raw_ints% [1183936991522043097886772910462604386755]) 0) 17 true) .empty .empty) .empty) (.node 439 (sourceLit (List.headD (raw_ints% [47513176904063731235587]) 0) 71 false) .empty .empty)) (.node 457 (sourceLit (List.headD (raw_ints% [285452693526108048271797597574502475]) 0) 38 false) (.node 456 (sourceLit (List.headD (raw_ints% [5506167815443226032141176311175]) 0) 52 false) (.node 455 (sourceLit (List.headD (raw_ints% [11426934494323390817775151176289875]) 0) 40 true) .empty .empty) .empty) (.node 458 (sourceLit (List.headD (raw_ints% [39615014854972546767943930039275]) 0) 51 true) .empty .empty)))

#time def treeG_J011_part074 : IntSourceTree :=
  (.node 464 (sourceLit (List.headD (raw_ints% [85153650490919791988827425]) 0) 61 false) (.node 462 (sourceLit (List.headD (raw_ints% [450164196532009358636283993375]) 0) 57 true) (.node 461 (sourceLit (List.headD (raw_ints% [9362944225496392442249348435951866275]) 0) 34 false) (.node 460 (sourceLit (List.headD (raw_ints% [905078981806025879269531246275]) 0) 57 false) .empty .empty) .empty) (.node 463 (sourceLit (List.headD (raw_ints% [3986745177139596338880521444154486525]) 0) 33 true) .empty .empty)) (.node 466 (sourceLit (List.headD (raw_ints% [156621919348190415759779475]) 0) 60 false) (.node 465 (sourceLit (List.headD (raw_ints% [2560656177441567351330430619279757825]) 0) 31 true) .empty .empty) (.node 467 (sourceLit (List.headD (raw_ints% [1943102736861675104065544214973134975]) 0) 30 true) .empty .empty)))

#time def treeG_J011_part075 : IntSourceTree :=
  (.node 459 (sourceLit (List.headD (raw_ints% [1307724210233121502141616022742135575]) 0) 37 true) treeG_J011_part073 treeG_J011_part074)

#time def treeG_J011_part076 : IntSourceTree :=
  (.node 435 (sourceLit (List.headD (raw_ints% [807343740067513496035995]) 0) 67 false) treeG_J011_part072 treeG_J011_part075)

#time def treeG_J011_part077 : IntSourceTree :=
  (.node 416 (sourceLit (List.headD (raw_ints% [367421314465386655160302592028014625]) 0) 36 false) treeG_J011_part069 treeG_J011_part076)

#time def treeG_J011_part078 : IntSourceTree :=
  (.node 473 (sourceLit (List.headD (raw_ints% [51729395459311188399828333782443517115]) 0) 23 true) (.node 471 (sourceLit (List.headD (raw_ints% [19402290081403233937030005226426519425]) 0) 25 true) (.node 470 (sourceLit (List.headD (raw_ints% [17215232680927086657567615]) 0) 63 false) (.node 469 (sourceLit (List.headD (raw_ints% [16031612456343605843879828673639876525]) 0) 26 true) .empty .empty) .empty) (.node 472 (sourceLit (List.headD (raw_ints% [1022388021856375972676685]) 0) 67 false) .empty .empty)) (.node 476 (sourceLit (List.headD (raw_ints% [58712849848480286851245]) 0) 71 false) (.node 475 (sourceLit (List.headD (raw_ints% [73475249316345861958026726743568300465]) 0) 22 true) (.node 474 (sourceLit (List.headD (raw_ints% [1955153094989346085109265]) 0) 66 false) .empty .empty) .empty) (.node 477 (sourceLit (List.headD (raw_ints% [436168159308217919246312321023008063705]) 0) 19 true) .empty .empty)))

#time def treeG_J011_part079 : IntSourceTree :=
  (.node 498 (sourceLit (List.headD (raw_ints% [6669115971012407251433320789263401025]) 0) 35 false) (.node 496 (sourceLit (List.headD (raw_ints% [733083218283735161329107429669290625]) 0) 36 true) (.node 495 (sourceLit (List.headD (raw_ints% [36548334129335019122588096715075]) 0) 48 true) (.node 479 (sourceLit (List.headD (raw_ints% [667916740083901351663318357675495149345]) 0) 18 true) .empty .empty) .empty) (.node 497 (sourceLit (List.headD (raw_ints% [72754669826923189845971163257325]) 0) 50 false) .empty .empty)) (.node 500 (sourceLit (List.headD (raw_ints% [101310256660562707713934290735512855025]) 0) 32 true) (.node 499 (sourceLit (List.headD (raw_ints% [13076352925411238262803999241675]) 0) 54 true) .empty .empty) (.node 501 (sourceLit (List.headD (raw_ints% [2034780050251693625018875726275]) 0) 57 false) .empty .empty)))

#time def treeG_J011_part080 : IntSourceTree :=
  (.node 478 (sourceLit (List.headD (raw_ints% [56650024853730005049963]) 0) 71 false) treeG_J011_part078 treeG_J011_part079)

#time def treeG_J011_part081 : IntSourceTree :=
  (.node 507 (sourceLit (List.headD (raw_ints% [47729954414757101328188145]) 0) 62 false) (.node 505 (sourceLit (List.headD (raw_ints% [421654282859844561806826075]) 0) 59 false) (.node 504 (sourceLit (List.headD (raw_ints% [121742600763111977490188513324578994925]) 0) 29 true) (.node 503 (sourceLit (List.headD (raw_ints% [901442841825020793260799771675]) 0) 57 true) .empty .empty) .empty) (.node 506 (sourceLit (List.headD (raw_ints% [36289245572776794871867260775586081175]) 0) 28 true) .empty .empty)) (.node 510 (sourceLit (List.headD (raw_ints% [206372489324563250257840916193464384625]) 0) 23 true) (.node 509 (sourceLit (List.headD (raw_ints% [10994966502241139144472195]) 0) 64 false) (.node 508 (sourceLit (List.headD (raw_ints% [208501812901491557444423627690111137425]) 0) 24 true) .empty .empty) .empty) (.node 511 (sourceLit (List.headD (raw_ints% [20522923594078488561944865]) 0) 63 false) .empty .empty)))

#time def treeG_J011_part082 : IntSourceTree :=
  (.node 517 (sourceLit (List.headD (raw_ints% [68530487395491449179731]) 0) 71 false) (.node 515 (sourceLit (List.headD (raw_ints% [573904677460916294536635]) 0) 68 false) (.node 514 (sourceLit (List.headD (raw_ints% [630495012111772351754430270791521716585]) 0) 20 true) (.node 513 (sourceLit (List.headD (raw_ints% [4835168636692894163878725]) 0) 65 false) .empty .empty) .empty) (.node 516 (sourceLit (List.headD (raw_ints% [3518478964724092067426937601125766843005]) 0) 17 true) .empty .empty)) (.node 519 (sourceLit (List.headD (raw_ints% [65786872803396278864339]) 0) 71 false) (.node 518 (sourceLit (List.headD (raw_ints% [5151783238229443761926701212863305862625]) 0) 16 true) .empty .empty) (.node 537 (sourceLit (List.headD (raw_ints% [1303988605335951257872702624818295575]) 0) 37 true) .empty .empty)))

#time def treeG_J011_part083 : IntSourceTree :=
  (.node 512 (sourceLit (List.headD (raw_ints% [484259070135958051261840466261063297295]) 0) 21 true) treeG_J011_part081 treeG_J011_part082)

#time def treeG_J011_part084 : IntSourceTree :=
  (.node 502 (sourceLit (List.headD (raw_ints% [158199854086117859248727793005093381475]) 0) 31 false) treeG_J011_part080 treeG_J011_part083)

#time def treeG_J011_part085 : IntSourceTree :=
  (.node 543 (sourceLit (List.headD (raw_ints% [166173344440397051926488835893402354525]) 0) 32 false) (.node 541 (sourceLit (List.headD (raw_ints% [120036145111555492598432987607416587575]) 0) 33 true) (.node 540 (sourceLit (List.headD (raw_ints% [16696668852635341779882124226775]) 0) 55 true) (.node 539 (sourceLit (List.headD (raw_ints% [9284564391478650255716552834747672175]) 0) 36 false) .empty .empty) .empty) (.node 542 (sourceLit (List.headD (raw_ints% [4519724297035396608674035445925]) 0) 57 false) .empty .empty)) (.node 546 (sourceLit (List.headD (raw_ints% [33129045438956768255880825]) 0) 63 false) (.node 545 (sourceLit (List.headD (raw_ints% [116621288408228842787527652086019479275]) 0) 30 true) (.node 544 (sourceLit (List.headD (raw_ints% [902124071028948151596710391075]) 0) 58 true) .empty .empty) .empty) (.node 547 (sourceLit (List.headD (raw_ints% [32403040099053444663736172345639811225]) 0) 29 true) .empty .empty)))

#time def treeG_J011_part086 : IntSourceTree :=
  (.node 553 (sourceLit (List.headD (raw_ints% [380800279217335674462183798696176263065]) 0) 22 true) (.node 551 (sourceLit (List.headD (raw_ints% [167567909161756782383780905740611345775]) 0) 24 true) (.node 550 (sourceLit (List.headD (raw_ints% [26764633328037469920321165]) 0) 63 false) (.node 549 (sourceLit (List.headD (raw_ints% [176438587988804345756663970342831384375]) 0) 25 true) .empty .empty) .empty) (.node 552 (sourceLit (List.headD (raw_ints% [12343819419227480780531385]) 0) 64 false) .empty .empty)) (.node 555 (sourceLit (List.headD (raw_ints% [483544513479080627838376817304385115655]) 0) 21 true) (.node 554 (sourceLit (List.headD (raw_ints% [720003885425887019692365]) 0) 68 false) .empty .empty) (.node 556 (sourceLit (List.headD (raw_ints% [339053278066995147131655]) 0) 69 false) .empty .empty)))

#time def treeG_J011_part087 : IntSourceTree :=
  (.node 548 (sourceLit (List.headD (raw_ints% [14733741927165083241364395]) 0) 64 false) treeG_J011_part085 treeG_J011_part086)

#time def treeG_J011_part088 : IntSourceTree :=
  (.node 582 (sourceLit (List.headD (raw_ints% [1118489014978561800036191693864426082075]) 0) 31 true) (.node 580 (sourceLit (List.headD (raw_ints% [398416317187879515896863981447438364625]) 0) 32 false) (.node 559 (sourceLit (List.headD (raw_ints% [3815949758061641058600064497512315563935]) 0) 17 true) (.node 558 (sourceLit (List.headD (raw_ints% [80410949937252893309499]) 0) 71 false) .empty .empty) .empty) (.node 581 (sourceLit (List.headD (raw_ints% [20766228953138729029919875679325]) 0) 56 true) .empty .empty)) (.node 584 (sourceLit (List.headD (raw_ints% [2780516111809464808314009887619016667325]) 0) 29 false) (.node 583 (sourceLit (List.headD (raw_ints% [9940891435895814010608870663525]) 0) 57 false) .empty .empty) (.node 585 (sourceLit (List.headD (raw_ints% [451272862655903998079258608575]) 0) 60 true) .empty .empty)))

#time def treeG_J011_part089 : IntSourceTree :=
  (.node 591 (sourceLit (List.headD (raw_ints% [33006343061996451278697465]) 0) 63 false) (.node 589 (sourceLit (List.headD (raw_ints% [18472517352089027338256595]) 0) 64 false) (.node 588 (sourceLit (List.headD (raw_ints% [1865292753437928901034691402430836780975]) 0) 24 true) (.node 587 (sourceLit (List.headD (raw_ints% [84786227341069971695335155]) 0) 62 false) .empty .empty) .empty) (.node 590 (sourceLit (List.headD (raw_ints% [1205136214585871515795470846549186690375]) 0) 23 true) .empty .empty)) (.node 593 (sourceLit (List.headD (raw_ints% [1877162695633646654163165]) 0) 67 false) (.node 592 (sourceLit (List.headD (raw_ints% [2196827476452150466878654025588718235105]) 0) 21 true) .empty .empty) (.node 594 (sourceLit (List.headD (raw_ints% [2415907221626913043943040118777888387935]) 0) 20 true) .empty .empty)))

#time def treeG_J011_part090 : IntSourceTree :=
  (.node 586 (sourceLit (List.headD (raw_ints% [896681061693053947428353955912569753025]) 0) 28 true) treeG_J011_part088 treeG_J011_part089)

#time def treeG_J011_part091 : IntSourceTree :=
  (.node 557 (sourceLit (List.headD (raw_ints% [2646142646107656228934312959079750715595]) 0) 18 true) treeG_J011_part087 treeG_J011_part090)

#time def treeG_J011_part092 : IntSourceTree :=
  (.node 538 (sourceLit (List.headD (raw_ints% [14046210585236967076739386662075]) 0) 54 false) treeG_J011_part084 treeG_J011_part091)

#time def treeG_J011_part093 : IntSourceTree :=
  (.node 468 (sourceLit (List.headD (raw_ints% [18262470560426934845459355]) 0) 63 false) treeG_J011_part077 treeG_J011_part092)

#time def treeG_J011_part094 : IntSourceTree :=
  (.node 621 (sourceLit (List.headD (raw_ints% [64806557787429376061912121131856869025]) 0) 36 false) (.node 598 (sourceLit (List.headD (raw_ints% [16017357930631806069547802459774699862135]) 0) 16 true) (.node 597 (sourceLit (List.headD (raw_ints% [201992303276012248772193]) 0) 70 false) (.node 596 (sourceLit (List.headD (raw_ints% [11954945466606488023401120552614556857955]) 0) 17 true) .empty .empty) .empty) (.node 599 (sourceLit (List.headD (raw_ints% [95035027071109507754659]) 0) 71 false) .empty .empty)) (.node 624 (sourceLit (List.headD (raw_ints% [1355376938365595270275697631825]) 0) 61 false) (.node 623 (sourceLit (List.headD (raw_ints% [160582794927369856495335066219728554575]) 0) 35 true) (.node 622 (sourceLit (List.headD (raw_ints% [12642976625087062819296955562625]) 0) 58 true) .empty .empty) .empty) (.node 625 (sourceLit (List.headD (raw_ints% [362142175027211706387692192463129518325]) 0) 33 false) .empty .empty)))

#time def treeG_J011_part095 : IntSourceTree :=
  (.node 631 (sourceLit (List.headD (raw_ints% [129696038178014341676461242601071918075]) 0) 27 true) (.node 629 (sourceLit (List.headD (raw_ints% [211106770681140569409753429011000674575]) 0) 28 true) (.node 628 (sourceLit (List.headD (raw_ints% [55318743486739805212606365]) 0) 63 false) (.node 627 (sourceLit (List.headD (raw_ints% [108034752699250062845577222945866242725]) 0) 32 true) .empty .empty) .empty) (.node 630 (sourceLit (List.headD (raw_ints% [47125436080318639432705215]) 0) 63 false) .empty .empty)) (.node 633 (sourceLit (List.headD (raw_ints% [227003399654351849052058778361567746505]) 0) 25 true) (.node 632 (sourceLit (List.headD (raw_ints% [322851931918265164033845]) 0) 70 false) .empty .empty) (.node 634 (sourceLit (List.headD (raw_ints% [72322425637984977154425]) 0) 72 false) .empty .empty)))

#time def treeG_J011_part096 : IntSourceTree :=
  (.node 626 (sourceLit (List.headD (raw_ints% [451405378837659825152282131875]) 0) 61 true) treeG_J011_part094 treeG_J011_part095)

#time def treeG_J011_part097 : IntSourceTree :=
  (.node 663 (sourceLit (List.headD (raw_ints% [60512797936244065287796692914025]) 0) 57 true) (.node 638 (sourceLit (List.headD (raw_ints% [60790676669379677731347]) 0) 72 false) (.node 637 (sourceLit (List.headD (raw_ints% [1163600352562353974308350949191850767795]) 0) 21 true) (.node 636 (sourceLit (List.headD (raw_ints% [65881226915482824714555]) 0) 72 false) .empty .empty) .empty) (.node 639 (sourceLit (List.headD (raw_ints% [1525176021571270626368467245282798037275]) 0) 20 true) .empty .empty)) (.node 666 (sourceLit (List.headD (raw_ints% [24073780263434603156240654273552858925825]) 0) 28 false) (.node 665 (sourceLit (List.headD (raw_ints% [5872780616118285079182049135875]) 0) 60 false) (.node 664 (sourceLit (List.headD (raw_ints% [23335113862512806439716898363744271652925]) 0) 29 true) .empty .empty) .empty) (.node 667 (sourceLit (List.headD (raw_ints% [225745082532500447561988733515]) 0) 63 true) .empty .empty)))

#time def treeG_J011_part098 : IntSourceTree :=
  (.node 673 (sourceLit (List.headD (raw_ints% [3288468215058595970378355]) 0) 67 false) (.node 671 (sourceLit (List.headD (raw_ints% [61244529098640827586712965]) 0) 63 false) (.node 670 (sourceLit (List.headD (raw_ints% [12305697109007124926428748610154856482425]) 0) 23 true) (.node 669 (sourceLit (List.headD (raw_ints% [18423113067325388937174885]) 0) 65 false) .empty .empty) .empty) (.node 672 (sourceLit (List.headD (raw_ints% [14404265410333685267708385027348487278495]) 0) 21 true) .empty .empty)) (.node 675 (sourceLit (List.headD (raw_ints% [1448214527024661524093505]) 0) 68 false) (.node 674 (sourceLit (List.headD (raw_ints% [12112310356251605295388721696362447388385]) 0) 20 true) .empty .empty) (.node 676 (sourceLit (List.headD (raw_ints% [49880661194124149291948105094537547855005]) 0) 17 true) .empty .empty)))

#time def treeG_J011_part099 : IntSourceTree :=
  (.node 668 (sourceLit (List.headD (raw_ints% [53448500628578103275900846745852679494225]) 0) 24 true) treeG_J011_part097 treeG_J011_part098)

#time def treeG_J011_part100 : IntSourceTree :=
  (.node 635 (sourceLit (List.headD (raw_ints% [241545338518479052013082912684187909035]) 0) 24 true) treeG_J011_part096 treeG_J011_part099)

#time def treeG_J011_part101 : IntSourceTree :=
  (.node 706 (sourceLit (List.headD (raw_ints% [3162092997477972452167165633875]) 0) 62 false) (.node 704 (sourceLit (List.headD (raw_ints% [71355813443168827450002273968625]) 0) 58 true) (.node 679 (sourceLit (List.headD (raw_ints% [148127679606409203170729]) 0) 71 false) (.node 678 (sourceLit (List.headD (raw_ints% [58453064633358848286186658288503749276745]) 0) 16 true) .empty .empty) .empty) (.node 705 (sourceLit (List.headD (raw_ints% [26232251262730500090818435903449307799525]) 0) 30 true) .empty .empty)) (.node 709 (sourceLit (List.headD (raw_ints% [51759646463128978720622819313764674097625]) 0) 25 true) (.node 708 (sourceLit (List.headD (raw_ints% [451545483808487634929190073395]) 0) 63 true) (.node 707 (sourceLit (List.headD (raw_ints% [24938058285028603659005272057119788867625]) 0) 29 false) .empty .empty) .empty) (.node 710 (sourceLit (List.headD (raw_ints% [100259468458284472064693865]) 0) 63 false) .empty .empty)))

#time def treeG_J011_part102 : IntSourceTree :=
  (.node 716 (sourceLit (List.headD (raw_ints% [921164711700798926377065]) 0) 69 false) (.node 714 (sourceLit (List.headD (raw_ints% [2131309404850836335907555]) 0) 68 false) (.node 713 (sourceLit (List.headD (raw_ints% [12588238213098870475291914800455945306455]) 0) 22 true) (.node 712 (sourceLit (List.headD (raw_ints% [40582005455871857088546885]) 0) 64 false) .empty .empty) .empty) (.node 715 (sourceLit (List.headD (raw_ints% [10179947648103772879284058394888944116105]) 0) 21 true) .empty .empty)) (.node 718 (sourceLit (List.headD (raw_ints% [203476158709090993481553]) 0) 71 false) (.node 717 (sourceLit (List.headD (raw_ints% [40571858373625317497481297501002741712645]) 0) 18 true) .empty .empty) (.node 719 (sourceLit (List.headD (raw_ints% [46251656460788683275238920326241364978545]) 0) 17 true) .empty .empty)))

#time def treeG_J011_part103 : IntSourceTree :=
  (.node 711 (sourceLit (List.headD (raw_ints% [11268128803583010193017058669346281137825]) 0) 24 true) treeG_J011_part101 treeG_J011_part102)

#time def treeG_J011_part104 : IntSourceTree :=
  (.node 750 (sourceLit (List.headD (raw_ints% [401771474596024704838553805899962536298575]) 0) 23 true) (.node 748 (sourceLit (List.headD (raw_ints% [1649484230870408737452238258401519167022225]) 0) 24 false) (.node 747 (sourceLit (List.headD (raw_ints% [1693919040005236449864577183695]) 0) 64 false) (.node 746 (sourceLit (List.headD (raw_ints% [233931790365278603882788141501147321322025]) 0) 28 true) .empty .empty) .empty) (.node 749 (sourceLit (List.headD (raw_ints% [451582330034622285707064423165]) 0) 64 true) .empty .empty)) (.node 752 (sourceLit (List.headD (raw_ints% [165885795446994477820564553682192010926705]) 0) 21 true) (.node 751 (sourceLit (List.headD (raw_ints% [139274407817928116542674765]) 0) 63 false) .empty .empty) (.node 753 (sourceLit (List.headD (raw_ints% [27428132595637473207033465]) 0) 65 false) .empty .empty)))

#time def treeG_J011_part105 : IntSourceTree :=
  (.node 759 (sourceLit (List.headD (raw_ints% [258824637811772783792377]) 0) 71 false) (.node 757 (sourceLit (List.headD (raw_ints% [298053599826474288716409]) 0) 71 false) (.node 756 (sourceLit (List.headD (raw_ints% [275877663545196582845141763541908663860355]) 0) 17 true) (.node 755 (sourceLit (List.headD (raw_ints% [2814404282677011147721605]) 0) 68 false) .empty .empty) .empty) (.node 758 (sourceLit (List.headD (raw_ints% [266121802355643691693663721719518184424415]) 0) 16 true) .empty .empty)) (.node 787 (sourceLit (List.headD (raw_ints% [129434924325153603770896706779133555094825]) 0) 30 true) (.node 786 (sourceLit (List.headD (raw_ints% [95749746665317287417035034775875]) 0) 60 true) .empty .empty) (.node 788 (sourceLit (List.headD (raw_ints% [7227221643829433434387498808175]) 0) 63 false) .empty .empty)))

#time def treeG_J011_part106 : IntSourceTree :=
  (.node 754 (sourceLit (List.headD (raw_ints% [88593595348539358506946596707285115063255]) 0) 20 true) treeG_J011_part104 treeG_J011_part105)

#time def treeG_J011_part107 : IntSourceTree :=
  (.node 745 (sourceLit (List.headD (raw_ints% [83101374675405397608366372240375]) 0) 59 true) treeG_J011_part103 treeG_J011_part106)

#time def treeG_J011_part108 : IntSourceTree :=
  (.node 677 (sourceLit (List.headD (raw_ints% [325057512047850348944247]) 0) 70 false) treeG_J011_part100 treeG_J011_part107)

#time def treeG_J011_part109 : IntSourceTree :=
  (.node 794 (sourceLit (List.headD (raw_ints% [18902894976234127863403245]) 0) 66 false) (.node 792 (sourceLit (List.headD (raw_ints% [12336550295257032431765985]) 0) 67 false) (.node 791 (sourceLit (List.headD (raw_ints% [195251672896220847322768373615308127580375]) 0) 25 true) (.node 790 (sourceLit (List.headD (raw_ints% [1806429579606947427300322386525]) 0) 63 true) .empty .empty) .empty) (.node 793 (sourceLit (List.headD (raw_ints% [76648778616947803672636319440868032810125]) 0) 23 true) .empty .empty)) (.node 797 (sourceLit (List.headD (raw_ints% [117652902585785632673830233020452961073855]) 0) 19 true) (.node 796 (sourceLit (List.headD (raw_ints% [473309892744053055336135]) 0) 71 false) (.node 795 (sourceLit (List.headD (raw_ints% [39206823850217792813831269156198085473575]) 0) 22 true) .empty .empty) .empty) (.node 798 (sourceLit (List.headD (raw_ints% [392631040943857583951265]) 0) 71 false) .empty .empty)))

#time def treeG_J011_part110 : IntSourceTree :=
  (.node 831 (sourceLit (List.headD (raw_ints% [3612998433621712782717187447815]) 0) 63 true) (.node 829 (sourceLit (List.headD (raw_ints% [1919700993466013930023640807835]) 0) 66 false) (.node 828 (sourceLit (List.headD (raw_ints% [18217154544490070020127016726130614219159825]) 0) 24 true) (.node 827 (sourceLit (List.headD (raw_ints% [109301098985359179015951652245435]) 0) 61 true) .empty .empty) .empty) (.node 830 (sourceLit (List.headD (raw_ints% [14011722493264326434221442427622233265257375]) 0) 23 false) .empty .empty)) (.node 833 (sourceLit (List.headD (raw_ints% [71264269766418786247094415]) 0) 65 false) (.node 832 (sourceLit (List.headD (raw_ints% [6082167737232072636508023402007668071645295]) 0) 21 true) .empty .empty) (.node 834 (sourceLit (List.headD (raw_ints% [1137786862522625500255234514346603409898745]) 0) 20 true) .empty .empty)))

#time def treeG_J011_part111 : IntSourceTree :=
  (.node 799 (sourceLit (List.headD (raw_ints% [109935072947427504209212400696638409722935]) 0) 18 true) treeG_J011_part109 treeG_J011_part110)

#time def treeG_J011_part112 : IntSourceTree :=
  (.node 868 (sourceLit (List.headD (raw_ints% [123755542273018045884726649861785]) 0) 62 true) (.node 838 (sourceLit (List.headD (raw_ints% [1616324639016926431087620006607729192757265]) 0) 16 true) (.node 837 (sourceLit (List.headD (raw_ints% [648566185661631821955861]) 0) 71 false) (.node 836 (sourceLit (List.headD (raw_ints% [2233359062868742157240059462454768806448445]) 0) 17 true) .empty .empty) .empty) (.node 839 (sourceLit (List.headD (raw_ints% [526437444075942384110153]) 0) 71 false) .empty .empty)) (.node 871 (sourceLit (List.headD (raw_ints% [14402225839056768128866979174852849520418125]) 0) 24 false) (.node 870 (sourceLit (List.headD (raw_ints% [32521645475063170307678575311885]) 0) 63 false) (.node 869 (sourceLit (List.headD (raw_ints% [19918398421823607736299877803845898060279675]) 0) 25 true) .empty .empty) .empty) (.node 872 (sourceLit (List.headD (raw_ints% [3613097126024074838976641575695]) 0) 64 true) .empty .empty)))

#time def treeG_J011_part113 : IntSourceTree :=
  (.node 878 (sourceLit (List.headD (raw_ints% [904501330379406059960457]) 0) 71 false) (.node 876 (sourceLit (List.headD (raw_ints% [9487607268927681125270955]) 0) 68 false) (.node 875 (sourceLit (List.headD (raw_ints% [1059373214822189914627571976034207238951595]) 0) 21 true) (.node 874 (sourceLit (List.headD (raw_ints% [26180687395092329191845585]) 0) 67 false) .empty .empty) .empty) (.node 877 (sourceLit (List.headD (raw_ints% [1998053257697170891892398996413862884300735]) 0) 18 true) .empty .empty)) (.node 909 (sourceLit (List.headD (raw_ints% [139113150220746157324915776324465]) 0) 63 true) (.node 879 (sourceLit (List.headD (raw_ints% [1396454493122071422669195205214452373311395]) 0) 17 true) .empty .empty) (.node 910 (sourceLit (List.headD (raw_ints% [173358909867853188324620464858389417747494775]) 0) 23 true) .empty .empty)))

#time def treeG_J011_part114 : IntSourceTree :=
  (.node 873 (sourceLit (List.headD (raw_ints% [5928870179998177029162750763125932006025045]) 0) 22 true) treeG_J011_part112 treeG_J011_part113)

#time def treeG_J011_part115 : IntSourceTree :=
  (.node 835 (sourceLit (List.headD (raw_ints% [13274086410880105567960035]) 0) 67 false) treeG_J011_part111 treeG_J011_part114)

#time def treeG_J011_part116 : IntSourceTree :=
  (.node 916 (sourceLit (List.headD (raw_ints% [31666583811441335110842243770639862840002595]) 0) 17 true) (.node 914 (sourceLit (List.headD (raw_ints% [46293174577462790733046771590660852638301615]) 0) 20 true) (.node 913 (sourceLit (List.headD (raw_ints% [1806584195146920628881444335055]) 0) 66 true) (.node 912 (sourceLit (List.headD (raw_ints% [236517781162140362698379690199653260398335295]) 0) 21 false) .empty .empty) .empty) (.node 915 (sourceLit (List.headD (raw_ints% [39087288379304552815731135]) 0) 67 false) .empty .empty)) (.node 919 (sourceLit (List.headD (raw_ints% [1282565216682869735810761]) 0) 71 false) (.node 918 (sourceLit (List.headD (raw_ints% [14368101422560440704051571964703173881648615]) 0) 16 true) (.node 917 (sourceLit (List.headD (raw_ints% [6893342526281153837447511]) 0) 69 false) .empty .empty) .empty) (.node 950 (sourceLit (List.headD (raw_ints% [310747945916555484957510127960815]) 0) 63 true) .empty .empty)))

#time def treeG_J011_part117 : IntSourceTree :=
  (.node 956 (sourceLit (List.headD (raw_ints% [7399920277594217922615045]) 0) 70 false) (.node 954 (sourceLit (List.headD (raw_ints% [56456574244822366287832380645]) 0) 72 true) (.node 953 (sourceLit (List.headD (raw_ints% [60611662835534634931885610240694798101090085]) 0) 24 false) (.node 952 (sourceLit (List.headD (raw_ints% [4516836656860758014815686227955]) 0) 68 false) .empty .empty) .empty) (.node 955 (sourceLit (List.headD (raw_ints% [11308450340660150204604799903656661349837505]) 0) 23 true) .empty .empty)) (.node 958 (sourceLit (List.headD (raw_ints% [5084339865522341717526597]) 0) 70 false) (.node 957 (sourceLit (List.headD (raw_ints% [7417132638436041054737461193556499988925465]) 0) 20 true) .empty .empty) (.node 959 (sourceLit (List.headD (raw_ints% [3242911732359592320345594189872180377084305]) 0) 19 true) .empty .empty)))

#time def treeG_J011_part118 : IntSourceTree :=
  (.node 951 (sourceLit (List.headD (raw_ints% [46940283926727489113371861008310566816978225]) 0) 26 true) treeG_J011_part116 treeG_J011_part117)

#time def treeG_J011_part119 : IntSourceTree :=
  (.node 998 (sourceLit (List.headD (raw_ints% [222980143007392873047547186229104825763966265]) 0) 16 true) (.node 996 (sourceLit (List.headD (raw_ints% [1415815059793057891078572143897412789939198045]) 0) 17 true) (.node 995 (sourceLit (List.headD (raw_ints% [3613259838957010746974088092415]) 0) 67 true) (.node 994 (sourceLit (List.headD (raw_ints% [1985866385314571108553386299292894391873184335]) 0) 20 false) .empty .empty) .empty) (.node 997 (sourceLit (List.headD (raw_ints% [22706338584095717853012669]) 0) 69 false) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [39747887825867300468617570339335]) 0) 67 false) (.node 999 (sourceLit (List.headD (raw_ints% [950443662209867995428959]) 0) 73 false) .empty .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [2031100186677211709371805498907521037272534355]) 0) 21 false) .empty .empty)))

#time def treeG_J011_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [66411021033463832590976348108938085982660297405]) 0) 17 false) (.node 1039 (sourceLit (List.headD (raw_ints% [210008496077954503766164809469616104255629045]) 0) 17 true) (.node 1038 (sourceLit (List.headD (raw_ints% [2202749839821672016935759]) 0) 73 false) (.node 1037 (sourceLit (List.headD (raw_ints% [1386146529239313726859622299123186789983496185]) 0) 18 true) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [83109035490691611684209228771085]) 0) 67 false) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [10866192090907116941829431206756389494104003215]) 0) 16 true) (.node 1077 (sourceLit (List.headD (raw_ints% [225832009061044076222726972829]) 0) 73 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [3455056017433476038442559]) 0) 73 false) .empty .empty)))

#time def treeG_J011_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [3613289438638121123845778552595]) 0) 68 true) treeG_J011_part119 treeG_J011_part120)

#time def treeG_J011_part122 : IntSourceTree :=
  (.node 993 (sourceLit (List.headD (raw_ints% [37941277450032984747406934158695]) 0) 66 false) treeG_J011_part118 treeG_J011_part121)

#time def treeG_J011_part123 : IntSourceTree :=
  (.node 911 (sourceLit (List.headD (raw_ints% [68656289383748053398074338071585]) 0) 63 false) treeG_J011_part115 treeG_J011_part122)

#time def treeG_J011_part124 : IntSourceTree :=
  (.node 789 (sourceLit (List.headD (raw_ints% [850621938666768858086430538857641920559925]) 0) 26 false) treeG_J011_part108 treeG_J011_part123)

#time def treeG_J011_part125 : IntSourceTree :=
  (.node 595 (sourceLit (List.headD (raw_ints% [866103093390857744848095]) 0) 68 false) treeG_J011_part093 treeG_J011_part124)

#time def treeG_J011_part126 : IntSourceTree :=
  (.node 355 (sourceLit (List.headD (raw_ints% [581438703101254036389495]) 0) 67 false) treeG_J011_part062 treeG_J011_part125)

#time def treeG_J011 : IntSourceTree := treeG_J011_part126

-- kcost: 0.399s estimated (133 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J001_check : treeG_J001.check 40 (sourceBaseG momentData 1) = true := by
  decide +kernel

-- kcost: 0.579s estimated (193 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J002_check : treeG_J002.check 40 (sourceBaseG momentData 2) = true := by
  decide +kernel

-- kcost: 1.416s estimated (472 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J003_check : treeG_J003.check 40 (sourceBaseG momentData 3) = true := by
  decide +kernel

-- kcost: 1.830s estimated (610 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J004_check : treeG_J004.check 40 (sourceBaseG momentData 4) = true := by
  decide +kernel

-- kcost: 1.830s estimated (610 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J005_check : treeG_J005.check 40 (sourceBaseG momentData 5) = true := by
  decide +kernel

-- kcost: 1.830s estimated (610 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J007_check : treeG_J007.check 40 (sourceBaseG momentData 7) = true := by
  decide +kernel

-- kcost: 1.830s estimated (610 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J008_check : treeG_J008.check 40 (sourceBaseG momentData 8) = true := by
  decide +kernel

-- kcost: 1.806s estimated (602 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J009_check : treeG_J009.check 40 (sourceBaseG momentData 9) = true := by
  decide +kernel

-- kcost: 1.806s estimated (602 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J010_check : treeG_J010.check 40 (sourceBaseG momentData 10) = true := by
  decide +kernel

-- kcost: 1.806s estimated (602 source nodes *0.003s/node; representative610-node checked command1.358s; includes tree lookup/decoder, excludes imports/declarations).
#time theorem treeG_J011_check : treeG_J011.check 40 (sourceBaseG momentData 11) = true := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
