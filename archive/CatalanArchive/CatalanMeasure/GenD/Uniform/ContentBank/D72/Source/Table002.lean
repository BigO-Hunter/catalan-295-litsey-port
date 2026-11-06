module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table001
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceSparse
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Retained exact sparse source values for the actual small/large check classes.
Odd raw magnitudes and explicit binary exponents preserve every integer.
This calibrates two required trees, not the full sparse source bank. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6

#time def treeT_J001_part000 : IntSourceTree :=
  (.node 9 (sourceLit (List.headD (raw_ints% [276011520207190855063314717468375]) 0) 34 true) (.node 5 (sourceLit (List.headD (raw_ints% [203071538891176454926462780119375]) 0) 35 true) (.node 3 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 36 true) (.node 2 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 37 false) .empty .empty) (.node 4 (sourceLit (List.headD (raw_ints% [234313314105203601838226284753125]) 0) 35 true) .empty .empty)) (.node 7 (sourceLit (List.headD (raw_ints% [163082066617221706879405494188175]) 0) 35 true) (.node 6 (sourceLit (List.headD (raw_ints% [721685007444027093661736957039625]) 0) 33 true) .empty .empty) (.node 8 (sourceLit (List.headD (raw_ints% [298582108831202304056711208571125]) 0) 34 true) .empty .empty))) (.node 13 (sourceLit (List.headD (raw_ints% [215044478955489574038102016960125]) 0) 34 true) (.node 11 (sourceLit (List.headD (raw_ints% [241057570341882477996956184166125]) 0) 34 true) (.node 10 (sourceLit (List.headD (raw_ints% [2057047742306444573090257040813625]) 0) 31 true) .empty .empty) (.node 12 (sourceLit (List.headD (raw_ints% [454352788573660774736766334532025]) 0) 33 true) .empty .empty)) (.node 15 (sourceLit (List.headD (raw_ints% [194795457471227605250428725468375]) 0) 34 true) (.node 14 (sourceLit (List.headD (raw_ints% [817334984572820163494155758772125]) 0) 32 true) .empty .empty) (.node 16 (sourceLit (List.headD (raw_ints% [372474458234232002977686548887125]) 0) 33 true) .empty .empty))))

#time def treeT_J001_part001 : IntSourceTree :=
  (.node 50 (sourceLit (List.headD (raw_ints% [276011520207190855063314717468375]) 0) 35 true) (.node 46 (sourceLit (List.headD (raw_ints% [203071538891176454926462780119375]) 0) 36 true) (.node 44 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 37 true) (.node 43 (sourceLit (List.headD (raw_ints% [140587988463122161102935770851875]) 0) 38 false) .empty .empty) (.node 45 (sourceLit (List.headD (raw_ints% [234313314105203601838226284753125]) 0) 36 true) .empty .empty)) (.node 48 (sourceLit (List.headD (raw_ints% [163082066617221706879405494188175]) 0) 36 true) (.node 47 (sourceLit (List.headD (raw_ints% [721685007444027093661736957039625]) 0) 34 true) .empty .empty) (.node 49 (sourceLit (List.headD (raw_ints% [298582108831202304056711208571125]) 0) 35 true) .empty .empty))) (.node 54 (sourceLit (List.headD (raw_ints% [215044478955489574038102016960125]) 0) 35 true) (.node 52 (sourceLit (List.headD (raw_ints% [241057570341882477996956184166125]) 0) 35 true) (.node 51 (sourceLit (List.headD (raw_ints% [2057047742306444573090257040813625]) 0) 32 true) .empty .empty) (.node 53 (sourceLit (List.headD (raw_ints% [454352788573660774736766334532025]) 0) 34 true) .empty .empty)) (.node 56 (sourceLit (List.headD (raw_ints% [194795457471227605250428725468375]) 0) 35 true) (.node 55 (sourceLit (List.headD (raw_ints% [817334984572820163494155758772125]) 0) 33 true) .empty .empty) .empty)))

#time def treeT_J001_part002 : IntSourceTree :=
  (.node 17 (sourceLit (List.headD (raw_ints% [357015360249491346852703163684775]) 0) 33 true) treeT_J001_part000 treeT_J001_part001)

#time def treeT_J001_part003 : IntSourceTree :=
  (.node 91 (sourceLit (List.headD (raw_ints% [862988510486880942256302685707375]) 0) 34 true) (.node 87 (sourceLit (List.headD (raw_ints% [649204088947484112826445626289325]) 0) 35 true) (.node 85 (sourceLit (List.headD (raw_ints% [921632368813800833897023386695625]) 0) 35 true) (.node 84 (sourceLit (List.headD (raw_ints% [2483721129515158179485198618383125]) 0) 35 false) .empty .empty) (.node 86 (sourceLit (List.headD (raw_ints% [3027328018239230535749883599010375]) 0) 33 true) .empty .empty)) (.node 89 (sourceLit (List.headD (raw_ints% [1028645012730582799971929236037025]) 0) 34 true) (.node 88 (sourceLit (List.headD (raw_ints% [1144787906056851883266762705508125]) 0) 34 true) .empty .empty) (.node 90 (sourceLit (List.headD (raw_ints% [7497579740292029156724501633462375]) 0) 31 true) .empty .empty))) (.node 95 (sourceLit (List.headD (raw_ints% [665382458350730690901979342372125]) 0) 34 true) (.node 93 (sourceLit (List.headD (raw_ints% [749185802412040337949722719704375]) 0) 34 true) (.node 92 (sourceLit (List.headD (raw_ints% [12521054326037373424636646142825]) 0) 40 true) .empty .empty) (.node 94 (sourceLit (List.headD (raw_ints% [2817487324016466034399974917484075]) 0) 32 true) .empty .empty)) (.node 97 (sourceLit (List.headD (raw_ints% [1201348299520329495150726640062225]) 0) 33 true) (.node 96 (sourceLit (List.headD (raw_ints% [1262195510911408324010624968657125]) 0) 33 true) .empty .empty) .empty)))

#time def treeT_J001_part004 : IntSourceTree :=
  (.node 133 (sourceLit (List.headD (raw_ints% [1148342165159123023616724371749575]) 0) 34 true) (.node 129 (sourceLit (List.headD (raw_ints% [105775724653206197401256437117125]) 0) 38 true) (.node 127 (sourceLit (List.headD (raw_ints% [1152821505397601721044073320985375]) 0) 35 true) (.node 126 (sourceLit (List.headD (raw_ints% [359280414961312189485280303288125]) 0) 37 true) .empty .empty) (.node 128 (sourceLit (List.headD (raw_ints% [243061011165131202973520066050575]) 0) 37 true) .empty .empty)) (.node 131 (sourceLit (List.headD (raw_ints% [2720265998992792291817122296324375]) 0) 33 true) (.node 130 (sourceLit (List.headD (raw_ints% [376316746261695972454307259284325]) 0) 36 true) .empty .empty) (.node 132 (sourceLit (List.headD (raw_ints% [310965470072499232129673250770625]) 0) 36 true) .empty .empty))) (.node 137 (sourceLit (List.headD (raw_ints% [55607565792323520064558651235625]) 0) 38 true) (.node 135 (sourceLit (List.headD (raw_ints% [1000076169721822935452909579355975]) 0) 34 true) (.node 134 (sourceLit (List.headD (raw_ints% [267070661728275381955810351372125]) 0) 36 true) .empty .empty) (.node 136 (sourceLit (List.headD (raw_ints% [235293500439751542825775308451875]) 0) 36 true) .empty .empty)) (.node 167 (sourceLit (List.headD (raw_ints% [2225039230743013403055796800015675]) 0) 35 true) (.node 166 (sourceLit (List.headD (raw_ints% [46515879116165019036924682049190375]) 0) 33 false) .empty .empty) .empty)))

#time def treeT_J001_part005 : IntSourceTree :=
  (.node 125 (sourceLit (List.headD (raw_ints% [1359017221810180890661712451568125]) 0) 37 false) treeT_J001_part003 treeT_J001_part004)

#time def treeT_J001_part006 : IntSourceTree :=
  (.node 57 (sourceLit (List.headD (raw_ints% [372474458234232002977686548887125]) 0) 34 true) treeT_J001_part002 treeT_J001_part005)

#time def treeT_J001_part007 : IntSourceTree :=
  (.node 176 (sourceLit (List.headD (raw_ints% [2738109167975883417801013348766775]) 0) 33 true) (.node 172 (sourceLit (List.headD (raw_ints% [1918918522126400392640376943183575]) 0) 34 true) (.node 170 (sourceLit (List.headD (raw_ints% [19581005770928757377997146268521625]) 0) 31 true) (.node 169 (sourceLit (List.headD (raw_ints% [2860331165911516447604391820772175]) 0) 34 true) .empty .empty) (.node 171 (sourceLit (List.headD (raw_ints% [2147545459606686837378155388567225]) 0) 34 true) .empty .empty)) (.node 174 (sourceLit (List.headD (raw_ints% [6369249997256518154533820056512525]) 0) 32 true) (.node 173 (sourceLit (List.headD (raw_ints% [1738537958167953519087663286460625]) 0) 34 true) .empty .empty) (.node 175 (sourceLit (List.headD (raw_ints% [1471182835475472364744503468604875]) 0) 34 true) .empty .empty))) (.node 209 (sourceLit (List.headD (raw_ints% [2620292318307905421699479081496375]) 0) 35 true) (.node 207 (sourceLit (List.headD (raw_ints% [48821522126960222479012828691161125]) 0) 34 false) (.node 177 (sourceLit (List.headD (raw_ints% [2563347707515695190061678295167775]) 0) 33 true) .empty .empty) (.node 208 (sourceLit (List.headD (raw_ints% [1738917208412750997108756667914525]) 0) 36 true) .empty .empty)) (.node 211 (sourceLit (List.headD (raw_ints% [14140473772943172794362901675872875]) 0) 32 true) (.node 210 (sourceLit (List.headD (raw_ints% [2107697673388124502695777302203525]) 0) 35 true) .empty .empty) (.node 212 (sourceLit (List.headD (raw_ints% [1525614519461688373118808887025975]) 0) 35 true) .empty .empty))))

#time def treeT_J001_part008 : IntSourceTree :=
  (.node 251 (sourceLit (List.headD (raw_ints% [6283245233945811173404953820246875]) 0) 34 true) (.node 217 (sourceLit (List.headD (raw_ints% [1848388115298707096768074928996775]) 0) 34 true) (.node 215 (sourceLit (List.headD (raw_ints% [4369097657812872283628000897800575]) 0) 33 true) (.node 214 (sourceLit (List.headD (raw_ints% [1204396634711402755176042583716375]) 0) 35 true) .empty .empty) (.node 216 (sourceLit (List.headD (raw_ints% [1000595834595969279092952851701125]) 0) 35 true) .empty .empty)) (.node 249 (sourceLit (List.headD (raw_ints% [11051006501390491529265661522544025]) 0) 34 true) (.node 248 (sourceLit (List.headD (raw_ints% [101109542369453999958935187960755625]) 0) 34 false) .empty .empty) (.node 250 (sourceLit (List.headD (raw_ints% [64268348414924216116386184339362375]) 0) 31 true) .empty .empty))) (.node 255 (sourceLit (List.headD (raw_ints% [3346403703370138655959666866260625]) 0) 34 true) (.node 253 (sourceLit (List.headD (raw_ints% [4363920119678799973387572261643275]) 0) 34 true) (.node 252 (sourceLit (List.headD (raw_ints% [10302636728690372009082147789505725]) 0) 33 true) .empty .empty) (.node 254 (sourceLit (List.headD (raw_ints% [15146709035492903938778416060428075]) 0) 32 true) .empty .empty)) (.node 257 (sourceLit (List.headD (raw_ints% [5441418969252059042681944518441225]) 0) 33 true) (.node 256 (sourceLit (List.headD (raw_ints% [6000086147649861149454988446834375]) 0) 33 true) .empty .empty) .empty)))

#time def treeT_J001_part009 : IntSourceTree :=
  (.node 213 (sourceLit (List.headD (raw_ints% [2689494879093677761664029514617575]) 0) 34 true) treeT_J001_part007 treeT_J001_part008)

#time def treeT_J001_part010 : IntSourceTree :=
  (.node 297 (sourceLit (List.headD (raw_ints% [129740563510973564146466047432425]) 0) 39 true) (.node 293 (sourceLit (List.headD (raw_ints% [3806570924798347123709059137444075]) 0) 35 true) (.node 291 (sourceLit (List.headD (raw_ints% [12531968660495260830505820665872375]) 0) 34 true) (.node 290 (sourceLit (List.headD (raw_ints% [2235827207000591756642471055085125]) 0) 37 true) .empty .empty) (.node 292 (sourceLit (List.headD (raw_ints% [1189407678621030700071536233305225]) 0) 37 true) .empty .empty)) (.node 295 (sourceLit (List.headD (raw_ints% [2694402844420007913787603790656875]) 0) 35 true) (.node 294 (sourceLit (List.headD (raw_ints% [789880871241849304552882419481725]) 0) 37 true) .empty .empty) (.node 296 (sourceLit (List.headD (raw_ints% [586451967193542344216678503639875]) 0) 37 true) .empty .empty))) (.node 334 (sourceLit (List.headD (raw_ints% [45758425761280650040566530138677125]) 0) 32 true) (.node 332 (sourceLit (List.headD (raw_ints% [39825237913290671312941134873983775]) 0) 33 true) (.node 331 (sourceLit (List.headD (raw_ints% [29489990078063656932874583061115125]) 0) 34 true) .empty .empty) (.node 333 (sourceLit (List.headD (raw_ints% [14666602738257691227757007471240325]) 0) 34 true) .empty .empty)) (.node 336 (sourceLit (List.headD (raw_ints% [15555136607710202160845841878420625]) 0) 33 true) (.node 335 (sourceLit (List.headD (raw_ints% [9291690236499450216886451845446975]) 0) 34 true) .empty .empty) .empty)))

#time def treeT_J001_part011 : IntSourceTree :=
  (.node 414 (sourceLit (List.headD (raw_ints% [211938342748271166483617602654087875]) 0) 32 true) (.node 375 (sourceLit (List.headD (raw_ints% [34980814383600618385416114976049625]) 0) 33 true) (.node 373 (sourceLit (List.headD (raw_ints% [32212096063693977065523016599095625]) 0) 34 true) (.node 372 (sourceLit (List.headD (raw_ints% [24732359363579534132588438127894225]) 0) 35 true) .empty .empty) (.node 374 (sourceLit (List.headD (raw_ints% [11507079253290294009545477793313425]) 0) 35 true) .empty .empty)) (.node 377 (sourceLit (List.headD (raw_ints% [11403438575359048108158928360583025]) 0) 34 true) (.node 376 (sourceLit (List.headD (raw_ints% [6945882367725280840019737830887475]) 0) 35 true) .empty .empty) (.node 413 (sourceLit (List.headD (raw_ints% [84262834716060445302596745040336575]) 0) 34 true) .empty .empty))) (.node 455 (sourceLit (List.headD (raw_ints% [88478764182335274049100743839019125]) 0) 34 true) (.node 416 (sourceLit (List.headD (raw_ints% [54406492159491034609986388073678625]) 0) 33 true) (.node 415 (sourceLit (List.headD (raw_ints% [36736626776661725821295459327806725]) 0) 34 true) .empty .empty) (.node 417 (sourceLit (List.headD (raw_ints% [42242014960860950747906135049065025]) 0) 33 true) .empty .empty)) (.node 457 (sourceLit (List.headD (raw_ints% [2687690849008249156364216232068475]) 0) 38 true) (.node 456 (sourceLit (List.headD (raw_ints% [14895372204468222490637860748459625]) 0) 36 true) .empty .empty) .empty)))

#time def treeT_J001_part012 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [13325043980941295972251767598034775]) 0) 33 true) treeT_J001_part010 treeT_J001_part011)

#time def treeT_J001_part013 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [3241557333992559543144833345070375]) 0) 40 false) treeT_J001_part009 treeT_J001_part012)

#time def treeT_J001_part014 : IntSourceTree :=
  (.node 168 (sourceLit (List.headD (raw_ints% [3466498115533555000909530578433375]) 0) 34 true) treeT_J001_part006 treeT_J001_part013)

#time def treeT_J001 : IntSourceTree := treeT_J001_part014

#time def treeG_J006_part000 : IntSourceTree :=
  (.node 5 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 42 false) (.node 3 (sourceLit (List.headD (raw_ints% [13538102592745096995097518674625]) 0) 40 false) (.node 2 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 37 false) (.node 1 (sourceLit (List.headD (raw_ints% [31033496712600299265685081269525]) 0) 39 false) .empty .empty) .empty) (.node 4 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 39 true) .empty .empty)) (.node 8 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 43 false) (.node 7 (sourceLit (List.headD (raw_ints% [62275271926627446177448585903275]) 0) 39 true) (.node 6 (sourceLit (List.headD (raw_ints% [17703672621282049916665985959125]) 0) 40 true) .empty .empty) .empty) (.node 9 (sourceLit (List.headD (raw_ints% [40852340351294545437953611297275]) 0) 38 true) .empty .empty)))

#time def treeG_J006_part001 : IntSourceTree :=
  (.node 15 (sourceLit (List.headD (raw_ints% [406680246278373867235169113004625]) 0) 32 true) (.node 13 (sourceLit (List.headD (raw_ints% [94622455983725221721645627526375]) 0) 35 true) (.node 12 (sourceLit (List.headD (raw_ints% [155983466436556895115009705675]) 0) 46 false) (.node 11 (sourceLit (List.headD (raw_ints% [84471809364402923888091990147825]) 0) 36 true) .empty .empty) .empty) (.node 14 (sourceLit (List.headD (raw_ints% [75767361229775174804324412075]) 0) 47 false) .empty .empty)) (.node 18 (sourceLit (List.headD (raw_ints% [2252992490449523311930754625]) 0) 52 false) (.node 17 (sourceLit (List.headD (raw_ints% [350213537860236951697554652419525]) 0) 31 true) (.node 16 (sourceLit (List.headD (raw_ints% [4613879239701665978014960275]) 0) 51 false) .empty .empty) .empty) (.node 19 (sourceLit (List.headD (raw_ints% [86278170771187225006328624396925]) 0) 29 true) .empty .empty)))

#time def treeG_J006_part002 : IntSourceTree :=
  (.node 10 (sourceLit (List.headD (raw_ints% [644671552035480809290358032125]) 0) 44 false) treeG_J006_part000 treeG_J006_part001)

#time def treeG_J006_part003 : IntSourceTree :=
  (.node 25 (sourceLit (List.headD (raw_ints% [143680357171804695668167672099830375]) 0) 23 false) (.node 23 (sourceLit (List.headD (raw_ints% [52715103471855659476736448613491375]) 0) 24 false) (.node 22 (sourceLit (List.headD (raw_ints% [270081977364366833933912925]) 0) 55 false) (.node 21 (sourceLit (List.headD (raw_ints% [1785130292618405868921301741507425]) 0) 28 false) .empty .empty) .empty) (.node 24 (sourceLit (List.headD (raw_ints% [33133555503878600942843175]) 0) 58 false) .empty .empty)) (.node 28 (sourceLit (List.headD (raw_ints% [4003000377994299853458675]) 0) 61 false) (.node 27 (sourceLit (List.headD (raw_ints% [698420476174341126704089092207497505]) 0) 21 false) (.node 26 (sourceLit (List.headD (raw_ints% [16278584956671822715928025]) 0) 59 false) .empty .empty) .empty) (.node 29 (sourceLit (List.headD (raw_ints% [1600237952289638808373890650371329855]) 0) 20 false) .empty .empty)))

#time def treeG_J006_part004 : IntSourceTree :=
  (.node 35 (sourceLit (List.headD (raw_ints% [130201792387435034595782123058974608875]) 0) 14 false) (.node 33 (sourceLit (List.headD (raw_ints% [30603437749586808440870588043447684375]) 0) 16 false) (.node 32 (sourceLit (List.headD (raw_ints% [60674946022260387557091]) 0) 67 false) (.node 31 (sourceLit (List.headD (raw_ints% [14158193250650361219996470482648265955]) 0) 17 false) .empty .empty) .empty) (.node 34 (sourceLit (List.headD (raw_ints% [29913876835092532582729]) 0) 68 false) .empty .empty)) (.node 37 (sourceLit (List.headD (raw_ints% [273773528018289433247669784307548873585]) 0) 13 false) (.node 36 (sourceLit (List.headD (raw_ints% [7378869973193727965957]) 0) 70 false) .empty .empty) (.node 38 (sourceLit (List.headD (raw_ints% [3642453774985166446305]) 0) 71 false) .empty .empty)))

#time def treeG_J006_part005 : IntSourceTree :=
  (.node 30 (sourceLit (List.headD (raw_ints% [1970522166032201229468075]) 0) 62 false) treeG_J006_part003 treeG_J006_part004)

#time def treeG_J006_part006 : IntSourceTree :=
  (.node 20 (sourceLit (List.headD (raw_ints% [551139341455816794393881625]) 0) 54 false) treeG_J006_part002 treeG_J006_part005)

#time def treeG_J006_part007 : IntSourceTree :=
  (.node 46 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 43 false) (.node 44 (sourceLit (List.headD (raw_ints% [13538102592745096995097518674625]) 0) 41 false) (.node 43 (sourceLit (List.headD (raw_ints% [15620887607013573455881752316875]) 0) 38 false) (.node 42 (sourceLit (List.headD (raw_ints% [31033496712600299265685081269525]) 0) 40 false) .empty .empty) .empty) (.node 45 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 40 true) .empty .empty)) (.node 49 (sourceLit (List.headD (raw_ints% [1338933223458306296218435912875]) 0) 44 false) (.node 48 (sourceLit (List.headD (raw_ints% [62275271926627446177448585903275]) 0) 40 true) (.node 47 (sourceLit (List.headD (raw_ints% [17703672621282049916665985959125]) 0) 41 true) .empty .empty) .empty) (.node 50 (sourceLit (List.headD (raw_ints% [40852340351294545437953611297275]) 0) 39 true) .empty .empty)))

#time def treeG_J006_part008 : IntSourceTree :=
  (.node 56 (sourceLit (List.headD (raw_ints% [406680246278373867235169113004625]) 0) 33 true) (.node 54 (sourceLit (List.headD (raw_ints% [94622455983725221721645627526375]) 0) 36 true) (.node 53 (sourceLit (List.headD (raw_ints% [155983466436556895115009705675]) 0) 47 false) (.node 52 (sourceLit (List.headD (raw_ints% [84471809364402923888091990147825]) 0) 37 true) .empty .empty) .empty) (.node 55 (sourceLit (List.headD (raw_ints% [75767361229775174804324412075]) 0) 48 false) .empty .empty)) (.node 58 (sourceLit (List.headD (raw_ints% [350213537860236951697554652419525]) 0) 32 true) (.node 57 (sourceLit (List.headD (raw_ints% [4613879239701665978014960275]) 0) 52 false) .empty .empty) (.node 59 (sourceLit (List.headD (raw_ints% [2252992490449523311930754625]) 0) 53 false) .empty .empty)))

#time def treeG_J006_part009 : IntSourceTree :=
  (.node 51 (sourceLit (List.headD (raw_ints% [644671552035480809290358032125]) 0) 45 false) treeG_J006_part007 treeG_J006_part008)

#time def treeG_J006_part010 : IntSourceTree :=
  (.node 65 (sourceLit (List.headD (raw_ints% [33133555503878600942843175]) 0) 59 false) (.node 63 (sourceLit (List.headD (raw_ints% [270081977364366833933912925]) 0) 56 false) (.node 62 (sourceLit (List.headD (raw_ints% [1785130292618405868921301741507425]) 0) 29 false) (.node 61 (sourceLit (List.headD (raw_ints% [551139341455816794393881625]) 0) 55 false) .empty .empty) .empty) (.node 64 (sourceLit (List.headD (raw_ints% [52715103471855659476736448613491375]) 0) 25 false) .empty .empty)) (.node 68 (sourceLit (List.headD (raw_ints% [698420476174341126704089092207497505]) 0) 22 false) (.node 67 (sourceLit (List.headD (raw_ints% [16278584956671822715928025]) 0) 60 false) (.node 66 (sourceLit (List.headD (raw_ints% [143680357171804695668167672099830375]) 0) 24 false) .empty .empty) .empty) (.node 69 (sourceLit (List.headD (raw_ints% [4003000377994299853458675]) 0) 62 false) .empty .empty)))

#time def treeG_J006_part011 : IntSourceTree :=
  (.node 75 (sourceLit (List.headD (raw_ints% [29913876835092532582729]) 0) 69 false) (.node 73 (sourceLit (List.headD (raw_ints% [60674946022260387557091]) 0) 68 false) (.node 72 (sourceLit (List.headD (raw_ints% [14158193250650361219996470482648265955]) 0) 18 false) (.node 71 (sourceLit (List.headD (raw_ints% [1970522166032201229468075]) 0) 63 false) .empty .empty) .empty) (.node 74 (sourceLit (List.headD (raw_ints% [30603437749586808440870588043447684375]) 0) 17 false) .empty .empty)) (.node 77 (sourceLit (List.headD (raw_ints% [7378869973193727965957]) 0) 71 false) (.node 76 (sourceLit (List.headD (raw_ints% [130201792387435034595782123058974608875]) 0) 15 false) .empty .empty) (.node 78 (sourceLit (List.headD (raw_ints% [273773528018289433247669784307548873585]) 0) 14 false) .empty .empty)))

#time def treeG_J006_part012 : IntSourceTree :=
  (.node 70 (sourceLit (List.headD (raw_ints% [1600237952289638808373890650371329855]) 0) 21 false) treeG_J006_part010 treeG_J006_part011)

#time def treeG_J006_part013 : IntSourceTree :=
  (.node 60 (sourceLit (List.headD (raw_ints% [86278170771187225006328624396925]) 0) 30 true) treeG_J006_part009 treeG_J006_part012)

#time def treeG_J006_part014 : IntSourceTree :=
  (.node 39 (sourceLit (List.headD (raw_ints% [9130602821399086908285609100156009679535]) 0) 8 false) treeG_J006_part006 treeG_J006_part013)

#time def treeG_J006_part015 : IntSourceTree :=
  (.node 87 (sourceLit (List.headD (raw_ints% [162248952611514316295091800731275]) 0) 39 false) (.node 85 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 43 false) (.node 84 (sourceLit (List.headD (raw_ints% [5206962535671191151960584105625]) 0) 41 false) (.node 83 (sourceLit (List.headD (raw_ints% [48528890832455501536272643864425]) 0) 40 false) .empty .empty) .empty) (.node 86 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 40 false) .empty .empty)) (.node 90 (sourceLit (List.headD (raw_ints% [2033194894881131783146513793625]) 0) 44 false) (.node 89 (sourceLit (List.headD (raw_ints% [457349835061725023981635075928925]) 0) 38 true) (.node 88 (sourceLit (List.headD (raw_ints% [20381539068198662509102857784875]) 0) 42 true) .empty .empty) .empty) (.node 91 (sourceLit (List.headD (raw_ints% [569165636256309803119165790608575]) 0) 36 true) .empty .empty)))

#time def treeG_J006_part016 : IntSourceTree :=
  (.node 97 (sourceLit (List.headD (raw_ints% [2903228432366753986183798251617475]) 0) 31 true) (.node 95 (sourceLit (List.headD (raw_ints% [2621238345200833227857490967839375]) 0) 32 true) (.node 94 (sourceLit (List.headD (raw_ints% [236199571643338615425694999275]) 0) 47 false) (.node 93 (sourceLit (List.headD (raw_ints% [581152018931498169383090293656225]) 0) 35 true) .empty .empty) .empty) (.node 96 (sourceLit (List.headD (raw_ints% [57311844270968510892264570975]) 0) 49 false) .empty .empty)) (.node 99 (sourceLit (List.headD (raw_ints% [5517138434992604002154545814315475]) 0) 29 true) (.node 98 (sourceLit (List.headD (raw_ints% [6974765988953808644099165925]) 0) 52 false) .empty .empty) (.node 100 (sourceLit (List.headD (raw_ints% [212731643624213314692109125]) 0) 57 false) .empty .empty)))

#time def treeG_J006_part017 : IntSourceTree :=
  (.node 92 (sourceLit (List.headD (raw_ints% [244344042799461957087674163225]) 0) 47 false) treeG_J006_part015 treeG_J006_part016)

#time def treeG_J006_part018 : IntSourceTree :=
  (.node 106 (sourceLit (List.headD (raw_ints% [49988526051085379169758325]) 0) 59 false) (.node 104 (sourceLit (List.headD (raw_ints% [203814866356609632048226575]) 0) 57 false) (.node 103 (sourceLit (List.headD (raw_ints% [61533235255722316134226862842983825]) 0) 24 false) (.node 102 (sourceLit (List.headD (raw_ints% [832196705547266754853850325]) 0) 55 false) .empty .empty) .empty) (.node 105 (sourceLit (List.headD (raw_ints% [278040470603040580145723916808100625]) 0) 23 false) .empty .empty)) (.node 109 (sourceLit (List.headD (raw_ints% [3987125857105090205258822087288650185]) 0) 20 false) (.node 108 (sourceLit (List.headD (raw_ints% [6137792289338761431234675]) 0) 62 false) (.node 107 (sourceLit (List.headD (raw_ints% [1600465238574534003986593661389788495]) 0) 21 false) .empty .empty) .empty) (.node 110 (sourceLit (List.headD (raw_ints% [6035478589956398477449275]) 0) 62 false) .empty .empty)))

#time def treeG_J006_part019 : IntSourceTree :=
  (.node 116 (sourceLit (List.headD (raw_ints% [5633751715474701154193]) 0) 72 false) (.node 114 (sourceLit (List.headD (raw_ints% [91436015209428242531453]) 0) 68 false) (.node 113 (sourceLit (List.headD (raw_ints% [82662108255616081319101175817738443265]) 0) 16 false) (.node 112 (sourceLit (List.headD (raw_ints% [1485122597854118129011347]) 0) 64 false) .empty .empty) .empty) (.node 115 (sourceLit (List.headD (raw_ints% [359453211605953900458147285636188341125]) 0) 14 false) .empty .empty)) (.node 118 (sourceLit (List.headD (raw_ints% [11115286171402289485609]) 0) 71 false) (.node 117 (sourceLit (List.headD (raw_ints% [767840811081190843518587200164247997415]) 0) 13 false) .empty .empty) (.node 119 (sourceLit (List.headD (raw_ints% [25912408764941960547416123291210246139345]) 0) 8 false) .empty .empty)))

#time def treeG_J006_part020 : IntSourceTree :=
  (.node 111 (sourceLit (List.headD (raw_ints% [37049421222618080647968030329234289405]) 0) 17 false) treeG_J006_part018 treeG_J006_part019)

#time def treeG_J006_part021 : IntSourceTree :=
  (.node 101 (sourceLit (List.headD (raw_ints% [2475355658787903668971930736682825]) 0) 28 true) treeG_J006_part017 treeG_J006_part020)

#time def treeG_J006_part022 : IntSourceTree :=
  (.node 129 (sourceLit (List.headD (raw_ints% [23059405515115275101539729610625]) 0) 43 true) (.node 127 (sourceLit (List.headD (raw_ints% [3124177521402714691176350463375]) 0) 44 false) (.node 126 (sourceLit (List.headD (raw_ints% [7289747549939667612744817747875]) 0) 43 false) (.node 125 (sourceLit (List.headD (raw_ints% [26034812678355955759802920528125]) 0) 40 false) .empty .empty) .empty) (.node 128 (sourceLit (List.headD (raw_ints% [112262112269070881236270193317275]) 0) 41 false) .empty .empty)) (.node 132 (sourceLit (List.headD (raw_ints% [242346913445953439615536900230375]) 0) 38 true) (.node 131 (sourceLit (List.headD (raw_ints% [347130835711412743464038940375]) 0) 47 false) (.node 130 (sourceLit (List.headD (raw_ints% [208248747355215239271840732315825]) 0) 40 true) .empty .empty) .empty) (.node 133 (sourceLit (List.headD (raw_ints% [332704619162367019060338620775]) 0) 47 false) .empty .empty)))

#time def treeG_J006_part023 : IntSourceTree :=
  (.node 139 (sourceLit (List.headD (raw_ints% [1180443374626071333042102825]) 0) 55 false) (.node 137 (sourceLit (List.headD (raw_ints% [38856327312161846980204729875]) 0) 50 false) (.node 136 (sourceLit (List.headD (raw_ints% [1107279049461229680311160927417375]) 0) 34 true) (.node 135 (sourceLit (List.headD (raw_ints% [2506753287711928759708915425]) 0) 54 false) .empty .empty) .empty) (.node 138 (sourceLit (List.headD (raw_ints% [1276507447253258517243121799598975]) 0) 33 true) .empty .empty)) (.node 141 (sourceLit (List.headD (raw_ints% [1150713807537889723142991375]) 0) 55 false) (.node 140 (sourceLit (List.headD (raw_ints% [2715430132110708388574108594959275]) 0) 31 true) .empty .empty) (.node 142 (sourceLit (List.headD (raw_ints% [2130242975703154768946616239095125]) 0) 30 true) .empty .empty)))

#time def treeG_J006_part024 : IntSourceTree :=
  (.node 134 (sourceLit (List.headD (raw_ints% [243264781473886473830722333064925]) 0) 37 true) treeG_J006_part022 treeG_J006_part023)

#time def treeG_J006_part025 : IntSourceTree :=
  (.node 148 (sourceLit (List.headD (raw_ints% [451022381200096438641252284591145495]) 0) 23 false) (.node 146 (sourceLit (List.headD (raw_ints% [67180056715617942238778122354135125]) 0) 25 false) (.node 145 (sourceLit (List.headD (raw_ints% [137547755348852430162540225]) 0) 58 false) (.node 144 (sourceLit (List.headD (raw_ints% [4409065891933328328745207114746225]) 0) 26 false) .empty .empty) .empty) (.node 147 (sourceLit (List.headD (raw_ints% [8427485273603389113457575]) 0) 62 false) .empty .empty)) (.node 151 (sourceLit (List.headD (raw_ints% [254059776495262327998825]) 0) 67 false) (.node 150 (sourceLit (List.headD (raw_ints% [1193443952407725698442465718458660165]) 0) 22 false) (.node 149 (sourceLit (List.headD (raw_ints% [8272584200683223009010675]) 0) 62 false) .empty .empty) .empty) (.node 152 (sourceLit (List.headD (raw_ints% [11445613985983859713985779923293011725]) 0) 19 false) .empty .empty)))

#time def treeG_J006_part026 : IntSourceTree :=
  (.node 158 (sourceLit (List.headD (raw_ints% [247033641531450705135458707928349561915]) 0) 15 false) (.node 156 (sourceLit (List.headD (raw_ints% [114625709609259432931182581288606866125]) 0) 16 false) (.node 155 (sourceLit (List.headD (raw_ints% [15380534593583927487181]) 0) 71 false) (.node 154 (sourceLit (List.headD (raw_ints% [26029335253014636439115293887145379445]) 0) 18 false) .empty .empty) .empty) (.node 157 (sourceLit (List.headD (raw_ints% [15156136888705076650815]) 0) 71 false) .empty .empty)) (.node 165 (sourceLit (List.headD (raw_ints% [12288431584184011118626978489275]) 0) 43 false) (.node 159 (sourceLit (List.headD (raw_ints% [934104049552140379913]) 0) 75 false) .empty .empty) (.node 166 (sourceLit (List.headD (raw_ints% [44779877806772243906861023308375]) 0) 40 false) .empty .empty)))

#time def treeG_J006_part027 : IntSourceTree :=
  (.node 153 (sourceLit (List.headD (raw_ints% [999723029676035028554619]) 0) 65 false) treeG_J006_part025 treeG_J006_part026)

#time def treeG_J006_part028 : IntSourceTree :=
  (.node 143 (sourceLit (List.headD (raw_ints% [70264341022862490114992175]) 0) 59 false) treeG_J006_part024 treeG_J006_part027)

#time def treeG_J006_part029 : IntSourceTree :=
  (.node 124 (sourceLit (List.headD (raw_ints% [4373848529963800567646890648725]) 0) 44 false) treeG_J006_part021 treeG_J006_part028)

#time def treeG_J006_part030 : IntSourceTree :=
  (.node 79 (sourceLit (List.headD (raw_ints% [3642453774985166446305]) 0) 72 false) treeG_J006_part014 treeG_J006_part029)

#time def treeG_J006_part031 : IntSourceTree :=
  (.node 172 (sourceLit (List.headD (raw_ints% [449917628623363529840403717525]) 0) 47 false) (.node 170 (sourceLit (List.headD (raw_ints% [12546300204998203442343121702125]) 0) 45 true) (.node 169 (sourceLit (List.headD (raw_ints% [2253543631366859123761958169005325]) 0) 38 false) (.node 168 (sourceLit (List.headD (raw_ints% [45374959239420380038513661491875]) 0) 42 false) .empty .empty) .empty) (.node 171 (sourceLit (List.headD (raw_ints% [6094794279110577853579737643497825]) 0) 36 true) .empty .empty)) (.node 175 (sourceLit (List.headD (raw_ints% [12947707669127901097308738348315825]) 0) 32 true) (.node 174 (sourceLit (List.headD (raw_ints% [429209666681395422694982242275]) 0) 47 false) (.node 173 (sourceLit (List.headD (raw_ints% [3296398596203756864465500110029775]) 0) 35 true) .empty .empty) .empty) (.node 176 (sourceLit (List.headD (raw_ints% [103120366142594929729106016225]) 0) 49 false) .empty .empty)))

#time def treeG_J006_part032 : IntSourceTree :=
  (.node 182 (sourceLit (List.headD (raw_ints% [1469230909528512691432132425]) 0) 55 false) (.node 180 (sourceLit (List.headD (raw_ints% [754980087377644703657884575]) 0) 56 false) (.node 179 (sourceLit (List.headD (raw_ints% [35331099877111668549625351772851725]) 0) 29 true) (.node 178 (sourceLit (List.headD (raw_ints% [24906795334254229692006398025]) 0) 51 false) .empty .empty) .empty) (.node 181 (sourceLit (List.headD (raw_ints% [40971526454983430548213806782665575]) 0) 28 true) .empty .empty)) (.node 185 (sourceLit (List.headD (raw_ints% [207495416332107326885800602972161025]) 0) 23 true) (.node 184 (sourceLit (List.headD (raw_ints% [358299861826290288871710825]) 0) 57 false) (.node 183 (sourceLit (List.headD (raw_ints% [334204336145726126559393741447159825]) 0) 24 true) .empty .empty) .empty) (.node 186 (sourceLit (List.headD (raw_ints% [21889807324441762748195475]) 0) 61 false) .empty .empty)))

#time def treeG_J006_part033 : IntSourceTree :=
  (.node 177 (sourceLit (List.headD (raw_ints% [14813236359012920898794776587060525]) 0) 31 true) treeG_J006_part031 treeG_J006_part032)

#time def treeG_J006_part034 : IntSourceTree :=
  (.node 192 (sourceLit (List.headD (raw_ints% [2579833826070079118969853]) 0) 64 false) (.node 190 (sourceLit (List.headD (raw_ints% [10509689811410047540572075]) 0) 62 false) (.node 189 (sourceLit (List.headD (raw_ints% [3229232242096452813001214466169677735]) 0) 20 false) (.node 188 (sourceLit (List.headD (raw_ints% [10717178257868016795680475]) 0) 62 false) .empty .empty) .empty) (.node 191 (sourceLit (List.headD (raw_ints% [39330991731476364052349775652119961155]) 0) 17 false) .empty .empty)) (.node 195 (sourceLit (List.headD (raw_ints% [473485516490514465593542118752463801115]) 0) 14 false) (.node 194 (sourceLit (List.headD (raw_ints% [633978968838322058428807]) 0) 66 false) (.node 193 (sourceLit (List.headD (raw_ints% [100467715520125674104671302954949744335]) 0) 16 false) .empty .empty) .empty) (.node 196 (sourceLit (List.headD (raw_ints% [2436695719527306583247]) 0) 74 false) .empty .empty)))

#time def treeG_J006_part035 : IntSourceTree :=
  (.node 208 (sourceLit (List.headD (raw_ints% [153501255551586715159798019433825]) 0) 40 true) (.node 206 (sourceLit (List.headD (raw_ints% [17287115618428354624509139230675]) 0) 43 false) (.node 199 (sourceLit (List.headD (raw_ints% [37328203467109419967261305938447241710895]) 0) 8 false) (.node 198 (sourceLit (List.headD (raw_ints% [19196987606007863816021]) 0) 71 false) .empty .empty) .empty) (.node 207 (sourceLit (List.headD (raw_ints% [19786457635550526377450219601375]) 0) 41 false) .empty .empty)) (.node 210 (sourceLit (List.headD (raw_ints% [2670041126077289602305639633636975]) 0) 39 false) (.node 209 (sourceLit (List.headD (raw_ints% [17108591188633913785013347775625]) 0) 45 false) .empty .empty) (.node 211 (sourceLit (List.headD (raw_ints% [13240561876421028929271199582875]) 0) 46 true) .empty .empty)))

#time def treeG_J006_part036 : IntSourceTree :=
  (.node 197 (sourceLit (List.headD (raw_ints% [1066170542666960083380334100453461860585]) 0) 13 false) treeG_J006_part034 treeG_J006_part035)

#time def treeG_J006_part037 : IntSourceTree :=
  (.node 187 (sourceLit (List.headD (raw_ints% [549296576325240147654306253942535505]) 0) 21 false) treeG_J006_part033 treeG_J006_part036)

#time def treeG_J006_part038 : IntSourceTree :=
  (.node 217 (sourceLit (List.headD (raw_ints% [32132019415216541374450643175]) 0) 51 false) (.node 215 (sourceLit (List.headD (raw_ints% [268777456267831982073611655075]) 0) 48 false) (.node 214 (sourceLit (List.headD (raw_ints% [2809869033255983916804055443899925]) 0) 36 true) (.node 213 (sourceLit (List.headD (raw_ints% [567130638084360040620468814275]) 0) 47 false) .empty .empty) .empty) (.node 216 (sourceLit (List.headD (raw_ints% [10733149570205441736686416493481075]) 0) 33 true) .empty .empty)) (.node 220 (sourceLit (List.headD (raw_ints% [29900239612890251772477134582933175]) 0) 30 true) (.node 219 (sourceLit (List.headD (raw_ints% [15463248337245659027669575425]) 0) 52 false) (.node 218 (sourceLit (List.headD (raw_ints% [12260221464506403864308532987862575]) 0) 32 true) .empty .empty) .empty) (.node 221 (sourceLit (List.headD (raw_ints% [1869206541972689091488546925]) 0) 55 false) .empty .empty)))

#time def treeG_J006_part039 : IntSourceTree :=
  (.node 227 (sourceLit (List.headD (raw_ints% [3365580512709593408684475]) 0) 64 false) (.node 225 (sourceLit (List.headD (raw_ints% [27594013309679732338646325]) 0) 61 false) (.node 224 (sourceLit (List.headD (raw_ints% [343022467929592783216884155676652275]) 0) 25 true) (.node 223 (sourceLit (List.headD (raw_ints% [907116181345612770512195025]) 0) 56 false) .empty .empty) .empty) (.node 226 (sourceLit (List.headD (raw_ints% [341855529763343211363356847680431275]) 0) 24 true) .empty .empty)) (.node 229 (sourceLit (List.headD (raw_ints% [13161772315052810582350275]) 0) 62 false) (.node 228 (sourceLit (List.headD (raw_ints% [352748186074952729628198315239755485]) 0) 22 true) .empty .empty) (.node 230 (sourceLit (List.headD (raw_ints% [842344337281001416116283029252357405]) 0) 21 false) .empty .empty)))

#time def treeG_J006_part040 : IntSourceTree :=
  (.node 222 (sourceLit (List.headD (raw_ints% [36711040503577121010320574304475325]) 0) 29 true) treeG_J006_part038 treeG_J006_part039)

#time def treeG_J006_part041 : IntSourceTree :=
  (.node 236 (sourceLit (List.headD (raw_ints% [244234097271995599731176956175250068865]) 0) 15 false) (.node 234 (sourceLit (List.headD (raw_ints% [48409045014096401226440715180658985445]) 0) 17 false) (.node 233 (sourceLit (List.headD (raw_ints% [790055398197022045207617]) 0) 66 false) (.node 232 (sourceLit (List.headD (raw_ints% [16439763759508644624378215805533937705]) 0) 18 false) .empty .empty) .empty) (.node 235 (sourceLit (List.headD (raw_ints% [387890415340979218633911]) 0) 67 false) .empty .empty)) (.node 239 (sourceLit (List.headD (raw_ints% [11724155209590740776717]) 0) 72 false) (.node 238 (sourceLit (List.headD (raw_ints% [572103259604058673109416684596762736755]) 0) 14 false) (.node 237 (sourceLit (List.headD (raw_ints% [23830994623731828681137]) 0) 71 false) .empty .empty) .empty) (.node 247 (sourceLit (List.headD (raw_ints% [482164730803152300671550088180875]) 0) 39 false) .empty .empty)))

#time def treeG_J006_part042 : IntSourceTree :=
  (.node 253 (sourceLit (List.headD (raw_ints% [41584405021545610930323810634266825]) 0) 35 true) (.node 251 (sourceLit (List.headD (raw_ints% [48815452296347211490469971781689425]) 0) 36 false) (.node 250 (sourceLit (List.headD (raw_ints% [46763482582266031012369817253375]) 0) 45 false) (.node 249 (sourceLit (List.headD (raw_ints% [3481553675779552845040342324475925]) 0) 38 true) .empty .empty) .empty) (.node 252 (sourceLit (List.headD (raw_ints% [855654969065274528694475206275]) 0) 51 true) .empty .empty)) (.node 255 (sourceLit (List.headD (raw_ints% [76968101395063584240421035856481775]) 0) 32 true) (.node 254 (sourceLit (List.headD (raw_ints% [705051609487324658545955386275]) 0) 47 false) .empty .empty) (.node 256 (sourceLit (List.headD (raw_ints% [82828545062618526172252819425]) 0) 50 false) .empty .empty)))

#time def treeG_J006_part043 : IntSourceTree :=
  (.node 248 (sourceLit (List.headD (raw_ints% [6397125400967463415265860472625]) 0) 44 true) treeG_J006_part041 treeG_J006_part042)

#time def treeG_J006_part044 : IntSourceTree :=
  (.node 231 (sourceLit (List.headD (raw_ints% [6444733387485850292590875]) 0) 63 false) treeG_J006_part040 treeG_J006_part043)

#time def treeG_J006_part045 : IntSourceTree :=
  (.node 212 (sourceLit (List.headD (raw_ints% [5610100452218670974348663843037075]) 0) 37 true) treeG_J006_part037 treeG_J006_part044)

#time def treeG_J006_part046 : IntSourceTree :=
  (.node 262 (sourceLit (List.headD (raw_ints% [2269182174416865491544961425]) 0) 55 false) (.node 260 (sourceLit (List.headD (raw_ints% [9423407638224501398406498825]) 0) 53 false) (.node 259 (sourceLit (List.headD (raw_ints% [160832443554990793279311176032949475]) 0) 29 true) (.node 258 (sourceLit (List.headD (raw_ints% [39357243496178853056894888325]) 0) 51 false) .empty .empty) .empty) (.node 261 (sourceLit (List.headD (raw_ints% [198230390448138583631603269880799825]) 0) 28 true) .empty .empty)) (.node 265 (sourceLit (List.headD (raw_ints% [2536684327104634938849272642441057175]) 0) 23 true) (.node 264 (sourceLit (List.headD (raw_ints% [68602039939915310205060525]) 0) 60 false) (.node 263 (sourceLit (List.headD (raw_ints% [2015302256083209618101123014039260975]) 0) 24 true) .empty .empty) .empty) (.node 266 (sourceLit (List.headD (raw_ints% [33298219294917701929097175]) 0) 61 false) .empty .empty)))

#time def treeG_J006_part047 : IntSourceTree :=
  (.node 272 (sourceLit (List.headD (raw_ints% [1932449780707885586810511]) 0) 65 false) (.node 270 (sourceLit (List.headD (raw_ints% [15813854818695573624128475]) 0) 62 false) (.node 269 (sourceLit (List.headD (raw_ints% [6051217730696074650026800988087721615]) 0) 20 true) (.node 268 (sourceLit (List.headD (raw_ints% [16207465843808730473795325]) 0) 62 false) .empty .empty) .empty) (.node 271 (sourceLit (List.headD (raw_ints% [12375972938484318736628718716044524195]) 0) 17 true) .empty .empty)) (.node 274 (sourceLit (List.headD (raw_ints% [946131827555722031986427]) 0) 66 false) (.node 273 (sourceLit (List.headD (raw_ints% [31050394555943482890354423489321757305]) 0) 16 false) .empty .empty) (.node 275 (sourceLit (List.headD (raw_ints% [301059203735027954029509324138079966005]) 0) 14 false) .empty .empty)))

#time def treeG_J006_part048 : IntSourceTree :=
  (.node 267 (sourceLit (List.headD (raw_ints% [6018985052538731529468015816829435905]) 0) 21 true) treeG_J006_part046 treeG_J006_part047)

#time def treeG_J006_part049 : IntSourceTree :=
  (.node 289 (sourceLit (List.headD (raw_ints% [11752858294800688600139604124125]) 0) 46 true) (.node 279 (sourceLit (List.headD (raw_ints% [35901013762210090190744029689938388593745]) 0) 8 false) (.node 278 (sourceLit (List.headD (raw_ints% [28465001641455793546253]) 0) 71 false) (.node 277 (sourceLit (List.headD (raw_ints% [887702235509004714469081548948538690335]) 0) 13 false) .empty .empty) .empty) (.node 288 (sourceLit (List.headD (raw_ints% [158916496588684753957837026903675]) 0) 42 false) .empty .empty)) (.node 292 (sourceLit (List.headD (raw_ints% [13606388187141470616204658906181625]) 0) 39 false) (.node 291 (sourceLit (List.headD (raw_ints% [30002022229343529970820508418125]) 0) 47 false) (.node 290 (sourceLit (List.headD (raw_ints% [1537898700464210611836495489528225]) 0) 41 true) .empty .empty) .empty) (.node 293 (sourceLit (List.headD (raw_ints% [27948089648173144958843675415075]) 0) 47 true) .empty .empty)))

#time def treeG_J006_part050 : IntSourceTree :=
  (.node 299 (sourceLit (List.headD (raw_ints% [5973498789733298507306328225]) 0) 54 false) (.node 297 (sourceLit (List.headD (raw_ints% [25348262823700992398901088125]) 0) 52 false) (.node 296 (sourceLit (List.headD (raw_ints% [16558737956214535625933654840750175]) 0) 35 true) (.node 295 (sourceLit (List.headD (raw_ints% [426048977753410816867523175]) 0) 58 false) .empty .empty) .empty) (.node 298 (sourceLit (List.headD (raw_ints% [14697934684531052282597005593231375]) 0) 34 true) .empty .empty)) (.node 301 (sourceLit (List.headD (raw_ints% [5684994554279123215429404975]) 0) 54 false) (.node 300 (sourceLit (List.headD (raw_ints% [32733050985525135376708510362504075]) 0) 32 true) .empty .empty) (.node 302 (sourceLit (List.headD (raw_ints% [40379837486140365655320673894081125]) 0) 31 true) .empty .empty)))

#time def treeG_J006_part051 : IntSourceTree :=
  (.node 294 (sourceLit (List.headD (raw_ints% [9693633997072406753379938797591725]) 0) 38 true) treeG_J006_part049 treeG_J006_part050)

#time def treeG_J006_part052 : IntSourceTree :=
  (.node 276 (sourceLit (List.headD (raw_ints% [231941889291231597306103]) 0) 68 false) treeG_J006_part048 treeG_J006_part051)

#time def treeG_J006_part053 : IntSourceTree :=
  (.node 308 (sourceLit (List.headD (raw_ints% [1416559216615944699959954375397420105]) 0) 24 true) (.node 306 (sourceLit (List.headD (raw_ints% [548707199335322931871478948690156475]) 0) 26 true) (.node 305 (sourceLit (List.headD (raw_ints% [5126003328779447233301775]) 0) 64 false) (.node 304 (sourceLit (List.headD (raw_ints% [418069947038404208721059714590652175]) 0) 27 true) .empty .empty) .empty) (.node 307 (sourceLit (List.headD (raw_ints% [19835897244079328294359275]) 0) 62 false) .empty .empty)) (.node 311 (sourceLit (List.headD (raw_ints% [146392522362651927055275]) 0) 69 false) (.node 310 (sourceLit (List.headD (raw_ints% [1723390516994269016535771004335019755]) 0) 23 true) (.node 309 (sourceLit (List.headD (raw_ints% [19253159372564650365240375]) 0) 62 false) .empty .empty) .empty) (.node 312 (sourceLit (List.headD (raw_ints% [7203934174498240840251733630394615475]) 0) 20 true) .empty .empty)))

#time def treeG_J006_part054 : IntSourceTree :=
  (.node 318 (sourceLit (List.headD (raw_ints% [78899743976236510339916216087943988395]) 0) 16 false) (.node 316 (sourceLit (List.headD (raw_ints% [14206276615758088574583091990707474285]) 0) 17 false) (.node 315 (sourceLit (List.headD (raw_ints% [139560353053685703338129]) 0) 69 false) (.node 314 (sourceLit (List.headD (raw_ints% [4339662614538229584021572922834307035]) 0) 19 true) .empty .empty) .empty) (.node 317 (sourceLit (List.headD (raw_ints% [136617910796304282581555]) 0) 69 false) .empty .empty)) (.node 330 (sourceLit (List.headD (raw_ints% [93774915761468785412928233749875]) 0) 45 true) (.node 319 (sourceLit (List.headD (raw_ints% [65393931374472862381]) 0) 80 false) .empty .empty) (.node 331 (sourceLit (List.headD (raw_ints% [147240969126056690648005683111495825]) 0) 36 true) .empty .empty)))

#time def treeG_J006_part055 : IntSourceTree :=
  (.node 313 (sourceLit (List.headD (raw_ints% [571197191255431770801447]) 0) 67 false) treeG_J006_part053 treeG_J006_part054)

#time def treeG_J006_part056 : IntSourceTree :=
  (.node 337 (sourceLit (List.headD (raw_ints% [458827654396234527035180399543217525]) 0) 31 true) (.node 335 (sourceLit (List.headD (raw_ints% [1163817050230204480192211130235259025]) 0) 32 true) (.node 334 (sourceLit (List.headD (raw_ints% [56601230905833614576233306216425]) 0) 47 true) (.node 333 (sourceLit (List.headD (raw_ints% [476988827010072670648872895632078825]) 0) 35 false) .empty .empty) .empty) (.node 336 (sourceLit (List.headD (raw_ints% [135308531547127812063919046175]) 0) 50 false) .empty .empty)) (.node 340 (sourceLit (List.headD (raw_ints% [14470587520708692630818814075]) 0) 53 false) (.node 339 (sourceLit (List.headD (raw_ints% [779835376254996552806897181933858525]) 0) 29 true) (.node 338 (sourceLit (List.headD (raw_ints% [62035807798625116538709464175]) 0) 51 false) .empty .empty) .empty) (.node 341 (sourceLit (List.headD (raw_ints% [849227241088665748423069061719330575]) 0) 28 true) .empty .empty)))

#time def treeG_J006_part057 : IntSourceTree :=
  (.node 347 (sourceLit (List.headD (raw_ints% [29098275704921936110306636899340578495]) 0) 21 true) (.node 345 (sourceLit (List.headD (raw_ints% [10841553978124299740224638224459812425]) 0) 23 true) (.node 344 (sourceLit (List.headD (raw_ints% [101656209193991279924035275]) 0) 60 false) (.node 343 (sourceLit (List.headD (raw_ints% [8321936140368723989660969502845507025]) 0) 24 true) .empty .empty) .empty) (.node 346 (sourceLit (List.headD (raw_ints% [48717833965553453803731225]) 0) 61 false) .empty .empty)) (.node 349 (sourceLit (List.headD (raw_ints% [39278677201014155748691739024629721745]) 0) 20 true) (.node 348 (sourceLit (List.headD (raw_ints% [23464328644349926114923225]) 0) 62 false) .empty .empty) (.node 350 (sourceLit (List.headD (raw_ints% [22692463926433727106352275]) 0) 62 false) .empty .empty)))

#time def treeG_J006_part058 : IntSourceTree :=
  (.node 342 (sourceLit (List.headD (raw_ints% [1707906189931128861942221775]) 0) 56 false) treeG_J006_part056 treeG_J006_part057)

#time def treeG_J006_part059 : IntSourceTree :=
  (.node 332 (sourceLit (List.headD (raw_ints% [36847261981865726200376310068325]) 0) 48 false) treeG_J006_part055 treeG_J006_part058)

#time def treeG_J006_part060 : IntSourceTree :=
  (.node 303 (sourceLit (List.headD (raw_ints% [21282281141738323766136975]) 0) 62 false) treeG_J006_part052 treeG_J006_part059)

#time def treeG_J006_part061 : IntSourceTree :=
  (.node 257 (sourceLit (List.headD (raw_ints% [71051960202630612994696555360788075]) 0) 31 true) treeG_J006_part045 treeG_J006_part060)

#time def treeG_J006_part062 : IntSourceTree :=
  (.node 167 (sourceLit (List.headD (raw_ints% [71022968986555047312742367200725]) 0) 39 false) treeG_J006_part030 treeG_J006_part061)

#time def treeG_J006_part063 : IntSourceTree :=
  (.node 356 (sourceLit (List.headD (raw_ints% [326299522923511216046413]) 0) 68 false) (.node 354 (sourceLit (List.headD (raw_ints% [1338656937466005051219361]) 0) 66 false) (.node 353 (sourceLit (List.headD (raw_ints% [261576288139887189778409899661949452505]) 0) 16 true) (.node 352 (sourceLit (List.headD (raw_ints% [2752110934896976078958289]) 0) 65 false) .empty .empty) .empty) (.node 355 (sourceLit (List.headD (raw_ints% [578797611065474647406889991199475616245]) 0) 14 true) .empty .empty)) (.node 359 (sourceLit (List.headD (raw_ints% [4495655153623003103293072947088933464495]) 0) 8 false) (.node 358 (sourceLit (List.headD (raw_ints% [79687907513392695489049]) 0) 70 false) (.node 357 (sourceLit (List.headD (raw_ints% [433101383804745880082422605245899513215]) 0) 13 true) .empty .empty) .empty) (.node 371 (sourceLit (List.headD (raw_ints% [153778960220155845354569250586125]) 0) 46 true) .empty .empty)))

#time def treeG_J006_part064 : IntSourceTree :=
  (.node 377 (sourceLit (List.headD (raw_ints% [84612005899725827266116869925]) 0) 51 false) (.node 375 (sourceLit (List.headD (raw_ints% [57037505059053107252705649947625]) 0) 48 true) (.node 374 (sourceLit (List.headD (raw_ints% [515763362998362297662392650822445725]) 0) 36 false) (.node 373 (sourceLit (List.headD (raw_ints% [175337137575636049760348915688375]) 0) 47 false) .empty .empty) .empty) (.node 376 (sourceLit (List.headD (raw_ints% [1097582098405346337688476510872258325]) 0) 33 true) .empty .empty)) (.node 380 (sourceLit (List.headD (raw_ints% [648903172312896011300063140483842225]) 0) 30 true) (.node 379 (sourceLit (List.headD (raw_ints% [38141812639691922509484151275]) 0) 52 false) (.node 378 (sourceLit (List.headD (raw_ints% [400035915658110317904792377170292025]) 0) 32 true) .empty .empty) .empty) (.node 381 (sourceLit (List.headD (raw_ints% [2196398241607392353847352275]) 0) 56 false) .empty .empty)))

#time def treeG_J006_part065 : IntSourceTree :=
  (.node 372 (sourceLit (List.headD (raw_ints% [201666521874622573112824318736222325]) 0) 37 true) treeG_J006_part063 treeG_J006_part064)

#time def treeG_J006_part066 : IntSourceTree :=
  (.node 387 (sourceLit (List.headD (raw_ints% [14440968360737062754685975]) 0) 63 false) (.node 385 (sourceLit (List.headD (raw_ints% [60648182563755702057621075]) 0) 61 false) (.node 384 (sourceLit (List.headD (raw_ints% [6649656352215107154776730644482898325]) 0) 25 true) (.node 383 (sourceLit (List.headD (raw_ints% [1026873193395502501425838575]) 0) 57 false) .empty .empty) .empty) (.node 386 (sourceLit (List.headD (raw_ints% [8646725180783008012738722429699186525]) 0) 24 true) .empty .empty)) (.node 390 (sourceLit (List.headD (raw_ints% [32385115133037079682548655007289642725]) 0) 21 true) (.node 389 (sourceLit (List.headD (raw_ints% [27675497916135201864606075]) 0) 62 false) (.node 388 (sourceLit (List.headD (raw_ints% [23432038838458157310466819397750898075]) 0) 22 true) .empty .empty) .empty) (.node 391 (sourceLit (List.headD (raw_ints% [13323342495224003774814675]) 0) 63 false) .empty .empty)))

#time def treeG_J006_part067 : IntSourceTree :=
  (.node 397 (sourceLit (List.headD (raw_ints% [94840806063603466732429]) 0) 70 false) (.node 395 (sourceLit (List.headD (raw_ints% [780415525251262237866845]) 0) 67 false) (.node 394 (sourceLit (List.headD (raw_ints% [244217637681734271442323607970612224365]) 0) 17 true) (.node 393 (sourceLit (List.headD (raw_ints% [1609716552386112537355395]) 0) 66 false) .empty .empty) .empty) (.node 396 (sourceLit (List.headD (raw_ints% [635622717528507001705222359162305513385]) 0) 15 true) .empty .empty)) (.node 399 (sourceLit (List.headD (raw_ints% [46206214649662589949977]) 0) 71 false) (.node 398 (sourceLit (List.headD (raw_ints% [748700359709691921442087469597675466795]) 0) 14 true) .empty .empty) (.node 412 (sourceLit (List.headD (raw_ints% [227473484183887297755321870722775]) 0) 47 true) .empty .empty)))

#time def treeG_J006_part068 : IntSourceTree :=
  (.node 392 (sourceLit (List.headD (raw_ints% [179402276538789152018943035317259542545]) 0) 18 true) treeG_J006_part066 treeG_J006_part067)

#time def treeG_J006_part069 : IntSourceTree :=
  (.node 382 (sourceLit (List.headD (raw_ints% [687707891144104285801786366143006075]) 0) 29 true) treeG_J006_part065 treeG_J006_part068)

#time def treeG_J006_part070 : IntSourceTree :=
  (.node 418 (sourceLit (List.headD (raw_ints% [107188204000826537993524275675]) 0) 51 false) (.node 416 (sourceLit (List.headD (raw_ints% [57308122122147362876833488039975]) 0) 49 true) (.node 415 (sourceLit (List.headD (raw_ints% [17668244666177798005388775956553522225]) 0) 32 false) (.node 414 (sourceLit (List.headD (raw_ints% [407275506057105714096931137593175]) 0) 47 false) .empty .empty) .empty) (.node 417 (sourceLit (List.headD (raw_ints% [8321829132846536174472631687434849075]) 0) 31 true) .empty .empty)) (.node 421 (sourceLit (List.headD (raw_ints% [4341998137414502341977436062151407225]) 0) 28 true) (.node 420 (sourceLit (List.headD (raw_ints% [1479451569936451867416583575]) 0) 57 false) (.node 419 (sourceLit (List.headD (raw_ints% [5620739274274768533669780852790813875]) 0) 29 true) .empty .empty) .empty) (.node 422 (sourceLit (List.headD (raw_ints% [2684890293283655845752482775]) 0) 56 false) .empty .empty)))

#time def treeG_J006_part071 : IntSourceTree :=
  (.node 428 (sourceLit (List.headD (raw_ints% [34299544798598324903820675]) 0) 62 false) (.node 426 (sourceLit (List.headD (raw_ints% [72578531161957950311510925]) 0) 61 false) (.node 425 (sourceLit (List.headD (raw_ints% [42355696839596557497989206931403374175]) 0) 23 true) (.node 424 (sourceLit (List.headD (raw_ints% [620248356619537381729697475]) 0) 58 false) .empty .empty) .empty) (.node 427 (sourceLit (List.headD (raw_ints% [109249327187606192093512921975846405905]) 0) 21 true) .empty .empty)) (.node 430 (sourceLit (List.headD (raw_ints% [32658531905836676622859875]) 0) 62 false) (.node 429 (sourceLit (List.headD (raw_ints% [148177633506651102735042816157377462855]) 0) 20 true) .empty .empty) (.node 431 (sourceLit (List.headD (raw_ints% [828105671020404434461606990394430562755]) 0) 17 true) .empty .empty)))

#time def treeG_J006_part072 : IntSourceTree :=
  (.node 423 (sourceLit (List.headD (raw_ints% [35691368892853950301653357930306881775]) 0) 24 true) treeG_J006_part070 treeG_J006_part071)

#time def treeG_J006_part073 : IntSourceTree :=
  (.node 437 (sourceLit (List.headD (raw_ints% [4651880356423310133559356268052544593865]) 0) 13 true) (.node 435 (sourceLit (List.headD (raw_ints% [3328684591842273695670287736330319973595]) 0) 14 true) (.node 434 (sourceLit (List.headD (raw_ints% [1880776167306220023491429]) 0) 66 false) (.node 433 (sourceLit (List.headD (raw_ints% [1173641924170426026373134382876126887855]) 0) 16 true) .empty .empty) .empty) (.node 436 (sourceLit (List.headD (raw_ints% [28382250145484438863777]) 0) 72 false) .empty .empty)) (.node 454 (sourceLit (List.headD (raw_ints% [1303042182502707776606930048172151575]) 0) 37 true) (.node 439 (sourceLit (List.headD (raw_ints% [100329301196463569047880269055591393214255]) 0) 8 true) (.node 438 (sourceLit (List.headD (raw_ints% [109993704613814237975809]) 0) 70 false) .empty .empty) .empty) (.node 455 (sourceLit (List.headD (raw_ints% [7254890798689981583588074805325]) 0) 54 false) .empty .empty)))

#time def treeG_J006_part074 : IntSourceTree :=
  (.node 461 (sourceLit (List.headD (raw_ints% [3721408038138415115818982025]) 0) 56 false) (.node 459 (sourceLit (List.headD (raw_ints% [4315399460070913467752507775]) 0) 56 false) (.node 458 (sourceLit (List.headD (raw_ints% [3960896608594212928283919655132278525]) 0) 33 true) (.node 457 (sourceLit (List.headD (raw_ints% [57477346133946814531365721779825]) 0) 50 true) .empty .empty) .empty) (.node 460 (sourceLit (List.headD (raw_ints% [2485918050980936261184858856153485825]) 0) 31 true) .empty .empty)) (.node 463 (sourceLit (List.headD (raw_ints% [207252137486019168040830525]) 0) 60 false) (.node 462 (sourceLit (List.headD (raw_ints% [1827145123135199028087824848004200575]) 0) 30 true) .empty .empty) (.node 464 (sourceLit (List.headD (raw_ints% [14520856270319421573438313642911991725]) 0) 26 true) .empty .empty)))

#time def treeG_J006_part075 : IntSourceTree :=
  (.node 456 (sourceLit (List.headD (raw_ints% [9382913382291572171538626233712890275]) 0) 34 false) treeG_J006_part073 treeG_J006_part074)

#time def treeG_J006_part076 : IntSourceTree :=
  (.node 432 (sourceLit (List.headD (raw_ints% [7819120625430051616898097]) 0) 64 false) treeG_J006_part072 treeG_J006_part075)

#time def treeG_J006_part077 : IntSourceTree :=
  (.node 413 (sourceLit (List.headD (raw_ints% [2090321002007053255551467445521857425]) 0) 35 true) treeG_J006_part069 treeG_J006_part076)

#time def treeG_J006_part078 : IntSourceTree :=
  (.node 470 (sourceLit (List.headD (raw_ints% [57896259186807011526247080575043910065]) 0) 22 true) (.node 468 (sourceLit (List.headD (raw_ints% [42908644174574017391523051289047753915]) 0) 23 true) (.node 467 (sourceLit (List.headD (raw_ints% [43696594440483824802138975]) 0) 62 false) (.node 466 (sourceLit (List.headD (raw_ints% [16854485829406774742625242250852093825]) 0) 25 true) .empty .empty) .empty) (.node 469 (sourceLit (List.headD (raw_ints% [40923591681061447943035275]) 0) 62 false) .empty .empty)) (.node 473 (sourceLit (List.headD (raw_ints% [4599687520657826542187307]) 0) 65 false) (.node 472 (sourceLit (List.headD (raw_ints% [324351697240807641221331977538585510105]) 0) 19 true) (.node 471 (sourceLit (List.headD (raw_ints% [1208449338163292053002825]) 0) 67 false) .empty .empty) .empty) (.node 474 (sourceLit (List.headD (raw_ints% [464712143244345877465405387452757331745]) 0) 18 true) .empty .empty)))

#time def treeG_J006_part079 : IntSourceTree :=
  (.node 495 (sourceLit (List.headD (raw_ints% [101062944346351095708232299039571223025]) 0) 32 true) (.node 478 (sourceLit (List.headD (raw_ints% [1951589998356809106058634399227434563535]) 0) 15 true) (.node 477 (sourceLit (List.headD (raw_ints% [132217195100272044177787]) 0) 70 false) (.node 476 (sourceLit (List.headD (raw_ints% [1346530937156883346982532688584007230105]) 0) 16 true) .empty .empty) .empty) (.node 479 (sourceLit (List.headD (raw_ints% [7973436245518956003229]) 0) 74 false) .empty .empty)) (.node 497 (sourceLit (List.headD (raw_ints% [158448443249511690919090651426841093475]) 0) 31 false) (.node 496 (sourceLit (List.headD (raw_ints% [521621133238306184226470275580775]) 0) 49 false) .empty .empty) (.node 498 (sourceLit (List.headD (raw_ints% [14396133584486910267339811513875]) 0) 53 true) .empty .empty)))

#time def treeG_J006_part080 : IntSourceTree :=
  (.node 475 (sourceLit (List.headD (raw_ints% [137545080256869723203073]) 0) 70 false) treeG_J006_part078 treeG_J006_part079)

#time def treeG_J006_part081 : IntSourceTree :=
  (.node 504 (sourceLit (List.headD (raw_ints% [1037768743268615962596946725]) 0) 58 false) (.node 502 (sourceLit (List.headD (raw_ints% [4757925782993174385885481275]) 0) 56 false) (.node 501 (sourceLit (List.headD (raw_ints% [35432690678280477836980305636304365975]) 0) 28 true) (.node 500 (sourceLit (List.headD (raw_ints% [354493486266807700041990525]) 0) 60 false) .empty .empty) .empty) (.node 503 (sourceLit (List.headD (raw_ints% [198183206868451525293588222614230791825]) 0) 24 true) .empty .empty)) (.node 507 (sourceLit (List.headD (raw_ints% [430094219353410599670494830051420596495]) 0) 21 true) (.node 506 (sourceLit (List.headD (raw_ints% [232498564040598672876191325]) 0) 60 false) (.node 505 (sourceLit (List.headD (raw_ints% [189978003485514187677023811355188493425]) 0) 23 true) .empty .empty) .empty) (.node 508 (sourceLit (List.headD (raw_ints% [53093644082369324700457275]) 0) 62 false) .empty .empty)))

#time def treeG_J006_part082 : IntSourceTree :=
  (.node 514 (sourceLit (List.headD (raw_ints% [1359455676675803259347939]) 0) 67 false) (.node 512 (sourceLit (List.headD (raw_ints% [11516068785182621231147103]) 0) 64 false) (.node 511 (sourceLit (List.headD (raw_ints% [2877254916935244303218206166408379681405]) 0) 17 true) (.node 510 (sourceLit (List.headD (raw_ints% [49188651456286219263210675]) 0) 62 false) .empty .empty) .empty) (.node 513 (sourceLit (List.headD (raw_ints% [4015985231682496233168177257741241273825]) 0) 16 true) .empty .empty)) (.node 516 (sourceLit (List.headD (raw_ints% [80780579965900845475519]) 0) 71 false) (.node 515 (sourceLit (List.headD (raw_ints% [11542103991976794383222684662157914642245]) 0) 14 true) .empty .empty) (.node 517 (sourceLit (List.headD (raw_ints% [16892614638086823418161166749291571087815]) 0) 13 true) .empty .empty)))

#time def treeG_J006_part083 : IntSourceTree :=
  (.node 509 (sourceLit (List.headD (raw_ints% [538360673286533175529326004467386599785]) 0) 20 true) treeG_J006_part081 treeG_J006_part082)

#time def treeG_J006_part084 : IntSourceTree :=
  (.node 499 (sourceLit (List.headD (raw_ints% [121127952200740045171415648111442098925]) 0) 29 true) treeG_J006_part080 treeG_J006_part083)

#time def treeG_J006_part085 : IntSourceTree :=
  (.node 540 (sourceLit (List.headD (raw_ints% [116156116098778172649045930399135127275]) 0) 30 true) (.node 538 (sourceLit (List.headD (raw_ints% [166370236466700116775658490737105650525]) 0) 32 false) (.node 537 (sourceLit (List.headD (raw_ints% [72387309921531624844729499670075]) 0) 53 false) (.node 519 (sourceLit (List.headD (raw_ints% [399277738382879562103130137146631855050705]) 0) 8 true) .empty .empty) .empty) (.node 539 (sourceLit (List.headD (raw_ints% [14413395182327193921210821544975]) 0) 54 true) .empty .empty)) (.node 543 (sourceLit (List.headD (raw_ints% [3099908683105021041558837075]) 0) 57 false) (.node 542 (sourceLit (List.headD (raw_ints% [31778400432010079780804655940295964825]) 0) 29 true) (.node 541 (sourceLit (List.headD (raw_ints% [7622383522399431285524714775]) 0) 56 false) .empty .empty) .empty) (.node 544 (sourceLit (List.headD (raw_ints% [169141494327812682146711595328406808375]) 0) 25 true) .empty .empty)))

#time def treeG_J006_part086 : IntSourceTree :=
  (.node 550 (sourceLit (List.headD (raw_ints% [422568154912919152476831843317298779655]) 0) 21 true) (.node 548 (sourceLit (List.headD (raw_ints% [344276931004262564887448727473325088665]) 0) 22 true) (.node 547 (sourceLit (List.headD (raw_ints% [145105375159631023271913375]) 0) 61 false) (.node 546 (sourceLit (List.headD (raw_ints% [156269031826700638191773326853484305775]) 0) 24 true) .empty .empty) .empty) (.node 549 (sourceLit (List.headD (raw_ints% [65263696483677201457879275]) 0) 62 false) .empty .empty)) (.node 552 (sourceLit (List.headD (raw_ints% [2228551522453629020775542211331208661195]) 0) 18 true) (.node 551 (sourceLit (List.headD (raw_ints% [29853462045673546415165475]) 0) 63 false) .empty .empty) (.node 553 (sourceLit (List.headD (raw_ints% [1729095316131198672239949]) 0) 67 false) .empty .empty)))

#time def treeG_J006_part087 : IntSourceTree :=
  (.node 545 (sourceLit (List.headD (raw_ints% [330056558452050694548866775]) 0) 60 false) treeG_J006_part085 treeG_J006_part086)

#time def treeG_J006_part088 : IntSourceTree :=
  (.node 559 (sourceLit (List.headD (raw_ints% [90653195622578202353933]) 0) 71 false) (.node 557 (sourceLit (List.headD (raw_ints% [190905124763331337724289]) 0) 70 false) (.node 556 (sourceLit (List.headD (raw_ints% [8849042117663027689257619284989900182035]) 0) 15 true) (.node 555 (sourceLit (List.headD (raw_ints% [809275355648324366535647]) 0) 68 false) .empty .empty) .empty) (.node 558 (sourceLit (List.headD (raw_ints% [12989434641373205206043897950836701960745]) 0) 14 true) .empty .empty)) (.node 582 (sourceLit (List.headD (raw_ints% [10486841261805688185163948275]) 0) 56 false) (.node 581 (sourceLit (List.headD (raw_ints% [893816238111944903355387137556776652225]) 0) 28 true) (.node 580 (sourceLit (List.headD (raw_ints% [14424738973887731767612165241775]) 0) 55 true) .empty .empty) .empty) (.node 583 (sourceLit (List.headD (raw_ints% [1835634420780193580677909757564710956975]) 0) 24 true) .empty .empty)))

#time def treeG_J006_part089 : IntSourceTree :=
  (.node 589 (sourceLit (List.headD (raw_ints% [2215854774747567343570263815319214109535]) 0) 20 true) (.node 587 (sourceLit (List.headD (raw_ints% [2070210289873799611397878399604328295905]) 0) 21 true) (.node 586 (sourceLit (List.headD (raw_ints% [427614552863502716221542225]) 0) 60 false) (.node 585 (sourceLit (List.headD (raw_ints% [1163153951136987269496668951272065973575]) 0) 23 true) .empty .empty) .empty) (.node 588 (sourceLit (List.headD (raw_ints% [23002932769315424642864025]) 0) 64 false) .empty .empty)) (.node 591 (sourceLit (List.headD (raw_ints% [10644926040278168576040412819745181267555]) 0) 17 true) (.node 590 (sourceLit (List.headD (raw_ints% [81338741511068183652547875]) 0) 62 false) .empty .empty) (.node 592 (sourceLit (List.headD (raw_ints% [4584348315122731296004593]) 0) 66 false) .empty .empty)))

#time def treeG_J006_part090 : IntSourceTree :=
  (.node 584 (sourceLit (List.headD (raw_ints% [1031069969918202539480945175]) 0) 59 false) treeG_J006_part088 treeG_J006_part089)

#time def treeG_J006_part091 : IntSourceTree :=
  (.node 554 (sourceLit (List.headD (raw_ints% [3086560945193804478237366482835726610335]) 0) 17 true) treeG_J006_part087 treeG_J006_part090)

#time def treeG_J006_part092 : IntSourceTree :=
  (.node 518 (sourceLit (List.headD (raw_ints% [154440685586729850379765]) 0) 70 false) treeG_J006_part084 treeG_J006_part091)

#time def treeG_J006_part093 : IntSourceTree :=
  (.node 465 (sourceLit (List.headD (raw_ints% [377655626364514573499213175]) 0) 59 false) treeG_J006_part077 treeG_J006_part092)

#time def treeG_J006_part094 : IntSourceTree :=
  (.node 598 (sourceLit (List.headD (raw_ints% [227369563939932825068813]) 0) 70 false) (.node 596 (sourceLit (List.headD (raw_ints% [486153035784720984633571]) 0) 69 false) (.node 595 (sourceLit (List.headD (raw_ints% [37842871131124077268575179063213711123115]) 0) 14 true) (.node 594 (sourceLit (List.headD (raw_ints% [2098734955586594085131959]) 0) 67 false) .empty .empty) .empty) (.node 597 (sourceLit (List.headD (raw_ints% [53899722303217398095899787530627630368465]) 0) 13 true) .empty .empty)) (.node 622 (sourceLit (List.headD (raw_ints% [107754729709991852946822810202060085925]) 0) 32 true) (.node 621 (sourceLit (List.headD (raw_ints% [7216180678705065599448844978275]) 0) 57 true) (.node 599 (sourceLit (List.headD (raw_ints% [1263369895712890704270488800560465995924655]) 0) 8 true) .empty .empty) .empty) (.node 623 (sourceLit (List.headD (raw_ints% [230841643084395848237659725]) 0) 62 false) .empty .empty)))

#time def treeG_J006_part095 : IntSourceTree :=
  (.node 629 (sourceLit (List.headD (raw_ints% [118759765670846195685032925]) 0) 62 false) (.node 627 (sourceLit (List.headD (raw_ints% [141254588851935846474814425]) 0) 62 false) (.node 626 (sourceLit (List.headD (raw_ints% [125860614913785828913111953052322708475]) 0) 27 true) (.node 625 (sourceLit (List.headD (raw_ints% [10953334554158622577063725]) 0) 66 false) .empty .empty) .empty) (.node 628 (sourceLit (List.headD (raw_ints% [215741669858692130813803709016375400905]) 0) 25 true) .empty .empty)) (.node 631 (sourceLit (List.headD (raw_ints% [201114372911697801708525]) 0) 71 false) (.node 630 (sourceLit (List.headD (raw_ints% [224160827479331023886678996500239416235]) 0) 24 true) .empty .empty) (.node 632 (sourceLit (List.headD (raw_ints% [1052046814728067444408108826051746575795]) 0) 21 true) .empty .empty)))

#time def treeG_J006_part096 : IntSourceTree :=
  (.node 624 (sourceLit (List.headD (raw_ints% [208311615806547612316399770279538018575]) 0) 28 true) treeG_J006_part094 treeG_J006_part095)

#time def treeG_J006_part097 : IntSourceTree :=
  (.node 638 (sourceLit (List.headD (raw_ints% [5113785957730524111231986197473866050965]) 0) 17 true) (.node 636 (sourceLit (List.headD (raw_ints% [3624228626682631197414694972277976367635]) 0) 18 true) (.node 635 (sourceLit (List.headD (raw_ints% [161182449992283714824539]) 0) 71 false) (.node 634 (sourceLit (List.headD (raw_ints% [1340733250344091431849849243759087675675]) 0) 20 true) .empty .empty) .empty) (.node 637 (sourceLit (List.headD (raw_ints% [147623955510694823454641]) 0) 71 false) .empty .empty)) (.node 664 (sourceLit (List.headD (raw_ints% [2662396319432131032321610425]) 0) 59 false) (.node 663 (sourceLit (List.headD (raw_ints% [53334787190735635128095369065890053036625]) 0) 24 true) (.node 639 (sourceLit (List.headD (raw_ints% [133512078434916623745]) 0) 81 false) .empty .empty) .empty) (.node 665 (sourceLit (List.headD (raw_ints% [12168789460482059918752916346618367215225]) 0) 23 true) .empty .empty)))

#time def treeG_J006_part098 : IntSourceTree :=
  (.node 671 (sourceLit (List.headD (raw_ints% [46740245794430573538949410284316109288605]) 0) 17 true) (.node 669 (sourceLit (List.headD (raw_ints% [11591612096208729028513173561728811548385]) 0) 20 true) (.node 668 (sourceLit (List.headD (raw_ints% [95248723313304997189086375]) 0) 63 false) (.node 667 (sourceLit (List.headD (raw_ints% [14039948419090786489480451591092978388895]) 0) 21 true) .empty .empty) .empty) (.node 670 (sourceLit (List.headD (raw_ints% [156180789830624207717517975]) 0) 62 false) .empty .empty)) (.node 673 (sourceLit (List.headD (raw_ints% [53518569194649780509082804434403352835145]) 0) 16 true) (.node 672 (sourceLit (List.headD (raw_ints% [8286971551225928013341007]) 0) 66 false) .empty .empty) (.node 674 (sourceLit (List.headD (raw_ints% [3611771042396471162397329]) 0) 67 false) .empty .empty)))

#time def treeG_J006_part099 : IntSourceTree :=
  (.node 666 (sourceLit (List.headD (raw_ints% [974412270068800973642614575]) 0) 60 false) treeG_J006_part097 treeG_J006_part098)

#time def treeG_J006_part100 : IntSourceTree :=
  (.node 633 (sourceLit (List.headD (raw_ints% [713813249747883155941161]) 0) 69 false) treeG_J006_part096 treeG_J006_part099)

#time def treeG_J006_part101 : IntSourceTree :=
  (.node 704 (sourceLit (List.headD (raw_ints% [51668294264283254229564170903653748888025]) 0) 25 true) (.node 678 (sourceLit (List.headD (raw_ints% [363126258102846468749751]) 0) 70 false) (.node 677 (sourceLit (List.headD (raw_ints% [178050909804470998538640690695162857160175]) 0) 13 true) (.node 676 (sourceLit (List.headD (raw_ints% [803306564153548733962741]) 0) 69 false) .empty .empty) .empty) (.node 679 (sourceLit (List.headD (raw_ints% [3973146925003165985631065065652772840263505]) 0) 8 true) .empty .empty)) (.node 707 (sourceLit (List.headD (raw_ints% [691903092364929280692985725]) 0) 61 false) (.node 706 (sourceLit (List.headD (raw_ints% [11161904541171773287448020722199785547425]) 0) 24 true) (.node 705 (sourceLit (List.headD (raw_ints% [1961382907965979187389532025]) 0) 60 false) .empty .empty) .empty) (.node 708 (sourceLit (List.headD (raw_ints% [12314015060221249442970021918961975181655]) 0) 22 true) .empty .empty)))

#time def treeG_J006_part102 : IntSourceTree :=
  (.node 714 (sourceLit (List.headD (raw_ints% [42792703191897049054284010484330651429745]) 0) 17 true) (.node 712 (sourceLit (List.headD (raw_ints% [38323871276606033983684539675902136682245]) 0) 18 true) (.node 711 (sourceLit (List.headD (raw_ints% [104695510365229570480135575]) 0) 63 false) (.node 710 (sourceLit (List.headD (raw_ints% [9798325476374080837419741589726896218505]) 0) 21 true) .empty .empty) .empty) (.node 713 (sourceLit (List.headD (raw_ints% [5431718552234395389576363]) 0) 67 false) .empty .empty)) (.node 716 (sourceLit (List.headD (raw_ints% [104777155899458576428887964359725700422205]) 0) 15 true) (.node 715 (sourceLit (List.headD (raw_ints% [2322311442458201443801017]) 0) 68 false) .empty .empty) (.node 717 (sourceLit (List.headD (raw_ints% [508058653132159087053459]) 0) 70 false) .empty .empty)))

#time def treeG_J006_part103 : IntSourceTree :=
  (.node 709 (sourceLit (List.headD (raw_ints% [262235127582373793071312575]) 0) 62 false) treeG_J006_part101 treeG_J006_part102)

#time def treeG_J006_part104 : IntSourceTree :=
  (.node 748 (sourceLit (List.headD (raw_ints% [501405645738319286314812975]) 0) 62 false) (.node 746 (sourceLit (List.headD (raw_ints% [2948353545863157401136449475]) 0) 60 false) (.node 745 (sourceLit (List.headD (raw_ints% [401177564653783973917760450882611623888975]) 0) 23 true) (.node 719 (sourceLit (List.headD (raw_ints% [226409889785491846034871]) 0) 71 false) .empty .empty) .empty) (.node 747 (sourceLit (List.headD (raw_ints% [164550524239657586109687879964103590369905]) 0) 21 true) .empty .empty)) (.node 751 (sourceLit (List.headD (raw_ints% [266806169449540013258482320586944569703555]) 0) 17 true) (.node 750 (sourceLit (List.headD (raw_ints% [368289465334123378425107175]) 0) 62 false) (.node 749 (sourceLit (List.headD (raw_ints% [86920508385561266515247001789966989904855]) 0) 20 true) .empty .empty) .empty) (.node 752 (sourceLit (List.headD (raw_ints% [71547624160325858426771547]) 0) 64 false) .empty .empty)))

#time def treeG_J006_part105 : IntSourceTree :=
  (.node 758 (sourceLit (List.headD (raw_ints% [652991048161471705357167]) 0) 70 false) (.node 756 (sourceLit (List.headD (raw_ints% [379751219576163177459569]) 0) 71 false) (.node 755 (sourceLit (List.headD (raw_ints% [550912266157433158860338643611340911512635]) 0) 14 true) (.node 754 (sourceLit (List.headD (raw_ints% [7251666062072319616755397]) 0) 67 false) .empty .empty) .empty) (.node 757 (sourceLit (List.headD (raw_ints% [660166337391197612892463024182642746217465]) 0) 13 true) .empty .empty)) (.node 786 (sourceLit (List.headD (raw_ints% [195007830056306100315156215080205919170775]) 0) 25 true) (.node 759 (sourceLit (List.headD (raw_ints% [13580852709253065137413389477114834040050735]) 0) 8 true) .empty .empty) (.node 787 (sourceLit (List.headD (raw_ints% [1128225226749114060221731875]) 0) 62 false) .empty .empty)))

#time def treeG_J006_part106 : IntSourceTree :=
  (.node 753 (sourceLit (List.headD (raw_ints% [253072401018198491360393512972813740622815]) 0) 16 true) treeG_J006_part104 treeG_J006_part105)

#time def treeG_J006_part107 : IntSourceTree :=
  (.node 718 (sourceLit (List.headD (raw_ints% [137140622142626805648784801115371928752455]) 0) 14 true) treeG_J006_part103 treeG_J006_part106)

#time def treeG_J006_part108 : IntSourceTree :=
  (.node 675 (sourceLit (List.headD (raw_ints% [133770984912919626008205524137949511363285]) 0) 14 true) treeG_J006_part100 treeG_J006_part107)

#time def treeG_J006_part109 : IntSourceTree :=
  (.node 793 (sourceLit (List.headD (raw_ints% [49820749951388276868466095]) 0) 65 false) (.node 791 (sourceLit (List.headD (raw_ints% [16474622185555862996560725]) 0) 67 false) (.node 790 (sourceLit (List.headD (raw_ints% [38561091454593592838913630100120046843175]) 0) 22 true) (.node 789 (sourceLit (List.headD (raw_ints% [740576163894264779558313375]) 0) 62 false) .empty .empty) .empty) (.node 792 (sourceLit (List.headD (raw_ints% [114241149086466989637398890455521216510655]) 0) 19 true) .empty .empty)) (.node 796 (sourceLit (List.headD (raw_ints% [223067555128987291215725339625807605545215]) 0) 16 true) (.node 795 (sourceLit (List.headD (raw_ints% [1232338654903529543238595]) 0) 70 false) (.node 794 (sourceLit (List.headD (raw_ints% [105139848913150721153054751244241544596535]) 0) 18 true) .empty .empty) .empty) (.node 797 (sourceLit (List.headD (raw_ints% [1010946225172493622784817]) 0) 70 false) .empty .empty)))

#time def treeG_J006_part110 : IntSourceTree :=
  (.node 830 (sourceLit (List.headD (raw_ints% [1112862862454406180691519575]) 0) 62 false) (.node 828 (sourceLit (List.headD (raw_ints% [1755044807759908834128650775]) 0) 62 false) (.node 827 (sourceLit (List.headD (raw_ints% [6075700037562137623975311002602485823094895]) 0) 21 true) (.node 799 (sourceLit (List.headD (raw_ints% [53322644796997482415287]) 0) 74 false) .empty .empty) .empty) (.node 829 (sourceLit (List.headD (raw_ints% [1130971565049929426818495862571165931601145]) 0) 20 true) .empty .empty)) (.node 832 (sourceLit (List.headD (raw_ints% [192046330808567949518200053]) 0) 64 false) (.node 831 (sourceLit (List.headD (raw_ints% [2201103683644449928431990005820738428259645]) 0) 17 true) .empty .empty) (.node 833 (sourceLit (List.headD (raw_ints% [1574785984365273342837988734315525723547665]) 0) 16 true) .empty .empty)))

#time def treeG_J006_part111 : IntSourceTree :=
  (.node 798 (sourceLit (List.headD (raw_ints% [261512857624285403621839111533635408732505]) 0) 15 true) treeG_J006_part109 treeG_J006_part110)

#time def treeG_J006_part112 : IntSourceTree :=
  (.node 839 (sourceLit (List.headD (raw_ints% [53366438842563998189777423075495830595470545]) 0) 8 true) (.node 837 (sourceLit (List.headD (raw_ints% [2908914544672599046559142409830278942505975]) 0) 13 true) (.node 836 (sourceLit (List.headD (raw_ints% [426293717663683182889513]) 0) 72 false) (.node 835 (sourceLit (List.headD (raw_ints% [2813562899063389918037413396204388515576485]) 0) 14 true) .empty .empty) .empty) (.node 838 (sourceLit (List.headD (raw_ints% [1368901402183515540212467]) 0) 70 false) .empty .empty)) (.node 870 (sourceLit (List.headD (raw_ints% [1053849382140742241140668602370925837914795]) 0) 21 true) (.node 869 (sourceLit (List.headD (raw_ints% [2769513451625552888698988175]) 0) 62 false) (.node 868 (sourceLit (List.headD (raw_ints% [5923463528382701287308593144557344207906645]) 0) 22 true) .empty .empty) .empty) (.node 871 (sourceLit (List.headD (raw_ints% [849268907485512372746547975]) 0) 63 false) .empty .empty)))

#time def treeG_J006_part113 : IntSourceTree :=
  (.node 877 (sourceLit (List.headD (raw_ints% [2399403516136971840331287]) 0) 70 false) (.node 875 (sourceLit (List.headD (raw_ints% [25458708588015401289046541]) 0) 67 false) (.node 874 (sourceLit (List.headD (raw_ints% [1364506286538971900531879231827042634354595]) 0) 17 true) (.node 873 (sourceLit (List.headD (raw_ints% [71112790428589836324866979]) 0) 66 false) .empty .empty) .empty) (.node 876 (sourceLit (List.headD (raw_ints% [2367427788805415335605962716952773304486055]) 0) 15 true) .empty .empty)) (.node 879 (sourceLit (List.headD (raw_ints% [942320243807535680890171]) 0) 71 false) (.node 878 (sourceLit (List.headD (raw_ints% [2385888829424028239315464186763008125040965]) 0) 14 true) .empty .empty) (.node 909 (sourceLit (List.headD (raw_ints% [46256736662011680871650249293887587731652015]) 0) 20 true) .empty .empty)))

#time def treeG_J006_part114 : IntSourceTree :=
  (.node 872 (sourceLit (List.headD (raw_ints% [1972621385471515949157192224909695995238335]) 0) 18 true) treeG_J006_part112 treeG_J006_part113)

#time def treeG_J006_part115 : IntSourceTree :=
  (.node 834 (sourceLit (List.headD (raw_ints% [35317417827243637634955301]) 0) 66 false) treeG_J006_part111 treeG_J006_part114)

#time def treeG_J006_part116 : IntSourceTree :=
  (.node 915 (sourceLit (List.headD (raw_ints% [19018537685560160490472654313028293634097035]) 0) 14 true) (.node 913 (sourceLit (List.headD (raw_ints% [14206185099406854250419549064962042238359015]) 0) 16 true) (.node 912 (sourceLit (List.headD (raw_ints% [328611288338472211614173961]) 0) 65 false) (.node 911 (sourceLit (List.headD (raw_ints% [31522076544859301788069405270048888385013795]) 0) 17 true) .empty .empty) .empty) (.node 914 (sourceLit (List.headD (raw_ints% [106908163029936035014778657]) 0) 66 false) .empty .empty)) (.node 918 (sourceLit (List.headD (raw_ints% [3429905630090428140450107]) 0) 70 false) (.node 917 (sourceLit (List.headD (raw_ints% [16030507765770723638288559325791907493382465]) 0) 13 true) (.node 916 (sourceLit (List.headD (raw_ints% [18638009105396470362814333]) 0) 68 false) .empty .empty) .empty) (.node 919 (sourceLit (List.headD (raw_ints% [252027331323711616442601992830169209409772975]) 0) 8 true) .empty .empty)))

#time def treeG_J006_part117 : IntSourceTree :=
  (.node 955 (sourceLit (List.headD (raw_ints% [20362363610480158431433029]) 0) 69 false) (.node 953 (sourceLit (List.headD (raw_ints% [128749248954941187644653491]) 0) 67 false) (.node 952 (sourceLit (List.headD (raw_ints% [7387363789846946459728053261284798097443865]) 0) 20 true) (.node 951 (sourceLit (List.headD (raw_ints% [55888986457987300374373575]) 0) 69 false) .empty .empty) .empty) (.node 954 (sourceLit (List.headD (raw_ints% [3210419703216970587471917458283749901001105]) 0) 19 true) .empty .empty)) (.node 957 (sourceLit (List.headD (raw_ints% [13839202073122526682151759]) 0) 69 false) (.node 956 (sourceLit (List.headD (raw_ints% [4162777474188686288716672899018880082402745]) 0) 17 true) .empty .empty) (.node 958 (sourceLit (List.headD (raw_ints% [3411154734086673849743273784757224842085375]) 0) 16 true) .empty .empty)))

#time def treeG_J006_part118 : IntSourceTree :=
  (.node 950 (sourceLit (List.headD (raw_ints% [11300721819967734657627395172879165473434305]) 0) 23 true) treeG_J006_part116 treeG_J006_part117)

#time def treeG_J006_part119 : IntSourceTree :=
  (.node 997 (sourceLit (List.headD (raw_ints% [117178371408267237600644973442812255143505375]) 0) 13 true) (.node 995 (sourceLit (List.headD (raw_ints% [186448323320325957107730063017131700029973685]) 0) 14 true) (.node 994 (sourceLit (List.headD (raw_ints% [408088832789828715563835307]) 0) 66 false) (.node 993 (sourceLit (List.headD (raw_ints% [222189456175695432460878155296151496879844665]) 0) 16 true) .empty .empty) .empty) (.node 996 (sourceLit (List.headD (raw_ints% [62811445336524163362917783]) 0) 68 false) .empty .empty)) (.node 1034 (sourceLit (List.headD (raw_ints% [209347777362827550110990485463016497275840245]) 0) 17 true) (.node 999 (sourceLit (List.headD (raw_ints% [1494483892528665394625954184965529909737939025]) 0) 8 true) (.node 998 (sourceLit (List.headD (raw_ints% [2602324110758024635425413]) 0) 72 false) .empty .empty) .empty) (.node 1035 (sourceLit (List.headD (raw_ints% [326639378347908081838103191]) 0) 67 false) .empty .empty)))

#time def treeG_J006_part120 : IntSourceTree :=
  (.node 1076 (sourceLit (List.headD (raw_ints% [1030577863325718431543693]) 0) 76 false) (.node 1039 (sourceLit (List.headD (raw_ints% [1980427764187301520535429]) 0) 73 false) (.node 1038 (sourceLit (List.headD (raw_ints% [103533752471920542201671878303783355775163875]) 0) 14 true) (.node 1037 (sourceLit (List.headD (raw_ints% [6121530407925204585095753]) 0) 72 false) .empty .empty) .empty) (.node 1075 (sourceLit (List.headD (raw_ints% [3163116114484914844668117704391132256383470235]) 0) 14 true) .empty .empty)) (.node 1078 (sourceLit (List.headD (raw_ints% [9640736705092384534766093]) 0) 72 false) (.node 1077 (sourceLit (List.headD (raw_ints% [1241199335980302458022261997925637182459396265]) 0) 13 true) .empty .empty) (.node 1079 (sourceLit (List.headD (raw_ints% [11757836423877164007188046237918739629483036975]) 0) 8 true) .empty .empty)))

#time def treeG_J006_part121 : IntSourceTree :=
  (.node 1036 (sourceLit (List.headD (raw_ints% [169797213423571211952863371421056179700362705]) 0) 15 true) treeG_J006_part119 treeG_J006_part120)

#time def treeG_J006_part122 : IntSourceTree :=
  (.node 959 (sourceLit (List.headD (raw_ints% [2429282603791887167539]) 0) 81 false) treeG_J006_part118 treeG_J006_part121)

#time def treeG_J006_part123 : IntSourceTree :=
  (.node 910 (sourceLit (List.headD (raw_ints% [4426164040796699596706456775]) 0) 62 false) treeG_J006_part115 treeG_J006_part122)

#time def treeG_J006_part124 : IntSourceTree :=
  (.node 788 (sourceLit (List.headD (raw_ints% [76118254589718168333358929022570807594125]) 0) 23 true) treeG_J006_part108 treeG_J006_part123)

#time def treeG_J006_part125 : IntSourceTree :=
  (.node 593 (sourceLit (List.headD (raw_ints% [13812426947946535933036160432908428015735]) 0) 16 true) treeG_J006_part093 treeG_J006_part124)

#time def treeG_J006_part126 : IntSourceTree :=
  (.node 351 (sourceLit (List.headD (raw_ints% [208218013236782115379949969838838004445]) 0) 17 true) treeG_J006_part062 treeG_J006_part125)

#time def treeG_J006 : IntSourceTree := treeG_J006_part126

-- kcost: 4s estimated (20000 provisional decoder/lookup/arithmetic units *0.0002s/unit).
#time theorem treeT_J001_check : treeT_J001.check 40 (sourceBaseT momentData 1) = true := by
  decide +kernel

-- kcost: 38s estimated (190000 provisional decoder/lookup/arithmetic units *0.0002s/unit).
#time theorem treeG_J006_check : treeG_J006.check 40 (sourceBaseG momentData 6) = true := by
  decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
