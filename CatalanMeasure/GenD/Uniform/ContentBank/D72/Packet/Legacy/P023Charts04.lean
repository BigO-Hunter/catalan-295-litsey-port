module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P023Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P023
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C008
#time def pivTape : List (Fin 48) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩]

#time def freeTape : List (Fin 48) :=
  [⟨47, by decide⟩]

#time def roleTape : List (Fin 47 ⊕ Fin 1) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩, .inl ⟨27, by decide⟩, .inl ⟨28, by decide⟩, .inl ⟨29, by decide⟩, .inl ⟨30, by decide⟩, .inl ⟨31, by decide⟩, .inl ⟨32, by decide⟩, .inl ⟨33, by decide⟩, .inl ⟨34, by decide⟩, .inl ⟨35, by decide⟩, .inl ⟨36, by decide⟩, .inl ⟨37, by decide⟩, .inl ⟨38, by decide⟩, .inl ⟨39, by decide⟩, .inl ⟨40, by decide⟩, .inl ⟨41, by decide⟩, .inl ⟨42, by decide⟩, .inl ⟨43, by decide⟩, .inl ⟨44, by decide⟩, .inl ⟨45, by decide⟩, .inl ⟨46, by decide⟩, .inr ⟨0, by decide⟩]

#time def roles : GraphRoles 48 47 1 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1163671364104359809615178711177255585490818780176401132826442502977552550556705773324555643835443220085126831006640145311885267992473137188887995343]) [5] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [2120727670658418095353427769906049051426465719681641706586636380894393134056061374230922781326681854878606403629320409667279291865197105259042278855775]) [1] [true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [4635063692950032355569681289467737912663860819268751539145408413493803926985790681886137272007757557768852666445170040765351288972080785038616264507925]) [0] [false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [4644472725409114072792656483489024799056964895953666264338959515752967323442945872291200272438491692784916937180464470915406608723425391373437393472125]) [0] [false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [2113360370726357086575569343585869188945890136064980050799746749996799550309800452508681765947354440570967070090006965021044847804403799892393066272375]) [1] [true]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [798292659727285823779479475894614829183173466068630499766427173108341301667427500795121310310965042963533581455329288896765691087978638180918618075]) [3] [false]

#time def tailRows014 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows015 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows016 : List Int :=
  decoded (raw_ints% [1883615454874582234123640007985379989492533007048783986122275557229416719766014172548217604562657840041535933307549245803820214640396517256116613975]) [0] [false]

#time def tailRows017 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows018 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows019 : List Int :=
  decoded (raw_ints% [848548359855544290594465337448093742523208544304335399330071299764913554634150561893193073411452502445738925025578141331592574432890230754840448275]) [0] [false]

#time def tailRows020 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows021 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows022 : List Int :=
  decoded (raw_ints% [72791286072524362966190713034942037815048050896355534069457949701774718597564353742483402154111369378760958288386336442598665881698910806023615075]) [2] [false]

#time def tailRows023 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows024 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows025 : List Int :=
  decoded (raw_ints% [60979045765195174770882040035574347280505569462808276542582467971332521558782911410833137277268909592031024446778434955816928138868378196582834925]) [1] [false]

#time def tailRows026 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows027 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows028 : List Int :=
  decoded (raw_ints% [36635155286189946577656516964443988396909447725620501640200599705999846294448769134448754454430662200207031044115559259773206428607407503013657875]) [0] [false]

#time def tailRows029 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows030 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows031 : List Int :=
  decoded (raw_ints% [13710446539460061790740520772136088807331541742761593671797098809313216471131584040863418386427255714866700064529617964078458362088822322176544675]) [0] [false]

#time def tailRows032 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows033 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows034 : List Int :=
  decoded (raw_ints% [1563452899197574108878044803526753986792610464756145289250811720863898439543286714069666023827059068873806249200813016082950786017027775167284225]) [1] [false]

#time def tailRows035 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows036 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows037 : List Int :=
  decoded (raw_ints% [253312870663978617413655027975775251991503221003660351504227065633598834598432428497936413511852479483647147605433395897091627977093777483246075]) [2] [false]

#time def tailRows038 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows039 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows040 : List Int :=
  decoded (raw_ints% [132596113856937519463168482899041069982792259165533388120978227384527442711266141471130093439308001837904437451186252947012116079314463918504225]) [0] [false]

#time def tailRows041 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows042 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows043 : List Int :=
  decoded (raw_ints% [35895114659664180781442019915154609559463373786161145229558908871675125675848924566857500822591814964590498140572511074067644086166459567326125]) [0] [false]

#time def tailRows044 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows045 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows046 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026, tailRows027, tailRows028, tailRows029, tailRows030, tailRows031, tailRows032, tailRows033, tailRows034, tailRows035, tailRows036, tailRows037, tailRows038, tailRows039, tailRows040, tailRows041, tailRows042, tailRows043, tailRows044, tailRows045, tailRows046]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 243713808082670679, 607961471833528647, 903606052351478391, 408653258148199, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 148605599185470525, 21287570016248979, 2657579116665153, 33492646265533, 34493884425]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 7, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 151387994194904603, 316775219116482765, 479454851877279743, 29647858210765, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 574818220719425045, 82182751500561625, 30784799536760355, 17884419880187, 34493884425]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 5, 0, 9] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 42752080057047641, 82153752508489405, 121632278287850089, 1287776777631, 2653375725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 11503129264860577, 9858052665717051, 13149481030992733, 382384666239, 2653375725]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 2, 0, 1, 0, 7] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 14506004138969, 3286080299633617, 1178500505039373, 16702287793, 241215975]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 7, 0, 2, 1, 7] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01

#time def chartRows041_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows041_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 7999856339602525, 1428740422078035, 2284494004056855, 40302108395, 241215975]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 1, 8] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows041 : List Int := chartRows041_p00 ++ chartRows041_p01

#time def chartRows042_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows042_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 3185008400933739, 5143448511010413, 7104202620437757, 19654382787, 241215975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows042 : List Int := chartRows042_p00 ++ chartRows042_p01

#time def chartRows043_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows043_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 10779199526665917, 1347097410982869, 3390769184895, 137214899495, 2653375725]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows043 : List Int := chartRows043_p00 ++ chartRows043_p01

#time def chartRows044_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows044_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 921127886614713, 5388403269205461, 3543418908064545, 270237044875, 2653375725]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows044 : List Int := chartRows044_p00 ++ chartRows044_p01

#time def chartRows045_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows045_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 68764961739507579, 22120174836938097, 19738301156030679, 5078031246511, 34493884425]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 1, 7] [true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows045 : List Int := chartRows045_p00 ++ chartRows045_p01

#time def chartRows046_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows046_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 18846794612867301, 24577310582145795, 30432132043502931, 2517392931665, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows046 : List Int := chartRows046_p00 ++ chartRows046_p01

#time def chartRows047_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows047_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 3704376525300633, 180768027125319, 2069991948020901, 6075502698933, 34493884425]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 1, 6] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows047 : List Int := chartRows047_p00 ++ chartRows047_p01

#time def chartRows048_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows048_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 2642697641777463, 1578738665705661, 3450924256520043, 38689526940519, 34493884425]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows048 : List Int := chartRows048_p00 ++ chartRows048_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040, chartRows041, chartRows042, chartRows043, chartRows044, chartRows045, chartRows046, chartRows047, chartRows048]

#time def graph : KernelGraph 48 47 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 4.3806 s provisional ×3 model; 7301 exact original rank units.
#time theorem checked : chart.check 50 48 basis.matrix = true := by decide +kernel
end C008

namespace C009
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

#time def chart : Chart := graph.chart chartRows
-- kcost: 7.2048 s provisional ×3 model; 12008 exact original rank units.
#time theorem checked : chart.check 50 48 basis.matrix = true := by decide +kernel
end C009

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P023
