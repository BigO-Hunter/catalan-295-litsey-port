module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C007
#time def pivTape : List (Fin 90) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]

#time def freeTape : List (Fin 90) :=
  []

#time def roleTape : List (Fin 90 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩, .inl ⟨27, by decide⟩, .inl ⟨28, by decide⟩, .inl ⟨29, by decide⟩, .inl ⟨30, by decide⟩, .inl ⟨31, by decide⟩, .inl ⟨32, by decide⟩, .inl ⟨33, by decide⟩, .inl ⟨34, by decide⟩, .inl ⟨35, by decide⟩, .inl ⟨36, by decide⟩, .inl ⟨37, by decide⟩, .inl ⟨38, by decide⟩, .inl ⟨39, by decide⟩, .inl ⟨40, by decide⟩, .inl ⟨41, by decide⟩, .inl ⟨42, by decide⟩, .inl ⟨43, by decide⟩, .inl ⟨44, by decide⟩, .inl ⟨45, by decide⟩, .inl ⟨46, by decide⟩, .inl ⟨47, by decide⟩, .inl ⟨48, by decide⟩, .inl ⟨49, by decide⟩, .inl ⟨50, by decide⟩, .inl ⟨51, by decide⟩, .inl ⟨52, by decide⟩, .inl ⟨53, by decide⟩, .inl ⟨54, by decide⟩, .inl ⟨55, by decide⟩, .inl ⟨56, by decide⟩, .inl ⟨57, by decide⟩, .inl ⟨58, by decide⟩, .inl ⟨59, by decide⟩, .inl ⟨60, by decide⟩, .inl ⟨61, by decide⟩, .inl ⟨62, by decide⟩, .inl ⟨63, by decide⟩, .inl ⟨64, by decide⟩, .inl ⟨65, by decide⟩, .inl ⟨66, by decide⟩, .inl ⟨67, by decide⟩, .inl ⟨68, by decide⟩, .inl ⟨69, by decide⟩, .inl ⟨70, by decide⟩, .inl ⟨71, by decide⟩, .inl ⟨72, by decide⟩, .inl ⟨73, by decide⟩, .inl ⟨74, by decide⟩, .inl ⟨75, by decide⟩, .inl ⟨76, by decide⟩, .inl ⟨77, by decide⟩, .inl ⟨78, by decide⟩, .inl ⟨79, by decide⟩, .inl ⟨80, by decide⟩, .inl ⟨81, by decide⟩, .inl ⟨82, by decide⟩, .inl ⟨83, by decide⟩, .inl ⟨84, by decide⟩, .inl ⟨85, by decide⟩, .inl ⟨86, by decide⟩, .inl ⟨87, by decide⟩, .inl ⟨88, by decide⟩, .inl ⟨89, by decide⟩]

#time def roles : GraphRoles 90 90 0 :=
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

#time def tailRows087 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows088 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows089 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026, tailRows027, tailRows028, tailRows029, tailRows030, tailRows031, tailRows032, tailRows033, tailRows034, tailRows035, tailRows036, tailRows037, tailRows038, tailRows039, tailRows040, tailRows041, tailRows042, tailRows043, tailRows044, tailRows045, tailRows046, tailRows047, tailRows048, tailRows049, tailRows050, tailRows051, tailRows052, tailRows053, tailRows054, tailRows055, tailRows056, tailRows057, tailRows058, tailRows059, tailRows060, tailRows061, tailRows062, tailRows063, tailRows064, tailRows065, tailRows066, tailRows067, tailRows068, tailRows069, tailRows070, tailRows071, tailRows072, tailRows073, tailRows074, tailRows075, tailRows076, tailRows077, tailRows078, tailRows079, tailRows080, tailRows081, tailRows082, tailRows083, tailRows084, tailRows085, tailRows086, tailRows087, tailRows088, tailRows089]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01 ++ chartRows000_p02

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [39840619758473101795147454508895, 2455874837944101245032727872797, 26094794331531496246694724626501, 194392357829205027332358844563, 276064867220418845574602316775, 13940217784770810575785088726957, 55211313747944667345811112345, 165641699735831642022817919835, 386495253208305820251609124265, 55211290931520813732001443095, 165642239724529510882980092085, 386495230391881966637799455015, 7420387589507696498324096312979, 276064281598873269486820806025, 21554996271856585470157725052499, 1766735655065361631197827393185, 10070663425100168672451777786339, 27208648206298920337283993972293, 15989136618499324098602048439701, 2650292850516610680591305503215, 2407164620172733605520126698731, 20759375668997982745798976870375, 53885883048897127721956415972465, 5797146346023530158310191513125, 171375427800843288057933220065895, 80387209825475320302604601978285, 97170757947901607991188815835605, 388333122193900807631425959057803, 58744772375973080167988402046715, 462537792046842487698170363288093, 35555954378674263112350962367415, 153972956184212743664410678539759]) [0, 1, 0, 0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 4, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2] [false, true, true, true, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [35401454950709324401924288962911, 136879423969553458460865850995321, 83479045138723972281415447422945, 50816234223404536384684117718457, 312716138523851046079572593927835, 393544739694001090179052725441525, 1595379000807049203762300097530045, 2429290281813480539303373167876695, 145758048246403101516741699081945, 1146627419530282381620645664274485, 30123042884973173803045141541011, 1642200802425478358945267716993645, 53991023903185472276747472906049, 1165617271543136041036115558168585, 25265876706510406304561132917901, 82970982994285414602800283303203, 473135839076304785756116111991441, 3020268283747065805199194515680695, 6463140653157415583545382877517029, 8111180281339181658335242134666115, 111967490592448594862888744768385, 1174903789105461289033743145157645, 105895214328135001902272415223175, 1272727999398028963284011904746355, 5361527099460353016506515587595, 821077545048848072285222646440283, 311613366720091412746200916124315, 7226715497446971067529059001237, 3814414037064966134921200536000605, 2011582180797363325856878681014777, 17414164549683141439806622655124301, 20147754394127611777990991637324623]) [4, 3, 2, 4, 0, 2, 0, 0, 1, 0, 2, 1, 6, 2, 1, 4, 0, 1, 0, 0, 3, 0, 4, 3, 11, 4, 3, 6, 0, 3, 0, 0] [false, false, true, false, false, false, true, true, false, true, true, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true]

#time def chartRows001_p02 : List Int :=
  decoded (raw_ints% [2567960570184600483936396871503345, 1080824192620495796736831553800283, 1787527121965616430111995050759455, 12101425670938158474563476913265515, 1638564918085598856356383767910135, 7398716384939052198681819910911995, 4582147917677865236511583331534475, 3683868786597498659592618013625, 12062869583204054715541974657500041, 17493439868818050320163802730382465, 37885453485484424882846413455196021, 41976662629485038220562046504341115, 3740360832763094739515195662982783, 7971660439203441377826341608354947, 2370175265690715630165789368097067, 12241611380333493950199121886979325, 3310400269737957617753876240047669, 7229153479807068209974674331604635, 5740340229999767781147961809405485, 880911162679781327849433758293885, 28289096406640374120032055906178645, 16675002538894778889699575439439215, 72027745642220418554238510426313565, 77767819490525154437659099234213959, 16808415946640838557736132287367675, 22549022558335638236611467098278251, 16483853522501149510460544783849, 753455356705962029802808125]) [1, 0, 2, 1, 4, 2, 1, 10, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 4, 0, 2, 0, 0, 1, 0, 1, 10] [true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01 ++ chartRows001_p02

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01 ++ chartRows002_p02

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01 ++ chartRows003_p02

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01 ++ chartRows004_p02

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01 ++ chartRows005_p02

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01 ++ chartRows006_p02

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01 ++ chartRows007_p02

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01 ++ chartRows008_p02

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01 ++ chartRows009_p02

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01 ++ chartRows010_p02

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01 ++ chartRows011_p02

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01 ++ chartRows012_p02

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01 ++ chartRows013_p02

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01 ++ chartRows014_p02

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01 ++ chartRows015_p02

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01 ++ chartRows016_p02

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01 ++ chartRows017_p02

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01 ++ chartRows018_p02

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01 ++ chartRows019_p02

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01 ++ chartRows020_p02

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01 ++ chartRows021_p02

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01 ++ chartRows022_p02

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01 ++ chartRows023_p02

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01 ++ chartRows024_p02

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p02 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01 ++ chartRows025_p02

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01 ++ chartRows026_p02

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01 ++ chartRows027_p02

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01 ++ chartRows028_p02

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01 ++ chartRows029_p02

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01 ++ chartRows030_p02

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01 ++ chartRows031_p02

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01 ++ chartRows032_p02

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01 ++ chartRows033_p02

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01 ++ chartRows034_p02

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01 ++ chartRows035_p02

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01 ++ chartRows036_p02

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01 ++ chartRows037_p02

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01 ++ chartRows038_p02

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01 ++ chartRows039_p02

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01 ++ chartRows040_p02

#time def chartRows041_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows041 : List Int := chartRows041_p00 ++ chartRows041_p01 ++ chartRows041_p02

#time def chartRows042_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows042 : List Int := chartRows042_p00 ++ chartRows042_p01 ++ chartRows042_p02

#time def chartRows043_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows043 : List Int := chartRows043_p00 ++ chartRows043_p01 ++ chartRows043_p02

#time def chartRows044_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044 : List Int := chartRows044_p00 ++ chartRows044_p01 ++ chartRows044_p02

#time def chartRows045_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045 : List Int := chartRows045_p00 ++ chartRows045_p01 ++ chartRows045_p02

#time def chartRows046_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046 : List Int := chartRows046_p00 ++ chartRows046_p01 ++ chartRows046_p02

#time def chartRows047_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows047 : List Int := chartRows047_p00 ++ chartRows047_p01 ++ chartRows047_p02

#time def chartRows048_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows048 : List Int := chartRows048_p00 ++ chartRows048_p01 ++ chartRows048_p02

#time def chartRows049_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows049 : List Int := chartRows049_p00 ++ chartRows049_p01 ++ chartRows049_p02

#time def chartRows050_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows050 : List Int := chartRows050_p00 ++ chartRows050_p01 ++ chartRows050_p02

#time def chartRows051_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows051 : List Int := chartRows051_p00 ++ chartRows051_p01 ++ chartRows051_p02

#time def chartRows052_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows052 : List Int := chartRows052_p00 ++ chartRows052_p01 ++ chartRows052_p02

#time def chartRows053_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows053 : List Int := chartRows053_p00 ++ chartRows053_p01 ++ chartRows053_p02

#time def chartRows054_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows054 : List Int := chartRows054_p00 ++ chartRows054_p01 ++ chartRows054_p02

#time def chartRows055_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055_p02 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows055 : List Int := chartRows055_p00 ++ chartRows055_p01 ++ chartRows055_p02

#time def chartRows056_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows056 : List Int := chartRows056_p00 ++ chartRows056_p01 ++ chartRows056_p02

#time def chartRows057_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows057 : List Int := chartRows057_p00 ++ chartRows057_p01 ++ chartRows057_p02

#time def chartRows058_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows058 : List Int := chartRows058_p00 ++ chartRows058_p01 ++ chartRows058_p02

#time def chartRows059_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows059_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows059_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows059 : List Int := chartRows059_p00 ++ chartRows059_p01 ++ chartRows059_p02

#time def chartRows060_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows060_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows060_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows060 : List Int := chartRows060_p00 ++ chartRows060_p01 ++ chartRows060_p02

#time def chartRows061_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows061_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows061_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows061 : List Int := chartRows061_p00 ++ chartRows061_p01 ++ chartRows061_p02

#time def chartRows062_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows062_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows062_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows062 : List Int := chartRows062_p00 ++ chartRows062_p01 ++ chartRows062_p02

#time def chartRows063_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows063_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows063_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows063 : List Int := chartRows063_p00 ++ chartRows063_p01 ++ chartRows063_p02

#time def chartRows064_p00 : List Int :=
  decoded (raw_ints% [2290817805439991849134348951129995, 1824858382727774232772932165940904895, 1842047781949884156337594579837932409, 20637341296227282809757367434947555, 1712624841623834601557658660862640243, 1727466929583349851545780678531877459, 13276635961357089282473055697749747, 1659759652357955970294873226461324455, 836457805514769098321896443982116301, 13282629992669320093083986637080307, 1659518297778406244427766438071641255, 836460802530425213727201909451781581, 20627882522634506067219428343491555, 1712890172328633250667209173009645683, 1727460000098788759681926662227626579, 2291906876342621995352926248947595, 1824541357959482292965521864819573695, 1842056785187021675667659158880932729, 113326892840877959195774113650661735, 2006254252500488866072383732874937843, 31698823407357242792417608007779961, 166031546421160453007849517661558093, 2277848929322994129748618319422220635, 577020784333225487729587635952534333, 59840740853122809980537891145056315, 2670380438185130678103781803521170215, 2713477647166553643848351626051920685, 172308486503487482513710871854884675, 3235300782972959089437224577743121675, 3297457583586019848797924934341915295, 502164219984754909118510703637383105, 4048848330213030538213468778360247615]) [6, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 6, 0, 1, 1, 0, 7, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows064_p01 : List Int :=
  decoded (raw_ints% [2072119388288874861471928690844533875, 742385387346385143001883209771011495, 5243957662911978725911267392292654095, 2694394191954444887532125647548731175, 562374818150416301013787538217828105, 7018389879598571110221001617444293595, 7255923407556107520093709581304130055, 435069526654887951037004000952470763, 9742956208115309134021567698035278935, 10120951150476491926269300661549669317, 2783435814681216355392328840856322075, 13979502306076778326813065632683825803, 3661166267944315021452411376553968611, 4558817873673096788156131065950792705, 20876699466840174555590883061460567235, 2748364845016446653669763176627873653, 973101378429551834960854855497459815, 32214773800769165479437589896486996623, 34330547661241084697201075322953460449, 6806591014708599216904605735947324009, 52015943576585833274338238437379281315, 55728540718094697810697125638827786987, 25087599721001412895086755502729248373, 86667501918437959214674435784065588695, 47214661234256654569796546306725841689, 47206724704903751114638540041856625755, 152366342460591484854685260448296274807, 83361823447209236574659194079018778753, 47526918353806381085714189101010395695, 275494400738052963673228595951492091715, 308984208306934986435385306401914974651, 24252885801310376555877031334873058495]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 4, 4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows064_p02 : List Int :=
  decoded (raw_ints% [532581689291042533540398773256379440367, 598061131425030761053829935282920234001, 433807321571178425395531632789646016207, 1051586746379985013461293598667429963555, 153236442425836524862047227343943839771, 969313101250888278957873661071175551669, 2267810975575756235122525304414963505195, 657252990557189725812445778153093071511, 615836089646021771625023867262626798945, 4928839151383538129292788242952132170231, 6061669422063734268707752242734055033493, 3045418364942266248353002743536930753935, 12121188409912104581122907180616992288315, 14615850510532353851913853198858423737143, 18261981071567970549654025117656221252905, 29292186070921668116116810191247578201711, 19484334155992428449136941901794253248959, 50645041413300557249677986431070466818831, 85169112696183986779739007651241877299935, 53937845398426692348802947676157597284827, 95835425787622472334768381308201829262677, 231872351724123897114828755915529445477035, 350191583785398886616820644399789319913839, 151669791706724916226218851297766403967505, 851852518997163765457886058116856511401351, 1148541602187543496191232812207258594309213, 1915353951723963895509893746274092249, 753455356705962029802808125]) [0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 0, 30] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows064 : List Int := chartRows064_p00 ++ chartRows064_p01 ++ chartRows064_p02

#time def chartRows065_p00 : List Int :=
  decoded (raw_ints% [156343206985671791233481678005449005, 1883609110073392469669478068730405683, 3805223368857634615823694315644758163, 87562260873479201926717530910603347, 1765271051798570354920734568908903475, 3561317900998483622663495106728705811, 28296928903307328221903498266448083, 1708484588326434065816043006909198989, 3445458711221697092514874077551654381, 28287476071814151537578213011525843, 1708677193991955698476927572376007309, 3445449258390203915830548792296732141, 87592080646821016035879303180826707, 1765059540470062368891199432932250675, 3561328815108839083404006308489084691, 156288322061617398402717791324975405, 1883861355285597730548686178737660723, 3805209217817277497842603402994886803, 241968551359104547061606606219118253, 2077636184593297165696635015582201485, 4203466091237999443306927800538980461, 356443567870469857611762719897508435, 2367798458003806824671899391175897229, 4801878210467573847980297126655607149, 515917343311526546112436318523450323, 2790523320334236880920160455377218355, 5674239121649570251704496165076565907, 748963079120769016433997842708908205, 3399633144626859916896772028222797875, 6939119544081865814250930326308924435, 1097429592554380942982618427973278765, 4288449478575774913788156140795034765]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows065_p01 : List Int :=
  decoded (raw_ints% [8785512215757015773667546596991111405, 1641916482976998252998502975339578835, 5594492329735621802862008884169355405, 11524858291288394969648668000303969005, 2504250742497431199162105589787885907, 7572282444529771419785162091474192435, 15671025516762824421809276565431433747, 3940459918958799533365069482726243885, 10602993814730484201186220063745127219, 22115736178219055154336451637945563539, 6347361182892759198829292435905945517, 15453202282447370486515301056926680205, 32403557280070613886530813556577752941, 10644097232478496662663515466635608915, 23297716180516002598844804935557018253, 49395015695441869748023621459119307373, 18290803569075698366392567432697741523, 36741396747404363811842331990197898035, 78329916496996064777079704358452657811, 33070413104939877483725853562556514733, 59879323318667399331629939800952501299, 129691133171011640627198125353706914067, 61146560443422135027563429677814628653, 102882222957284118779294039115310927501, 223908106719373653138487408594078057453, 120723594324092318573381217587935642323, 182172444205511669386756799156581758605, 405778261486888106739432055859828328429, 242246316118051801866320395284411617875, 344329411605468755926056474291182212147, 768748171929032227179133668732175588627, 530815581547810508582089186613005206317]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows065_p02 : List Int :=
  decoded (raw_ints% [666665076441615273119397589725404994355, 1541810069594894537627543250629592412819, 1166965426571259744509704199548185604269, 1405960574701089773090234847517192624781, 3239591077713964790719336636790783223405, 2904758269654468249604959580928017921107, 3000595929584134762138805988821776202893, 7311314773939692784834000417266986748781, 7075250584582210168175971669976696006099, 7215477114010026272300154009373228466995, 17291323628176371202614931668171700675987, 20760279654447314934830138655451014165165, 17151097098748555098490749328775168215091, 45126853867205896305621041993599410847251, 56810534013831981060013879984475704679981, 48736036422904656141960431320275256797325, 122697667535485192300465060633526129692397, 210127019308965592106700688004503299180499, 130772165126412517218518509297726577575053, 389635220858282765467179628622505133552877, 657774104231858962001780782083223463619411, 468990075040835840355361807329281855158323, 1257536344399107319575661098710231896352787, 3561817630304923452670211641347157692432429, 1446320373590130441222080073464173504813875, 5477128078935889734247653522140613052404627, 61899477747551662610268374900784487, 753455356705962029802808125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 30] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows065 : List Int := chartRows065_p00 ++ chartRows065_p01 ++ chartRows065_p02

#time def chartRows066_p00 : List Int :=
  decoded (raw_ints% [1277478946615555139572048528895935, 59506429316887067295729501577782315, 60115131866676578318225732670789439, 357892410670320898847166056399649, 55613918630003868782433769648212823, 56128604330764184443692971387398973, 459681618946913533224606835889743, 53780150746161932914174844675387931, 27118676534567993657539850162955317, 459802000363363312323333163144783, 53775192154216214649535342304653851, 27118736725276218547089213326582837, 357797511390106843936120330519329, 55619358747615386163468177327967063, 56128465496476227782246241138387773, 1277828003508244794061022966476735, 59499952336457924152513267592963115, 60115311549053144746112768393418559, 3976744844391527779103492290898455, 65841982775681344515956361059780943, 16661928100115290528334576654317621, 5879089449244878423303493366664917, 75406931714024035268927236756556935, 1195367917095274504933520191794279, 4288592795817388860239215048394915, 89358340572660858209170334526440611, 90959821734977224459527215738288603, 24455630915671482085597506889483, 109715674080563146150840957143716255, 112058290355435801007831569362493729, 18562371219502413545194610470328605, 139443472687956053520474028636101795]) [2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 7, 2, 0, 1, 10, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows066_p01 : List Int :=
  decoded (raw_ints% [71570972301881006690426051680118815, 27970687587554216045188500191587899, 183965158958572800331619399025030675, 94837501705409321485617607011077067, 5421423315881088446487575815344705, 251326223038172917701228029402453391, 261017077525421566588324320736499673, 34396506025649457046031322837898529, 357450705066767630619221825116061235, 373181476103769188252287572935054371, 113403178609441927797933751098303875, 526498271243368574069478612105641623, 69422208345563753767785496213644413, 191639117589476056563291898730167105, 811063419504535341810956829509276735, 215104990740857003625877404884406571, 170096839119461265390877976705257733, 1293054741601272800322646207026310043, 1392252758791826601848557471678308855, 154598639654705450521252619312251873, 2171838132460225464937980643151338599, 2350840995649570934715323902337831813, 1197869994321666872331018656710727177, 3766632976076560008662688116022340011, 2083552774295029804565676518148783241, 2363759550195910851772908410606838951, 6963318109746892954262055269994247307, 3864367546553818666617640051807566305, 1269701222398624276518313834757500195, 13221671176860203415754321758449695815, 15171299532898045291081443853251972341, 5493826990030685052723705584606471299]) [2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows066_p02 : List Int :=
  decoded (raw_ints% [27278537668124881378555076626114250427, 31237758402553912502602110361494915719, 26799915813969940598505801891525564783, 57172287097105683837543966435301466207, 17256332049146305801638830855558355775, 64307417615047167423779471312271790381, 134478200924004643772578284192216509559, 20016582703200291403605074578253847283, 92357286793663274757770514752419997287, 314401957557294353532661851684388627731, 409154652827976048168161097443142563219, 62339697258084091184510153584503898945, 873336495273310841834742402211576487855, 1092586804479975327159783355624013749353, 1802973810309622138565197439683444676213, 2309272269815985271436986766388513393971, 1697139096427135097600531011991744808563, 5580525224440077938122169231885558017939, 8085231736511799396095532160945355192707, 5388888613801985135944214347776246155639, 1841456025905457304336363867246843828961, 24631373167576297023925663693930745465727, 45821598866531365079392419803387551592593, 53617395381754034485529788184821420186341, 125938417394461066873622819664743360246211, 182519686044526750919833818048979893228651, 62670089759907688597369829728581309, 753455356705962029802808125]) [0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 2, 0, 1, 0, 25] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows066 : List Int := chartRows066_p00 ++ chartRows066_p01 ++ chartRows066_p02

#time def chartRows067_p00 : List Int :=
  decoded (raw_ints% [175408211884293030036833889503749, 1971995052227627876432718737661773, 3987006460471423026819481530248655, 97775375503389434690435567410323, 1839603196359502120349928903083133, 3713822873083740562092212073334583, 31511987041679428789553135169323, 1776444301220849007051847602841127, 3584535510538671698612223370754937, 31505499534282900100158184042283, 1776579222276143262770822632744487, 3584529023031275169922828419627897, 97795824948882671377145190767763, 1839455300289414807252163970925693, 3713830347514440741400131794437943, 175370630185376160168179603687941, 1972170872173908605525113014280013, 3986996802648699572945456588893647, 273490484671474963683548204972877, 2190196560660167127588523178301575, 4435857917505550696797184397554465, 406992631946143418959999931032835, 2519151841516858532892209424225767, 5116341034123169079440732533560177, 596405749517583587923726720707723, 3004181824552453965508523040367245, 6119739415586896086324459185300735, 879485215244519239089252518919485, 3711963340552025708739662865641213, 7595630380348998913337438424927943, 1311823666305084023996278289516645, 4763152255041492443687028078206215]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows067_p01 : List Int :=
  decoded (raw_ints% [9786939261898602176422969233364073, 2005965090051878083550675848027195, 6335610673162193756732219444674503, 13104728018255564283969923370907913, 3133067526079522551237043575038947, 8775082435145248610788379774260605, 18243760634386964918757642793974055, 5074673364845437353490389829708565, 12601745725321238859206306594752397, 26451501525311924823485076198721567, 8427101317581222379214964439801373, 18924429164836123317769159433677735, 39953276207738584556190430468231505, 14673118504880023736361146024153811, 29455948360483683617636235474355143, 63053496030199830671766540932186689, 26194276673114052725924802070136987, 48270666174596170790491451481985357, 103920891208193907134052489026477487, 49721885295284376937763894689888653, 81844501706711789069485839614629117, 179837053176592336797741185786503127, 96374923931974302996955302994664053, 147714436765164924666019240861762663, 325933862403851016732460383471055833, 202787768736357109636132659793759947, 274594349570660395063396445603957223, 625096555072182429365548346259479833, 431239706874657953349632431306598579, 553289974237879143938284560449282557, 1259124030683197492351313437359838359, 1029401285261701684854902538626795173]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows067_p02 : List Int :=
  decoded (raw_ints% [1137073763319976301762661308217154381, 2719765022819557130555848407293232111, 2430833191707430026741053464155411309, 2612092544761282513648089637702872903, 6179999499788688842151804410075438593, 6827155866433240790892351242708147747, 5998740146734836355244768236527976999, 15437988557929359659785209116938997649, 18170251563606382074811224618987412011, 16266404277627764095432792123119168397, 40435395987968982525488784978634557407, 64137856614922770881353756459672643677, 42339243273947600504867217474502801021, 122743504166498135481653766057294613095, 196144923282832660133657860514766509829, 144542117507473305858140305042464455751, 383026284064253566496665383031733766601, 1008694229599306865799005537545498662619, 434629089839612920772182938504035820679, 1587865436946393092429328781091998939049, 3639446700931610769309304972490126572291, 2161930576706087037456151380133461780989, 6236006367477310727537639291127624173959, 47214021314893694983935794331563780500661, 7713522491702834459390792883484288965261, 57089474383302616480782738595181531246911, 1040603668088929014214078854938101, 24305011506643936445251875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 25] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows067 : List Int := chartRows067_p00 ++ chartRows067_p01 ++ chartRows067_p02

#time def chartRows068_p00 : List Int :=
  decoded (raw_ints% [11555922855052592362069195470015, 1002387271472914378417671325099841, 1013561078426131775381868398208843, 12881087746946154733439694923667, 932287502538928433449511907557725, 941575211512029096466712226481449, 8251720435368608879451596850605, 899338569497345140550153765710505, 453780657791384089060190619891755, 8253101232446290248094881023405, 899280620797453997931705520155305, 453781348189922929744512261978155, 12878912246256213943418579150739, 932350974427130301542533289804125, 941573622104804577623956563281193, 11557920625330857844625351701695, 1002311918767503709479054153361217, 1013563129098640436889295128389451, 72522811906331980509883386838497, 1117277704432424027056538917031245, 141539702938286981097209990254341, 108342864327280183272373050010875, 1292403166392831631518587700715205, 328295824934977003139984089721025, 20032058622789263326201605805705, 1550649161741544760146031117074745, 1581782633049502302441922255340615, 118873928977223026810118363033423, 1933429042322088057957039086497765, 1979786959986262462671771827853101, 359586358705457255745679735122735, 2501640593559328974626978021342129]) [3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 3, 4, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows068_p01 : List Int :=
  decoded (raw_ints% [1288560588323082886018844144521341, 554036022421373585066503817235849, 3371774477143917080939758026988705, 1745371778886498306424935920700633, 441406500345381281724707987156085, 4717784683244823314892993290285525, 4927592580885132761365791632949285, 22525501084714500163523199881985, 6903026479906967334737421924237385, 7252037650997623335280692399708495, 2463405813079750322878247113815997, 10484312960931735356754932460073685, 2789268883374775417156106076492883, 4319707448101771448417971928724695, 16756649732225968626250410379501373, 560630899833769482497520104641007, 2009225072920087245307544301577827, 27763142753338821150426820174972465, 30296796534462743869568792483548227, 7650179248771165613636394166524465, 48904250898947364551171119204746605, 53634055323685424078071758022908465, 31529405919246139967495251626897675, 88964576743508146059517973507168185, 50231909870236947636419898991427535, 65890698359452378869299390439037029, 175021874575931924421152125712337305, 98941962009586207054817220024394887, 76958445946563347963786473855230295, 352527370181317661536715535263316301, 417691514271751488906506778198287393, 89388471186237247209047991072765409]) [2, 1, 0, 2, 2, 0, 1, 7, 0, 1, 1, 0, 3, 1, 0, 6, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows068_p02 : List Int :=
  decoded (raw_ints% [790689442148438708131443916554179665, 929162290909827173670271690199809619, 981688549486283084470001324502592665, 1782742909161113616881483392427562845, 141775295321316202936029061187091495, 2574336851397257139194650889520891315, 4717443640093571046011449214564550325, 1456107531506149867660279298254236975, 554315054973376903917076679103941133, 12080090314750142173660086950511128105, 17267807856995887072508994948200897343, 13392863213673228460301452288856496915, 40193607158389692896704356677216782837, 52922575163916374455785126391576949301, 134096171408641220198113009861960742887, 119222996024135969856071705261363103425, 106902236499952025787250520415625343009, 479428562122261506796181226493046592065, 576578292792954573689156396125059754385, 413664603265403389284397638593129010485, 3013896100479503247966916497276472117305, 2036937244513181997040796611233549471685, 7334549969612074781298809498232248847645, 3320075794368057889380254153053216291737, 24687747096628980557424488374336836692825, 39922948525515544392274675717210923416151, 1059784769846342144830145180088903, 24305011506643936445251875]) [0, 1, 1, 0, 5, 1, 0, 3, 5, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 0, 24] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows068 : List Int := chartRows068_p00 ++ chartRows068_p01 ++ chartRows068_p02

#time def chartRows069_p00 : List Int :=
  decoded (raw_ints% [3399345133597353742800753459315, 35476883844777094129883914768025, 71797635500570392335485229863877, 1884136925880888791241336548605, 32921406522195944462800561636537, 66514153441092149801443139855957, 605527474437156963093704501261, 31708609993015316547401241670815, 64024489040774104047108098806091, 605445160919669073377660790797, 31710351573321630536613152634015, 64024406727256616157392055095627, 1884396223782125829700841106685, 32919500314854654694156563252409, 66514248111958411060470556993109, 3398869183475808455284723220595, 35479144020885882196014834847385, 71797513519216345345456121320389, 5345196558785391781403342924835, 39717238681806271604726009693599, 80541579261477545582144187465819, 8048618786303776007074287531133, 46169537138456665758821520697055, 93935394606566713370621817921787, 11964687632695041307830334888109, 55814476254413823618874584755865, 113948701025565530685526440341029, 17968694418110041342997062824355, 70098912403846748374482190473273, 143882083076370613336353838053493, 27363302327805775655918573810195, 91751865090633906304868710404575]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows069_p01 : List Int :=
  decoded (raw_ints% [189214079822286430335269474688043, 42928274551687703383977723267885, 124825517059458299686319338093663, 259505656701779909375165771766123, 68941206266115330393832282287261, 177608414194009313072824156940345, 371375137519582943152975777321269, 115573836945789553643906518040723, 262707929591688960473983902668185, 555890180731487827190714577649253, 198946503122103143456847189994435, 408756088085588420360637193021791, 870410520799380524291468285684411, 362518958135735172678193880557085, 660600935835895247387678282657055, 1431875982057218840426509356235931, 677242284103049118639568443947725, 1133794004357058765717024954135961, 2471637224296003131744271680740741, 1365502508133670004471206500458307, 2015085504041993484666815170552505, 4514382016532722254855046625146773, 2801584075604454602184796105716531, 3864799020624398774659437955052575, 8681468600270846861511049231321611, 6398072641330188999086438672246605, 7618253655250902689036407381985567, 17881125317205490462782284009284747, 14607426443965876314468333726809405, 16660944303284776772832315299545785, 38886624402501555776337056408340757, 39170131224272723940613941670336435]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows069_p02 : List Int :=
  decoded (raw_ints% [36833106543182655317973074835604377, 92664182070740156031419331805486597, 101120706458729023725113499685337699, 95001206751830224654060198640218655, 232955019753741903697146773161160731, 339724393720257398094560082191751357, 239074519460640702768200074206279775, 673800119932728325516820355038249787, 1012503460955050608757572897332729325, 774449994192345020843180363023721369, 2026027974608036332368953334562730469, 4930037412887887173431565738966682595, 2264081441370741920283345868871738425, 7968568848450974114558091970862142389, 17456097639263032370202592210091608915, 10634524819968119367706311840957086559, 30354703900601893658192249919920433899, 212480034407410965211953400297483070573, 37176276719896806660688530289054956255, 260290835947275891240348242427495113387, 932417603601066020630725573567445585629, 435594593634790049791613112435923227705, 1405188473955752877083027216292423769589, 8825177733418136847172951782963588303405, 1902011483922028847922139677423946127513, 6487571655861317949459198993103718948187, 9399622579270968259785747915399, 838103845056687463629375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 24] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows069 : List Int := chartRows069_p00 ++ chartRows069_p01 ++ chartRows069_p02

#time def chartRows070_p00 : List Int :=
  decoded (raw_ints% [225393445903741842779097296585, 9051306475803591779625162228043, 9161928158393024024270167859819, 31215524589870850706589567697, 8370976057367488897798784305255, 8461417069866573533059256725073, 79737591706986971238581499983, 8052409688927724557014296061739, 4065977640720309878083979341757, 79746596800463666590414919759, 8052025690539541012844458305323, 4065982143267048225759896051645, 31211979679068932156597634769, 8371396076129579223375955740775, 8461406720767111575362988101201, 225419459153983684896608444105, 9050809040269746841855582617931, 9161941476507630402408986067563, 713929839652934560602609648463, 10174751749361448702548823293615, 2581677558617133083201203151059, 1079643633743596521928624085069, 11906528398881485084266021211783, 1515035463483132926917005792221, 811480110600731625788822680369, 14493326284335834790263319633891, 14822887562810123188842315783575, 613398374291056208502483422251, 18398369283687338090576602654735, 18899441281175811274429894833317, 3799882275277354853424136170445, 24307700272992734126303054389907]) [2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows070_p01 : List Int :=
  decoded (raw_ints% [12576458526808695480931982346383, 6010142514618301020561495752171, 33597898384796757504273147336515, 17481470921756523417924798307691, 2473397803191559132341811157807, 48348270331465938208549037398591, 50866675570897584385778336998781, 8361929374706972777247794360003, 73172263235861703621742125861427, 77484125533077766469641170350015, 29852201864555551934204156535403, 115243705329121720426531392278615, 7753761634190453997396307225339, 54716856752282836783834447362665, 192581070694083911358558752003039, 52157311190971413169094879875873, 53965474378893266040677672268331, 334111132338253067561869181729275, 371277050273955021541569311402819, 6790916507258980368865474487543, 624304865725230039683980130149687, 696517327264028925426619839540857, 485029899811784972870831594985577, 1203348445267402554776649916134779, 699428277654050635050573309063905, 1087718220531208454349618929807111, 2564424464972369931167306510091995, 1485802337825547348660798571460249, 177963152983644768935036191088255, 5554221327392236372175125635363223, 6906733343920619454631795130139689, 3615925141234197419943423217711037]) [2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 1, 0, 3, 2, 0, 1, 6, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows070_p02 : List Int :=
  decoded (raw_ints% [13954066255925635143009622739740315, 16985994074127330597479220622973843, 23678757432681870856047499636535047, 34481622457265815731722511377051519, 11974150447319399073353391673732741, 69597003449472371631111815275793669, 108669095986653118567199621285880503, 4411636333482244961892902550226865, 164675582749495352039746971292326181, 312869636255155302256169772480226195, 540120531619894914491178639467705711, 288566714470511651530719416860549765, 1426073757982615934885175391624489951, 2023738555000932224693550249494557133, 13588085254089532594160298861918754693, 4929937067783341726747680442249022435, 8383045333486255712488363389427755443, 59366991269125020171832178292949939619, 55778414774340746311526370839299508723, 44860583595093532095484601966862102599, 134573468189507101093343915231002947703, 242397902144283422414076393614048780911, 389205714298716320010574278697337645995, 1577350114727259065554871495031368497993, 2097397076257772871181976272856747654525, 4082199816511262855493692929684086432793, 9612715050200507709828362452989, 838103845056687463629375]) [0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 0, 22] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows070 : List Int := chartRows070_p00 ++ chartRows070_p01 ++ chartRows070_p02

#time def chartRows071_p00 : List Int :=
  decoded (raw_ints% [321800669515735209504236710045, 3098872568701022304020381871065, 6278851119104355357648378365407, 177163906328818059746529298251, 2858177880887597844123759784297, 5779886543259802088397612357111, 56759557530106191425155115539, 2744544756043386184527323274563, 5545963079400877837225927943321, 56754248593853099545028258323, 2744658765827385461273449553219, 5545957770464624745345801086105, 177180621198458061177109448523, 2858053253231092383617379791209, 5779892640256935906067938792951, 321770020474330050896682805405, 3099020008224301583627668450265, 6278843281929724018141731046879, 511015383160682112959962837493, 3501593294179752485410745402019, 7111628685564736181998376689777, 780198980409205129698129879867, 4121050774545665809547594125251, 8402843049134623424656469407137, 1179480073677273970202749278291, 5061991254998162744807005161753, 10362522103221102524557348565295, 1810061874030203938458578901861, 6480010921900213749953092681833, 13352064050928580433218676745447, 2824677718002510947085914236125, 8682115003058570621724162965475]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows071_p01 : List Int :=
  decoded (raw_ints% [17986803642961295318763169883433, 4569429647404401631790422908291, 12129366357905235644124921154083, 25380911008368207897639507027849, 7585106396803022211060983963259, 17820974297867373885305008782057, 37535447052575631740490913899399, 13259221629857101188508177220877, 27299579151511280066246889080601, 58379775079235755140060075083535, 23829459516143229368847300014757, 44339417557581576262321363223811, 95468456225236085697415552319169, 45952684901496905559181794667755, 74958498183797738803941489110115, 165250600642876220625444647001681, 90714502152663009246111087697347, 136244787360575387380684952559321, 301917787697036135430737529366783, 197718793550652507621744313592213, 256387502489123757296163664504809, 590351083400351652298592930656343, 435116709048779839190838720196429, 531682374461880402624173579743747, 1223186585999783999111175964444985, 1111005080817776663022248931202419, 1126620920586683435677841104897667, 2769308375866340501324263615843833, 2773524108700904295729207740631595, 2753692536097433728668671442148585, 6653837565385021460075720287677847, 8842699306778971504439925205114109]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows071_p02 : List Int :=
  decoded (raw_ints% [6673669137988492027136256586160857, 18270060980864897260244853233423551, 25610812564175400918750041045319381, 20439091149655376737548521852376803, 52723572851819269683434819483857041, 117679144873829111311322749928082203, 57895294266339293864636338676799619, 196013530289823781913507610457258625, 407959591229405399051823672704747443, 255797380897313599360194021708541209, 721652266393058292276654033090088271, 4639156979241498643892226852485481285, 873814476725150091968283684086294505, 5768768836863962335220704558280316999, 20173777283824103192610719495330354493, 9534111339380310887144647726679503779, 30581703099929564171723650906096152777, 174901865246648765237112991760616492573, 41221369044373356477189722674747003491, 124146384862895097872778621359189985303, 1031777597967432127673296236141384455589, 340269619153917219587081335794553481367, 1330825848076975990783187849261190933465, 1941465627952068943649527062109044887661, 2022333826890490898869402749608021907687, 421137818092339174806957023293530501393, 1650162947155022641788153768863, 279367948352229154543125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 22] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, false, false]

#time def chartRows071 : List Int := chartRows071_p00 ++ chartRows071_p01 ++ chartRows071_p02

#time def chartRows072_p00 : List Int :=
  decoded (raw_ints% [10737362361405557761381829093, 1586595089094913743806232947971, 1608024691318492850161563401933, 23625912939750283882218624299, 1457656495759583032334784590407, 1474873966547747820306071520591, 15029977733601582926823521191, 1397587785576911472748483953579, 706296081467322834807405375401, 15031161800749477700854950823, 1397536584825176700627490505643, 706296673500896782194421090217, 23624049402157682099322768683, 1457712432779909383551903756871, 1474872607606858406288342668623, 10738216231803435827317047269, 1586528980042438157422072655107, 1608026436265601257105524584141, 137565358624959160915771310459, 1801335352197619330026049269479, 114468595296561744039989517047, 211050549514325322279598752073, 2136790414542274801085157896943, 545028358221068096958800583821, 80853930561225113345655818229, 2645537550254920619144444277771, 2714579704643498163497424360273, 250000969730852804721203306451, 3430453303521876614615650988607, 3537997366350104226322454246091, 796710359637818793373756983069, 4645545308101743056914070729379]) [4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 5, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows072_p01 : List Int :=
  decoded (raw_ints% [2417354832724814314569308921031, 1300178334890013768881318895723, 6617294742073151788110678920883, 3465799179988730595696846860427, 1113539111270686808834737695273, 9846258647661798132439346312271, 10458854917408848577944488007123, 981143341935428268728729330313, 15525607632238646258788580483067, 16610506507691935270528880718921, 7398127460559879282882204796479, 25544552118628650432099015597279, 6983301833998381907081500709163, 14312713510500555728909255436813, 45118117474478163390317399668983, 6205506038381745330014682883743, 1903166383657574738128693572781, 82795406160630873347736037344531, 94407423956075714179085815671253, 32857556940775286370118638590161, 166920766028562946630553788326967, 190573199976147482729382190016071, 163567738384442873217606703554529, 345655861686833164308685146065819, 209928026121070464343613085375461, 401039564757585415290719284825903, 821191719566334439500980602545083, 492231677692084608597776079565677, 622071133025648665843107882162983, 1949814120717174825471562285369431, 2629645186193051964172487208283223, 110872062235978355525824656488521]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 4, 5, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 6] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows072_p02 : List Int :=
  decoded (raw_ints% [5797760783771523766245843659848947, 7421693443795656672685091980241861, 15814977807406524460061577496315139, 16141438086922404332777118315900119, 3348072155344186063696632310523709, 54195770803761943913099311121363153, 69057672013397621606492153645109503, 24198831463480489220683486775466991, 148650866000521188802969423650169459, 232924521301970179985174362801352731, 745594560659768656007710952823908953, 1286357337705281149261582777225003471, 2447471528021736642454002932047820847, 3912912700072415709742754201874593731, 21282843731945893393374698996731685211, 10523783222944219374077836580601380499, 7398608178231457692554389620203542269, 126450491107270992398205178392184193037, 82683903399761836931044793054878919997, 81265275597839900588344328314661481393, 110410219505261632922896894983949945893, 495278181206139750218742876988135391649, 68160603292427527729100045053607264037, 535877430283408025551247322492538762503, 800597852642331226452130366816720647147, 2296169556851727840321683034884447677761, 1693923590209737312252618034677, 279367948352229154543125]) [0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 0, 21] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows072 : List Int := chartRows072_p00 ++ chartRows072_p01 ++ chartRows072_p02

#time def chartRows073_p00 : List Int :=
  decoded (raw_ints% [37005867395668692696406897245, 326472719183857725533281393899, 662445074405540783851241414899, 20209159039676502952742509507, 298966487826014365621553123755, 605230047970195588202092008147, 6451411495728173589298439715, 286054401104504719627796374885, 578569477434790911660051058925, 6450985753958015460583605795, 286063664834558018442956244325, 578569051693020753531336225005, 20210498843906545871844555715, 298956372612420750548963586475, 605230536290885314863764386515, 37003412865442917073831137885, 326484662522371110186645355755, 662444448000234777809440080115, 59453232954487500062568834685, 372963198343306584696625862245, 758901093820165194945840052685, 92285833062115644499361292355, 445391128431346110311783025125, 910640159836768339507770179725, 142336286787214990962789184355, 557534864467537873695348446955, 1145262279686098974969920656435, 224202742490235565426250791677, 730063702005776092237361393835, 1511801308963549531358960632467, 360284996770289099518699927965, 1005940349448009004547850030309]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows073_p01 : List Int :=
  decoded (raw_ints% [2096289048224074196303911352109, 605115892250928039655632776163, 1450633695546354291274761249765, 3061689937245291335478244056237, 1045465718966224534999652829315, 2216172133949865083859115582635, 4712271548462443910133529661715, 1925811663949359736421290840605, 3541565133478803361274066908395, 7683548931378028181554473331635, 3648609669085952581534791702333, 6067795461848584556701697263845, 13257970264413340499510555874573, 7571568787736291852174732287235, 10838784471650708524343650313061, 24478148721235584933220079864141, 16008401821723647695277306421027, 21210933037321168261051161838315, 48058119330695524480672118572403, 38808407253837310941892514020285, 42855588115098003914898263155115, 102874928406256483117841939013715, 93358734326093748387754438816605, 98827747544995790144836189878885, 235042069986187542447488891850605, 281555899445248075806234158528419, 229573056767285500690407140788325, 609956703757529366641477489195629, 789813379512622966165098002279235, 661939546435491941757304506935723, 1681325982715400408612809650003283, 3411870674997243481201050226052061]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows073_p02 : List Int :=
  decoded (raw_ints% [1809199815792531433020603145346795, 5883010037225266855978957878334579, 11548822004263616849496713818485245, 7485680896429978904159404959039845, 20843702716486127186676721922871885, 122083869963190480877206964052791235, 24906843824319765132014030782317285, 154476394683940224913380399794148365, 525382449761378407637618460783194339, 251653420822810940658573333064622315, 801942714408509113428205824630133939, 4137647219084375576054969171893270915, 1075671743347076580407250952348705963, 2810322054914488054989144886479942637, 24775553504022376853345967121873017059, 8023641017345940211451365010721919515, 31723522778021240484390081180246230611, 39907523691768042263553357215294474595, 48475435264697677126284683291397328155, 16591552590275575074182691086824773075, 403411856746182252746188125912961139715, 71791406366190144315655349419867029675, 426727827847674719935558792041430841235, 112720745465934368073480004971150237795, 758348278227666828366091568534524951275, 717418939127922604608266912983241743155, 43715683862575592284228019509, 55873589670445830908625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 21] [true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows073 : List Int := chartRows073_p00 ++ chartRows073_p01 ++ chartRows073_p02

#time def chartRows074_p00 : List Int :=
  decoded (raw_ints% [1243573577765524729895863433, 41933509517870687748172218497, 42565680237374328196998772069, 339193336869043412295438129, 38223556645815869726241871909, 38721759734367105088025292687, 429548653346563473731775149, 36506416127965993151445208433, 18467718866772183982555882511, 429572729557247593492692653, 36505362032429615831314771313, 18467730904877526042436341263, 339174398935606255108905009, 38224707046194983525415979045, 38721732135054724698800995215, 1243642938652731641345373833, 41932152415399315913057251457, 42565715608102613001927362917, 4036931843362954225502915477, 48173850555416836656178969709, 12272483332192757627530256515, 6301068243820417922392976079, 58079879788851132815068913365, 3714245838497150166126057351, 4941727207805249196673010797, 73378123530698508345750874025, 75612456075385318973755915289, 1962162389168379359185675373, 97613697451293126388452999741, 101193209604342852240587339867, 25902722982747663033386308407, 136167319984086647839692485961]) [2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 5, 2, 0, 1, 4, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows074_p01 : List Int :=
  decoded (raw_ints% [71396615850218775073729525629, 43910308676782033383653432337, 201224589382283778521998233369, 106303131679983623282249396001, 4941473112443679468607201695, 311808554691214781374306215309, 335580141835848151445867451459, 73324059489818561129095669887, 517478868578679264512859141849, 561291830614584145201774018353, 296730723220645426018586377081, 898401030609763270407071574405, 125583834101858336684818966901, 614183520408795846831110838707, 1704401761461260968587204650173, 478896229111076991582062237749, 724610308018182364451417392995, 3355135112244946657731514929233, 3978989052889468542062194575693, 854366737675470841510485925925, 7501284225606719884198543794133, 8845676619627716637006973065383, 10010962160273646835210955836315, 17025002915052480121899289744033, 11137052865301623419129936302699, 27598375718896145443397031932661, 47545132866701307225042367139393, 29941721804886519558433930187187, 28854566480268447267617542099079, 127418505790637061895487417474677, 202900085249742973630735060703351, 192789914154891604209154579572341]) [2, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows074_p02 : List Int :=
  decoded (raw_ints% [509218196550996463506923040724657, 703898179480599971119514388244349, 3921737201661647362493373532443357, 1669737819029769895568724054053405, 1252803802363007635507799269958097, 16779092405939651080819647434493719, 16196167003197585913480417170498085, 3214005602131666123168027255846183, 62743187094061592672474933121874087, 68786107442788374218847313792028281, 82995236965130205278786000762484991, 11840904541374642468315192129498813, 485749329749295155466319047804494611, 966299501801230508595908163294157197, 1117808543227422004127342706382289023, 2962485455149120097669841871359667847, 303154424610892811220368876599896103, 11832384225197982033943384098580708697, 3985484843160392861043051777724661481, 6171941959601809207814994525881602757, 284426720280248876967321252570150423, 44367051445642808038103694522963166941, 21900854382159609433834803129782710827, 57429611059145224139924253326495134869, 5116170205807571201911228304520152055, 95233781498372829861752273543768762295, 45052827392905377656790498935, 55873589670445830908625]) [0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 7, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 0, 18] [true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows074 : List Int := chartRows074_p00 ++ chartRows074_p01 ++ chartRows074_p02

#time def chartRows075_p00 : List Int :=
  decoded (raw_ints% [234684427340300858274530575, 1880565499178813103030500511, 3822725041675604207352575261, 126909234355111964019780249, 1707475115156490246047544175, 3461131379980191385058264437, 40343068527181293973299713, 1626747030468589174990940013, 3293879077097898127065184475, 40341163261920999664929281, 1626788978102127658100944749, 3293877171832637832756814043, 126915227774432851669430937, 1707429356992431174320798575, 3461133562868991684091174261, 234673455936760560359476495, 1880619433650993361439806623, 3822722246580185096120081693, 382357783995829136803807943, 2176776268865952295039751565, 4439753486512774793283366131, 605603530137481575330891113, 2645335001642651635047422509, 5427714800646085505418065187, 956969178494273365231728353, 3387983329140915445701533791, 6990287509277840445980684653, 1556652408458776319406056983, 4559273358631198365510879215, 9503909096230890130618469989, 2592661104683827939201230575, 6501288146058468084513647757]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows075_p01 : List Int :=
  decoded (raw_ints% [13653222609373494389225757547, 4565228037579068065105671537, 9744595567998854243913340365, 20811111751636390393532659659, 8287273097291276881523908041, 15631744221216604214724990831, 33663612886506735340162239237, 16342057938673163896736704127, 26319141762581408006961156447, 58292943922471176118422851405, 33084385530602719339483523191, 48315860098562932008198399085, 107719387391747059354643078723, 75918391062837714700223426585, 92487912823786846685928202829, 216722163985187493394350028499, 175300840557417275656245486929, 200152642224238361408645252255, 467941395605442483750818942013, 498288298724586066166573378631, 443089593938621397998419176687, 1141530534887445825573637807573, 1348547039640233866765564362079, 1196729239673410493741792009517, 2988365873252265758505775548283, 5453501980384087030732410270561, 3140183673219089131529547900845, 9790414893276586656003750180923, 17964369758983651304879098311545, 12103733200441584555206612550639, 33208286632644324991615258763029, 175528690895254941380469913316719]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows075_p02 : List Int :=
  decoded (raw_ints% [39068923191186391741287744523935, 226701347286882917676964270391293, 746290454238801851335869182292903, 363161114990951467316146439184077, 1148520492420939710393303366000915, 5285418250964016485206598461332151, 1531649831668790094413026109109741, 3390607304304274923477425913038333, 32219076698603769670879315376875967, 10207675386937081503097050483480225, 40895102253872061079563339751246451, 43144445571450453162348653966915575, 62906503565538749247345604644642193, 29969733381025377588094001161206843, 481502891456604540466127398358577487, 76081215755963824821600257450350925, 494677603647029616040382051164286219, 50330642589366059048797562078587951, 900099279347670331684909192072512781, 925849852514268097457711887444275755, 4479427690214943604830129937720687703, 24580069422768293275994866706824977, 3603908480290041566421215612354999899, 2215718974368197033472203086331924001, 8058756101082216877975350683368862625, 10299055144873182204723548636407611603, 1014352367253976266406776459, 2429286507410688300375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 18] [true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, true, false, true, false, false]

#time def chartRows075 : List Int := chartRows075_p00 ++ chartRows075_p01 ++ chartRows075_p02

#time def chartRows076_p00 : List Int :=
  decoded (raw_ints% [15904899503972047984236715, 970021800834685845181315135, 986546180761142314792258893, 17178589105736357794270833, 875831364655822400529308931, 888569404533781407266770367, 10814391640425305592021011, 832593087988794982827148471, 421698917340941693043103845, 10814827329547863072730643, 832573798094121178161224887, 421699135185502971783458661, 17177903955915464930169201, 875852397306986435118071043, 888568905612384736499986367, 15905526388984097524229035, 969997029741444897602578495, 986546819080152056457240909, 104978278207059784786706511, 1130340819530731995505735603, 144393400355393528917607945, 167334397157279849706856757, 1389910142569684036749404539, 356864969551871966458606707, 16885477132854695466524247, 1799678408159851394333162631, 1864961909490442843005671537, 221771195785937786516156893, 2470580679072384546606956347, 2578671935187993543502373275, 765008735892847801793287025, 3573847974447353686462417775]) [3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 3, 5, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows076_p01 : List Int :=
  decoded (raw_ints% [1893611531326358459163987043, 1359666147857450465445544087, 5530615622643775753780104447, 2955948973201507592783402599, 1306471101227016674885584319, 9012512565877155548244594123, 9884506296714499000783517923, 646344602638043412690002713, 15982384432459909152864778999, 17668205320272879652074708265, 11531508543838831924503467219, 29695539850294544754324680939, 8592617671304014719524549297, 26046506951652205737793642425, 62108418607815236850878647875, 4496780386294193533774706677, 17943314406616460558048257763, 133881567656903367705499250639, 169768250758825144510381980309, 95238343722285415274201684523, 349201449113678605779650772083, 432018195829861817290978380407, 743966694970482953037862041589, 895788317435186689899112726823, 683230789122457800438621895521, 2414101964270250040945694931483, 3325068228995610417931098938439, 2262265118742824297430400382057, 11311376023263510441858170783245, 10552196174516186853681892452755, 29561384248282919519522837262087, 23882952644892092113724716156729]) [2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 3, 1, 0, 5, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows076_p02 : List Int :=
  decoded (raw_ints% [93816076415103693952796465204399, 147715946874378308858138043455493, 638736273780107420837796451485609, 392679438492789660673277350960419, 6179508067596261617574367865675, 3934098445644302168197771516976323, 2461129018705325989398389340738037, 1242080808937642583140081877966283, 591547260912950519778160639670901, 15343714344084419012117808716944873, 4170043594091268342532813911474247, 28080238043039714396162598211769465, 16468383330509090643502751128730795, 56722810579291764608017667629431891, 898276247622118716142287042934407, 209298190000233296157182976977210847, 55992505208874537342100288505018207, 499740604059554048520137945806178657, 12875278340020615778933602956993167, 194326934944713546276039827919538325, 141628105942274627432876482278376357, 1789664226237982897923368806247503781, 1171650685833530395937970566202008021, 12875282124669352351801196495644079, 1120149569198176403684078255270017689, 1841165326197274551257382772126123489, 1050165778777030506729205753, 2429286507410688300375]) [0, 1, 1, 0, 7, 1, 0, 3, 4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 9, 0, 1, 0, 17] [true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, true, true, false, true, false, false, false, false, false, true]

#time def chartRows076 : List Int := chartRows076_p00 ++ chartRows076_p01 ++ chartRows076_p02

#time def chartRows077_p00 : List Int :=
  decoded (raw_ints% [139404506962373816157868337, 1004010978833118523940733531, 2045608945990368904303768071, 74471783028691370315522751, 902193460194876564205166203, 1831732655999303717830376983, 23554114875211190208851663, 855067412775735783309688029, 1733706758095401157306002569, 23553314184931991627047631, 855085230444454183787462877, 1733705957405121958724198537, 74474300864158502312246463, 902174041145599766563783291, 1831733572454212452663492631, 139399901079506463024358193, 1004033832172771188411955803, 2045607774397877418000097287, 231056671694941541447487457, 1180973843304612692612499677, 2416064347172325422471942937, 375290753495371291002357183, 1466147175562654271306930717, 3022411772362638254921787577, 611080092193790283855135983, 1931555350295355274617214043, 4008782618051799829779280743, 1035463292374766644851996897, 2688307359950234839017202683, 5655326002620356758486413623, 1803610885850450920736842833, 4002481935044888564321207837]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows077_p01 : List Int :=
  decoded (raw_ints% [8494400180845574324075253353, 3378529831483659173155741423, 6295529131651136680490888349, 13676540898179684417967837609, 6531255937099567803337349471, 10759541598012206910632690683, 23586326666762911394460928503, 14145696092750469231796248657, 19358041005850272287165587291, 44263278696612948429594526631, 31219126139601047083965307009, 39050933783513145374225187997, 89628100928964464745356082297, 83307692942482973955225358431, 81796293285052366455096201309, 204154920011048485784546747737, 216527778568600156954919801871, 205666319668479093284675904859, 503990391522131616694691908039, 815747592739412017055517938561, 514851850422252680364935805051, 1536265762830143790705129648471, 2604591256013667420959895481969, 1837161505147303127395711781981, 4956604611583223228720543069001, 23366741204711256024327337657359, 5724034362449587522284726768989, 30927937072308146674007776208329, 97945951766821476571727135348479, 48570643914569815176050387096699, 152240630043840879270062249214167, 616113446319971832175956251343759]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true]

#time def chartRows077_p02 : List Int :=
  decoded (raw_ints% [201615937896092540665738997465947, 365926864509309476334166866781113, 3838566495026489839103707527045087, 1183656248725373849175862115590819, 4820606805855771147613830645169959, 4093642107032263298729427763932159, 7475517052156887137541676056624227, 4565531193849997687988110408282887, 52226378223114594048869597032483887, 7003627965339152748282993412273499, 51754489136296859659610914388133159, 3834103188429338876893333984075041, 96977239394072300960197518008343547, 107814970547840792585373845404692087, 443580125092794321096103996442239087, 14671834342197830502069661380423581, 331931051356524189633836817053471959, 284154480639261746071428356691394001, 790183010791516341232010474876134627, 1059665657088580256801369170187105047, 2796331637215540363853195705532818847, 553637126936325661640787052002364421, 1452511499487698360980398178654319799, 2871187935347907995527028886260416401, 4802480263639564386474380936189503067, 7120031072051146720360622770447555047, 273126681619092840057704551, 2429286507410688300375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 17] [true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows077 : List Int := chartRows077_p00 ++ chartRows077_p01 ++ chartRows077_p02

#time def chartRows078_p00 : List Int :=
  decoded (raw_ints% [9543896981426235078367285, 260189135098867390194205675, 265275667117357226868726355, 4971038561776038635615, 232186611210142123229777895, 236007186179987429586252265, 3181088592959515504992255, 219466387200798081691247595, 111322705306255293477760245, 3181180936612179078183135, 219462256838304061209808875, 111322751478081625264355685, 318137395019470206365987, 232191110947246798003980135, 236007080533398476210606089, 9544162450595337806918245, 260183843400796247624655211, 265275802075212198428154163, 32156962801131635100727951, 308544410552009500459326095, 79130272444383627285679651, 52617348402487723036864845, 388811694605322788027567015, 50161925122644233410038925, 44074694989695782077779445, 519013804161960392606785475, 542062139363033154472735135, 37721524031848928089671589, 741409254522889044649802575, 781097625469820430986980381, 275829570970367909688623485, 1122558188671543242041530899]) [2, 0, 1, 12, 0, 1, 1, 0, 2, 1, 0, 2, 6, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows078_p01 : List Int :=
  decoded (raw_ints% [603906646283792026517145111, 520864431807236523102980059, 1844727538404360683404296515, 1002253647672594242912946883, 273792739838621923073558525, 3206015915900489334453451135, 3620542686506912701223107925, 1179629798812093993919433615, 6225411375822311452581232915, 7074973243485588381356209255, 6090628523673429681037021963, 12643054306397241285808920055, 970303835298950378139506153, 15483854207900528564436959945, 30587925470516030176729320767, 9274836024089291073926520089, 28095221325814445273795308831, 74578471137999355543556759835, 108773640955886583407733657963, 22039885646471765805787727365, 255349696077031592367091791415, 341283168779289600401626094545, 1511404140149348388501438000505, 779854811825095861328764035515, 1014503197050206057674682956985, 6284406426594079478564365224023, 6300966256674425146372843793435, 4912408480421919991207584569249, 4630834182060595444679669793135, 25917480518201413775586224931607, 20937450069046844096457823982559, 116894396194073010185137892489799]) [2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 5, 1, 0, 3, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true]

#time def chartRows078_p02 : List Int :=
  decoded (raw_ints% [141885727569264629083376589586885, 291772915913677628024170967307237, 217345525632346194746001133154055, 909237689034382667705516914986785, 77054045667369363412111404783195, 3024238200178868147697124905492165, 727496374960120149900627943029335, 91667735723179277774833763109795, 247742007899125902788813521267785, 11187715111681089923082982706981875, 6453089759118856842069432367541175, 6114902332550445584441615961935185, 2709432438153127372211136113171615, 17511035555284673690119404437663995, 17520023912858374638731128392804875, 86650722209126039427982872683981085, 29745334399172415333308498339104805, 147046968669648840384963381729733715, 67370663213280371182713377458047885, 35018137979222817539807628329359615, 40422397244435124662040033071029255, 501537152469469322111870654234953775, 378772833605834974112738770672569965, 357214224359181919263871502794381341, 579387692697681623409927151678420195, 173966026134788365766844102632075697, 284363461080209697025460925, 2429286507410688300375]) [0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 0, 15] [false, true, true, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true]

#time def chartRows078 : List Int := chartRows078_p00 ++ chartRows078_p01 ++ chartRows078_p02

#time def chartRows079_p00 : List Int :=
  decoded (raw_ints% [42351591930552678843637679, 270551520157247747950144699, 552909242204501361395381333, 22276490958409110051651689, 240006130116700934601598955, 488281159315539572500091965, 7001874315500950241023777, 225998538240429527846841321, 459002794041629512207416499, 7001703285518181369621601, 226002381485699034119551401, 459002623011646743336014323, 22277028601930696953621929, 240001944811465890586084523, 488281354899095621659257853, 42350609032510220522503919, 270556438689560428026795259, 552908992533536539135383701, 71725838901315202797396503, 324703162876486331631092361, 666985440467361962455284123, 120335511593527628136475257, 414008116492190833621588265, 859046790962204793389155883, 203544372727369137699160033, 565374186063541587904042875, 1182926675283101559224791173, 364036722950424327115144551, 821096861946929109019908331, 1750507770960895024039095757, 671831526622042902548014703, 1293447631964390242134331977]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows079_p01 : List Int :=
  decoded (raw_ints% [2786376020533362253702255011, 1371117070653706966855840113, 2164759915191014914115937737, 4829324617809112123106109827, 2880291719069686110369324793, 4035681773271804175846012203, 9080733407532505200331274733, 7186050190933198170042843903, 7925343353330387134854587323, 19147075317535389480743443429, 17843488729376305484949118439, 18407782155138200515931700009, 44176614237844893135735405771, 62281660380754004267015686473, 43612320812082998104752824201, 124301763347975202887700210683, 191803862245955838513784287985, 142971102916646209049963072955, 378387285974685045668500185141, 1567596120882288953961102063543, 427220045303994675132321400171, 2137787269102929838143386536669, 6460728049210226660363649896575, 3278163344681224116972167200041, 10166111439195445452468138496787, 35535264794135804531174486779391, 13348676143724447995859621193321, 18908425305730132418342698386029, 227504378065346181305382427524151, 67792366243590384945376806358741, 281948068165212118254899612689571, 180298867357811577070212393706383]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false]

#time def chartRows079_p02 : List Int :=
  decoded (raw_ints% [441660079986967914614905233854981, 329153578872746722490069646507339, 2790449435982631766771312626001463, 292805368472032769195047981054025, 2641594724467696621351455373200507, 712829600518547058067465915165593, 5139238791978295618927720018147945, 6144873760968875446190233914367563, 21435371012720337195351506922161791, 1718464569509126885329979811385211, 14577667651232914691093807092628635, 17024539625535883917987736357933433, 37731503233462378771775293826175637, 53037578289489135804433050372723859, 122587359919373486587527758934468367, 32330614681562640950645492904481655, 52525242004348466865106972203811075, 144169566573323141126667734050481681, 207443216605284594403280224042761097, 319282168497045094579302465188761123, 567381476553925192645712802393924583, 256008518465083641302689975196481707, 103929741483556956939742603154681779, 850775776776814897942139958872661857, 927319736502565790888145380745088069, 1522086994814297047527595364421268219, 148815208533763510059754753, 2429286507410688300375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 15] [false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, false]

#time def chartRows079 : List Int := chartRows079_p00 ++ chartRows079_p01 ++ chartRows079_p02

#time def chartRows080_p00 : List Int :=
  decoded (raw_ints% [1468391661236945181137605, 141093215799659830443307469, 144322153127881615020156707, 3083731166275105607026029, 124056823876312276698804265, 126407557505435842357003809, 1908812777274220351017089, 116423366469458985587099237, 59165641197805705395967331, 1908852505812785539704017, 116421572767215395294735909, 59165661062074987990310795, 3083668731076602481529013, 124058776492710127745915305, 126407512092115966483383633, 1468420188332926651551295, 141090922615828215146968013, 144322211060932584658852019, 20331203812122596811096109, 171048222519363780595556745, 22050097047464824335294811, 34402181007786921743931711, 222415737864318602391352449, 57783540299907028309346577, 15134317937378771388016191, 308656946550511467571283589, 326073613956930120533382783, 54704461102120203633613413, 464564824862378944599611505, 496019807910685613352674373, 216875903068840189429222875, 746292635367473096640190893]) [4, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 4, 0, 1, 1, 0, 4, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows080_p01 : List Int :=
  decoded (raw_ints% [411152316591883105024562037, 443989045398987841702921389, 1332068437137739702316503005, 741584790825797120590634169, 534803988949616271120917319, 2522248816963424463451876449, 2996766604949814625126024365, 647603962078817192301557991, 5610500348734669871283841557, 6656790431164315936574090967, 8683379017256374236527643273, 12883912210224499540276804305, 4482646324183989735576991551, 26205785599254827562587236635, 40344016417760166817394414649, 1650617184788973773169463941, 6366703559822399023376998401, 117707054607243809790625750845, 282760049426818757052074031579, 415783070516339252469545615927, 855282072075027241809650209977, 1318060704373814030739229212265, 4245959158102440495386276353993, 3443971618737957829546990678261, 1048166156347973979853977954937, 27630457274895477689168623843191, 16128554560334734739735455205995, 16986374372846933072131428053529, 9047724267206465354283614109145, 107077857480843952927127504694503, 43507757486176413124864251731959, 5005752012588252581034401660149]) [2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 6, 6, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 7] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false]

#time def chartRows080_p02 : List Int :=
  decoded (raw_ints% [56253239577316988094533457667165, 294955819853884682769904682735867, 111641052107803363327390662367461, 1174394657741748707817679320303641, 22717656273979256602609282854777, 2330615210457344513062201870949129, 502817448008530441404096107137009, 373002289395551234612828539307201, 509740944914973214073814428662831, 8148066184087629344431128163492875, 5861588147699442307808773742829257, 6321999275957723388272030424254985, 7653037670631040983776934751468287, 4743446624556111612440029391029389, 15893128237299572124105404711603859, 42427928023574157761745115230547005, 16640286706885565256544747475571609, 55599264920513955224267605111291803, 55919475278567247512644684094947149, 3212781634721626293536352724272363, 44162888532962319946468618859939733, 179969131658481663135325305214620207, 150350605255881847704277548279715995, 52009022589353446066077581161769913, 297383632985131312059104266784570715, 30640291964392703332904461352515809, 156069286417777176469257547, 2429286507410688300375]) [0, 1, 1, 0, 6, 1, 0, 3, 3, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 2, 2, 0, 1, 3, 0, 1, 0, 14] [true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, false, true]

#time def chartRows080 : List Int := chartRows080_p00 ++ chartRows080_p01 ++ chartRows080_p02

#time def chartRows081_p00 : List Int :=
  decoded (raw_ints% [26504415459287310127744375, 147628949750618832578197625, 302965011547290134585183753, 13659075063908858930173609, 128831646337383991879241753, 262801521024093965527265769, 4259583793714054282051081, 120310799622801114717850407, 244882862166471052315041079, 4259509739407953338169577, 120312478749955883315139591, 244882788112164951371159575, 13659307789931371976582857, 128829819101617021394189561, 262801605641504276685912009, 26503990240170936785912215, 147631094329818627268305305, 302964903671606585448407081, 46157835725599669995026231, 181837799581958894966013991, 375626729637377192229345527, 80880467281271538396138793, 239946765781017967258357767, 502665032644248400620510551, 143827935154716254200954377, 343598734144501971758291577, 727373435080236193217603721, 277436929753693634551596759, 527602636090450475660266521, 1148638299988646081970154857, 553431278751730471364966775, 898472593651889240861485095]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows081_p01 : List Int :=
  decoded (raw_ints% [1979506508494070187886718391, 1286531808808942340601504873, 1634465193593911418390200071, 3819469596054742999853190039, 3034473856985403156128245833, 3471536211269773922064494841, 8140475261849088496582940745, 9753090100138298015512338711, 7703412907564717730646691737, 20928039218972789668223525289, 28796355637032871001074692279, 22977716411546369953089172263, 59477484956143958684810556279, 212418135245503489234145117865, 65296124181630459732796076295, 300691975838680318920030366423, 857772306165685334375225322889, 447813986902553348421379407993, 1370882417249869142529400807177, 4042224011643861349509870512041, 1780840736513001128483246722073, 1813569288228306872605244381975, 26798890090325070005621163039497, 7636634036385169350598361616089, 32654683390197238227736277933513, 13849491236089550865074182118377, 51816939444137138882759079356921, 45604082244432757368283258854633, 292737674778110034513055828129225, 20062348435793932379550002620665, 260983083769766828009846751392969, 129736506885875444939666197058711]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false]

#time def chartRows081_p02 : List Int :=
  decoded (raw_ints% [533658410112082930143352576901529, 683457265433752307462568776580905, 2010247070057620955030874480624073, 279535362207544822258882396738087, 1197053297737993202628639506984457, 1927322703251850702986635081503703, 3486835730003158979918396384346617, 5134623071047464860646149069112233, 10313383389699421806764084267206921, 3575110044296156583714387766269319, 3251437615400106243131300116590985, 13854164569305491808679184547913175, 17139931049395684633609772150067225, 27418985574405019858574568931711081, 42955266130100626580487916990118793, 24133219094314827033643981329557031, 1682115986390114913234163510494537, 72432648208270536919750969955803287, 68770601210805568527366061830170361, 117070030324761278413473050456416617, 152436826874151047750957646112345929, 120732077322226246805857958582049543, 37065851658880767582266374299873975, 308915101771232573664163063291042839, 236103052537496526974549230394521497, 424286076986502853832854335103514793, 2573979898488886286819751, 2429286507410688300375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 14] [true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows081 : List Int := chartRows081_p00 ++ chartRows081_p01 ++ chartRows081_p02

#time def chartRows082_p00 : List Int :=
  decoded (raw_ints% [5373231134535696178614993, 223193398508663490847228479, 229332331871693690536816273, 5526879413718672984085601, 192485416158438320797484123, 196785648506113559854185099, 3377329622664100423321329, 178978363198914106974543671, 22794320007001514182836571, 3377379369105962819950437, 178976097667781919104198807, 45588652450613493964830419, 5526801256853103104892227, 192487880675337958254345419, 196785591685266144889056567, 2686651258378160732135097, 223190507722606743943336623, 229332404265997636955921797, 38585847001951638399413101, 278460720943439101682668523, 144705730667487280606207837, 68268266844103817236288771, 377533895730413297540989027, 198132787590515008424058773, 8047454287315687617018059, 551533788319854370627823607, 593293110622184835956695261, 125280970410656746766118777, 892570970118617305030144803, 972614320040549331361221759, 562029404979742720124046219, 1553781551605108344756773823]) [3, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows082_p01 : List Int :=
  decoded (raw_ints% [446301416460401386254376383, 1289371955509961716519767201, 3140688590037588185526329679, 454575878291413747707664869, 1983659433190612291339191549, 6711269373644955210835842627, 8893297848222496280859469251, 2859784171691981537783075871, 19009964055562486516239862071, 24299753401371647014670155833, 79842682921755071416129845417, 52467816120716659815365056563, 57790786504947322290966152367, 318610453816835065330838316671, 338380695742582772180759243739, 257017354874242390664450233411, 344084183974921151816525984183, 1326909631388056921138718323247, 543691572334364760606365153239, 4661294809394725525609741617133, 5166966247856155656883656503189, 11242617927023500419091952324237, 3524485973963534896194181952007, 35963448843769747283739214613817, 532522549120294267941164175203, 95571749526692713067054400412381, 8930977647997983927893071304839, 20513878482201707847282832189473, 25800607972001455694031823443063, 346323549263001104984478387035707, 229228479399502455844249376056399, 38576871439123472177603103397701]) [3, 1, 0, 4, 2, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 2, 0, 1, 1, 0, 6, 1, 0, 3, 2, 0, 1, 5] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, true, false, true, true]

#time def chartRows082_p02 : List Int :=
  decoded (raw_ints% [215335841424009629480147658849343, 336400247682470187609336631420691, 646007546927634334915243173021979, 2122596222840901114382120230417157, 799818868818040038683114729402943, 2983939598924240475166438786228731, 2368694346286527710180825033238573, 369147157180263031442483077200433, 535776095494332665259912452270083, 9813162172856060786283634914497767, 8008442677239427860130704558790261, 5865338341556186222751154138807187, 14776140709532117578136373439404083, 563974758081716736707695899336551, 21051642714267298062164803278645629, 37109544559593428995725598195959729, 8054586159824488442739853914230863, 39344935485285459238428242525115417, 69430430147537074670522839675178433, 435157870883743518584249262826677, 42492940402996684837992587738242737, 120270197381548407957987371904501939, 110405764422999036319717441591147227, 29024196248896726972890317648621223, 270513093076436404033417862230763463, 79294860233405498104141346473147809, 250825256409836475251276245, 55873589670445830908625]) [0, 1, 1, 0, 2, 1, 0, 2, 4, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 6, 2, 0, 1, 3, 0, 1, 0, 10] [true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows082 : List Int := chartRows082_p00 ++ chartRows082_p01 ++ chartRows082_p02

#time def chartRows083_p00 : List Int :=
  decoded (raw_ints% [49646540193903167876386235, 235564939698437770531900307, 486385616224528064780593817, 24874018735008587309879541, 201174136332187126372307275, 411865057295616309594328041, 7677551262350139441863485, 185816902228420595912141225, 379313487298257582842585015, 7677458034772271285086645, 185819033807486847488580305, 379313394070679714685808175, 24874311637132003962719853, 201171818297965138482314515, 411865163742583989933614673, 49646005302750428920218995, 235567657081750855414020011, 486385480682466422816553521, 89771454680793146811786427, 300463828903465996322752505, 625802940666009998548558943, 167359543136687123311378605, 415110566443337149037592865, 882933938483490268671723975, 318850458596464923887499445, 635182915176840242945509715, 1369143940216642315870602025, 690817253733372685854363323, 1052811483636266996812591755, 2378811652546479925612464793, 1539973973806816946370770835, 2016817422643585614654236361]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows083_p01 : List Int :=
  decoded (raw_ints% [4609602880086669557837598951, 4529405934544513551046873797, 4132759431249900889554133425, 10678982788438000055255243583, 12728591613713486054868791325, 11075629291732612716747983955, 27936980336695999661170908705, 83810125836318596393014482915, 29589942658676872999291716075, 124475697786728082109054182945, 330049776012800392255949592395, 178695880964369805502776949785, 538335599635847070758018258255, 1296493761443982088018480005635, 689689494684277657511190900865, 428108385795334625004512154985, 9003978708346070608634533858395, 2414291641923594370534183061485, 10728580855585387321657526019015, 2148149999093665961410614355435, 17318267922007863559757876815925, 17584409564837791968881445521975, 86249161163409592433848111819235, 1882008356263737552287045649385, 70812901597665466426377280652695, 55125704155513128631066871487573, 155180054404811321307938346822545, 212187766916588187491292263959503, 521658189592306033645942888002995, 112133416667289994814420788624531, 254344718520204717523583752555919, 594406323471729007596155469910573]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true]

#time def chartRows083_p02 : List Int :=
  decoded (raw_ints% [888136324779800745983947429183445, 1370409231584239758765682110469487, 2366709669847386877341580970518875, 1076679230276168020377890151196615, 401894114791418110979743390138815, 3640201246263251781360226159983565, 3845283014914973008699214511854305, 6408805030902056769681550520641255, 8746737026147794394824442189780203, 6203723262250335542342562168770515, 1302269251017514156217334490844617, 16765433815964706026852442856985445, 13648191037380615780949669867706101, 24209901591094986265459550555921031, 27614259089115850914443798309923763, 27327144369679076511362323545200375, 13361076317943841377868195102982713, 63934238838090116541620785557845605, 41580327140851086047937926752141425, 78187421609262126078196388764786655, 76751847781108576141563507031948035, 100541333306501156571879247570490835, 65369812666243666478253667290684225, 212085300409023386088277932061040829, 111923368421366066235189087311754645, 223467335523888295751587771802304639, 134008039104607808164245013, 55873589670445830908625]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10] [false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows083 : List Int := chartRows083_p00 ++ chartRows083_p01 ++ chartRows083_p02

#time def chartRows084_p00 : List Int :=
  decoded (raw_ints% [71645437024136631294933199, 626836240048683810919092423, 162081428613151734800342747, 35823227899826359575993099, 526524314808256804893783155, 270428524764321974165222345, 335828214469566493056451, 483543328449378372615120027, 494287318765791460976645159, 5373306159474487501059091, 483538303356152293782557427, 494287428221714308200956909, 35822884054800819049774089, 526529777725174272623592755, 135214231148866025563212295, 71646064793546747276391769, 626829839575355569981653783, 324162936721905834289507519, 264876940116278945055799, 813114036899361261729159831, 855588931576893235723975895, 127686052064974569345712813, 1169297812933494849455930135, 1246578029046377194283970609, 536337209473082625641769617, 1834602453419157816494862335, 509571835662352239654291463, 1161732403071985360474686541, 3314646650825825352023008603, 1868178477597238472366811005, 203912087723550368831043263, 6481532065707099258393608499]) [1, 0, 3, 1, 0, 2, 6, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 10, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 5, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows084_p01 : List Int :=
  decoded (raw_ints% [8160682761843268206505000759, 4458893589769555595146807599, 16365020265133048957209777435, 20341063344959185298095308165, 55212111939638505799739119209, 42152680783863544019568069291, 21117740616034200572032010643, 214236337111161528490924297265, 237213468023687072156166254271, 176959705757468418289395729523, 47370467849397918322249485611, 899098029228509657983265258351, 189771736964268328086276013465, 2710602958986166725121416682391, 2794496474337779700467800824833, 6368905140526968471485101148023, 532284623410525237027856250545, 20785725642660824142988068200777, 2814456608772194171175019565565, 48278238159230413117403569434341, 665357980695678752356375822653, 18776348173776080834865673711313, 279657479709351301871744178239, 172327226994260828326626209536587, 121627091909579541426718171671559, 136065322670619480228194817080853, 142519271630492187805976643435715, 114707396028862452390088207675555, 337050391565658253701130594854391, 916195354370695013498932327110237, 180972108233939916636902109172913, 1153157166520737748989096136913353]) [1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 8, 0, 1, 2, 0, 1, 1, 0, 3, 1] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false]

#time def chartRows084_p02 : List Int :=
  decoded (raw_ints% [1205682294632140826998545735981849, 46109171009659914370178552683655, 59488181584475358844788548963883, 3696433311712255982457452220543175, 3148997319243269060762686809124919, 1993758565654706605876191717054971, 6408804948180705105134388531395175, 1065101998637067332043536941859233, 8203270422809797115270776832472431, 12253635213525396864552081515896593, 2781421388870535748744905831180785, 11792201134854915004544077651065277, 26404276743058483355948718798494549, 3768377421718512552853161253065147, 1842531425552762676999041907265717, 34915169325894263153624229088364515, 33735949100262092730822425661186455, 15355496895407052466960146657635897, 91517734492318327971989963266511339, 32505458118292190628886802862166133, 92594415470405096854965665757531671, 87928805837362156582056944172722661, 22699987785731752789999789052659333, 71778614245550300975312614359156513, 278859927389302059447872699763615345, 55807876183890903519826103804506245, 719971151476743570496304187, 279367948352229154543125]) [0, 2, 6, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 5, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 0, 9] [false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, true]

#time def chartRows084 : List Int := chartRows084_p00 ++ chartRows084_p01 ++ chartRows084_p02

#time def chartRows085_p00 : List Int :=
  decoded (raw_ints% [171454977290252235072047465, 670014066948722613363010801, 1396846201657528543120258731, 82399932367775603684271279, 555377157418553694685200465, 1142991291999500704363939987, 25079103410947974858839461, 505214202213171405994468243, 1035512256220777125820829247, 25078897343078734945968361, 505218950596657744967521543, 1035512050152907885907958147, 82400579631543479654279679, 555371996899328875886404965, 1142991527127530100508206187, 171453795834624510224819465, 670020109859744704276080901, 1396845902593698090387305331, 327039352496013394169994771, 898279588568577896336043895, 1895339050924335994782119567, 671984833584932194117652017, 1324098814851771492616070443, 2894363237005281583069766355, 1417147501486312508557162791, 2242249255738442284571347929, 4983495572076526285744581163, 3798991290920779250206275457, 4158393817824396509730396025, 10199634364483618044508019411, 10079604670174554390952758955, 9840231837580000784983898843]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows085_p01 : List Int :=
  decoded (raw_ints% [24078230325578951685667053823, 58474827766589609889616324313, 24317603158173505291635913935, 92632662762343115966236137091, 223154300445440832755616488591, 126789887370759220564216547469, 374261790974373558611468949995, 702715110286894995750091679687, 470626204049055170802868891117, 105299018867080604383006241101, 5206969187010875901647153711069, 1278640333203030770935966811905, 6014983316164851501780251631857, 225642243230845336116655768095, 9943312169972696632491438531021, 11447594746406572739544061111021, 42857033210711360621946387241399, 1729924819664721443169278348095, 31183796221073942546285670362283, 36328443641932331304343265141169, 75770754251450024611401335951777, 110369273073717634472575322744851, 223852404516472030451511897643141, 70926962464199941165517251934243, 77154687800822064674593309757121, 301254229412377561463706603337911, 371934054781494036291622459334505, 602261321729671656589811810738173, 881026529474311088867383833533215, 531581496360555181761895954741579, 22489021667738129186134580542869, 1566571435085899897001046352898921]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, true, true, true, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false]

#time def chartRows085_p02 : List Int :=
  decoded (raw_ints% [1390119004167128141443145207731925, 2425108942892472856682295605889267, 2834359935173616538635329239747917, 2601561373811244612240196751056263, 1157320442804756215048012719040271, 6299648550035831453790290640265199, 4278600866180104935827513271763909, 7976688042404691777377607160972845, 7804684126769603106954416795748423, 9997735726260418295340384529474135, 6471652465670920124213481005489621, 21277232671265397077116392005054945, 11330767387359101278081320319732937, 22610264332364080059857327795313747, 18918792046757629179076750423985973, 32556729616270375858892399480635755, 24968704956871847957896969376382719, 63113911076972614022420117646191047, 26506816706156157080072180528239009, 57063998166858395243599898693794301, 41067624125945679219801458015641007, 93671092537674852185947835811746339, 79110285117885330046218558324344341, 169080866292838436222973783266721433, 55628431545735201359530735503043005, 131038205300898785396556682958018099, 392075294736945194548076549, 279367948352229154543125]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 9] [true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows085 : List Int := chartRows085_p00 ++ chartRows085_p01 ++ chartRows085_p02

#time def chartRows086_p00 : List Int :=
  decoded (raw_ints% [614117893752430004119317125, 1089971982490719247581203495, 4556383781450257853545458681, 294778919716764635419853589, 881160961358194677131867283, 3647486967981063214006287967, 85974641897960330093663977, 397596531386977306080674953, 3266733406366338248492770401, 85975225021715358098713927, 397593159730117173519101653, 3266733989490093276497820351, 294777088324755541712376939, 881168287795669970260063833, 3647486302836564176308911217, 614121235857199557107310875, 1089963407784989888750580245, 4556384627018519275128599031, 1265099100872341978174325623, 373822380913217381841843677, 6435604963748060810410235529, 2616195195494836774625977143, 588765627164332966731226467, 10316899260115239563210538295, 6706344758190850473732972811, 4111484719147706301993351851, 19639439213800926811569488249, 17244959707849937229076511419, 9061407266848182340657878679, 43590743679841714514378972479, 93410492231922645264777074055, 10678222213498821765534931635]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows086_p01 : List Int :=
  decoded (raw_ints% [154246195619614297008232557953, 349850517608494474640463557719, 51235949749385413802717476367, 597507205460031416913473189727, 966360913099180837330709077861, 371206962035492118171533420989, 19003190030654945776772330415, 7475723061414355913354419641717, 863889013600410009725274125127, 8461087164544191696461901049993, 1392537124305210553646663828473, 888064512422357974397860777591, 17329347350263758163462984520183, 56475094316247960080416962097895, 35256658404775321302686530525, 37753209841678991363307313749239, 54154199405126448522379771915611, 49370578216869096285234075877167, 148382503563053399966104047762745, 271493061446765558710270915813813, 51897773267220827959007833962011, 68956358478585710221787096135457, 397388686059935947704251026973513, 111061241614948231212518419968323, 737838105985287216636309038922783, 985761174240970460963139190774311, 172745456396357559872621596505751, 149465617804252703377420875121985, 1897975785469138224598572594392715, 763638691011073998538102350837665, 2734271341905855982184290910045041, 2930000152849921140398983056291653]) [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0] [true, false, true, false, false, false, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true]

#time def chartRows086_p02 : List Int :=
  decoded (raw_ints% [1552484872676423104853329401381213, 1702246974525073066383880448146103, 7099615754688949902205972146184617, 541590365459711785465220176363497, 8327368933013797976221074754330167, 7455486114975218245680707374659159, 1386782720503131699338160686200851, 7971498572727529632746339525855625, 22466375839555178117870478217203819, 5289124653136371103819826669205171, 21950363381802866730804846066007353, 16671162672290348442634884668122725, 16919244957542651320517835472400415, 27745576549067696406040439615088447, 62755019300787383057676325240094553, 5691019009576988669407528999458777, 51680605424010035094270770293128831, 33223243717147963948417956956679351, 22917887171622365868579244883847069, 81212381007649454203529138576544033, 158950422625994613360805117953694779, 21841205697993986609602898957761797, 110961285335493123105693936333830097, 59208318997677733946455853515715157, 113114648282749881623646628186000641, 210703388963810002520043200771809719, 2585250837601343928832387903, 838103845056687463629375]) [1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 9] [true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true]

#time def chartRows086 : List Int := chartRows086_p00 ++ chartRows086_p01 ++ chartRows086_p02

#time def chartRows087_p00 : List Int :=
  decoded (raw_ints% [779977152771733818000073831, 2376952795674871560056007291, 5042578297521555792944512523, 350066883350585440906076151, 1885648349074950414888431401, 3912534261399236534038362541, 104408264369532113601946631, 1676819028973700678243854989, 3458059113679118979530339759, 104407713286205654968485281, 1676831820335886187684538139, 3458058562595792520896878409, 350068613921128260357974001, 1885634455546111988180825551, 3912534889803126436223337691, 779973995337389102598944881, 2376969048178142708400486141, 5042577499061643799180256573, 1615212855843226024324641209, 3445582446220890193378715313, 7437764350242258926103842663, 3985800937476058871170925617, 5607394759864594757049768559, 13038778143561543821599409489, 9930688349628123930836097081, 11417184321173007935720566547, 26955267430665726623606432187, 50058575005438013623715653833, 25468771459120842618721962721, 86944530785731864178158183101, 183547958130062077347944229769, 111534334332049035183151874213]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows087_p01 : List Int :=
  decoded (raw_ints% [320551063921231955149818066703, 436474894659052533244960710703, 392564687719244997314610422259, 67624127392241499252801585769, 3562935817535545300712696000399, 761415454986056031306769547193, 3931786584802356334704855125333, 1179448339390721193329937917167, 6733306947351845604110781578539, 8674170741728622828747489042899, 24499686643300502135388775123689, 3120312133767498417966645381527, 14646067562181158113311348163623, 26380832736906045484396164512769, 42266066339249158666666768668839, 65526586942387705733096287800081, 107508981064684860344249702009959, 49641353340044592550825683644011, 15601561385391109126757249697109, 171617239159860520908293166618551, 172751895790120562021832635351079, 294727781609936490379300118325619, 357134063272494260558411155753049, 293593124979676449265760649593091, 109210957497302750729182129191121, 750293561957832970346353160123201, 541516230754867959094989676155019, 998216667733024480175582186685129, 972119467909126152346730404949071, 1206993998935989491426945670653311, 776390761781731298175204941859259, 2600819943473297370609996610852751]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, true, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true]

#time def chartRows087_p02 : List Int :=
  decoded (raw_ints% [1402722705063384345598471133743123, 2796548649600692224781522073942563, 2262743057450697364875674608952153, 3994645888010605249793047551052191, 3134625535623292230515844075843161, 7683380202536249885573182426326801, 3122763409838010384152878084161183, 6811497724363655019933012959435793, 4607837960817621232581177233178183, 11372114517061894521353317301601411, 9887039966082283672925018152584411, 20144320994901243802198066730376567, 6092912511797232081009476382195183, 14865118989636581361854225810970339, 8276042093782039846917934581355113, 28916527472740593083042816159151723, 26733397890755785317134357959991793, 48097705749835289756185707613974513, 10459171675766847612826392780515043, 29640349952861544285969284235337833, 12992528170875345054709666407924303, 67278884026929986429328599068797303, 64745527531821488987445325441388043, 106460282747296758434908476892423023, 15525884665983842496592940035333563, 54707283386350614502172817858959283, 2911277725146644805472293177, 838103845056687463629375]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows087 : List Int := chartRows087_p00 ++ chartRows087_p01 ++ chartRows087_p02

#time def chartRows088_p00 : List Int :=
  decoded (raw_ints% [28495525330486889718199104095, 2415290284843451040893651579, 164551456700004153493205251683, 12823031929362818615640485499, 14691660563631707616602324265, 123232899440154445159365662089, 3561884706339305072677894015, 25821612628132398038657939765, 106847982804452321471047282575, 3561899836532326800665919265, 25821436420924110160526754515, 106847997934645343199035307825, 12822984421037012310343774149, 14691756232332362419661929515, 123232882192214682310045001239, 28495611991634447876196893345, 4830552605245140308858816083, 164551478604886142496585668733, 69102261241280383441297197821, 57879124456299172715520752375, 262149351837800973814079759899, 167413434264834082928964242405, 107746682083241505912167726485, 498665047343915440184341200125, 783640456927449154093264376425, 56323139680283313911121248695, 1449718938536198677206569818955, 2805436148175213743171877718525, 445693569505345330002716051455, 5038795543638861574471711913905, 5603042560718437062663756595015, 3030728706896346998816362713305]) [0, 5, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows088_p01 : List Int :=
  decoded (raw_ints% [2241189131095638254979833037415, 49001132487293073934065043536535, 4711655421707746402658324492105, 52362985916915872741748967094135, 23430899161641125338731645227315, 22985201890198363467624340411615, 124795017565850072014545655857985, 303582868632182062544516936815705, 7035638645837217935347492429855, 155356951904690865191239635730405, 365420046335112300820307680455029, 257612464851785335609268255992475, 824359866871985228556064253001139, 1203634812215449709529282922519315, 337277491751763429078917710735609, 13854899008352180152910989063147, 2105927960648336245854792951429839, 118252793420458046740001833315855, 3323417671872138135536986863012301, 3619563579489542128673994634694005, 884325234448286408387937620347115, 1809782053030932252717785179748135, 8390806494935021662188490412451825, 2673541232125877754753979968167165, 10200588021393631538144699867397695, 8917288698068421892208823276509519, 6622156026038448845412615171757595, 9674105818260231308124367003340001, 26832633109648661862845001286437675, 3121873732971272068727421654171177, 26075815989456852446929457559607193, 18714040937664353940439705501878289]) [0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0] [true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false]

#time def chartRows088_p02 : List Int :=
  decoded (raw_ints% [1263154817725638313589524132167505, 34194408161441160369334753344166579, 73697121693935493536626258180626925, 12470293471721809802984862193535935, 58216754470158687107731210338338635, 34003880421605062080734881603341835, 53486644610325280519193872065946845, 97909995742489118563622586915623725, 180683650070970896170250430574668807, 5383396737470813069437504852451475, 116777534750086839687362725262386917, 53188940063682885879851848459707885, 63598502730322807825528279254360981, 244272244757374849977761307377347839, 405324036520006399794108035011096617, 31655353113799633602101829049901985, 214240731826314435696198576093456663, 68389158473108139837755515428962055, 278127031059360784143051476502374655, 551175609873212695652551095675591225, 846257622136708874337830765070530595, 18366902679654253117826843189530035, 363471170736604318523035184823901425, 59215713936136188791389274330103753, 142032647769337022548694822142038985, 1150513078937177004069476675564328267, 96523491015245521605702177889, 24305011506643936445251875]) [5, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 9] [false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, true]

#time def chartRows088 : List Int := chartRows088_p00 ++ chartRows088_p01 ++ chartRows088_p02

#time def chartRows089_p00 : List Int :=
  decoded (raw_ints% [40963609686807771732696955855, 87275094661006235666766882275, 192717140789460591282096328759, 16029224529652932295188056175, 64478436441646583882632490629, 135724306572999887254211316729, 4630727755369834276009978477, 55216645601700371076390769925, 115064354287977120683013282077, 4630713407183616457642985827, 55216980930906915330612533675, 115064339939790902864646289427, 16029269577821491567856438625, 64478072416067603991676741579, 135724322924796010890145713879, 40963527529777474510741444705, 87275520086549898466325410925, 192717120032394976968743597209, 97955900060447903435722097315, 146405127475622553013159630989, 331636547622620354915207139229, 426373350084565227426756152403, 283187320207445705337769605555, 855965797767633485777685388947, 1486427585848508483660839271025, 999151827644753007866671935795, 2768766733700707196865280812375, 2409697107833886057272838223215, 3256042491904462672659448147605, 1845497211715329623253281860185, 23097842638867305335834593189965, 3820242388023019106679004510635]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true]

#time def chartRows089_p01 : List Int :=
  decoded (raw_ints% [23662042534985861769854149552995, 14516962903660451818439967572925, 42939642785830147999009738232325, 61276848077513618924128710315885, 127290879522502606855061854087905, 32854168195343922743558939656485, 51497068541328536112493176199095, 170994590705384745195188480721057, 211642116259175065711113969943485, 349782538769215888162743511008057, 450025946191364582185573894682685, 309135013215425567646818021785629, 70751183283236051172358097046429, 870253916924927224716496451663565, 688409776123554098660033819421885, 1249528679833055755729712249299821, 1207964446651509471633423182256945, 1431372820634428881786174881541501, 911818150106473508812785518706441, 3142439372165457270969438745453073, 1727519117179464844606812545092005, 3438585668710493233790076409003577, 2648862386029566284081593460433197, 4853505923696485660152702609364645, 3932162654846384220677921694023453, 9220912998575377936468607551370205, 3570205654879667723556374375774389, 7937612729758559999872279317779949, 4898376658960765545869467613486305, 13588320073454270212784512493375765, 12260149069373172390471419255663849, 23432245328785949235371948206183265]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false]

#time def chartRows089_p02 : List Int :=
  decoded (raw_ints% [6226547663041863368182560851198221, 16070472918373542390769996564005721, 7644917816991524001830314316568093, 33276170584117628257959383918990765, 31857800430167967624311630453620893, 53493260153918679717740665548427501, 9063287970941184635478067781937965, 29280377540742236095259349411374701, 9592537830605497320135451049733745, 73710349723719731177521947177864237, 73181099864055418492864563910068457, 112320211764532190238091193101147665, 10121787690269810004792834317529525, 48731649731082269065362080240812953, 7600069606611178209486592870291725, 150930073805344649298660439024431093, 153451791889003281093966680471668893, 220466689810113037235404321348922109, 5078351522952546414180351423053925, 74614967527720934350924233747544941, 4586483639869568926589217385270431, 290003305814881425172148203673413125, 299668140977703540512917772481737481, 409319266561015615660652174355134625, 14251318802691684267358786193594787, 105064641943442506221145184488126713, 116840375238134181507396642307, 24305011506643936445251875]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, false, false]

#time def chartRows089 : List Int := chartRows089_p00 ++ chartRows089_p01 ++ chartRows089_p02

#time def chartRows090_p00 : List Int :=
  decoded (raw_ints% [883370737417227150801347573345, 817082136194575518773154222131, 3621669397630079337356824000957, 353348582263898840521110162833, 552067193911850574504583991675, 2384950077948953346034366264779, 88336116419295666397395212477, 231866776965338339126022029649, 1943265379265758839115860889469, 88336327651396282849064402627, 231865538746277454053594389599, 1943265590497859455567530079619, 353347919137245943678316367983, 552069881582072961101108461925, 2384949837286501682094910850229, 883371946566615550071379752095, 817078996629800851785505147181, 3621669702990363175844606970307, 3621840835994058188535054200707, 358860457037172127793122053505, 8126882485551036914451040923109, 12278943146291505349435957808075, 277432489538991190020034959243, 24027666467836600452422052931891, 15370799644670262705158201261913, 13714384974440193860608446022095, 20935809969457843096699809478053, 167488523849788990111026507219945, 10931879812046403664837641914025, 161923513525001409719484899003805, 131181695284109677551148095846165, 76887069437674398125209030598925]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows090_p01 : List Int :=
  decoded (raw_ints% [460593732658900077381659502069915, 807495920464143310731274138554555, 71056787548078040607992868880095, 215720492521133555798466540638475, 1212701449437520641697180318897383, 653721781588794514480856077356705, 2235917862422797508226920998090413, 2501197014904093091900275029663945, 1070587874341364560481194581137193, 947422296956225058023826287323851, 5419260149405358215238868698256677, 230934404164412322177427369038405, 6973034867353226249115317440596771, 5874022795206694050110012313254835, 1087168068765998413689418529279871, 6518272221551890414244173825598613, 17609436364404390558574826547409487, 4026547561891395472690593360947595, 16965186938059194194440665035065709, 11166960553000601457110874872526113, 13260764089340396903817152430290003, 23407662749462983295904616709949083, 47108173116945052324062960722738893, 3570206495554602992210140755789259, 34867470920482670485269218885315923, 17433731137885882902891130344632147, 16923704513802327710122904146224445, 64541912899541839906441049263422669, 110137817741271334501067505813173375, 10293318146776676918470848833053629, 63029635979615377497517586894382853, 21285709006055112311675698455669137]) [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0] [false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true]

#time def chartRows090_p02 : List Int :=
  decoded (raw_ints% [76290408713666679080821697520724485, 151881744714831599686909394251887091, 232972892806971697228958028547766189, 2748097714819608848301212405653877, 102376857098195209853724332751548235, 15093996603822480030329210277428923, 19585310511663127268517041378380213, 320255753301344427052353151021885501, 455908758843539217934350558021095831, 4101605744544044637124360654813415, 150747002146017270912326617276639253, 15441359905746615928173983088136135, 299226274750234199786214226994054127, 622097120895303104774851158385871219, 838135779025722571386422732828114661, 9771482825145330282649171871474775, 200597298224672850683397591354107307, 94447281134679690833214662852132469, 269454752137744185800104252917030267, 1133180358385075112903034987034354437, 1463604009704557087145059264917845559, 74904315484389030267916319109182919, 235976370184802283408809615031358653, 259840113483495363317346289396391751, 924694505429068715544850759083785025, 1959420493372854733871215169345595963, 2252520067523653244079085787151, 753455356705962029802808125]) [1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 8] [true, false, false, true, false, false, false, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows090 : List Int := chartRows090_p00 ++ chartRows090_p01 ++ chartRows090_p02

#time def chartRows091_p00 : List Int :=
  decoded (raw_ints% [1987607825621981926435080853695, 496920213170050389286526852355, 5256269930188943543028546376919, 485860489024177914267841935011, 320245312971690014861839528451, 2782801615542783702325623588213, 132508325537352714470628270153, 507979937315922864305211769699, 2164432800981253073587153383049, 132508124614541445980534637303, 507982300406027315253050786749, 2164432600058441805097059750199, 485861119725445770828968610461, 320244030965232155142873203501, 2782801844398429021906562997963, 1987606675812501060987642066945, 496921710065736543041009698605, 5256269639936375853723173675369, 3290588132050669795883343222955, 2628094737742965371273388473947, 216016446560159632913710971691, 1468613084794781818352332570957, 473438730264550792365544115195, 7265888252386214412417429175153, 77604752362267780249059901068635, 3246357601436161902135941809881, 68947428196674478697634373002157, 73276193849802487778140728852639, 70029732678034967571211195225515, 219828374408744746724835002923431, 320003773490016434386099300910505, 9565318931404831210034583832815]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 1, 1, 6, 2, 5, 1, 0, 1, 0, 0, 1, 0, 0, 4] [false, false, true, true, true, false, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, true, true]

#time def chartRows091_p01 : List Int :=
  decoded (raw_ints% [26899205231469199883123569134435, 540759985249233865863082174092309, 124987020405990733407444052842495, 887662963970719500132305044137249, 846850391570747423110168578679095, 464237433797995216182805503429789, 581572557649205942885218639550463, 2103279117277281802625087894316147, 596876350758765956295280472994105, 2368556951198823282850037833444779, 105400827384685029882456551251995, 819520841739643293221141195443179, 1392711415160572303677910453864503, 3047544327199490356042186180465865, 1089536887396194521824024347037815, 1249019765558199145711964068308661, 2646468022294093734857797314517639, 1114011742729923531410522492511343, 8444699694337683560074431319648735, 14749366948625961044646359072045803, 97308195931118700814610810467489, 8951135276582371219429725066914707, 3133387647694047441431755058129067, 10293319977706266919004269102000431, 20567114577514284822644329080831443, 31514826509660870503469360990401091, 1576456512796148228397982090649243, 14081099579840633122256786967698715, 1925981604840308705548486310242395, 5305376632988650896116272972100165, 43669944484661194920177661647857411, 61417523440990742978339820892185207]) [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 4, 2, 1, 1, 1, 2, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0] [true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true]

#time def chartRows091_p02 : List Int :=
  decoded (raw_ints% [5461329563190007455476628431143, 19673560561169856763710645554570191, 1547915016717672449742652132666291, 40196016909036139393874729003784547, 21046728508898986160383942678021995, 13933498482951776276884173647310237, 1722677562739752688317904242462867, 12092621897291460337026157100530667, 15267787134830318540219750288237629, 71271970954578070821198660174697349, 150921018793027449429345453667780859, 191113258062770404370391086338628615, 11822432009350813163583941803311895, 24924452134912636400825882382610127, 39502422327774968242602225280876867, 59920643554096166774596213081965633, 255540132525458009013819194002115609, 312735515471717789624906203580670849, 6919997579606038769754570869391243, 17692960618484812368484784297678373, 82699660032162113414514184409912241, 192894228363525456075713777416739583, 413128136122364715407905172288261463, 492188846498512688288687863607873163, 55019669713737958335495900932347269, 3638949656014140533731493090300541, 3621938877905462734731813615307, 753455356705962029802808125]) [7, 0, 1, 1, 2, 3, 2, 1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 8] [false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows091 : List Int := chartRows091_p00 ++ chartRows091_p01 ++ chartRows091_p02

#time def chartRows092_p00 : List Int :=
  decoded (raw_ints% [547765567662295032317298003971, 51069125003395366740869857241, 8992412104653647454750153168445, 132506430185021249618263688403, 46927026123145867878689210087, 463754674334725155823452009873, 22084264649980519780559861063, 71770069828560217345215740561, 309163979499723386424628460407, 22084288572655226902917877913, 71769787596311215976818559111, 309164003422398093546986477257, 132506355098244567725544595053, 46927179200607722124066809237, 463754647093297888175448950223, 7067014278029675129789008979971, 51069035673638945925590788541, 16607190313094354424204905704387, 3886880829902423388324933528433, 8568684012449122237759146875555, 19787323761221606165668981155925, 71023626947859060325897429207575, 618462546789530849087123061809, 55123184016539877548553381580083, 79150717563157968147537730818667, 15613735733852484522034570583005, 205297528527556906021988541606325, 121199460198655783042750457171135, 19942295027486874749156213470119, 21024662846701654042012679041361, 233741825073412128546857387997435, 89971988730950813998681316005125]) [0, 7, 0, 4, 6, 4, 4, 5, 4, 4, 5, 4, 4, 6, 4, 0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2] [false, true, false, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true, false, true, true, true, false, false, true]

#time def chartRows092_p01 : List Int :=
  decoded (raw_ints% [333916622425366257547595166127209, 263423410656983067013308818871195, 193857235018438379048544961057197, 304235036841795319081143735253449, 781259712229964922675072189601119, 86725710963016126507313751433035, 740448086045152670607237273218865, 839562409377804175704988050063825, 293701238605763271813263614271961, 2203853187172431010859630875576143, 3991808883296640729492768010534933, 492659565525739669675733044331685, 2627518105502013894338125185022615, 960055811647218150854140768850269, 2817003928873587642239713553447089, 5659271177151436472976752426707279, 8654279903602050576678450524366073, 58424530765184810147300965564823, 3955064538097832254555838866509063, 121729235789754108749111428566707, 729659496841057866804842121364873, 3030606874635216599059460919152077, 4191363784004278754481652798007647, 4880174259384488454509497437061, 1282486145158816264171303307422277, 301849539161470867849912008173193, 2732044790322163020871968555277901, 5775699468324565886502868113603117, 7475677675356308815144247249742379, 153364856710427678152210752805127, 1398128667870272060791467127966069, 5021838113890356026474315104571777]) [1, 1, 2, 1, 1, 3, 1, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 2, 4, 2, 2, 3, 2, 2, 3, 2, 2, 4, 2, 0] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, true, false, true, true, true, true, false]

#time def chartRows092_p02 : List Int :=
  decoded (raw_ints% [2371816442517072897136139347232239, 40517063486796679530217172615405569, 50050415259101642480562287405241339, 3794919260206934601256629082130761, 4511513658414606923870799685263993, 12171854058652916323541060707975997, 31075883718965059303473172627383427, 66733782976169165727974147798481329, 79645474761666429754712409994638119, 2094233699611495430571107906461309, 739837726844347703197201488180793, 12117554350349883730736541526965219, 12142397760675342612809809341813673, 52310210594605272459691347268374675, 60810623041217976096728420662392017, 7929086951126892869594325714042601, 3617141903737180093699468132947877, 21597303576396103370403674606639887, 36525827519867290871108801978764671, 78790784713876899373432627136084027, 89729712773712073342372633203639357, 6834108312634605250404674446298643, 10658375516560929401463668539084557, 71495175598264106547359134776072819, 26601942626922391235631915612437343, 229637850112566394429177064105182419, 4222323268495676211216427582237, 753455356705962029802808125]) [4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 0, 3, 0, 0, 9] [true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, true, false]

#time def chartRows092 : List Int := chartRows092_p00 ++ chartRows092_p01 ++ chartRows092_p02

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040, chartRows041, chartRows042, chartRows043, chartRows044, chartRows045, chartRows046, chartRows047, chartRows048, chartRows049, chartRows050, chartRows051, chartRows052, chartRows053, chartRows054, chartRows055, chartRows056, chartRows057, chartRows058, chartRows059, chartRows060, chartRows061, chartRows062, chartRows063, chartRows064, chartRows065, chartRows066, chartRows067, chartRows068, chartRows069, chartRows070, chartRows071, chartRows072, chartRows073, chartRows074, chartRows075, chartRows076, chartRows077, chartRows078, chartRows079, chartRows080, chartRows081, chartRows082, chartRows083, chartRows084, chartRows085, chartRows086, chartRows087, chartRows088, chartRows089, chartRows090, chartRows091, chartRows092]

#time def graph : KernelGraph 90 90 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 5.1336 s provisional ×3 model; 8556 exact original rank units.
#time theorem checked : chart.check 92 90 basis.matrix = true := by decide +kernel
end C007

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030
