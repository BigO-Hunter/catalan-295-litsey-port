module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C007
#time def pivTape : List (Fin 76) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]

#time def freeTape : List (Fin 76) :=
  []

#time def roleTape : List (Fin 76 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩, .inl ⟨27, by decide⟩, .inl ⟨28, by decide⟩, .inl ⟨29, by decide⟩, .inl ⟨30, by decide⟩, .inl ⟨31, by decide⟩, .inl ⟨32, by decide⟩, .inl ⟨33, by decide⟩, .inl ⟨34, by decide⟩, .inl ⟨35, by decide⟩, .inl ⟨36, by decide⟩, .inl ⟨37, by decide⟩, .inl ⟨38, by decide⟩, .inl ⟨39, by decide⟩, .inl ⟨40, by decide⟩, .inl ⟨41, by decide⟩, .inl ⟨42, by decide⟩, .inl ⟨43, by decide⟩, .inl ⟨44, by decide⟩, .inl ⟨45, by decide⟩, .inl ⟨46, by decide⟩, .inl ⟨47, by decide⟩, .inl ⟨48, by decide⟩, .inl ⟨49, by decide⟩, .inl ⟨50, by decide⟩, .inl ⟨51, by decide⟩, .inl ⟨52, by decide⟩, .inl ⟨53, by decide⟩, .inl ⟨54, by decide⟩, .inl ⟨55, by decide⟩, .inl ⟨56, by decide⟩, .inl ⟨57, by decide⟩, .inl ⟨58, by decide⟩, .inl ⟨59, by decide⟩, .inl ⟨60, by decide⟩, .inl ⟨61, by decide⟩, .inl ⟨62, by decide⟩, .inl ⟨63, by decide⟩, .inl ⟨64, by decide⟩, .inl ⟨65, by decide⟩, .inl ⟨66, by decide⟩, .inl ⟨67, by decide⟩, .inl ⟨68, by decide⟩, .inl ⟨69, by decide⟩, .inl ⟨70, by decide⟩, .inl ⟨71, by decide⟩, .inl ⟨72, by decide⟩, .inl ⟨73, by decide⟩, .inl ⟨74, by decide⟩, .inl ⟨75, by decide⟩]

#time def roles : GraphRoles 76 76 0 :=
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

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026, tailRows027, tailRows028, tailRows029, tailRows030, tailRows031, tailRows032, tailRows033, tailRows034, tailRows035, tailRows036, tailRows037, tailRows038, tailRows039, tailRows040, tailRows041, tailRows042, tailRows043, tailRows044, tailRows045, tailRows046, tailRows047, tailRows048, tailRows049, tailRows050, tailRows051, tailRows052, tailRows053, tailRows054, tailRows055, tailRows056, tailRows057, tailRows058, tailRows059, tailRows060, tailRows061, tailRows062, tailRows063, tailRows064, tailRows065, tailRows066, tailRows067, tailRows068, tailRows069, tailRows070, tailRows071, tailRows072, tailRows073, tailRows074, tailRows075]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01 ++ chartRows000_p02 ++ chartRows000_p03

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01 ++ chartRows001_p02 ++ chartRows001_p03

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01 ++ chartRows002_p02 ++ chartRows002_p03

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01 ++ chartRows003_p02 ++ chartRows003_p03

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01 ++ chartRows004_p02 ++ chartRows004_p03

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01 ++ chartRows005_p02 ++ chartRows005_p03

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01 ++ chartRows006_p02 ++ chartRows006_p03

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01 ++ chartRows007_p02 ++ chartRows007_p03

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01 ++ chartRows008_p02 ++ chartRows008_p03

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01 ++ chartRows009_p02 ++ chartRows009_p03

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01 ++ chartRows010_p02 ++ chartRows010_p03

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01 ++ chartRows011_p02 ++ chartRows011_p03

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01 ++ chartRows012_p02 ++ chartRows012_p03

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01 ++ chartRows013_p02 ++ chartRows013_p03

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01 ++ chartRows014_p02 ++ chartRows014_p03

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01 ++ chartRows015_p02 ++ chartRows015_p03

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01 ++ chartRows016_p02 ++ chartRows016_p03

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01 ++ chartRows017_p02 ++ chartRows017_p03

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01 ++ chartRows018_p02 ++ chartRows018_p03

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01 ++ chartRows019_p02 ++ chartRows019_p03

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01 ++ chartRows020_p02 ++ chartRows020_p03

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01 ++ chartRows021_p02 ++ chartRows021_p03

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01 ++ chartRows022_p02 ++ chartRows022_p03

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01 ++ chartRows023_p02 ++ chartRows023_p03

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p03 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01 ++ chartRows024_p02 ++ chartRows024_p03

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [2987843792825016917263287, 1460965019141081940029049, 8299630980953160173419025, 104775356578098349739494711, 331877969426374469634293, 1659846723216261546094915, 4979909218701768786521445, 11619693476438667413845555, 331906285245242764342043, 1659845283428861463313165, 4979937534520637081229195, 11619692036651267331063805, 2987755965793611867576537, 55770662540296700187138297, 8299599785559491713147775, 162006961100937730542154057, 30540989672966834189157829, 13278387682043725071789155, 75690412678379248512055077, 204499235959190705657503199, 86311390891151840920410961, 120172027234166937276722893, 19920011460194241780801945, 36183407582440096065147191, 338606316827330901455227479, 156024444372229599133903075, 404997696258288500594836495, 174281643385638364270460175, 139426247056895247295253619, 1288034010406995269797698485, 604177766028724154754810355, 730316914167030040901595215]) [3, 0, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 3, 1, 2, 1, 3, 1, 0, 1, 0] [false, false, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [673893916560267838331209363, 2918657526717090798470136289, 441518157074353384601430995, 3476374622957056027366239559, 41827806709562098925022609, 66808340598081075487487855, 1157239880344183321857662967, 532145656316944051279595561, 1826482979548689243981060261, 514383080629280413588459449, 627415292494943823198374685, 763853867333941077847274757, 503926492646426919670577679, 2350333382197269349518402705, 2957824764690059986850012625, 11990626846542745890675146535, 8019005311880355516162833943, 18258206312400848698876039685, 1095502797207381703121653335, 8617912848055372157719295855, 3228048673932991505891527157, 226398342711498647323977863, 12342556783020728725176014435, 3246315723701278283412428011, 15380696030592333117241799709, 8760611289584889545721440905, 189909426361387113825741883, 1247189092446915813110281373, 7509101771087883454293691359, 3555994406232796750344410803, 22699888375318829457709749185, 48575952304147681438112425407]) [2, 0, 2, 0, 2, 5, 2, 3, 2, 4, 2, 3, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 3, 1, 2, 1, 3, 1, 0, 1, 0] [true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false]

#time def chartRows025_p02 : List Int :=
  decoded (raw_ints% [3355363145816912909435596453, 60962524068694489340235369545, 420760622483926204564833615, 8830577358314011151778533335, 1848226938338970780444939707, 1591799481934925173881225875, 4782829461671957485315702545, 10315937160310987735382963735, 682502192569991162055531249, 12342185703716424801868892073, 292759714862749742329098065, 434449061470511892604702463, 817594390233884247356332949, 28668162627353225068108083415, 944919530255558414569148691, 130881240748848718623896839703, 67338018672094801134251225257, 151428373342665812843126261869, 19299851751745233313576945335, 8121030033536130848878661249, 42915356485960506490026465723, 13435362568618626129594379215, 90953523406310074310700745645, 24631099197950523314078139685, 99427281369541309595926639843, 55606743063291938201103621535, 34441598522729271204800571525, 3545408950613867278323518525, 66487766000045640102587672177, 90648308928418826264694338843, 131473448846857678493713740495, 284712009576675640842520676783]) [4, 0, 4, 0, 4, 3, 4, 3, 7, 3, 6, 3, 6, 0, 7, 0, 1, 0, 1, 0, 1, 2, 1, 3, 1, 2, 1, 3, 1, 0, 1, 0] [true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows025_p03 : List Int :=
  decoded (raw_ints% [1410934346722272136335289, 51657195779478633899732831, 22651455271802363881875, 0]) [5, 0, 8, 0] [false, true, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01 ++ chartRows025_p02 ++ chartRows025_p03

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows026_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01 ++ chartRows026_p02 ++ chartRows026_p03

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p03 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1]) [0, 0, 0, 0] [false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01 ++ chartRows027_p02 ++ chartRows027_p03

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [6265758598027116017433753385, 839573780689465490013895741, 224820874517692961468984199835, 227273979843743048398563772349, 2261211240904157963629433443, 2141418339086245960211264099, 216293904678761687487921013007, 109207985629570539259120671161, 2222507723490448103847563875, 2142560331915834792280437347, 216255201161347977628139143439, 109208556625985333675155257785, 6386437121586600925056055081, 839118855615321912290804797, 224864146006425026657042762395, 227272624428809077440917391293, 11856421413026651239346079467, 6060384535772522696964749525, 243107004541038278821444896943, 246106344345276698133173328719, 18383796338540278171969782185, 19194408443425312614638567779, 273347222292605208232760758595, 69355380465061764035435348887, 28153619683594042875268627279, 29034062810458013387806423817, 319884638314739529279999168059, 40706249139266297768023298393, 41445215536103689628718658525, 21822612069588279121337907997, 389483473534437261783986453863, 398329280063764953774668626955]) [0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 4, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 2, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [63536845800904810837997319647, 16501680452321878226598542863, 494465534871445762250702432035, 507981226012229024923738614401, 95507980099236740320863387989, 102226714786062126348373649545, 653510360771587313409563139671, 338107331303789332089253217699, 154354053144870213913770502555, 161761152784116386544200093903, 903372394015694267644197030215, 470101265088878588535540089423, 242828524747488378028395982513, 66573406199156918201355620291, 1300554971908052859586363515283, 1368257307758501236420702753913, 425163396546663721251127457075, 225185066008277603387492754119, 1968546893202204958865886954871, 2084921064571684116001110743315, 708325210225405006569291136289, 803961818849317402560243628879, 3102035499974273686686305548235, 208703313464847295333521242527, 1374033458399795875851264785863, 1474437889112661005047249878005, 5184394168599474569106861470387, 1404413180849883783235958346829, 2441359429425647261917178804005, 1454310132562029320553173444623, 8999787056424917706875305060255, 10000710877636254779097430154567]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 5, 0, 1, 0, 3, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows028_p02 : List Int :=
  decoded (raw_ints% [5377728743245144164739765163111, 183113178480351862484428484459, 16818875229095709133532249027371, 18768952854131573019705488546501, 10241669929569102806610136880525, 13079988967727725227297707622901, 32438273901909956104882151071007, 18854281766615278923252453836045, 26458887268527551131230791567443, 29348706245217261611376502813883, 69138831100006610042723079518975, 40068629373087772342589559054437, 54235380514244841376434291240121, 4802465670053445826289932636115, 149833098882779002550388162326539, 186325415712247939517194543100597, 172428154586403298998456314663675, 97622266080983306310739218207161, 376496633983427142925278768230335, 458409398595069685359311901692759, 381886438960815011112566825089817, 639385910499434958453550268150971, 930811227530645453036301907983827, 323259960314117814108585151564513, 1621342609489706512590611107760575, 1879892038705094592224819766772577, 2934040275981166976739479840834219, 119134930951906275222272207536925, 3894996496880150332605490026479341, 4448892268051660522883944945458433, 8450379382351023821935580975074135, 14589994365269416445105420298871043]) [0, 6, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 5, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 6, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows028_p03 : List Int :=
  decoded (raw_ints% [57771658278930019371604488305, 233990570089258772318674938277, 22651455271802363881875, 0]) [1, 0, 22, 0] [false, true, true, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01 ++ chartRows028_p02 ++ chartRows028_p03

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [799837446827306482843480879, 1600891013917310198828874981, 25854589599181602914516453287, 52279802016909946287131203321, 230430748543263257887097355, 513424559518465800888474269, 24824321403811033173785875053, 50165486443474170287413854071, 233849824876901396840727051, 513225351882439190332627613, 24827740480144671312739504749, 50165287235838143676858007415, 789181802554338844870898479, 1601525493185999692177685733, 25850772107575911554451130279, 52280038080906582559368320761, 1390837556386420297772847457, 2908393761982496495333586355, 28030791466516670697094876215, 56789957336075078746879592849, 2245930608637813550250579317, 4618859543632080264461729243, 31667559631540904545118302989, 64317210641689655506674908447, 3355020313602113130649452395, 7050554523952479048305113077, 37268510553780831226018334701, 75986624709274214819441750767, 5145137812062918285060742047, 10658769344500933924256002141, 45768668679445862641728529143, 93695948577727627792002865985]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [7672242751273918147741067793, 16352769419117284734918640491, 58586049242782699074530338983, 120707487341345846451177508617, 12215915523623814889294403349, 25518828287553210030436425075, 78474207517680432111565810125, 162579085048016341216532574183, 18933582776584872134542975659, 41267417035554718395009496621, 109623705817889119135403189133, 229365330371124269641978495879, 32451752994315877631638638575, 68501009083666926855981027509, 161009041588789868901584803367, 339133756490345914892969020009, 53164929402117226314141802209, 119697487460939857234952222787, 246625723985222972847365244151, 527332253034952698983902270305, 100613363123329384209982202581, 215114375546407344891523006507, 400404016510669583371489248941, 862144116042299901110377499599, 175837095444038695048939805643, 414653126405104513986922004805, 676854475078037662630411257165, 1491911617993811759988822510911, 377018698798802253665982195743, 818538467301941933206874937837, 1229710269320878611345333258551, 2725103211700858207182619453553]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows029_p02 : List Int :=
  decoded (raw_ints% [707202441562240664032845678545, 1783316033807534433699595014203, 2313931409681921529044161132839, 5326957712810334574089089405593, 1775208485691785285667516475573, 3924422206887003954986520941059, 4796342336935947478744523286957, 11034695953504872962775205360855, 3591225000828196674605163252427, 10016536120454282309767051728189, 10162775823455929439017203014957, 24975654280846159227528778030103, 11075413753560385984656260475951, 25004895712339073296391289968645, 24829414577844512098278626743335, 59997086113639514833687119726937, 24267738916729177948864895732961, 79696215533767586311944748480339, 60172567248134076031799782952247, 164698197359746174442023158175921, 99781539480516430741503445018805, 230818292980637383263945775705851, 184221845645379684722168123704013, 475212705874151144017913682362111, 237805768083512727096019765641131, 1060342537612513189316808398945813, 521809153209408842559691334363949, 1766373536467301716598667857013775, 1545291999577484493700073821590559, 3675873558398492583622041056601853, 2304906920870406063355784921595639, 6502589632478307489537517312561441]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows029_p03 : List Int :=
  decoded (raw_ints% [13327213523004454698679967083, 26940346515413628242980039151, 2516828363533595986875, 0]) [0, 0, 22, 0] [false, true, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01 ++ chartRows029_p02 ++ chartRows029_p03

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [399292056225897630897349851, 212423482750322211032967429, 13094978382560945856842901417, 13250467599340178830967570721, 139423441216925264985181257, 135029812475265560979381321, 12556262885118122960960370309, 6345295410682134423961127271, 138019688758685916950187081, 135070242480155558338165833, 12554859132659883612925376133, 6345315625684579422640519527, 403665033620175664437470427, 212359130775158509685594373, 13096543855038745194313033641, 13250419755399631422990393633, 753523290202230831659627049, 96528375898956654716743659, 14253732178861151690410131117, 14447365024141601680095531651, 1178196414741975623179072563, 1236636313307632585843336629, 16185451883805358145248830729, 1028514271540055468979551097, 1836629133544348265355574341, 1897494124251340254196231623, 19200277432091682033783477633, 4897589695549965085928096451, 2738521815174688862894705247, 726948419447304726241102299, 23775428380810719162033757221, 24395646584240419502873026623]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 4, 0, 1, 0, 1, 0, 5, 0, 1, 0, 3, 0, 3, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [4317501947263149628712651949, 2248173405110359413604603101, 30831452143248557653641114417, 31799787072250357235046642021, 6611861531181887188516815663, 7164793545036877557444716339, 41760815621693594470870582029, 21730463713753976809850282281, 11117949170520586224032582081, 11695209557567146745697234373, 59490626323396067883419979773, 31160465265055988961421257637, 17933078358045527346206957667, 10016876005710169425437650663, 88541653851962181453659519521, 94049892099099463519415050973, 33150902159069714487054707889, 8828149700728939842561366663, 139625634369077423286921185077, 149396242913435561740535818951, 57015512535478081160665493163, 66571180725548207271752697649, 229792049063625218934641386129, 62820005610474882095633495813, 119102795672166952278625096381, 128823747148254679956432530243, 405910357271270252373931975673, 55834368789462801951339901393, 220073884713206734107814435047, 17130976071560104881091448611, 745087037656643938760371507101, 849594314608918773664614919163]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 5, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows030_p02 : List Int :=
  decoded (raw_ints% [537131903481266291895598744629, 295827551348951716872282672831, 1502292825851116964763784686777, 1715345034451783885506643442601, 1072282719115874417079249458343, 1472769775128074029758718260399, 3111707448448257673738632889749, 1889884956138880674504963524331, 3209381758799280992980775380281, 3611613442373385006819709781313, 7393371926363413083798657728373, 4432076564889610192794177545187, 6955407532779103624238038906347, 5602574527953670504782913401033, 17558161217941797701017472015001, 23680915628059946401973891673753, 27700399399271875796806454015289, 998664130817295071426593481991, 52213968149992777122061964936637, 66843316870120729697190709899531, 65472802413290913924753018757923, 142460636485374873847855774813869, 145387169962555566843621437709849, 30157650692706130728837184517139, 411196541715645791745110607724341, 488219172059100319280791301827263, 622056514091492272513485064192113, 217985253521531059739836138194561, 1065010802391818779708190973102447, 1339170988637456062660775914224189, 2098263858198956843966786645018901, 6716844140695048808883239511502263]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 6, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 3, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows030_p03 : List Int :=
  decoded (raw_ints% [3373567609696710871935062817, 13675314564840823253033505579, 2516828363533595986875, 0]) [1, 0, 21, 0] [false, true, true, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01 ++ chartRows030_p02 ++ chartRows030_p03

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [90265584052943876711206053, 182311856063811527465208813, 2698835537169366235438119045, 5463279089962277549258198493, 26438256387322572372042357, 58233863187825767270348685, 2582131696729099786354870635, 5222733370710640254522640995, 26674370451937486914593397, 58220402083496145100257165, 2582367810793714700897421675, 5222719909606310632352549475, 89530319650439888743369893, 182354688239201741615549421, 2698572500896092076555384965, 5463294999929008519068356061, 158974366725586218829765659, 333867251694771948096698355, 2947077187272118184128520517, 5979516939862982208780603837, 260255450287931569790495499, 536413893018870505519486419, 3366307004285635972748781675, 6849798084576624662396788611, 393342518736291652628216181, 832548844248956253979594605, 4019904973309859195167493355, 8218760821844451421895869635, 618157200737397632912261349, 1284054731422762286662655565, 5031404692783548480707970885, 10335364397516169962538119805]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [938452542634437654872572251, 2022273312701034042620029267, 6588014436155383768492804485, 13641692441639966291820804637, 1549484339395795142582652683, 3249630202096709964720178355, 9075951318185616565948029419, 18913595956437710299161012259, 2461839182767391989402479093, 5456890145442054391195487693, 13087274840348803697933161195, 27620116303976474655076678307, 4440617585953529661003364517, 9427619987289026154049514285, 19989731609069725348339004805, 42504626436707555200321680285, 7512165619903600996689820443, 17362783830146766603983361075, 31942514814926856006032189765, 69295030254143347958354555645, 15260618834532801553583716747, 32894062992546289604630073619, 54715299269363258556305726955, 119551877076836404166967990339, 27754722696123375105402893301, 68248217036438671015603338925, 97730640800019435215292337003, 220694157105821364787201402883, 65726369846097790266817174501, 144290928333717079849205010061, 191211733342240600587512404805, 433233302475977115652009751869]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows031_p02 : List Int :=
  decoded (raw_ints% [129374394279115204059372777819, 349737572927321582255119029395, 386312497467453594913702357125, 927261803737015777756333791325, 374999987450314966124675328651, 841317232260653607065238800115, 890686879196883765097750463595, 2118316608924990967076691620835, 803260095341562077821754165109, 2536949155466045402745663987213, 2068946961988760809044179957355, 5496582996651689976887594408163, 3092378132798651683723144315557, 7116456595966483228938584708205, 5964585190128974570589078438021, 15149988748084218608571843103581, 7244896830994101012609126620187, 30739351028397027406801662858867, 16301860153921727266921349373765, 53005796372447729244312090670653, 43896530262007201104661928161803, 104048547146423819245009969234515, 67443287246923029384192404155755, 187793694547268575896123722764035, 113059136937839135268086955525237, 1099864111016027102872179002005485, 224398954446769365756941287842795, 1391706352709719498013312694004035, 1929713417894368734103522164798693, 4733207242115418473469017609107661, 2267171509278977235128550408166725, 7224777705841165074354509305117181]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows031_p03 : List Int :=
  decoded (raw_ints% [1394550560611155056074662549, 2822795473013044538361703653, 503365672706719197375, 0]) [0, 0, 21, 0] [false, true, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01 ++ chartRows031_p02 ++ chartRows031_p03

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [34463332683864559097329595, 9158618673937971893792925, 1031520114896575612643459073, 1045006604006221909269060259, 11832638488346622801811433, 11592956517194234561848297, 985224143724364430744318045, 498389586396637893566020131, 11756783591780866453559273, 11595098476078977304169449, 985148288827798674396065885, 498390657376080264937180707, 34699465209100799111370683, 9156915488897534075929245, 1031604537628680339960995841, 1045004075183829643482247843, 65354933812378080538567281, 33575877693740113778449045, 1131658936650159219610933805, 1148783492526900007342862913, 103197688716063950039087115, 108991349263226547071024305, 1300211559178601250188588201, 331231649294401695492696327, 164215085808400207667355709, 170134768495421789043610851, 1567624333703065407895031025, 100253294683515944880338779, 248911213648822790800644871, 133434311401838573354451369, 1980750633160288406363031605, 2041056106235354053837934053]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 5, 0, 2, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [405436978108662797566965501, 52987737301788859063164905, 2635098824917773994730641977, 2731826627453342073052156031, 635822423791095104086701087, 699520897122290416691616555, 3676358226817531896384308565, 1927624711494971681124545913, 1121001762798308661026098545, 1185986637774615307661317245, 5433182413406935661497108197, 2870378478943424543301012813, 1866120601710748804506370803, 133471516515367942659216147, 8420304777915993127029577545, 9062287859907351476810801223, 3688934090763742060150993257, 1980781171145703325602643923, 13975359470390483991686941605, 15159394466444645210563547421, 6602260585927393680012794067, 8016290568405188689855808965, 24266554147081619731850728929, 3392155922142655068953080529, 15171707011002225339246654469, 16594342890246423019790348535, 46040521744011238751110177465, 12936970208948213065317700433, 29431696953053847720655291135, 19578853607140863957866798055, 90643925708067311811012123069, 107499930940321003196794746377]) [0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 5, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows032_p02 : List Int :=
  decoded (raw_ints% [82595727940016990882377147701, 23086902402946182324624051841, 202671350601138150414044561905, 239005247766387460411024549851, 174767285614051087708575242919, 270530116980112083329934107327, 460034364155206229004996952525, 300941487179142136519727432271, 649990168752329167020208795769, 745842177129362062455248353425, 1284791818521586483733780991213, 809127634233879209412318662647, 1508621085398738828072000579243, 779815450706020850259645101755, 3443403072672654478825990366225, 5483359248421203882318466085739, 8809814871746526780990111673825, 5210407910414294480057782239505, 13761839029817920087888102619293, 19023436872073876243472610971769, 22555012454422563450410033989147, 105992140481631189952778383704153, 45126666355987010319288248282265, 33859098293633413789091639788733, 370048722145933106129303355164493, 453487597958653736904066964435339, 437730400956342679899001637435905, 86864516451852322751651488411803, 1051297935088326171907251113423223, 1695764193699273007724721211713755, 1859077058190601957935556106023621, 2243124657825073696532163551697747]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false]

#time def chartRows032_p03 : List Int :=
  decoded (raw_ints% [266495861895110042935197167, 1081641078701973796844231959, 1510097018120157592125, 0]) [1, 0, 18, 0] [false, true, true, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01 ++ chartRows032_p02 ++ chartRows032_p03

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [1689079659295994087015259, 3432347980919563085805669, 46200437697238309127213827, 93647367811947339142351633, 496775904152848110866431, 1091494082139540970729901, 44014582133789466929332137, 89123525748888235085816063, 499643303322608367288319, 1091333549320692791607725, 44017449532959227185754025, 89123365216069386906693887, 1680156396149016959505243, 3432858382667617424115813, 46197249232430852512547587, 93647557148057697122417425, 3005760669714592561932821, 6347456077719963319737379, 50883166298294462033985651, 103427871608445277866270617, 5003234419861724556103873, 10341859976230381373839739, 58892161387870779152022345, 120117187662395622559847735, 7671490443022721073538911, 16378897223498858701629173, 71566886250755224781665129, 146837944862124862635316647, 12411579141090550700076651, 25881312781145555274114317, 91649955834868496555280691, 189098154866769276611060137]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [19267976837087288074536421, 42095618369173521960844939, 123329511813046335329893763, 257075086017088353846019393, 33243703923081917072540385, 70109983457161946892712067, 175841192573215540476970569, 369280687843423822699576399, 54464582231072771565806943, 123438003014637105425931357, 263549478727370229115317897, 562828674315222875018219823, 104703137644046750647708443, 224070837113518512002934741, 422717198602489751328833283, 910337514443378492447085921, 184270816707870751144645653, 441808153563483586707684563, 711691152954407253121187379, 1576216505120380591157705225, 410371536067178920478369377, 894412628394667104789754219, 1306333505729456924744202409, 2912437287078531282655144007, 783811367947105617478124031, 2052208602488354138782613477, 2500516409743741462700695817, 5859058517961552526227511703, 2126422933015318122130609515, 4738586497988888071466137277, 5410750710706165202309429363, 12649853618438794736476262457]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows033_p02 : List Int :=
  decoded (raw_ints% [4440515762000034281192931493, 13468385778464949887184362747, 11977689405721517605632970371, 30856825894892632695126762481, 15929317099914513089852252993, 36449765601390108964172497459, 32347522267636064976678154857, 80774977274747691546483622687, 36600381240951157467447557439, 147396109157882030862638725005, 84877220608501735533977965289, 264620852034019831373294845151, 205662138733947233700530082139, 485534093087777326188747096005, 327139740583400126701955604867, 897551054279679188424680666161, 523143527466709027508986470293, 4744036849238612016901058436355, 1055945406784056387911472157299, 6127121996606068531514486198521, 8236124504809858745083613849985, 20170065578936349629634096292059, 9815213439060624160504072477577, 31041224424781030178049640926935, 23344738620786272741591978413855, 142849045011368889592872480263851, 41396076564656755647179664741417, 91637755007651509785188743044857, 340623691769120183414012531205397, 870785520547528051201770327738131, 275882876583677155025240888050125, 1105272320566548450579831551046839]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false]

#time def chartRows033_p03 : List Int :=
  decoded (raw_ints% [23944758678267151607114543, 48539857896433451114078651, 65656392092180764875, 0]) [0, 0, 18, 0] [false, true, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01 ++ chartRows033_p02 ++ chartRows033_p03

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [870865506453053607033477, 464051168330619186636765, 23650238248489858611756039, 23994873683915310940907027, 296068296018518481211607, 292048850367024015527639, 22483304446018286523510955, 11387361248443524276052929, 294806697021994507346135, 292083881672906501153495, 22482042847021762549645483, 11387378764096465518865857, 874790428666155471133317, 463995497717627981740509, 23651639972709912528124935, 23994832405301093502366227, 1667576427386718404311303, 429631809605216055120655, 26194006828762786403569555, 26641350639157213686329865, 2664165670243864602174557, 2835669360148824299133027, 30525748926393369410055415, 3899443404715862775743189, 4346769672720849587871691, 4520295827219293951332305, 37536684269358083600101663, 9637878106273755114102711, 6723478293191612027411281, 456146521675118587327179, 48606932235270545215384635, 50370152599116211804978013]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 5, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [11399651128103515946245203, 5991408918508245083405785, 66730061656565673189041119, 69651314782934599369024447, 18408490798667316747344593, 20668214777786419939857245, 96538203583336505882630915, 51151173698868754737846631, 34456226385707530318494591, 36736950227741892016090123, 149402920767711352948470099, 79853756201632910715820315, 59626857340885190680026717, 35300847996654216007951763, 243486004494304073946991407, 267046158624316145463634279, 128696842905755816385066079, 17465462462080541011291237, 431809704740945081012084203, 477371554314268905569867701, 241874255634180488911160709, 311613490766503802986170263, 802380803280881386308310991, 232177186194354259161591965, 634008608891898417737293555, 703886550214044142805013765, 1678263667806960292956765255, 121513049109872811402346993, 1305654727438199246834307241, 484917331182108077904128231, 3617927004137057957528366051, 4587764660700441436859078577]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 4, 0, 1, 0, 1, 0, 3, 0, 1, 0, 5, 0, 3, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows034_p02 : List Int :=
  decoded (raw_ints% [4513359235145432335060143659, 2573893825187125889116666767, 9436940966720689539422816951, 11675221635803125526708925035, 10258777403767943195978739577, 20106684990741562880486773393, 24209077605634065070461700187, 18464847138459470092714515981, 55395825920284932794929470759, 65245149018513695175488876607, 89863680929686941061369910523, 61140764143087099120702340981, 139930166829716971916117825333, 305711775666802445515896421705, 285189673679688845772417206615, 798950228638292784448686401979, 2110438045754700687500006252215, 645484276501669178013197447941, 2535557886264106505188541284163, 3992310885978574387533269037153, 5966942165687588501295028837293, 17263153540843837503870553392693, 10612938097706395693983576373671, 167014149200915412566945227559, 83096936540505227705572277497573, 106327004899630161593498622747847, 66517056277111243510293672286609, 33569765997333146375413417676079, 265081088683197779464144964833535, 15987755110624142314756059925137, 414695081500814250680010914617717, 112704028003969608577103814051067]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 7, 0, 1, 0, 3, 0, 4, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false]

#time def chartRows034_p03 : List Int :=
  decoded (raw_ints% [6130275938735728054697379, 24922976020576549314180557, 65656392092180764875, 0]) [1, 0, 17, 0] [false, true, true, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01 ++ chartRows034_p02 ++ chartRows034_p03

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [985979712168365549815023, 2013510921552394214163219, 24400531460061310266568735, 49539489063978763023708555, 289105065527886173777111, 636981710959723157531875, 23125446682365058542976601, 46888996431466645652013461, 290226421304691582305495, 636919904890070373819619, 23126568038141863951504985, 46888934625396992868301205, 982492032698643756805359, 2013707300001814139031315, 24399286492145199290615839, 49539561830288877381152139, 1772204113301649182146417, 3769181282986389644717085, 27153982638145492229567615, 55322450413277081164900539, 3011462306670837168335977, 6247364403146038927711245, 31937649058117978580050009, 65338996099409509737328869, 4699600079648754336604119, 10146681652705218579137811, 39648711444437570084990105, 81733042155260767244177925, 7882700839442091316731407, 16521397168039367760767875, 52231012363528415738325631, 108401120976005353584083611]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [12577792577545798551468817, 27993382779208230010494989, 72691505780516305606525855, 152915900923252951355346475, 22948479563882771601320937, 48758914556741562988718013, 108217777921944875759315609, 229668198259202744354559477, 39043077408171784223325335, 91329331343750127532203651, 170209334893999431583961881, 369756444159694434875481141, 81624028307273915016435695, 176550772555980644274417459, 290876440609445130823722911, 637636548059425206682102251, 150810411089241674292638193, 382359742579610358350000829, 523310880005960720132796799, 1196547063195016209306520539, 381474634673463453098289577, 843841256143981658728871981, 1055595925768665847523724569, 2422748061918608226385393349, 773922831851794736968526615, 2251680049801436538314304307, 2210993392293924037590540761, 5518269367864026423428569637, 2574039801225820149593265807, 5852349155406180407087279139, 5558956025371538924152333183, 13622298573071643368830153083]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows035_p02 : List Int :=
  decoded (raw_ints% [5782695876508925778019500049, 22047614918883533277472445997, 13915691703106284851765099039, 41522262647361357053389878219, 29955798283523394849312626089, 70395231462724296475790731101, 49654185863138605479097225177, 133965109028969186806653055317, 75096170481892877474936709975, 631534958520400177609989737763, 154706154628554877803346561241, 835895299012093660892433524181, 1082921777793491205420793429487, 2647191535801785182126060837971, 1312724102903938960699076700703, 4114621793334279020628484099915, 3053443345534695075935598106993, 16651708567849667350463651163043, 5449089226232125242055468237183, 9889895238713603147709106225157, 40493225604562216058219291969559, 103745021925994230203322290182323, 31990693032795395740228225625383, 130286625732557500701495047570523, 129557035988398723366141594532521, 110639009058409632509147249036883, 202040954625756335164589112127463, 123392638600142098395670088715963, 520885315698178927808796979108367, 1411523852848538027488690992177603, 189287325084023869278066272448383, 1398770223306805561602168152498523]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows035_p03 : List Int :=
  decoded (raw_ints% [12693255586114837908191879, 25776499992765578618935887, 65656392092180764875, 0]) [0, 0, 17, 0] [false, true, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01 ++ chartRows035_p02 ++ chartRows035_p03

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [256747302378923194677129, 17192230430954677087357, 6271830828903862863099995, 6375162055747388042182757, 86741617724576113952771, 85935055698267315602915, 5928341908800363554470095, 3007075656576922946591065, 86490315035006160171011, 85941932410897775915555, 5928090606110793600688335, 3007079094933238176747385, 257528717298154897272969, 17190865229692615702609, 6272109638443954658132315, 6375153965952455980652069, 498667625069011450250027, 257866518601132892936025, 7028305980811121005655311, 7165940846829803617765863, 808068181372885345715177, 868838022782988126348051, 8335041787253017801620515, 2137627976703764382496491, 1360548103317170363711823, 1421707719321208440044665, 10503658071943073511047515, 1355132206114906762047335, 2157666489277607687039837, 1190910097430759595018025, 14021872664537851561799175, 14644585563101981726459395]) [0, 5, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 5, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 2, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [3851399697573691022352703, 1019295591370810121308237, 20030938851389150271191715, 21103588123446741401728393, 6448263577507972209186549, 7453529138340522453495785, 30330602126470813502730967, 16317149813635252170228563, 13066189700772454373257339, 14075570576283522267976047, 49845055404751240085174855, 27081699670947274530964479, 23721639326081208116202961, 7399008729697847337467205, 86632884431604902574635155, 97835004836969460679773825, 57874671322230686793812019, 31879606117942190445645115, 168229195079916797484650135, 191190251991645230920932875, 115565866972994941861333921, 164603053672217113097588191, 341669733375142426139796075, 13111016184367085153431603, 369405809420647881873872903, 418469885554851430451703365, 826641409768785249875002899, 250656364281703817114775713, 819502056405115016197733733, 759317273045459492577286667, 2015549275594548147946609535, 2939729888772585684065379551]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 6, 0, 1, 0, 3, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows036_p02 : List Int :=
  decoded (raw_ints% [4066128262132798026348952967, 595667556947474976922651815, 6901179594132461190493296235, 9223704890443304484601167405, 10109603241648488192629218413, 40848668121376387269478369845, 21076911097913747409471467615, 27418856733699745784730375885, 139109337740075774666306089587, 169848673490987698559973306427, 170295852079638010268406775615, 132767527539881788699456214021, 391066415242150756714651828121, 125157729025460071090654330685, 700471605061864541649364693323, 565878103632929292766348911011, 4926289497039099562996548327749, 3159308332569793800595681221091, 3834751476735084264632531806305, 7885756600976197462682945998673, 15812954081722302035487004941351, 5874201429276134346846965535275, 24573995055496485863116085075405, 2082542959209912679256835726395, 60049003377588241021358420351551, 81736164059035298422213788554385, 19662054240369453122755330334795, 4955012103216986378252088199005, 222659603562687013681625318455789, 6695723701997057860232273810157, 302370661180644707825739069142135, 174407805114501196194711747358779]) [0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 4, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 5, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true]

#time def chartRows036_p03 : List Int :=
  decoded (raw_ints% [1632144532820696514444281, 6650237742642662875580469, 65656392092180764875, 0]) [1, 0, 15, 0] [false, true, true, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01 ++ chartRows036_p02 ++ chartRows036_p03

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [15448432328450294235245, 31694588906262069192695, 341555672260070635383221, 694866788936268771944291, 4490712161684273779601, 9963600567730635303743, 321616527769936067368375, 653208599462276067447853, 4502655516357571186961, 9962951268334561463231, 321628471124609364775735, 653207950162879993607341, 15411303665638254332141, 31696650782695546853495, 341542430306605190294837, 694867552213910101924067, 28068038717757013855747, 60257521775490151975345, 385021772690000458482725, 786821724772095800752907, 48967662449828021907055, 102052076872459911527305, 462057473857585494245527, 949131323420045864255557, 78100790127506765384753, 171208165940196277823399, 589125926434920281537335, 1222391566232702053606261, 137247089175551002970237, 289589748715999989764927, 804473805737978049892325, 1683189480888898321194587]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [226584528953391208204627, 517905945415045892812345, 1168305423866920261067189, 2490685175019944203771859, 445395743747758366245199, 955781628003758180357425, 1840285696568069835517015, 3964372748438748276941629, 794187239558608420019825, 1950544111421524592896175, 3079868679874436621782039, 6870698487864031050195229, 1867317999978073979507501, 4097427564678188077654823, 5741373919411119021309365, 12918670163963743720746227, 3666031889841619776274819, 10222384171664802057813409, 11274723809230812777091685, 27238481900306733856214459, 11245386563668290583569679, 25382683344017522516752825, 26186142262740723136936183, 62843549415989058430780693, 24608561670856844090091473, 88595243461250805050427095, 62040090497265857810597335, 176821476221257385997960613, 116727977017119631337101565, 272838564371167355344478255, 203376629185242333237790373, 538255284053675546392865963]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows037_p02 : List Int :=
  decoded (raw_ints% [287612613037238603924661907, 2229870065179784989924921321, 607717219239600568499553845, 3040963913604627891662265539, 3767786927267973140663417263, 9190233159766305447814570273, 4663116759544812313087633015, 14461067138550718329401757133, 10557279851959426010377644113, 50548016203154883789162292705, 18988183538772211464128694391, 26896715904837860011945965299, 125978379037496592739743290899, 323619279414232953935016197545, 96432915646764955265236952395, 401064011522225697736124455549, 405839080605432148400923457405, 256470709537878901468054838545, 628250375289693696405903700699, 468212581398579750203085814549, 1450597959324118692477699882799, 3969345037397566447022602216297, 416508503428992847670872724695, 3757603165536865598287571240293, 5443333236752327657490728124401, 1013982679070496371192794405511, 7310439699505439197639300731895, 8740930882004928416502967862101, 10309299074687781265073567320579, 30491280534495081804129552834145, 2444473861569985590056461535717, 20736366973419657016433790566533]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false]

#time def chartRows037_p03 : List Int :=
  decoded (raw_ints% [178502052294260464809233, 363280688921265420568493, 3455599583798987625, 0]) [0, 0, 15, 0] [false, true, false, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01 ++ chartRows037_p02 ++ chartRows037_p03

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [2706809805789635862167, 1461937102746528832941, 58801070104187657226141, 59916206743182780547165, 910665327206232827549, 904821003354416572717, 55183594971191788536425, 28043755767167653154283, 908856446784435226397, 904869864342822274189, 55181786090769990935273, 28043780197661856005019, 2712431891008651471511, 1461859542454729224477, 58803074428563077633181, 59916149344575992733181, 5361156110836095626397, 43508269545569478687, 66876662430407824731089, 68408926931318344454071, 8841489894650730363439, 9638516768068094454969, 81079308435894650720925, 5226031387576208261311, 15509931172134821466601, 16309678359212178486771, 105430729502680202550965, 27391174332124901280679, 25377361197928340650443, 7175121640184784201189, 146318021872743364668009, 154574862248450920414243]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 8, 0, 1, 0, 1, 0, 5, 0, 1, 0, 3, 0, 3, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [48537292674965044451537, 25935993274367798988845, 220232675745636749769989, 235147335357925655196689, 85035999647083962357243, 102825105036623081712543, 353805968067685756578769, 194922213471642167443461, 192691128177359357684149, 210509428999641994375769, 631533095892129076620161, 351589480489774705487617, 371619459996765299777535, 253571615266443250528631, 1195843684066253734081845, 1420831620512077906408265, 1092642873960656046989829, 307059580831216606961997, 2660106018023675080849209, 3156213174369830835313515, 2356048085381388317634759, 4117241936549038449925509, 6108796977365719445473797, 2125423358560933928271753, 10664228701472721117442689, 12425611538422709217850303, 19129073764219828880551245, 3130568363651935422607853, 26017940665364006318881075, 12075281999869142186028105, 55811243131056556316875009, 134072414446591330086937967]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 4, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows038_p02 : List Int :=
  decoded (raw_ints% [323708913963611816197694521, 197146893167727772404815367, 405538097760032378833450605, 624968456781000012384793541, 903739376749234540524252819, 2013257670707120334977168277, 1632986388472878735555397945, 496997713795332388891372001, 10184218350290562237154873267, 13101213515249179962698238939, 7647492585068448961075222503, 8054233306773482537729075609, 32940156737164829917007462041, 4290052912877472720319171025, 50771867672523841115237557811, 20629574303041199597518048107, 110384955127640003833723165549, 18988153143958729284281943133, 26672930717951332801478145697, 139855756674383580117375839007, 419791147088564159346583311199, 52935526245654621231836201553, 556849032934155495981784622445, 43087063508963504452933448203, 738225144322149837599544981735, 1105080729600671137776991523445, 238415035700569817728822951909, 176862173820827120230421934067, 3363663776846949035255459441509, 241697955583093016162276334273, 3863473885468529055126181471335, 2779321247216351683347784596805]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 4, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 3, 0, 1] [true, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false]

#time def chartRows038_p03 : List Int :=
  decoded (raw_ints% [15376969977494323272077, 62840080948675838213047, 1151866527932995875, 0]) [1, 0, 14, 0] [false, true, true, false]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01 ++ chartRows038_p02 ++ chartRows038_p03

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [184806540748711682637, 381022414874675760509, 3594408522919172473165, 7332075621293000731101, 52957298671308293101, 118833303708561989885, 3356644683499152497427, 6832219902709762980707, 53054530674204289069, 118828082184095746877, 3356741915502048493395, 6832214681185296737699, 184504401691091208717, 381038987864493055805, 3594300847867343991181, 7332081751233885540381, 340014641672599405107, 739346756840690697155, 4118819891231034605005, 8452467495939069293341, 614159828645091375379, 1287590524285963253059, 5072994361548725385491, 10479404777065723243555, 1006846749609144350253, 2256134273490850198653, 6694000939802961111123, 14023129574842536695267, 1884415219118320321421, 4011983375272982078333, 9585262908530425782797, 20291247223606368972253]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [3248289562700179163571, 7738702628797487566339, 14717967690348925267789, 32041933227676838616925, 7096410913076296484115, 15436978335997282192515, 25062668166125400915475, 55217614192471608375779, 13432845283141792253229, 35884706183521255328957, 45591924362343489652819, 106539298711990145897251, 37807310887682629667341, 84638614874529511587517, 96832080533167911573389, 227062619770040912813725, 80229762690551971587123, 272032913040537505868099, 214869154111402512827853, 583734147685107930269341, 345798989812288438894611, 803184028687462041763011, 640897906614242923309587, 1658951089413107477900451, 834540315059795234149677, 5924704532695764636331005, 1821237211486326596353875, 8386839650796334155994467, 9834529445459650365468045, 23924718350830536674904317, 12490306972005772195971597, 38236262534322635467229789]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows039_p02 : List Int :=
  decoded (raw_ints% [27345837495681977384722867, 112744346720207275039732349, 49670673913147399946162509, 50583365835054102897598243, 290014897877238155214378477, 747465703592369497203311101, 212998386468408777883493101, 910793416147630875140641693, 942247448925944661362588115, 386285520628178250285763133, 1445260733271591594460459693, 1271973599111822122058189661, 2947080836985483978511080973, 8164942519431752514481928765, 559572654787947722688033165, 7279254440948108642709502237, 11377970813818481733304283699, 3618568112290515131186107075, 14884624305591913434503397837, 19062765072670376288377538077, 18465886240041417182747434221, 56069144066247227080015435709, 7796708879368977985060247315, 33387810881286335660451790557, 86584486466230101527840286675, 53756244075425692966465634435, 97253663826902540725527473581, 143213199022959255706932860701, 84122371021650234305496738701, 287657481801034924644903234173, 99715779271482407947871021555, 90688038702649975971504739037]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true]

#time def chartRows039_p03 : List Int :=
  decoded (raw_ints% [1889607531833942077901, 3856549018083838245805, 67756854584293875, 0]) [0, 0, 14, 0] [false, true, false, false]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01 ++ chartRows039_p02 ++ chartRows039_p03

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [208436760328784306899, 56964439432932094745, 3967212385361455676137, 4055890909092171114171, 69921707673241574993, 69613334090733521001, 3688853917359429794245, 1879209908634854607095, 69826839312333372881, 69615866961237595065, 3688759048998521592133, 1879211175070106644127, 208731496893525209491, 56962430067220425149, 3967317385204380174505, 4055887937370332583915, 424109047976143010521, 221523050832746417661, 4600157930074048394517, 4726783759304707119833, 715234813816160110755, 795390584753057180689, 5739501791866351515793, 1491305111430814283961, 1326983663403765490725, 1407278012276119979091, 7781720269086277117273, 1020986130344054286953, 2259909908480788824159, 1327135243846756455913, 11368613840970831432157, 12229437542722067186541]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 2, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [4770278470408708508261, 645654795702120205763, 18398802219860328764577, 20048946396032541744471, 8860486613169640743735, 11586166049497086901803, 32029567303438678016573, 18400175405573295146189, 23853412501240357611481, 26580603264091627451981, 64743466417848676371789, 37483560062367652323081, 49755101440716153841227, 5111726271799068459503, 138351980359805187824497, 183335343737612027450191, 203786866012467716114257, 117911541062131975852507, 391893947812989057779981, 500946046210661074507253, 485963495031404220750315, 1646000701323173664675877, 1081644308856860994644553, 148923114353631168180509, 5408288949217418501088621, 6568335858521072557658599, 6975896753105683716483489, 2649276597375586228305655, 14970802040618049007706839, 14186994951699472697591801, 27354987742941151225278949, 11208547655375527924302383]) [0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 5, 0, 1, 0, 2, 0, 1, 0, 1, 0, 5, 0, 1, 0, 3, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false]

#time def chartRows040_p02 : List Int :=
  decoded (raw_ints% [148845852644049298097236707, 48047654032340088521855323, 106520062860490097864250919, 231773153688134827406907277, 486041561269960869162918593, 72659298000092208532291647, 741407476774500265124406219, 175652235908701486481018461, 1411566167184339870552240481, 1970267122158681560218397537, 184117129139878736264915669, 845810974170685397894326131, 5543977715536007368932027779, 265947234397042333227551931, 7139661011860225975749183929, 4725678008088221688917257523, 8244365847903677276775465143, 6362277124152365747320708551, 4439272879492556067905746565, 6935087302628340472813951855, 39953463012947578793946765901, 13317821703152591625615800135, 43758555981358700002816484479, 8244365813521415898267792273, 34880005061188468362205796405, 61515648162885316825948504827, 48832013933117810434557453975, 951272700352941350453845975, 216256045542111909373329192399, 44181340523376764221657358245, 202304036670182567300977534829, 165098692415285906876524756917]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 5, 0, 2, 0, 1] [false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows040_p03 : List Int :=
  decoded (raw_ints% [1043912286422559995759, 4283748666823899493151, 1151866527932995875, 0]) [1, 0, 10, 0] [false, true, true, false]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01 ++ chartRows040_p02 ++ chartRows040_p03

#time def chartRows041_p00 : List Int :=
  decoded (raw_ints% [741949881217490755423, 1538490856764454950393, 12444532049563957917735, 25477499399339962355173, 208105675334917675267, 474896528472548592385, 11494476493011549487045, 23464112014102958812395, 208368174942228921187, 474882587295413041825, 11494738992618860732965, 23464098072925823261835, 741134500041285916543, 1538535086397936350361, 12444241667602375570695, 25477515746619172654021, 1386432997771071946449, 3070700181729667959695, 14571809165414733433687, 30086751014746776964077, 2627399867875906109949, 5552487349444883081959, 18585642031061711490085, 38709938545921328005731, 4463741965366881997571, 10351230176242242941865, 25676783864304499597605, 54613656071608454029555, 9147576553874815778639, 19720792144222321179585, 39288102383546197373815, 84685678392073018151005]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows041_p01 : List Int :=
  decoded (raw_ints% [16682689215328128804321, 42726067419247545045367, 65118368152749141956775, 147132537955542884375957, 42939179853964016703453, 95244468442592856252975, 124740237222041287464549, 285103073817383285674299, 87927887961929550294723, 280131898834604158206033, 255607305037934854462725, 660479441094580300133307, 341468841891385199119167, 787227041538962807289225, 685004034891249603876615, 1727838381468147265628565, 803588511333225666045393, 5183390605399289904903615, 1830061388115860469041175, 7698456028406399977821405, 8418135346240743278597277, 20412517796338844684601559, 11051785245689829413683845, 33294364430144534567326579, 23185176388862977145963171, 80183897147355870650423655, 42655096980793549838244293, 26477014920872491398495517, 215156282418678438871370929, 556866721093364775553127439, 149316009049021911887163465, 663527633161593137602046611]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false]

#time def chartRows041_p02 : List Int :=
  decoded (raw_ints% [706606053738235650509476191, 132856147887821483795661415, 1071078345205936001268010585, 1087538206367136429359512635, 1894080685670792707481646141, 5334229925123764054485916895, 116396286726621055704159365, 4379547866644449108922065675, 7586904532644178344518017699, 3409345544357608910974086273, 9597381505041592107703823205, 13123123336125822074382068843, 10249198662243931574569508993, 32262859732273570621705017095, 6935087375441838877652331911, 15730390851790139636348861979, 51614226672703456438789033903, 36762094497056621207868354193, 54928337959505549135706210985, 84755345081120331465922233267, 39953463013537602036410868413, 146373289879447409397226200135, 66589101618671403538084376475, 24855850301270456723435612675, 264453880404523071160419697347, 225134599619697025598295771145, 237818241799389269658746189285, 396363739800414891718957583955, 118592024583189693160658720817, 540957182218022083747420039519, 383680097620722647658507165815, 80541157202089833569833315581]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true]

#time def chartRows041_p03 : List Int :=
  decoded (raw_ints% [6593240965390724336579, 13507995128052208652783, 3455599583798987625, 0]) [0, 0, 10, 0] [false, true, false, false]

#time def chartRows041 : List Int := chartRows041_p00 ++ chartRows041_p01 ++ chartRows041_p02 ++ chartRows041_p03

#time def chartRows042_p00 : List Int :=
  decoded (raw_ints% [7566173533281635933175, 4209309276612423135885, 123721187938562006936141, 127090274046435813800533, 2532891357420442881581, 2525343501304400510129, 113622123047859928121385, 58073155995953283509317, 2530582242904919655821, 2525404502838679787273, 113619813933344404895625, 58073186496720423147889, 7573344882965322719031, 4209212529617075438505, 123723741059214647270477, 127090202555513676960061, 15996428228101038414157, 1052313525112833003715, 147293514170281008403665, 152345644016553155896511, 27781864268053912690415, 31870645817798098676645, 191071806666435959508237, 50263326559039145658149, 55922426506983530911593, 60014489222123846297807, 274776097441473403110245, 36617305159509815950881, 100431239606474410677627, 31511199748620043044419, 431129763554931344699465, 478997729492682546082531]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 5, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 3, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows042_p01 : List Int :=
  decoded (raw_ints% [247394290257988336443857, 136511136605532063791645, 778955293419394091820949, 878064801698226845843497, 496869272721805426767819, 766758159750662667147515, 1523218856399187855032625, 958922617329976820287151, 1825899803301051478610565, 2095825042737224852273685, 3845987932422044760411009, 2390214218573920579997751, 4234631291624991025105791, 6487899004858220051578947, 9906519027348087264127365, 19852051489601506115427081, 41608029652314726883809429, 12587321254582571221939073, 55749179971287805173042585, 83177134517648231106341267, 113946449477066694758300519, 178126377178358928685780655, 211303659100669226815152533, 5574994705297551586460387, 982006437319883831143533087, 1274079032280640225112421925, 656756328742147909570080035, 374201341775344891622471419, 3246249703959859932920922045, 1954626354721957622129015, 4885012470021891673634535167, 2645788312679814503786050641]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 7, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false]

#time def chartRows042_p02 : List Int :=
  decoded (raw_ints% [7974890192048424848250405017, 5673118329640898043165970759, 156371981933326758305052195, 8825544433304186870362147837, 32681415956990194581747878083, 8412727289180745334182951079, 40499934167105292671693230905, 14292254190883364145438520217, 39686812949305832675014356867, 63955499351750293815393362655, 33494537174789654578426752121, 13479131840401410095166685571, 209129787465379704493292614969, 39606392879429807863385531555, 215322063239895882589880219715, 170126548791412729732497796907, 141095244844626778754515334365, 33876531931385265374163376475, 283356605860648808328657500319, 21672920900809777534038151783, 1010988319580454638957489993439, 447384665089521933463219133181, 868726958564432609383347827485, 185017460360353458497641074191, 373533223647448322816618788519, 937136836056915265948806212377, 1506182054497438925524219032405, 7822427202313140672030538049, 4012469216513219057119477265909, 481978308575677145220270541475, 2879820385663228454411877022023, 2614732399885603345324911160709]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 4, 0, 1, 0, 1, 0, 3, 0, 1, 0, 6, 0, 3, 0, 1] [true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false]

#time def chartRows042_p03 : List Int :=
  decoded (raw_ints% [32821840367960910717329, 135508892599660660072303, 65656392092180764875, 0]) [1, 0, 9, 0] [false, true, true, false]

#time def chartRows042 : List Int := chartRows042_p00 ++ chartRows042_p01 ++ chartRows042_p02 ++ chartRows042_p03

#time def chartRows043_p00 : List Int :=
  decoded (raw_ints% [9271932734141128137501, 19366264369184381393529, 130542161850188652362493, 268659400117583854094401, 2519255217836703886613, 5894521100018399725393, 118750973898210820338379, 243398614648381072975479, 2521400969777736459941, 5894408287951159415137, 118753119650151852911707, 243398501836313832665223, 9265269854183549797005, 19366622135604757549593, 130539790474113139168653, 268659532259869749629953, 17681303593064679045235, 40296562267010712119831, 157486363921361368010893, 328322716662485219299377, 35965247493708516352187, 76863095432222515843455, 211132915008134563408315, 445482374361718447262663, 64114392283963319937301, 157932634047882645736369, 311212554785806399697803, 680278103841823608842487, 151671236034130135245949, 333061571463842507606697, 526998183103899854881053, 1171272309353548762185553]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows043_p01 : List Int :=
  decoded (raw_ints% [298666278575461424784195, 892839355973862293199463, 977335697713491414911197, 2397173236791253562991713, 1036674918762671601584587, 2368900434132312210391183, 2312676895051624441279979, 5658913026897428066582359, 2365784752163819792828997, 13742636797711248497855681, 5715136565978115835693563, 21770450258740988774829223, 21717029172332185808468781, 52445232349177814674139513, 29797950490474121436991341, 87958319405630051946824417, 59090621601527437938512467, 165150383019709374352750985, 110605601264333745183972589, 24746831264901507731787055, 470199038414805810390995685, 1223729433808128251277358625, 300502815548944627268510629, 1413626648092739133361896665, 1566151412388172319711238347, 53029751465787090130112367, 2336853266351922757370744661, 2690385833366654474769367657, 3496442360259576269553247645, 10072158542852676839346148489, 406562318480518807528735363, 7328742958020235274446668465]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, true, false, true, true, true]

#time def chartRows043_p02 : List Int :=
  decoded (raw_ints% [14717583777574373459297040035, 8537825086405674584039388231, 17807463819353430921321552317, 25938726587278586697832205185, 15855959742596974020068551253, 52609259578644624392950061713, 16669087854330830360550041099, 18132707904960363111078468297, 88224183449669674205060060955, 70800052062093764599741712607, 87411055337935817864578571109, 141542019545698752103770242617, 50704222517748793230705247949, 207056768692490859916878567385, 124931016269856698838933384115, 5285302915301656786633387839, 400929275799153807577406699827, 368171908397882657113848506327, 326702482047045901969178563661, 569943374175071860244093685873, 116218957320291094157821634949, 666124518367684894420216432833, 611412800525908615388763628539, 271990764205269622937725759367, 1500740397893941408102196295595, 1480528404058145901557090513807, 1005546554688323886871254302005, 1874662158220561173039581187273, 156642944991882107248033198525, 1834238502739682738481311292777, 2349644007590383187725417399075, 1520952059539024336115360408303]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false]

#time def chartRows043_p03 : List Int :=
  decoded (raw_ints% [69907047292164890249997, 144012832243384117743965, 65656392092180764875, 0]) [0, 0, 9, 0] [false, true, false, false]

#time def chartRows043 : List Int := chartRows043_p00 ++ chartRows043_p01 ++ chartRows043_p02 ++ chartRows043_p03

#time def chartRows044_p00 : List Int :=
  decoded (raw_ints% [2523386312826428087631, 5773004013065031001593, 34510580611828543263289, 71427292594782629400021, 843486329113060040519, 1683686367975433323763, 31143707969889055135139, 63970602213742165074665, 842986235101681521143, 1683712535752976014729, 31143207875877676615763, 63970628381519707765631, 2524938930415649027691, 5772921040938635794791, 34511133041395007164597, 71427261958211319575151, 5652977985944292013057, 12027020214911852165115, 42689049957754948205345, 89227203214061807535057, 10223145527519471276425, 24776028035104842491097, 58565173471218711494827, 126030251464078502191269, 23452787029226450416287, 51236695320621424088901, 92241106027964633187539, 202042974819804768771267, 45344671055270476068803, 131340887186260544262379, 161038564112461559672629, 384620557326686737122547]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows044_p01 : List Int :=
  decoded (raw_ints% [148539645232753685970865, 337737017993023272801983, 354922880400485721712297, 853698462505970554186909, 333050074465268697593433, 1829422504383300261022965, 836512600098508105276595, 3020857984882294088011857, 2844205214603309440888199, 6851748360572828136477585, 4013767889167086243758227, 11702028849838422485512407, 7682036217473768693585339, 18925995938155668038386689, 14540009321244164378231765, 372218727744417416396697, 56060269525862182904832255, 146410569549389389936921005, 33838223987144249833015151, 165708784215289475391704391, 188382636264528182757762839, 27272587711037678179391647, 278281129777534615495610245, 339391941475716543508017043, 378280366632843192061574639, 1106053516711557091793731885, 88383399409219606191798445, 739388987524802870106323195, 1643928936421955982222077331, 1060599209710594286924302947, 1933825903645579568091853525, 2906041713946954248824358027]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows044_p02 : List Int :=
  decoded (raw_ints% [1544939820055566582657123407, 5317138016377942911804815625, 2032815020011968967656807449, 1350497092720394376056154651, 9188325329066708640517461767, 7782779076278315935130836131, 8700450129110306255517777725, 14450414185376653222991806407, 4356032325632351993430374679, 19305937189896053130204377625, 13532743132544662902604864813, 2927256071758916027918264913, 39088135057594110914065467659, 37171479193520973659021284375, 29911424250681800004890977525, 53550160311658110761307397087, 8189344053778626503518741247, 57383475284127664410186379477, 60810215254497284415437703937, 33338164221051420010142301985, 137476397518292186727400744119, 139044576035209295105052543639, 84855526317573528815481781429, 163089887098285539505096621131, 5052987019944409748215142207, 146014210690002418943890692501, 217278936815921305794667383341, 156120252443492415666258472269, 419398844858408205118751844707, 439999489393653041045451905883, 207172895062431309072299603573, 429893447640163044323084126115]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true]

#time def chartRows044_p03 : List Int :=
  decoded (raw_ints% [4629245865581871418865, 38600148303923830200807, 65656392092180764875, 0]) [2, 0, 7, 0] [false, true, true, false]

#time def chartRows044 : List Int := chartRows044_p00 ++ chartRows044_p01 ++ chartRows044_p02 ++ chartRows044_p03

#time def chartRows045_p00 : List Int :=
  decoded (raw_ints% [1624898211907658378061, 428509565802307600409, 9233434576424943618203, 38316666536491952111321, 210125041859312393351, 255614313034130643899, 16421720857223604071643, 33866132757936968732453, 420483875071862800273, 1022445074465945487437, 8210977324288421042607, 16933060290133195822147, 812086241253395080515, 3428115132407842566361, 18466611006155495046517, 9579170196785044924523, 3187401424730242010389, 954750935959685799219, 1454886557087032951121, 49382803407225508658205, 56851872213966395357, 988570029795458215359, 33742625981510467834021, 72837931371630326497701, 13892760241949023669707, 39030996096880757525809, 3432026616677949381839, 63843023972619207734627, 10749858016618942276627, 97245979040437343815721, 111804618175271982885639, 8248844471329891150337]) [1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5, 1, 8, 5, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows045_p01 : List Int :=
  decoded (raw_ints% [94600333705974125748719, 30637161876981662211781, 124702191973860938870433, 851403592154700456015001, 374094540292494585086523, 449344201481654188973033, 1092193798238685173662631, 3138974988113023807295629, 2003775116977281045689453, 4274135068742665706118771, 1922078997900477694762565, 331108362648487428534495, 6652004726012441336894747, 34889692724292366674417775, 7456076339246646238574911, 9625402766934514380866889, 45175141661512249046946015, 180462902272981214902411, 16483806863195944489827605, 84940929537501221951639635, 20138760321026946315043229, 7497211531811688297447155, 30555327830188241746083519, 143420213735002005812915021, 363886597129244729563218103, 258331710917621643874803665, 103471577645791068269326875, 320831346835298837603013823, 4557262714177405572453153, 1052771030754372977814427055, 486108094005055046003523811, 4774269567692301835424867]) [1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7, 3, 1, 3, 6, 1, 1, 1, 1, 3, 2, 7, 1, 1, 6] [true, false, true, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false]

#time def chartRows045_p02 : List Int :=
  decoded (raw_ints% [1886099031223282771918068629, 210068098847062354483481067, 845827875462790841275773305, 2886092447697025472415871335, 351386647300460914368720989, 874300028380939239009977805, 2874981487547942625732173261, 1069437124949767352243808651, 7474952669068953026523007113, 7347175688099176390193832781, 2651372238060966114764137915, 4887469338336582996994967675, 479163628270237550697895321, 9519383228806703772158198263, 11819369888650410154655492301, 1900682783991409653006392467, 24597064613601410368047822355, 3183533902738645835116366267, 1717002747686434414348515087, 27384923314750231841063558531, 98010745009379690546303115, 1384855640650781379067746161, 39117172555167923207206367971, 30695504286246896456910550091, 70480617034576489546956549347, 75238745319836987195893551921, 3822419814916691101922469557, 33350465642001296402033470203, 2575085632649008205561107517, 45121780451195348245590807111, 111360318084506051184580735871, 3025559254770132242324052663]) [1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4, 1, 4, 5, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6] [false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true]

#time def chartRows045_p03 : List Int :=
  decoded (raw_ints% [20091767364757545614467, 41744743062910412914593, 65656392092180764875, 0]) [0, 0, 7, 0] [false, true, false, false]

#time def chartRows045 : List Int := chartRows045_p00 ++ chartRows045_p01 ++ chartRows045_p02 ++ chartRows045_p03

#time def chartRows046_p00 : List Int :=
  decoded (raw_ints% [41471224636192960437173, 199173924587397012213901, 456366563434937764594205, 1914002502007611253520611, 6923806761787724048941, 55323879316950481451245, 200523862637584678029575, 1659504698103263759855465, 3460643091598343795423, 55324402184784275261035, 25065167757374205196435, 1659505220971097553665255, 41486870975572972995533, 199172267250150241368547, 456372127459953631320185, 1914001890406032070294837, 102355952932610920195789, 442608069826111095742655, 600214951368137524511507, 2555782227482293407406039, 24551161623164535294443, 1073337035545391090095823, 112372524660758090882855, 4071727332853795593244517, 289081248321073802594473, 2600377062650132275841215, 836775993456764307303665, 7745441431049318959181555, 1247642776380520783107779, 12172081351052409994123015, 3499357259936197002904055, 22517899844751861229145785]) [1, 0, 1, 0, 2, 0, 2, 0, 3, 0, 5, 0, 1, 0, 1, 0, 1, 0, 1, 0, 4, 0, 4, 0, 2, 0, 2, 0, 1, 0, 1, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows046_p01 : List Int :=
  decoded (raw_ints% [9098633301649220822718511, 43576166884390955742459899, 13845633337965938608730345, 78266148080195226965728699, 12065628752355996656957549, 87030860384328523496830405, 23537762072163576372681977, 34811454580257659211358193, 18049001086925216368422389, 761123614289830150131420509, 18296306761590646222025015, 813343020093901014416892721, 496470854403738681550577383, 363947026789204158156190085, 714048090145502997386056555, 1938413661172935322704503315, 773386690713674935892343793, 4715483907747921523780505495, 437132253835566743044290145, 2413123219785782042919812095, 916295345181077583386598823, 5675986605407321258511673223, 1000358954400604631598612235, 12804593732941024825211990813, 1213881423377487172236730577, 18695788347481940553730901465, 2619427175785877257733691539, 215208009133594470007237429, 17505444034696302198330374449, 32710904791567561457750474993, 14694352529879522027336452525, 51621901148183096481488613887]) [1, 0, 1, 0, 2, 0, 2, 0, 4, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 2, 0, 2, 0, 1, 0, 1, 0] [true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false]

#time def chartRows046_p02 : List Int :=
  decoded (raw_ints% [4727746124580017283383735059, 56221861517347705299467175875, 27472050439995806942283091915, 28110944422402952639771913005, 32135906651441986465515040103, 130332497192363948889016767395, 20763754493734091636065361675, 158443414287308701548712030265, 734718884496003564106782019, 138510239320625279058011872229, 12857555844046017743341709435, 150265672159047371379716925431, 196904301547541223476187696283, 416785251657180136696119931565, 96982730333157095785881148879, 405029818818758044374414878363, 20037773024113675487317410923, 290680935979390986153062870639, 313924804904811994749386256085, 531134134496547194917471939289, 16489399486723736268871418399, 1144720635496699707714510167615, 6053068926444809073974428805, 904267436979543498950101098965, 54718420685247130997028400501, 528174787787499592004993853425, 415397915295943856482561955765, 1520813284688743614659617413155, 1274709254103647676596992844197, 2806519047263802011340247835753, 334476582141265701637812131665, 1813880550362557988685624276023]) [1, 0, 1, 0, 2, 0, 2, 0, 3, 0, 4, 0, 1, 0, 1, 0, 1, 0, 1, 0, 6, 0, 6, 0, 2, 0, 2, 0, 1, 0, 1, 0] [true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false]

#time def chartRows046_p03 : List Int :=
  decoded (raw_ints% [248918894035565362515689, 132073526662188016608407, 1510097018120157592125, 0]) [1, 3, 7, 0] [false, true, true, false]

#time def chartRows046 : List Int := chartRows046_p00 ++ chartRows046_p01 ++ chartRows046_p02 ++ chartRows046_p03

#time def chartRows047_p00 : List Int :=
  decoded (raw_ints% [38744971914620944267045, 82993771693295418468345, 333865710616863408267247, 702768744430779306122107, 9211476581621984613687, 23976644979811319462771, 285909262120620479386515, 595798327757672568190991, 9214635118242274568877, 23976481868755985813777, 285912420657240769341705, 595798164646617234541997, 38735170082649407103487, 82994288626000217691915, 333862225858132451014069, 702768935141373438047689, 79303601968459346607979, 212094768272145137796655, 451900997909241204725535, 997857992039518793536259, 226847162524722175273865, 507179480854205387502725, 758051762402422726607379, 1717132241165869318835639, 481361034690507077849741, 2207592411341055953116953, 1466259959617651979730985, 4431904133361130659455317, 3225615590776375575260559, 7696123391977850512827019, 5173236585084534632841285, 14335619936680037125399289]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows047_p01 : List Int :=
  decoded (raw_ints% [8459654567712442797283179, 12476415148091458526589345, 16858506743573353005385023, 9555328180566429111636963, 45097755022384178223005607, 119591171147747057302316355, 19779593711098382420337405, 122512258115272086717268737, 157446486818438200955904675, 75162874811099976884985695, 222323835551920761599247687, 317266304074119120904570787, 209664979037060626364843567, 659060210262049659062908691, 170105343333298336190308795, 266631031376830561273352209, 1056236949268416266352034923, 885340188577306264668105783, 1095796584972178556526569695, 1811031430216186485004366683, 551458500419280629732701847, 2330050326370291220964035915, 1600575033821314193145902771, 366321292423201528708436551, 4613420601170437448814703059, 4505818986499139723203077015, 3564304067768403885401502135, 6469548020446229415458676379, 766661729761876080955953935, 6254346736726162081539792195, 7411062939176965253260251259, 4721020270219207057121961199]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false]

#time def chartRows047_p02 : List Int :=
  decoded (raw_ints% [15588790615099009449982379579, 16270267657072436466236286487, 8944389405683920277678082255, 17803594123579391490654117483, 596292354184977951551859881, 13714725525361984974610516819, 25129472374967907679212321715, 20359136255289842982279887151, 44210826374192935302307132979, 47742117289683461157844861455, 18485061645040049671542951383, 41097706559755603150175491123, 7658874185166029662627316833, 25361799392434672296420544635, 70354762204399014636477401195, 63478024457004392011599807943, 110252173529394339220402855915, 121322602325835654070468392735, 32238537139829294921298137887, 83206377261265934355289129427, 29799731778048659362758390473, 39582226514905828602379289691, 172290442447272293504459384275, 164946753072195759823378232471, 249016090115303315150678216243, 276966184048282733149103648903, 46925915889982362283460441495, 151601657490992801928104706123, 85699919644007495359609255793, 49666460842436293950773329115, 381641925649293172793747913531, 378901380696839241126435025911]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false]

#time def chartRows047_p03 : List Int :=
  decoded (raw_ints% [93152670632871088133573, 196440629031018681147613, 503365672706719197375, 0]) [1, 1, 7, 0] [false, true, false, false]

#time def chartRows047 : List Int := chartRows047_p00 ++ chartRows047_p01 ++ chartRows047_p02 ++ chartRows047_p03

#time def chartRows048_p00 : List Int :=
  decoded (raw_ints% [27654840446141629262343, 147538762656354039050115, 230501576097066990235959, 995781140353377514199049, 2306780724870153408777, 36883822874054902609551, 48404903187861186834627, 811358554822968572539383, 144144740172624280047, 36884014150328631691521, 24202219152876510953301, 811358746099242301621353, 27660610307713337480613, 147538156553584564686525, 230503626901773379030029, 995780916803155497999399, 82991672567109935802291, 368847238781307016644501, 341155909776596652312933, 1512166312138047079330425, 87601641669686903779653, 1512286901333861132413113, 299675432841540197837265, 3393300452253215228388039, 539444331044001790746105, 2563519106621199566381769, 926721405555228892363023, 5016312783414737746782345, 698514401431754540554953, 3209025927363660580665135, 1431597269731369882109517, 4370805962672276732498979]) [1, 0, 1, 0, 3, 0, 3, 0, 7, 0, 4, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 1, 2, 1, 3, 1, 3, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, true]

#time def chartRows048_p01 : List Int :=
  decoded (raw_ints% [1635631966033670133407763, 34967230037547582679602669, 71322016306513490259441, 33805450002238966527768825, 23279203112141730693450471, 27387318411980688412894021, 32104035498084842915383635, 96159998451767237620265515, 25713615676437453507637973, 21073001694017312637579677, 29669622933789120101196133, 5629587086048821883434735, 140435985311405324778811941, 63295079443582000236439127, 136479978054053658185253781, 116700257003714269278467951, 53405268524920102119505347, 261092280049103517413764641, 223510694840538880844560375, 98898392845489021616049515, 555810008359772155367330529, 565699931081082830387385403, 385704582044153376642275501, 727893818284697326185100529, 33625423082298752079395599, 2452684438599050598022615903, 907889167321626779930210431, 2721690558864070028267327825, 3429802762989399900439694565, 7352779029430828980224447491, 1681275274510743844738064901, 7083772909165809549979735569]) [4, 1, 7, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 1, 0, 1, 0] [false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true]

#time def chartRows048_p02 : List Int :=
  decoded (raw_ints% [425922657287431675186267163, 4662739338378050320014892973, 5537000694787575420364026629, 9773812600218588210189290087, 1118048426992789196353390233, 19669910745177142681840998481, 372683007983413309409603509, 14558837483336604791666601367, 551764642644986803843255479, 7279411444299973911291418259, 3533227512597391815369242963, 26949336784213773562216181589, 20637916001402181912864583955, 45987784039225341289390855415, 4297947380432667436014590187, 26317858699311541638466092085, 6919010607000924679034709421, 8887811057014223760404738729, 31854873988835774027913883563, 63417831681522659167452208771, 21681874136209127515669370763, 97277333014275204319697623661, 2294931838290778162195074271, 42747312389766768912650153619, 8734423538219809468027425015, 393899740929400568913484447, 32711229512719715145891870049, 8357640596823222758108251633, 42301919140083951003032096369, 23795424649628534040857540383, 856266089144426389112801305, 7867942937840889662468006011]) [1, 0, 1, 0, 4, 0, 4, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 4, 2, 4, 2, 3, 2, 3] [true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows048_p03 : List Int :=
  decoded (raw_ints% [129078208271604309749151, 285829975752432888312291, 2516828363533595986875, 0]) [1, 1, 5, 0] [false, true, true, false]

#time def chartRows048 : List Int := chartRows048_p00 ++ chartRows048_p01 ++ chartRows048_p02 ++ chartRows048_p03

#time def chartRows049_p00 : List Int :=
  decoded (raw_ints% [92230299146587550581065, 202870941074659901933241, 534893963611484356970199, 1161996947738616213376803, 18431621412424851915771, 55329204960350158571193, 424232043052471954473363, 903796801703606152872369, 18435132050736937270221, 55329025112262766147743, 424235553690784039827813, 903796621855518760448919, 92219407535476509670815, 202871510882259643463391, 534890093276997486768849, 1161997157850041170060053, 202869074642829330314931, 829923021691865759259495, 829978575455303326754595, 2194791690424166572782939, 1161888486562596348218313, 5495917918345656086776455, 2194736136660729005287839, 11545347342577720750861323, 1484635935288817030012449, 4905716801496286235177061, 3162948246900479706765525, 12135548459427090602460717, 6003074514607075351722585, 4050459522797530248432225, 1355490332417778614944611, 7197190088353709950953993]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 2, 0, 2, 0, 2, 4, 2, 3] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, false, true, false, true, false]

#time def chartRows049_p01 : List Int :=
  decoded (raw_ints% [21882163088454908314025079, 1912268334993286555418149, 29240727935479762280692275, 22947182473921916669491039, 19171107331624307093082359, 133616857914098668907391955, 31951783692310363501634995, 11231834658518417342737415, 29289201584826240758813079, 225793112293573888439719759, 3261754061831840832084365, 370641804866190974689849129, 865362741145635772620851, 176800187632162146260551915, 48460332150315881234521191, 121417270947720285304232529, 207686983085154283054310841, 439109634826797402160574511, 124612122642852692947202075, 494492551511239263116893897, 9889864798158663690019213, 1408316196476209592918667355, 342188970526165639691532129, 2326092548875937068191206277, 2318183047202096034656064423, 5089980815026562932220564535, 909867705904798821129859055, 4172204462626835456948025613, 493174179815005517668512541, 1105026167110286183299546139, 3721224932921900373454436019, 3526066471716413011284748935]) [2, 5, 2, 3, 2, 1, 2, 1, 4, 1, 7, 1, 7, 2, 4, 2, 3, 2, 3, 2, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 1, 1] [false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true]

#time def chartRows049_p02 : List Int :=
  decoded (raw_ints% [5514583741052679436592181783, 6158563462044854378335330803, 1300184628315773545469233223, 3737523157438727550350128007, 1781133621799355401154810581, 1308340414310425410640391067, 8595901991167808383216225587, 8587746205173156518045067743, 11693531813272241060182585079, 13158945621750673763627096891, 1316496200305077275811548911, 5879539830887942656222420215, 4711961238756220808043834205, 804182167861944049788489495, 17721989252333539144037968195, 18234303284776672370061027611, 22725818626508570775847232479, 25644733774783622835909824367, 291868135418810823765430079, 8214612657868894515637286251, 10549791535306324928169017981, 2585240855536221004464824089, 33567478297233706527781680539, 70303933720841255707559045325, 644377513149765619183131943, 93086526828604388142788281227, 359638623869378978528781771, 20197352252226911430764411813, 2644499585092589226939551313, 3187631558571975176815369827, 3719940533210667600937912543, 31508601328779800070203543087]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 7, 0, 4, 0, 4, 2, 5, 2] [false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows049_p03 : List Int :=
  decoded (raw_ints% [19597633211189747110977, 341216972203319028827511, 2516828363533595986875, 0]) [5, 2, 6, 0] [false, true, false, false]

#time def chartRows049 : List Int := chartRows049_p00 ++ chartRows049_p01 ++ chartRows049_p02 ++ chartRows049_p03

#time def chartRows050_p00 : List Int :=
  decoded (raw_ints% [248938908124586186259821, 3983590005101505703538721, 705370049380272480912567, 13941693946900619364672011, 166030607893450644214249, 663923365936308320268941, 2157571773378466906916377, 9294180575862805340864349, 166015666099765340679199, 663924891044443222771091, 2157556831584781603381327, 9294182100970940243366499, 248962083369181592813471, 3983585173814896536871071, 705374166105727532421867, 13941692165830280003008661, 705430293559601206234497, 53114598702720148006339933, 3070571002699839070126199, 124815708061300854165858861, 28549132641859456664328261, 29213377928378824739396239, 64400585360411788525089805, 148716928835642177432802555, 97598527909051357367804713, 533803712549353014222253905, 4648809906780112178386647, 414300161642089661528847589, 91788947343277439037743185, 594885889976404474935790461, 117350781797235306424291025, 1542989764167847150686891955]) [4, 2, 5, 2, 3, 2, 3, 2, 3, 2, 3, 2, 4, 2, 5, 2, 5, 0, 4, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false]

#time def chartRows050_p01 : List Int :=
  decoded (raw_ints% [59256054169716598683489933, 910917785927936440498261195, 149883674970796146778544277, 158020041144189372313080013, 857471463935624923839787833, 1756770130411335890537977575, 676216222333465827649679145, 2509667875195082958723158757, 76684905799347154508577957, 1979853538339140210971028075, 1457002780469743596980889021, 2286584467267278638290108257, 1341977595338035412896829997, 5871838270935925596362663967, 651818658002837191660674465, 5565107342007787169043583785, 213621491892218395133383011, 6310029855719953887292628055, 2207417745233090999690887473, 16563861370167471643519867449, 13386912172209842699947012131, 30001865846914808836352564819, 3702755223708605120649930195, 19748034332467291080125325425, 4082527470063997016992072601, 7215650405033686188884801907, 21172194865982444837589014927, 42534249774348413727593088337, 3595952189671440365351994905, 65044357740875435009937286839, 109777974416408783382339741, 29725758371560707471229000409]) [3, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 4, 0, 6, 0] [true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false]

#time def chartRows050_p02 : List Int :=
  decoded (raw_ints% [181119534003068534082772515, 228723536791193146439815769, 5484020359361623771543533989, 88975136253688527478641831, 6951311807302923203555986683, 7875420843524330943865469299, 9167587958375579675136287, 602433915019864582918051971, 412146793058420469160143169, 1134318659815022812532743437, 10266821327687038116187404609, 21704631667022601363608097803, 6205670918211313948792766975, 28093096838054055724170181571, 1152653835731773971883016011, 5254146511216431548029340331, 6567587509676163682280259023, 37743803812717937911161552911, 8913137755183508803991388481, 304521750606881836088757728127, 166628331033481704186006863057, 376170627734541054683314967637, 28522573126863746136097424823, 33905073314941280683395686599, 95454665744986955769543313707, 91479857644576448398076866571, 233560423651604913819452751941, 501555558694058783764787520807, 66514451219719791831754155975, 598611919978344906923759367377, 15739321129428175565494860437, 5576503639709674760894979999]) [7, 4, 4, 10, 4, 4, 5, 6, 7, 3, 4, 3, 5, 3, 4, 3, 4, 0, 5, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0] [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false]

#time def chartRows050_p03 : List Int :=
  decoded (raw_ints% [1659679006885131148084955, 4481320988000531267052683, 22651455271802363881875, 0]) [3, 3, 7, 0] [false, true, true, false]

#time def chartRows050 : List Int := chartRows050_p00 ++ chartRows050_p01 ++ chartRows050_p02 ++ chartRows050_p03

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040, chartRows041, chartRows042, chartRows043, chartRows044, chartRows045, chartRows046, chartRows047, chartRows048, chartRows049, chartRows050]

#time def graph : KernelGraph 76 76 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 3.0600 s provisional ×3 model; 5100 exact original rank units.
#time theorem checked : chart.check 100 76 basis.matrix = true := by decide +kernel
end C007

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032
