module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P023Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P023
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C010
#time def pivTape : List (Fin 48) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩]

#time def freeTape : List (Fin 48) :=
  []

#time def roleTape : List (Fin 48 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩, .inl ⟨27, by decide⟩, .inl ⟨28, by decide⟩, .inl ⟨29, by decide⟩, .inl ⟨30, by decide⟩, .inl ⟨31, by decide⟩, .inl ⟨32, by decide⟩, .inl ⟨33, by decide⟩, .inl ⟨34, by decide⟩, .inl ⟨35, by decide⟩, .inl ⟨36, by decide⟩, .inl ⟨37, by decide⟩, .inl ⟨38, by decide⟩, .inl ⟨39, by decide⟩, .inl ⟨40, by decide⟩, .inl ⟨41, by decide⟩, .inl ⟨42, by decide⟩, .inl ⟨43, by decide⟩, .inl ⟨44, by decide⟩, .inl ⟨45, by decide⟩, .inl ⟨46, by decide⟩, .inl ⟨47, by decide⟩]

#time def roles : GraphRoles 48 48 0 :=
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

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026, tailRows027, tailRows028, tailRows029, tailRows030, tailRows031, tailRows032, tailRows033, tailRows034, tailRows035, tailRows036, tailRows037, tailRows038, tailRows039, tailRows040, tailRows041, tailRows042, tailRows043, tailRows044, tailRows045, tailRows046, tailRows047]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 243713808082670679, 607961471833528647, 903606052351478391, 408653258148199, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 148605599185470525, 21287570016248979, 2657579116665153, 33492646265533, 34493884425]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 7, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 151387994194904603, 316775219116482765, 479454851877279743, 29647858210765, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 574818220719425045, 82182751500561625, 30784799536760355, 17884419880187, 34493884425]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 5, 0, 9] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 42752080057047641, 82153752508489405, 121632278287850089, 1287776777631, 2653375725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 11503129264860577, 9858052665717051, 13149481030992733, 382384666239, 2653375725]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 2, 0, 1, 0, 7] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 14506004138969, 3286080299633617, 1178500505039373, 16702287793, 241215975]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 7, 0, 2, 1, 7] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 7999856339602525, 1428740422078035, 2284494004056855, 40302108395, 241215975]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 1, 8] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 3185008400933739, 5143448511010413, 7104202620437757, 19654382787, 241215975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 10779199526665917, 1347097410982869, 3390769184895, 137214899495, 2653375725]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 921127886614713, 5388403269205461, 3543418908064545, 270237044875, 2653375725]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 68764961739507579, 22120174836938097, 19738301156030679, 5078031246511, 34493884425]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 1, 7] [true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 18846794612867301, 24577310582145795, 30432132043502931, 2517392931665, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 3704376525300633, 180768027125319, 2069991948020901, 6075502698933, 34493884425]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 1, 6] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 2642697641777463, 1578738665705661, 3450924256520043, 38689526940519, 34493884425]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030]

#time def graph : KernelGraph 48 48 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.9300 s provisional ×3 model; 1550 exact original rank units.
#time theorem checked : chart.check 50 48 basis.matrix = true := by decide +kernel
end C010

namespace C011
#time def pivTape : List (Fin 48) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨15, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩]

#time def freeTape : List (Fin 48) :=
  [⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩]

#time def roleTape : List (Fin 15 ⊕ Fin 33) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inl ⟨12, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inl ⟨13, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inl ⟨14, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩, .inr ⟨27, by decide⟩, .inr ⟨28, by decide⟩, .inr ⟨29, by decide⟩, .inr ⟨30, by decide⟩, .inr ⟨31, by decide⟩, .inr ⟨32, by decide⟩]

#time def roles : GraphRoles 48 15 33 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291]) [4] [false]

#time def tailRows000_p00 : List Int :=
  decoded (raw_ints% [7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 13706686301949182498164783002207154076072298588707868042611983641023543694376521937021297457478044793829398635863634933162579593390778639915569709950355389, 0, 7017830644416279357952501466999684499492103583655160398031201062725945442516037053928812523482309536100015772498226074193827062044495132691728338589008913459, 14035654031014260797012870364129747386441120461073588835848536686929999814036816285683716821711068470540667874060407159973067813860573796328500030083590872627, 14035654031014260797012870364129747386441120461073588835848536686929999814036816285683716821711068470540667874060407159973067813860573796328500030083590872627]) [4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 14, 0, 5, 5, 5] [false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false]

#time def tailRows000_p01 : List Int :=
  decoded (raw_ints% [40010123719729848342211058740121311227052459024485784659626414709177403506481434911255933492743577300822914413139805816905568605203619084725450033172125]) [6] [false]

#time def tailRows000 : List Int := tailRows000_p00 ++ tailRows000_p01

#time def tailRows001_p00 : List Int :=
  decoded (raw_ints% [0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 13579738408904665450689976409404373148072074010249062223770381815415029988502371674053710384986163555253361957878702122756585209001067902495210194589150947, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 13579738408904665450689976409404373148072074010249062223770381815415029988502371674053710384986163555253361957878702122756585209001067902495210194589150947, 13579738408904665450689976409404373148072074010249062223770381815415029988502371674053710384986163555253361957878702122756585209001067902495210194589150947, 27811311519255052761905204256329777819794694279226811394495607396491872487448115010635907093705213562818248960671626935820072818262603533365147125613008093747]) [0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 4, 0, 14, 4, 14, 15, 4] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows001_p01 : List Int :=
  decoded (raw_ints% [20000953349670657195132462633729034775777772581913449868536255575056620226593538769401705368227832194573720456274485456195222319265899785185054909504675]) [7] [false]

#time def tailRows001 : List Int := tailRows001_p00 ++ tailRows001_p01

#time def tailRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 196806110686348318373106766995746755183136527987605259165079038575762666361655435529525769845350172282028763009047358377405617103564809979629812323517681376441, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 196806096170711722535322501856007511958050354575131795244651307698718884219664919885177953394843071078710035667175268400576444483107977041519899029328827467859, 98403051714265010227107317212938566785296720640684263602432586568620387645330088853675930810048310840184699669055656694495515396668196755287427838211627211075, 196806110686348318373106766995746755183136527987605259165079038575762666361655435529525769845350172282028763009047358377405617103564809979629812323517681376441]) [0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 4, 5, 4, 6, 5] [false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false]

#time def tailRows002_p01 : List Int :=
  decoded (raw_ints% [14506776551623042634745530338337462425780742895355775798045446550551900453904221836401493802499882776156971096618731747346831204862753707293119320578559075]) [1] [false]

#time def tailRows002 : List Int := tailRows002_p00 ++ tailRows002_p01

#time def tailRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 185614900803405683634621801710453829829452428243395151074780691005296486684801592466331718178847017005286131144752666382056430911968257361517359516037792336329, 0, 185614886287769087796837536570714586604366254830921687154352960128252704542811076821983901728339915801967403802880576405227258291511424423407446221848938427747, 92807446772793692857864834570292104108454670768579209557283412783387297806903167322078904976796733201813383736908310696820922300869920446231201434471682691019, 92807446772793692857864834570292104108454670768579209557283412783387297806903167322078904976796733201813383736908310696820922300869920446231201434471682691019]) [0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 4, 0, 4, 6, 6] [false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, true, true]

#time def tailRows003_p01 : List Int :=
  decoded (raw_ints% [26348244334866641507786594443042517442753142552212113131433821733573501268195564648603458421976794940551667558177577971971539598585836234863420839612912225]) [0] [true]

#time def tailRows003 : List Int := tailRows003_p00 ++ tailRows003_p01

#time def tailRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 98055216121667956824824813692232740308218917742686344720911930136209366440914056886792706416126214956842314013851743101445638352959993142607555433543047113, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 392228122304969746191431824638552573775962377207477339097513159066728536758914049721079050918055461486732926991451960820368863640256441625386868828599142743, 784448986791641573490731079407483535008838048178222717981160879611566002522570277268249876582560321314102183046858933226151417052096414195817090562771331195, 98055216121667956824824813692232740308218917742686344720911930136209366440914056886792706416126214956842314013851743101445638352959993142607555433543047113]) [0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 7, 5, 5, 5, 8] [false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, true]

#time def tailRows004_p01 : List Int :=
  decoded (raw_ints% [45976714869440797483262189153877179843195734648535105408802601352543711494790267322771505800892864414415256042906589594271391117503248590109618071474525]) [0] [false]

#time def tailRows004 : List Int := tailRows004_p00 ++ tailRows004_p01

#time def tailRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 54395161434992991607526263665852416377252439067018941693661229637816560181828927133662527531127996454124691173839523301790256551321677890589677954691344755, 0, 217573387921674047537972484793788052965923050031343806560779480029375169732057886360741884870961384157135093759313104792574715976870242507402064724338424729, 435154033661646013968077539457197718474932806299419573335424398580641410459373594895391994995473369973633858454671197999735742182156954069760776543103803749, 435154033661646013968077539457197718474932806299419573335424398580641410459373594895391994995473369973633858454671197999735742182156954069760776543103803749]) [0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 7, 0, 5, 5, 5] [false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, true, true]

#time def tailRows005_p01 : List Int :=
  decoded (raw_ints% [13812929573936790157057548847614820157891005062448022242219225886576322368886195989837926450504351130575674125168909700973832926296764994290269068693525]) [0] [false]

#time def tailRows005 : List Int := tailRows005_p00 ++ tailRows005_p01

#time def tailRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 149490187770244294990833735280467740252686893653368888711020306729112825781791068322979559322938344372065496374707596041709184632939087763233262455528813799, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 149504703406840132775098875019710965338860306126832809138751183772894967772306712670796009830039547690792838246797572870881805089772025873146556644382722381, 74748722794271106941483152575044676397886799945050424462442872625501948388524445248443892288244473015714583655376292228147747430677778409094954774977884045, 149490187770244294990833735280467740252686893653368888711020306729112825781791068322979559322938344372065496374707596041709184632939087763233262455528813799]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 4, 5, 4, 6, 5] [false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, true]

#time def tailRows006_p01 : List Int :=
  decoded (raw_ints% [6145104319688144019961281224639478326272111385574717992456951123129913906792304743098132901616952630706784462611479395478370194977466459434502704004325]) [0] [false]

#time def tailRows006 : List Int := tailRows006_p00 ++ tailRows006_p01

#time def tailRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 87728929685013273793241142489649858257275569903066806250321123546612651315547063283599871214913432647068916052787268144989166157096136969931276559987063865, 0, 87714414048417436008976002750406633171102157429602885822590246502830509325031418935783420707812229328341574180697291315816545700263198860017982371133155283, 43860835933357677450554286310014122857094431833167423018227842512360790160144620554845822980681415493852622558371139865201427964339833957487314732780054787, 43860835933357677450554286310014122857094431833167423018227842512360790160144620554845822980681415493852622558371139865201427964339833957487314732780054787]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 4, 0, 4, 6, 6] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, true, true]

#time def tailRows007_p01 : List Int :=
  decoded (raw_ints% [1032409990942010381414203058905002581713038348742378260387296618068225143852782797827346625423527091118307254564862527447703123792305958081934873665725]) [1] [false]

#time def tailRows007 : List Int := tailRows007_p00 ++ tailRows007_p01

#time def tailRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 3367096335558642956380745271606819496825132656758838689716205598029383721504371360324122442906111400132394839954961004135291303666572169247200441981888203, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 13475643160532490717655550956048890530387236863767314972730260914008605881275307615204715025175047259893250295864832431127475443082757731945448862354507103, 26944028502767062543178532042476168517687767490802669731595083306126140767292793056501204796799492860422829655684676447668640657749046408934250630282059915, 3367096335558642956380745271606819496825132656758838689716205598029383721504371360324122442906111400132394839954961004135291303666572169247200441981888203]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 0, 5, 7, 5, 5, 5, 8] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, false, false, true, false, true, true, true]

#time def tailRows008_p01 : List Int :=
  decoded (raw_ints% [426354099634557139761800457487858827077429847374289053417648213248074033269553844285143851374861686476355393613474263996613654119765045108281414056575]) [1] [false]

#time def tailRows008 : List Int := tailRows008_p00 ++ tailRows008_p01

#time def tailRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 1893946357252187231660760453460199946544913716400172388557634032875291403283924513878958835039036814616915275490531786277531949280553492740720603134917685, 0, 7568527610710830034510471944219187243092948628868729340365097609610094617877875881607610086605545599103990165917138730523817568705744916006235318112716449, 15144313039719578961153513758059987029272603494469418894595633741111260231013573937123445426761692857571651267879265875633945365827958886969117730652387189, 15144313039719578961153513758059987029272603494469418894595633741111260231013573937123445426761692857571651267879265875633945365827958886969117730652387189]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 5, 5, 7, 0, 5, 5, 5] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, true, true]

#time def tailRows009_p01 : List Int :=
  decoded (raw_ints% [124411488473341477773940104507135602008128961861239328404878153488287304066765049243608666953141869487643060875531366662727365583993744687596299220175]) [1] [false]

#time def tailRows009 : List Int := tailRows009_p00 ++ tailRows009_p01

#time def tailRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 3746405166375207368896133689044543998314123209626968316267215383858877995027619909419228932327998322155165549725695839084164917128067538946155662490897093, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 3760920802971045153161273428287769084487535683090888743998092427641019985543264257235679439429201640882507421815672668256785373961005648859449851344805675, 469207873084140782628587944833269567675103680794866066266581738218743623785680260415931773234824997689854560721335531708809393193067074237850344614731423, 3746405166375207368896133689044543998314123209626968316267215383858877995027619909419228932327998322155165549725695839084164917128067538946155662490897093]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 0, 5, 4, 5, 4, 8, 5] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, false, false, true, false, true, true, true]

#time def tailRows010_p01 : List Int :=
  decoded (raw_ints% [23013895598517417357904586892990811544458305317376916310780680255436548153712412907888787088267748675428947069458582588591736658821485148097136314675]) [2] [false]

#time def tailRows010 : List Int := tailRows010_p00 ++ tailRows010_p01

#time def tailRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 1984830544536280887766480377829523358142970019734638189221316094292283164050054550312233560762318593899169509846969679927555963412915412182200938919540555, 0, 1970314907940443103501340638586298271969557546270717761490439050510141173534410202495783053661115275171827637756992850754935506579977302268906750065631973, 247196590779795249454238813525988851882032972875334746919484696550151521099029047050501038401464616816937321725247658167655716874555794653194230561573283, 247196590779795249454238813525988851882032972875334746919484696550151521099029047050501038401464616816937321725247658167655716874555794653194230561573283]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 5, 5, 4, 0, 4, 8, 8] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, true, true, false, true, true, true]

#time def tailRows011_p01 : List Int :=
  decoded (raw_ints% [20329513426716258743036512707034048384733698257783588079825166610253566795053125395660452373999698832594869128913990222249242672763088778896414273975]) [0] [false]

#time def tailRows011 : List Int := tailRows011_p00 ++ tailRows011_p01

#time def tailRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 10825763353284285026670164762099021095511275081175393616011507570129940422315922980580042779262535568649336120922778450015781487694185099523667036179235, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 180470031950467452559292505815196880614886638030766511721622643013150042014876941597505938018802228462060313979752869786562732219576016549025767005822051, 353682245603016012986015142008781218143067039329572809577806764135229088771931709286786622487002797560449691914517324986815236022682978141404439584689811, 10825763353284285026670164762099021095511275081175393616011507570129940422315922980580042779262535568649336120922778450015781487694185099523667036179235]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 0, 5, 9, 5, 5, 5, 10] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, true, true, true]

#time def tailRows012_p01 : List Int :=
  decoded (raw_ints% [6543527327457264042769719516150460286506395419903605512124215748059661484401961968690007876924200808092179975363103112409601830937955768973436120725]) [0] [false]

#time def tailRows012 : List Int := tailRows012_p00 ++ tailRows012_p01

#time def tailRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 2680287726528206156600031843054671758427802489602083774263625752853189933580191685742903161282794703422578908150302477544287328902033839917237033209245, 0, 78511388950983704878631149356136953182983442935306466910997502200231082616743960035547647610447771145851589015821264695106966108396027920704490635741549, 164280596199886301889832168333886449452673122602573147687433526291533160491310093979320548771497201655374114076630943976524160633261110798056075698437389, 164280596199886301889832168333886449452673122602573147687433526291533160491310093979320548771497201655374114076630943976524160633261110798056075698437389]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 5, 10, 0, 5, 5, 5] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, true, true, true]

#time def tailRows013_p01 : List Int :=
  decoded (raw_ints% [827001962125719308891781827841319153482675320415431741710541204197297660190166924355438392780964007463009976383048659630514567986684311459710851325]) [0] [false]

#time def tailRows013 : List Int := tailRows013_p00 ++ tailRows013_p01

#time def tailRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 15761713343021894571964626967463593056411404457098462977187010070289909916499785639463296816178369319577920665525668121403074818021572082431756867155725, 7257818297918892132569869621612543086706236731960213865438521891070995257822173908225253550601659363670936044988414586310228416469054956647094426954291, 30277349938859678837104366210688679229823877921018890708064053852431900432144133455913803917381688046919792755502497294023531650959681995725945721064307, 359680181889699792258351509204314627236213143579041825666023936896264143348780617932633599480937948175763386101782542308020363038916047485607051470469, 15761713343021894571964626967463593056411404457098462977187010070289909916499785639463296816178369319577920665525668121403074818021572082431756867155725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 5, 4, 11, 5] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true, true]

#time def tailRows014_p01 : List Int :=
  decoded (raw_ints% [223877830132325495533853878210819299822373062304287062796758914632637758840269742523490232630505149934150936902750751568959896165420208321413041625]) [0] [false]

#time def tailRows014 : List Int := tailRows014_p00 ++ tailRows014_p01

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [52575845278679, 255247668854663, 764730671017719, 4876282170903, 456907156884377, 707278543568137, 12690998968791, 245495104512857, 715093260366025, 27690442189847, 482289154821959, 755474701524663, 95685272033513, 300875988892551, 878850415748023, 81784233606825, 673659698888985, 1056319921388361, 294024593238423, 464444456106201, 1432128748233609, 227777860748247, 1261708885365831, 1953931202220279, 976917112664745, 920000177602695, 3158626175633271, 756264524531817, 3215543110695321, 4891807812829833, 4155660930303063, 2432529226666329]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [9803733267664713, 3320940417003159, 11526864971301447, 17280334614970935, 25518281352016233, 9074410060672647, 46119556383990327, 21428181187303209, 62563427675333913, 93066018923309769, 272699022079097367, 51930772435279065, 387193222189710345, 243713808082670679, 607961471833528647, 903606052351478391, 408653258148199, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1375717360475, 37799574891511, 16058464452529, 74292886849, 23682848197655, 30146868449791, 48166109887, 35422202512343, 29937854234095, 2040434262731, 25224163714039, 16181808687961, 2334630074123, 43583939563267, 4592335214097, 3511955843077, 34562684010531, 46097223473053, 3333316610949, 71679586307883, 59787768381105, 22298017270737, 61229216898123, 22188104718435, 20754092447121, 160871655390831, 65902264295799, 21878756135703, 144245586686607, 240073645581531, 20662793763351, 510931753562079]) [1, 0, 2, 4, 0, 1, 4, 0, 1, 1, 0, 2, 1, 0, 4, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 2, 3, 0, 1, 3, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [410239845177747, 491108497885239, 474850286900223, 491999759058195, 474259995770487, 2475365745103035, 487342002943029, 2399499100105815, 2371890269982171, 7222626207754233, 2364459968283351, 21671358545949555, 16750544344532565, 148605599185470525, 21287570016248979, 2657579116665153, 33492646265533, 34493884425]) [1, 1, 0, 2, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 7, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [3372093820339, 21966617476365, 55923622601191, 1033674924579, 30584911304487, 51517853856273, 1402804724739, 19899267627207, 51886983656433, 2199376410739, 33390520753965, 55489164791911, 8128213551685, 24298020448685, 65816754754335, 7599220734101, 49646947857335, 81544189040121, 26577340710491, 39496461916887, 115720750484713, 23761395995019, 102801629278317, 166059487190223, 101745396547869, 87019253906925, 291566279733111, 92427528568365, 306292422374055, 485739204849345, 550206250665171, 271874311043655]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [1128372984082881, 515731446237891, 1406704923704397, 2194310680985943, 5158774242042069, 1303337203519437, 7868816369265903, 4994150681186469, 11724253407788535, 18021741292494441, 152525482854347115, 11291638565892375, 175541374828028025, 151387994194904603, 316775219116482765, 479454851877279743, 29647858210765, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10] [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [1031602196549, 18765568739309, 8426408841819, 118751924155, 12876862234869, 15583711638779, 77184987205, 17815553346069, 15500577764879, 1295493793049, 13494342132509, 8475220766169, 1412051122545, 22997528518265, 4914496611983, 1154650698789, 19142546622689, 25688640365633, 1117248685105, 41471939698889, 34776237901209, 16772208092095, 37018525584369, 14004360183431, 16137144623559, 108560772067269, 44463396724689, 41844751844031, 101567104078605, 188753441760999, 40851663101679, 443318786819517]) [1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 3, 0, 1, 3, 0, 1, 1, 0, 3, 1, 0, 2, 2, 0, 1, 2, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [354146271652419, 721858506505605, 428380408892037, 578854052180691, 715001757139005, 3330752812841937, 324321046000749, 2469042248409849, 3288387437448057, 23061908112423789, 2465448876972299, 82340104761957105, 62537837115480973, 574818220719425045, 82182751500561625, 30784799536760355, 17884419880187, 34493884425]) [1, 1, 0, 2, 1, 0, 4, 4, 0, 1, 4, 0, 1, 1, 0, 5, 0, 9] [true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [144209595935, 1034680370299, 2431343959327, 68589310503, 1252453993093, 2218545052889, 80273933103, 897501749293, 2230229675489, 107145660215, 1413001859299, 2417649268807, 430927111985, 1111793069723, 2955722041007, 416438334025, 2274856083269, 3803087487017, 1575072933727, 1944669737773, 5794598754769, 1491258677383, 5425001950723, 8860930365879, 7520961283969, 4927187092539, 17873150327231, 7244709578169, 20466924518661, 32638821189369, 61236583559439, 19416606248877]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [101120114326977, 60229116036951, 142940091637539, 222585813923367, 1571570692956369, 139874838322779, 1854385622916687, 1566839719682089, 3286081477550277, 4992796035555145, 42719916993019841, 3273554277686957, 36160281237782607, 42752080057047641, 82153752508489405, 121632278287850089, 1287776777631, 2653375725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9] [true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [909556969, 373713509577, 353278843231, 3877060127, 274632530869, 10009248753, 2528690657, 358205269069, 159473795313, 16690118569, 284747293497, 354856518421, 8823947985, 491726217621, 423532547499, 129226768137, 425930461257, 73506888447, 126771140813, 1008633290169, 422026508263, 289277621053, 933015024509, 1549379399445, 35510117287, 3322854258593, 2696096518143, 4327505176153, 3205662530877, 948970446361, 4295183528865, 20632874963205]) [6, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 5, 0, 1, 1, 0, 4, 1, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [8107226137953, 51081792946869, 20386396646337, 122673221698509, 25513151420785, 429287218538157, 326889413275387, 2571197387569487, 428596819378897, 133890960538185, 2571662371273987, 9855502331739791, 3642557563727217, 11503129264860577, 9858052665717051, 13149481030992733, 382384666239, 2653375725]) [2, 2, 0, 1, 3, 0, 1, 1, 0, 5, 1, 0, 2, 2, 0, 1, 0, 7] [true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [1966984151, 28305910555, 31437591435, 2435021841, 30635304013, 56506192727, 2663188101, 23435866873, 56734358987, 401382749, 35961680215, 7826076135, 7186653125, 29857990857, 40096488661, 14120576683, 64708292715, 108686860255, 63144261313, 58099144223, 185951698251, 7697046435, 190996815341, 77668082761, 221239711917, 181251887183, 407364063179, 437324346767, 1075955663009, 1694531896959, 9668588142821, 1055900580717]) [1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 3, 0, 2, 1, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [11800444386547, 301561959565, 20413131948651, 3889876904431, 112257509441567, 20355865992877, 91873010470803, 224601337628517, 428616905817617, 632862377453257, 1857348602725617, 428846809264157, 999884887643843, 14506004138969, 3286080299633617, 1178500505039373, 16702287793, 241215975]) [0, 5, 0, 3, 1, 0, 1, 0, 0, 0, 0, 0, 0, 7, 0, 2, 1, 7] [true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [16087271441, 36304962075, 145121162139, 1237146601, 14105991637, 127796744097, 809673751, 17533907737, 127369271247, 17440987391, 29021657025, 145619932389, 18059014275, 52508802865, 181119934055, 78606955723, 11770167825, 277785904053, 77829495363, 32778939647, 434222355139, 508466987147, 124910166663, 1020518837649, 505169284887, 639582745735, 2034155109683, 10119597278335, 315039725775, 12658921672905, 10109387295087, 5379590012035]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [32887906246327, 214814434062313, 10739466746637, 171817140520899, 214849309502037, 204055254038243, 601480884085249, 1632995999733043, 25513730344425, 816665806145757, 1632850264833435, 89308796605925, 4082512070712235, 7999856339602525, 1428740422078035, 2284494004056855, 40302108395, 241215975]) [0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 1, 0, 1, 8] [true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, true, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [10344629267, 69386996421, 146890433029, 7669069085, 67158807341, 128876734677, 8071650155, 54048858251, 129279315747, 9070300277, 83302107651, 146421266179, 47369333517, 72189458805, 202860899973, 46963805475, 178040774685, 297194038965, 291617678955, 166117069755, 635775523395, 288940418325, 761276132595, 1216333620675, 5308390422765, 743997906405, 6813664461765, 5299601549475, 11378056978125, 17421656434005, 102367290610005, 11343201005355]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [79646032626525, 102398758113675, 193356524241885, 284412081350205, 708998941957005, 193454315221995, 322188102493125, 708854303364195, 1224641359672125, 1740041347814325, 3184044935341269, 1224254291506395, 735149284162749, 3185008400933739, 5143448511010413, 7104202620437757, 19654382787, 241215975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 8] [false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [73827658847, 1726133239, 475031939133, 3049670679, 90129612847, 398154609607, 2002368489, 107422856617, 397107307417, 77141461889, 11516497667, 476251137795, 78683490509, 92282159253, 632076090193, 468558265509, 170815471845, 1179317846211, 466666538925, 653122584015, 2114542650645, 7706408569365, 318741005385, 10287617758935, 7698349480665, 2089882788345, 25692375808965, 133436795906175, 8335831491435, 100046070616545, 133461659730735, 125077264752795]) [0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [366944526253455, 834190513127625, 31281457059825, 333784327143435, 834105976915365, 354556624187415, 2002080817186425, 3402822805149603, 708980148676065, 566636011047813, 3403174970641803, 2693709556774773, 7372633786839219, 10779199526665917, 1347097410982869, 3390769184895, 137214899495, 2653375725]) [0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 6] [false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [10663569577, 246927164281, 248909905721, 35982014479, 208238368853, 419183518655, 36976526305, 174963135323, 420178030481, 9877165651, 282191421463, 248331609695, 67837412881, 253980460531, 403760766759, 270428151637, 824890724511, 1349299336679, 4083085038837, 794836763805, 5702812527153, 1019160924855, 8991060802185, 6931270632705, 15719530646775, 8948124162645, 22469468811135, 62899247655375, 116765184372015, 170716307864745, 350331318111105, 116850371148105]) [2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [116715762590985, 87564041360985, 583897451850195, 408651623073015, 321131653672641, 583661959739775, 58483601550297, 1284869479637499, 1985155777530933, 2686363297428657, 3686779523368197, 1986076999535223, 284453253697959, 921127886614713, 5388403269205461, 3543418908064545, 270237044875, 2653375725]) [0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6] [true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, true]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [3950370308663, 3347521056213, 16361754677381, 72145912839, 1429085564073, 12339238455879, 47511288825, 1637687571687, 12314603831865, 4028262717257, 2905682416971, 16390377837947, 4065183677333, 7303637860631, 24483824232537, 56661575688613, 217839565447, 85210583598483, 56617495150141, 15991303387311, 198489654437237, 764194744678419, 63588361244445, 509087595091041, 764383557378735, 700229531129175, 2037665897148195, 3737313762540225, 350397598067145, 935264308013295, 3736732903242225, 1518542115705525]) [0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [8409310973795745, 12142955019971967, 3035937707107935, 3088857066003, 12144921836206467, 9105870788560917, 24284787999112431, 31237327399391949, 2277246032274633, 5192382435926949, 31229158966036629, 2766432076353879, 57274103929501629, 68764961739507579, 22120174836938097, 19738301156030679, 5078031246511, 34493884425]) [0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 1, 7] [true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [2112153823669, 9507153084875, 18026989629651, 1952975454319, 6407682721107, 13961860351663, 1976512457809, 5601202176237, 13985397355153, 2037755249419, 10360707636725, 17999665062381, 30311485903035, 9676712675075, 50348906214835, 30291266465097, 70983679442795, 110951658582967, 353864605503703, 70259245605269, 212621680455639, 354013721459797, 636745531564611, 920500007419139, 1486271378742843, 637768197314325, 211757649863907, 1485782610827025, 2335797225921075, 3183811639433775, 4203835531278831, 2333797024339725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [465758718981969, 4205565170931621, 6071873836636587, 7943641983228483, 9542495744850891, 6077333317523517, 2606711409309213, 9534653234516841, 13013117653065195, 16470437570058519, 18795214117605495, 12991973151510165, 7209876686969865, 18846794612867301, 24577310582145795, 30432132043502931, 2517392931665, 34493884425]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 7] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [8045054830369, 1083594840773, 16256955965363, 33188900745, 1938760885951, 8178712234249, 21916389495, 2134000780801, 8167439722999, 8080675965919, 980338637723, 16270032078413, 8097857635249, 319208648335, 32448565679581, 80864912524135, 10058534910695, 40318489209305, 80884870611235, 70650235777415, 202068272344675, 283162682137685, 17706583925135, 209539181775, 283076683096235, 106256223180135, 566448904415695, 679208075818461, 212250347395695, 170317511693469, 679472018830101, 466695629458191]) [0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1] [false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [1188362582955093, 1335351382136115, 233610835717203, 532483219649079, 1334460890163885, 217163938169481, 2137329052650921, 2309695772336139, 867239218729479, 1162094170478667, 2313383435732031, 1441040019658215, 3460985037589503, 3704376525300633, 180768027125319, 2069991948020901, 6075502698933, 34493884425]) [0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 4, 0, 1, 6] [false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [70809134731015, 1481596166217, 6569919150023, 501530696389, 525879320689, 1505944790517, 502883397739, 478534773439, 1507297491867, 16207011640583, 1531646116167, 80532800107975, 145626981391257, 23863568015607, 48887169642699, 36415413403023, 121120643532585, 10630493895189, 101106000615425, 121798085596485, 10176681974555, 404154916865375, 283303358929115, 727165463530635, 792595015190657, 141178415634445, 338725365205353, 49592298759437, 254645828130771, 155918303767037, 81906908321883, 255559974441051]) [0, 5, 0, 5, 5, 5, 5, 5, 5, 0, 5, 0, 0, 1, 0, 2, 1, 5, 2, 1, 3, 0, 1, 0, 0, 2, 0, 4, 2, 3, 4, 2] [false, true, true, false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [91289084642145, 1307404009880943, 400609438444293, 1887601865893911, 1956897058903473, 796284060998841, 1238108816871381, 492727354833303, 1155678182014887, 336212207670663, 683604211930137, 1174625358334371, 120386889561123, 2642697641777463, 1578738665705661, 3450924256520043, 38689526940519, 34493884425]) [3, 0, 2, 0, 0, 1, 0, 2, 1, 3, 2, 1, 4, 0, 1, 0, 0, 8] [true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014]

#time def graph : KernelGraph 48 15 33 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 84.3822 s provisional ×3 model; 140637 exact original rank units.
#time theorem checked : chart.check 50 48 basis.matrix = true := by decide +kernel
end C011

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P023
