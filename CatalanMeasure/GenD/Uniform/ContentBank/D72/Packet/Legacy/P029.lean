module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCert
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P029
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

#time def basisScales : List Int :=
  decoded (raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows002 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows003 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows004 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows013 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows014 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows015 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows016 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows017 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows018 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows019 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows020 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows021 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows022 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows023 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows024 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows025 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows026 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows : List (List Int) :=
  [ambientRows000, ambientRows001, ambientRows002, ambientRows003, ambientRows004, ambientRows005, ambientRows006, ambientRows007, ambientRows008, ambientRows009, ambientRows010, ambientRows011, ambientRows012, ambientRows013, ambientRows014, ambientRows015, ambientRows016, ambientRows017, ambientRows018, ambientRows019, ambientRows020, ambientRows021, ambientRows022, ambientRows023, ambientRows024, ambientRows025, ambientRows026]

#time def ambientIndex : List Nat :=
  [0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 4, 0, 0, 5, 0, 0, 6, 0, 0, 7, 0, 0, 8, 0, 0, 9, 0, 0, 10, 0, 0, 11, 0, 0, 0, 0]

#time def colTags : List (Option (Fin 27)) :=
  [some ⟨0, by decide⟩, none, some ⟨1, by decide⟩, some ⟨2, by decide⟩, none, some ⟨3, by decide⟩, some ⟨4, by decide⟩, none, some ⟨5, by decide⟩, some ⟨6, by decide⟩, none, some ⟨7, by decide⟩, some ⟨8, by decide⟩, none, some ⟨9, by decide⟩, some ⟨10, by decide⟩, none, some ⟨11, by decide⟩, some ⟨12, by decide⟩, none, some ⟨13, by decide⟩, some ⟨14, by decide⟩, none, some ⟨15, by decide⟩, some ⟨16, by decide⟩, none, some ⟨17, by decide⟩, some ⟨18, by decide⟩, none, some ⟨19, by decide⟩, some ⟨20, by decide⟩, none, some ⟨21, by decide⟩, some ⟨22, by decide⟩, none, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩, some ⟨26, by decide⟩]

#time def basis : DiagView 27 39 :=
  ⟨fun x => colTags.getD x.val none, fun a => basisScales.getD a.val 0,
    fun a x => Mx ambientRows a.val (ambientIndex.getD x.val 0)⟩

namespace C000
#time def pivTape : List (Fin 27) :=
  [⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩]

#time def roleTape : List (Fin 13 ⊕ Fin 14) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩]

#time def roles : GraphRoles 27 13 14 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0]) [1, 0, 0, 0, 0, 0, 0] [true, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 1, 0, 0, 0]) [0, 0, 0, 1, 0, 0, 0] [false, false, false, true, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012]

#time def graph : KernelGraph 27 13 14 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 15.0546 s provisional ×3 model; 25091 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C000

namespace C001
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩]

#time def roleTape : List (Fin 14 ⊕ Fin 13) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨9, by decide⟩, .inl ⟨12, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inl ⟨13, by decide⟩, .inr ⟨12, by decide⟩]

#time def roles : GraphRoles 27 14 13 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425]) [6] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 27894706383700777808816942504949702839182513385989911397140757415286183086632776876423134154571716783326142118558608075]) [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 0] [true, false, true, false, true, false, true, false, true, false, true, false, true]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 3135947191126563761758888538883295309924900394322380739962139463035142520904078813326384128111781035373667278523975]) [6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 4] [true, false, true, false, true, false, true, false, true, false, true, true, false]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 30038008203757067837111399174315380065776403303216502707327804196599696264055402608094215663300356789951000342374864575]) [6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 0, 0] [false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 79156423830801849994817230028984434483792300063384635080702557061664164029570408797773652799814009540012162844630675]) [0, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 9430947070166058771280796550733668096912447088497269265892350978667184718563430700987619004137421222247920875974725]) [0, 0, 6, 7, 7, 7, 7, 7, 7, 7, 7, 0, 5] [false, false, false, true, false, true, false, true, false, true, false, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 12095300249574854712642013363712665117307287571881036450434253405731774681622576368762222497222603954876412959612925]) [0, 0, 0, 6, 7, 7, 7, 7, 7, 7, 7, 0, 3] [false, false, false, false, true, false, true, false, true, false, true, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 3135097545377547920793253471726822040751551016601990782737968188625909068418847659820491440650895701556764713319925]) [0, 0, 0, 0, 6, 7, 7, 7, 7, 7, 7, 0, 4] [false, false, false, false, false, true, false, true, false, true, false, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 6757347342078138014106544332667651017478056372513452222327967666651066385274471310968583293032568320159624205336175]) [0, 0, 0, 0, 0, 6, 7, 7, 7, 7, 7, 0, 1] [false, false, false, false, false, false, true, false, true, false, true, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 3350998381063394397727255933666914308415275352921506472879717025562258071555255742014542840267643237698681263538225]) [0, 0, 0, 0, 0, 0, 6, 7, 7, 7, 7, 0, 1] [false, false, false, false, false, false, false, true, false, true, false, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 1303624564541423957339207684695447206172211786230815849301703244413232460692250196082798242134765493204522747406675]) [0, 0, 0, 0, 0, 0, 0, 6, 7, 7, 7, 0, 0] [false, false, false, false, false, false, false, false, true, false, true, false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 603554282363419551195292826882059826052482169950630651680653977670529276073005593558975345612835353618053661075825]) [0, 0, 0, 0, 0, 0, 0, 0, 6, 7, 7, 0, 0] [false, false, false, false, false, false, false, false, false, true, false, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 31432719379312465381332667563902238655739535240501699590106326157392085852349903839025966102713297749868593689725]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 7, 0, 1] [false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2327211517611069443868961934808223206796905397268460542179059158415856644548585361378271769113686115646651056204425, 0, 13431629611337926595195077780222728308947156190302926586949328932767448557421302951200464170827340085989736121975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 132263110255814672878354573267316191158388781866411621707431700107698176306983626237506270509977876096816426942805359]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2] [false, false, false, false, false, false, false, false, false, false, false, false, true]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [28506852627, 1799781540471, 2790709226529, 62951677107, 962420833431, 2825154051009, 121589003507, 1925684894685, 3009694731623, 457799757605, 1205598840445, 3589083492735, 385144090213, 2841284409895, 4432027340553, 1526334164683, 1975887020871, 6343505595449, 1188974705547, 5893952739261, 9058814465679, 5885588004477, 4353836431965, 16133377175703, 4651881734205, 17665128748215, 26670846914385, 31991287063683, 13657599900375, 63314015712273, 26494785428163, 81647702875581]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [121800088204119, 301370630251317, 66647170756701, 449665503883599, 704804019789, 2029052025, 0]) [0, 0, 0, 0, 1, 10, 0] [true, false, true, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [5014608595, 748349836389, 953894821249, 3179357485, 1119322937349, 946553816809, 77282625859, 799219556149, 32392308519, 86185457715, 1428453440785, 600010978091, 141126010683, 1143961387009, 1568459435263, 133904371195, 2557461526249, 2118520199019, 1023051255665, 2215196356569, 1704690098537, 961955832129, 6649666548909, 1348596821217, 632754195075, 6063019685085, 11418376677597, 606908491107, 26897800791309, 21335678167053, 43152428092095, 25484091400509]) [3, 0, 1, 3, 0, 1, 1, 0, 6, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 4, 0, 1, 4, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [17335843547001, 42353611052655, 199507513159689, 77424706666377, 973953255629, 2029052025, 0]) [3, 1, 0, 2, 0, 9, 0] [true, false, true, false, false, true, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [3282808263, 74598100853, 126559174489, 4276996143, 48678265373, 127553362369, 6201526375, 83152093139, 138031884887, 25020685825, 61081318123, 169254097087, 23280098345, 133193464789, 217554881257, 92210572127, 107641514813, 333045551729, 83455622903, 317614609043, 508711746759, 441331665425, 274552760619, 1033499035087, 409699038105, 1200277939893, 1884529738617, 3597812296335, 1093950836829, 5892041073057, 3460430487687, 8395902532563]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [12950283857079, 92416989586593, 8014811812203, 108827703931359, 4057561961, 156080925, 0]) [0, 0, 0, 0, 4, 9, 0] [true, false, true, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [76643779, 15908183717, 19204417533, 48726589, 21887501117, 19092748773, 1971743929, 16687809141, 10629699529, 2106184095, 29774476833, 12668663541, 241311753, 25112545521, 35165487273, 1872679951, 60662381217, 50378183173, 34460555053, 55075424737, 46164729015, 33497344511, 198504601429, 80143678797, 64056117221, 189064802781, 450009170989, 63245584995, 1223402476965, 959215979853, 6018027291849, 1200994162701]) [3, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 6, 0, 1, 3, 0, 1, 1, 0, 2, 1, 0, 2, 3, 0, 1, 3, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [3615112805841, 6005457538535, 25295511644361, 9626855221033, 19510992649, 156080925, 0]) [2, 1, 0, 2, 0, 7, 0] [true, false, true, false, false, true, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [130978113, 1824459569, 3272776231, 149487093, 1317338549, 3291285211, 187881131, 2123433755, 3628653435, 841310525, 1693100811, 4657845091, 812593919, 3806054805, 6311749535, 3710572949, 3318288649, 10834916403, 3557374755, 11227200703, 18102864107, 26020581237, 10433038159, 47680820099, 25471187791, 63268363177, 99172589127, 568704819973, 61375413741, 693348596891, 566357841355, 1200678003123]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [1828411258219, 13207065181667, 1194091096451, 10812296082093, 425469293, 14189175, 0]) [0, 0, 0, 0, 2, 7, 0] [true, true, true, true, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [47128279, 818895841, 3799693043, 30073129, 1057386541, 3782637893, 513663589, 424484485, 4326374611, 534469025, 785525065, 5374507225, 2327243357, 1383437995, 8236219607, 2291443717, 3898293487, 12854906681, 15010273873, 229680107, 30156624271, 14861707013, 295446365, 60028605157, 297853346225, 18536588725, 372743658395, 297355974913, 316761913585, 967952979533, 6316959119267, 157946281819]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 7, 0, 0, 1, 0, 0, 1, 0, 0, 2] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [5051650164821, 6318882289783, 3000098602841, 17687491573871, 1923410661, 14189175, 0]) [0, 0, 2, 0, 0, 7, 0] [false, true, false, true, false, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [144001175, 1330740479, 2504502783, 154565825, 1029761129, 2515067433, 177526263, 1639872129, 2847159521, 927000607, 1384813655, 3951686391, 912044969, 3493873343, 5790731967, 5717071105, 3208903593, 12419848041, 5633310455, 14928015553, 23770229601, 104085208351, 14475524503, 133488748407, 103786350697, 223098432255, 341360307455, 2007209442879, 222048225897, 1562062784727, 2008471057545, 3791320453503]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [5577743285151, 13901834834335, 3794893889193, 6315620491639, 1324251979, 4729725, 0]) [0, 0, 0, 0, 0, 8, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [10307019, 477003229, 1071683027, 6601269, 584372779, 1067977277, 206345191, 490205767, 1280923737, 210950731, 997063161, 1698219659, 1255738761, 912107229, 3164909151, 1247954577, 3508540683, 5668602489, 20616062883, 3408016383, 27532619949, 20583741471, 44740666449, 68732424303, 356740390659, 44575499325, 267424224885, 356848098579, 668740114869, 981012714123, 2230674133983, 669120697833]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [892813321281, 2230259252067, 3792608153097, 5353746707331, 540995023, 14189175, 0]) [0, 0, 0, 0, 0, 5, 0] [true, false, true, false, false, true, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [188499907, 1123043339, 2229462995, 195470605, 917919749, 2236433693, 211159327, 1513984549, 2643063625, 1450102927, 1340238403, 4304325879, 1440949741, 4414190403, 7195378547, 21834540861, 4222137885, 30470869149, 21781052175, 48083272125, 74086462185, 336245926785, 47784242235, 240378412425, 336436083075, 624408581445, 913060422285, 1873429232205, 625087923915, 623932726845, 1872633781935, 3122449882965]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [4369995740985, 6869170375137, 3120179639955, 626540852217, 1208981451, 14189175, 0]) [0, 0, 0, 0, 0, 6, 0] [true, true, true, true, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [12671967, 6416889393, 1752067257, 8143905, 7498272927, 1747539195, 2278645289, 6547191873, 9301377689, 2301602531, 16612854083, 13881625509, 16030637063, 15753601997, 24122251083, 2001462787, 144857950587, 28082295221, 432189045963, 143847220365, 287836460487, 432346669965, 1583898233265, 1152372176415, 1057028179935, 1585539459495, 264668756745, 1056766556865, 6872327206215, 2378463493545, 6867200642649, 6868592995425]) [3, 0, 3, 3, 0, 3, 1, 0, 1, 1, 0, 1, 2, 0, 2, 5, 0, 3, 1, 0, 1, 1, 0, 1, 2, 0, 2, 2, 0, 2, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [3259458171, 6869208369639, 20596475364381, 13733149554117, 220592403, 156080925, 0]) [1, 1, 0, 1, 5, 5, 0] [true, true, false, true, false, true, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [8763981599, 29182796607, 62971304543, 8901424289, 25024526337, 63108747233, 9219513599, 46985645185, 81229685121, 137140025535, 43463553535, 227589224255, 136970843097, 321265696255, 501700092887, 1601194201703, 317405239729, 962523265719, 1602221532497, 2881122707151, 4165938999919, 6725239940463, 2887037825265, 957079408047, 6721597465665, 10569357173775, 14403916814175, 19021826501631, 10556157106065, 2103687778209, 19036952835441, 27474295829487]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [35955091558863, 43178165061711, 27517748564817, 11813879332593, 35867643071, 156080925, 0]) [0, 0, 0, 0, 0, 7, 0] [false, false, false, true, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [1196590395, 113460044927, 241141261819, 771455685, 126484626497, 240716127109, 237668952979, 115002956297, 479156535773, 119109143003, 601822532455, 477521887379, 297262560011, 591439528309, 296209604831, 1189491513605, 4154378427721, 2970960963311, 2082339934625, 4166526526111, 2113696167, 8325673836893, 12504341049279, 16663488360061, 19972508233713, 12484821147675, 5016653963241, 19984704364341, 27440675418147, 34940558634813, 39296805595545, 27484587581007]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 3, 0, 2, 1, 0, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [15628457403609, 4906272149295, 51152935772943, 7864815673287, 121168926107, 2029052025, 0]) [0, 3, 0, 3, 0, 5, 0] [false, false, true, false, false, true, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [235602768859, 248588701819, 707619927387, 236414389669, 223428456709, 708431548197, 119168387903, 721417481157, 147897839209, 1070827651617, 700102008321, 180033953439, 2142598774119, 3561893125311, 5004389891109, 5947453335577, 3585095539917, 1199535329651, 2970758949899, 8333013545843, 2672358976431, 5827784482709, 8297940259679, 621923105013, 11676571108363, 14978124384993, 18356755233677, 19272765154677, 15055201957047, 10760561187363, 9593034939267, 23567405924361]) [0, 0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 3, 0, 0, 0, 0, 0, 0, 1, 0] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [3462284230731, 14389919702877, 23316937800021, 4526126079657, 471611348123, 2029052025, 0]) [3, 1, 0, 2, 0, 6, 0] [true, true, true, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [22013886147, 2558439520551, 4106743225809, 69444643587, 1526289819111, 4154173983249, 194721182627, 2697328807725, 4418339809463, 594862683605, 1915732184365, 5207923675695, 590555776693, 3887054174935, 6393342135993, 1952597522203, 3096843737751, 8936495434889, 1768340612667, 7792249219341, 12657433569759, 7276680667437, 6633524963085, 21702454849863, 6616426796685, 22345610554215, 35595562313985, 37762894265043, 19866378556455, 79974883375713, 35387915994483, 97871399084301]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [153125693635239, 335788180698597, 90642210545421, 524301790328319, 1032189277989, 2029052025, 2029052025]) [0, 0, 0, 0, 1, 10, 10] [true, false, true, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013]

#time def graph : KernelGraph 27 14 13 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 14.1180 s provisional ×3 model; 23530 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C001

namespace C002
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 26) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩]

#time def roles : GraphRoles 27 1 26 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [22013886147]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [4106743225809, 69444643587, 4154173983249, 194721182627, 4418339809463, 594862683605, 5207923675695, 590555776693, 6393342135993, 1952597522203, 8936495434889, 1768340612667, 12657433569759, 7276680667437, 21702454849863, 6616426796685, 35595562313985, 37762894265043, 79974883375713, 35387915994483, 153125693635239, 335788180698597, 524301790328319, 1032189277989, 2029052025, 2029052025]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 10] [true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [22013886147, 2558439520551, 4106743225809, 69444643587, 1526289819111, 4154173983249, 194721182627, 2697328807725, 4418339809463, 594862683605, 1915732184365, 5207923675695, 590555776693, 3887054174935, 6393342135993, 1952597522203, 3096843737751, 8936495434889, 1768340612667, 7792249219341, 12657433569759, 7276680667437, 6633524963085, 21702454849863, 6616426796685, 22345610554215, 35595562313985, 37762894265043, 19866378556455, 79974883375713, 35387915994483, 97871399084301]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [153125693635239, 335788180698597, 90642210545421, 524301790328319, 1032189277989, 2029052025, 2029052025]) [0, 0, 0, 0, 1, 10, 10] [true, false, true, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows : List (List Int) :=
  [chartRows000]

#time def graph : KernelGraph 27 1 26 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 27.6042 s provisional ×3 model; 46007 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C002

namespace C003
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩]

#time def roleTape : List (Fin 14 ⊕ Fin 13) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inr ⟨12, by decide⟩]

#time def roles : GraphRoles 27 14 13 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025]

#time def graph : KernelGraph 27 14 13 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 18.0492 s provisional ×3 model; 30082 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C003

namespace C004
#time def pivTape : List (Fin 27) :=
  [⟨25, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 26) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inl ⟨0, by decide⟩, .inr ⟨25, by decide⟩]

#time def roles : GraphRoles 27 1 26 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012]

#time def graph : KernelGraph 27 1 26 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 35.1858 s provisional ×3 model; 58643 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C004

namespace C005
#time def pivTape : List (Fin 27) :=
  []

#time def freeTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩]

#time def roleTape : List (Fin 0 ⊕ Fin 27) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩, .inr ⟨22, by decide⟩, .inr ⟨23, by decide⟩, .inr ⟨24, by decide⟩, .inr ⟨25, by decide⟩, .inr ⟨26, by decide⟩]

#time def roles : GraphRoles 27 0 27 :=
  fun a => roleTape.getD a.val (.inr ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows : List (List Int) :=
  []

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011]

#time def graph : KernelGraph 27 0 27 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 36.7308 s provisional ×3 model; 61218 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C005

namespace C006
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩]

#time def freeTape : List (Fin 27) :=
  []

#time def roleTape : List (Fin 27 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩]

#time def roles : GraphRoles 27 27 0 :=
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

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [1277156303523, 14344725799, 610912330589, 2734006947, 15156346609, 1890802641059, 1905240913565, 461765232515, 11704265559, 1904261998313, 1420237822077, 3821207177437, 3805798032343, 721248382899, 1919671143407, 3798919125679, 1192780105133, 5685046014615, 5708115629841, 2356422359881, 3775849510453, 5735053208565, 3322555419575, 7667319327953, 7617196189259, 844657712171, 5785176347259, 7509498770171, 1073660192421, 9341518612171, 9507074251077, 4130867921487]) [0, 6, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1] [false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [7343943131265, 10101086847681, 5212433481393, 12264217967493, 333121986467, 2029052025, 0]) [0, 0, 1, 0, 0, 7, 0] [false, false, true, false, false, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [5285148865, 495463843029, 734555821369, 2908817215, 931366608789, 725050494769, 65093929339, 542004918469, 100222461621, 63341636715, 1191742326145, 465107629511, 124008370143, 795371465329, 1241573636023, 98382424735, 2183809287289, 1686355225779, 926490271145, 1582430863209, 1404805173197, 730107054969, 5889770371869, 1116551918127, 147956543235, 4502859083085, 9930924110997, 121666668603, 24828207905949, 18558866889813, 41670239664375, 20076192664269]) [3, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 6, 0, 1, 6, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [16030609987371, 36617352644775, 191509166563449, 71205016129317, 755696416829, 2029052025, 0]) [3, 1, 0, 2, 0, 9, 0] [true, false, true, false, false, true, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [3157943523, 89187677393, 151867520629, 4401860883, 59521899713, 153111437989, 7607914435, 97991399159, 165121213307, 27656511325, 74737728583, 200385639067, 27230323085, 153304421809, 255272473477, 100407944387, 129198374753, 382910740949, 94597274963, 354120310583, 577915960299, 468083447405, 318392924679, 1140596682667, 447478750845, 1290287205393, 2056158880917, 3708804742515, 1213350426369, 6212442374277, 3631452229347, 8707896690423]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [13552699346139, 93078865556733, 8476254885063, 110263017132219, 19378183019, 156080925, 0]) [0, 0, 0, 0, 2, 9, 0] [true, false, true, false, false, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [159530795, 12990268409, 16673582919, 91209941, 19718774249, 16536941211, 1831105123, 13719947937, 2318808277, 1842601545, 27043194741, 5556043221, 3663476811, 21090354117, 31393728051, 3335491289, 56351009229, 45391664251, 33346389847, 47774284429, 21352259169, 30822166313, 189736568617, 37394398209, 126223248805, 171062949681, 432846256759, 120941547681, 1199522559057, 927175849731, 6000925117683, 1138595331129]) [2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [896248007847, 5939269941521, 25203223029789, 4777544780495, 16992644509, 156080925, 0]) [4, 1, 0, 3, 0, 7, 0] [true, false, true, false, false, true, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [129086223, 2045513759, 3656236021, 151378983, 1481636039, 3678528781, 209190041, 2348271725, 4039097805, 881247275, 1900016121, 5129535121, 872445809, 4110766275, 6883228205, 3834775559, 3644907739, 11590449573, 3726187665, 11780317393, 19151412797, 26425911267, 11097283069, 49303511729, 26043607681, 64632139927, 101773030677, 570386523703, 63184498431, 698203162061, 568949079865, 1205405187333]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [1837538765629, 13197036757877, 1201082658161, 10790548912383, 946330561, 14189175, 0]) [0, 0, 0, 0, 1, 7, 0] [true, true, true, true, false, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [48749899, 724158331, 3471013223, 28451509, 986973331, 3450714833, 495398809, 47038115, 3974565151, 500237525, 370593035, 4970201485, 2275941737, 1252847365, 7746380747, 2184984337, 3758313877, 12207306821, 14865577093, 1718915851, 29257868251, 14514281273, 9311945485, 58637726617, 297362700605, 17952112975, 370514708495, 295914514573, 315986591575, 963791923673, 6319180180847, 78466656887]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [5059473742601, 6327478081603, 750399198659, 17706132005051, 1759881561, 14189175, 0]) [0, 0, 4, 0, 0, 7, 0] [false, true, false, true, false, true, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [71527615, 720633787, 1348116339, 77755885, 555954937, 1354344609, 94090359, 876145557, 1526190853, 473484491, 744135655, 2093765703, 470985457, 1823114539, 3038235651, 2889586205, 1686106569, 6398807313, 2858858455, 7602286949, 12147251973, 52143936683, 7403823479, 67150047111, 52036280321, 111890160315, 171330264115, 1003184295507, 111476384121, 779817751071, 1003587719145, 1894478430699]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [2786589765723, 6953424523115, 1895699054169, 3163247038247, 709821977, 4729725, 0]) [0, 0, 0, 0, 0, 7, 0] [false, false, false, false, false, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [1770389, 4585009, 167962177, 1047659, 23207911, 167239447, 33798951, 37727731, 202086057, 34049101, 80214773, 269934109, 207627241, 1121513, 511610451, 204542357, 143921007, 923780049, 3431321233, 276319189, 4559643639, 3419364411, 3719163247, 11410329283, 59472632329, 230980225, 44642938635, 59521397089, 27876734541, 163636968053, 371707043483, 55825713489]) [0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [148548678341, 371431308017, 315953574401, 891687029841, 84866283, 4729725, 0]) [0, 0, 1, 0, 0, 4, 0] [true, false, true, false, false, true, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [46983085, 297339899, 586125233, 49009543, 241802249, 588151691, 1699625, 395358985, 345774617, 91380247, 350578249, 555729111, 364726327, 1126400961, 1841705537, 5467950411, 1080030903, 7674382275, 1364481003, 12062301783, 9300128349, 10503885243, 11995878927, 29986450617, 84066089277, 155999862105, 228070072455, 468483435831, 156136299627, 156347274099, 117088197093, 780967009557]) [0, 0, 0, 0, 0, 0, 5, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [546591749151, 107283778875, 780569277117, 77502087663, 316554159, 14189175, 0]) [1, 4, 0, 1, 0, 4, 0] [true, true, true, true, false, false, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [9473961, 138302457, 1221940761, 5664855, 164814243, 1218131655, 411393383, 282269769, 1635189893, 413027267, 741021869, 2459610543, 5821160947, 173824259, 8693798757, 5805500479, 205068213, 20320460183, 78602846481, 6500797515, 52476885819, 78663757725, 72040663665, 209743490025, 384295826355, 36081480105, 95888578605, 384049424715, 156127581345, 864233829675, 1248935285733, 311886464505]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [652031343, 1250314488633, 936680123043, 2499901805709, 615707361, 14189175, 0]) [0, 0, 1, 0, 0, 5, 0] [false, true, false, true, false, true, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [2188394051, 7599648663, 16270083347, 2227957421, 6482040633, 16309646717, 2334178151, 12055563505, 20871782289, 34339919415, 11150396935, 57545879855, 34325007123, 80735402335, 126210806393, 400127771837, 79800411181, 239591958321, 400323265373, 719520141339, 1040042995531, 1681867313907, 720846119565, 241501053003, 1681186443765, 2644214486475, 3604554810675, 4753144282779, 2641526767965, 532596971661, 4755675255909, 6862074079083]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [8976222567027, 10808330348139, 6869823743853, 2923567474797, 9229238699, 156080925, 0]) [0, 0, 0, 0, 0, 5, 0] [false, false, false, true, false, false, false]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [23611665, 1055890873, 4515657217, 14235375, 1190131903, 4506280927, 4563795307, 133765781, 9084311609, 18273794587, 2876963605, 72866222251, 183006772021, 22554299579, 91866755183, 183156336175, 159991063181, 458029863379, 640505717345, 40150509149, 680482209, 319960995823, 120128663541, 639873613391, 768536660073, 239659977525, 191297949141, 769709710611, 528279332991, 1346948421543, 1509771160005, 265024866543]) [2, 3, 2, 2, 3, 2, 2, 6, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [606886972149, 3006516015525, 490745913507, 4812284391237, 2269634441, 156080925, 0]) [1, 0, 3, 0, 2, 5, 0] [false, false, true, false, false, true, false]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [29443099493, 31920304223, 89921278869, 29559045323, 28557875153, 90037224699, 238989741691, 91038394869, 1195759901867, 2140431527109, 353221242303, 705681883551, 535191185301, 1776277947633, 623359768983, 1487814814603, 1787543498901, 36761988583, 5946690809683, 4174981310779, 10721566433439, 11643148495213, 2079573655391, 5025108747909, 1457378815931, 3734083592217, 285579223043, 2415537170229, 3749941608333, 663237715023, 19265472830019, 5928065088699]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 6, 3, 2, 4, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [27977966751483, 28472539848189, 11765589613353, 18770899733313, 59682189181, 2029052025, 0]) [0, 0, 1, 0, 3, 6, 0] [true, true, true, false, false, false, false]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040]

#time def graph : KernelGraph 27 27 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.9594 s provisional ×3 model; 1599 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C006

namespace C007
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩]

#time def freeTape : List (Fin 27) :=
  []

#time def roleTape : List (Fin 27 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩, .inl ⟨23, by decide⟩, .inl ⟨24, by decide⟩, .inl ⟨25, by decide⟩, .inl ⟨26, by decide⟩]

#time def roles : GraphRoles 27 27 0 :=
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

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022, tailRows023, tailRows024, tailRows025, tailRows026]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [1277156303523, 14344725799, 610912330589, 2734006947, 15156346609, 1890802641059, 1905240913565, 461765232515, 11704265559, 1904261998313, 1420237822077, 3821207177437, 3805798032343, 721248382899, 1919671143407, 3798919125679, 1192780105133, 5685046014615, 5708115629841, 2356422359881, 3775849510453, 5735053208565, 3322555419575, 7667319327953, 7617196189259, 844657712171, 5785176347259, 7509498770171, 1073660192421, 9341518612171, 9507074251077, 4130867921487]) [0, 6, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1] [false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [7343943131265, 10101086847681, 5212433481393, 12264217967493, 333121986467, 2029052025, 0]) [0, 0, 1, 0, 0, 7, 0] [false, false, true, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [5285148865, 495463843029, 734555821369, 2908817215, 931366608789, 725050494769, 65093929339, 542004918469, 100222461621, 63341636715, 1191742326145, 465107629511, 124008370143, 795371465329, 1241573636023, 98382424735, 2183809287289, 1686355225779, 926490271145, 1582430863209, 1404805173197, 730107054969, 5889770371869, 1116551918127, 147956543235, 4502859083085, 9930924110997, 121666668603, 24828207905949, 18558866889813, 41670239664375, 20076192664269]) [3, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 6, 0, 1, 6, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [16030609987371, 36617352644775, 191509166563449, 71205016129317, 755696416829, 2029052025, 0]) [3, 1, 0, 2, 0, 9, 0] [true, false, true, false, false, true, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [3157943523, 89187677393, 151867520629, 4401860883, 59521899713, 153111437989, 7607914435, 97991399159, 165121213307, 27656511325, 74737728583, 200385639067, 27230323085, 153304421809, 255272473477, 100407944387, 129198374753, 382910740949, 94597274963, 354120310583, 577915960299, 468083447405, 318392924679, 1140596682667, 447478750845, 1290287205393, 2056158880917, 3708804742515, 1213350426369, 6212442374277, 3631452229347, 8707896690423]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [13552699346139, 93078865556733, 8476254885063, 110263017132219, 19378183019, 156080925, 0]) [0, 0, 0, 0, 2, 9, 0] [true, false, true, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [159530795, 12990268409, 16673582919, 91209941, 19718774249, 16536941211, 1831105123, 13719947937, 2318808277, 1842601545, 27043194741, 5556043221, 3663476811, 21090354117, 31393728051, 3335491289, 56351009229, 45391664251, 33346389847, 47774284429, 21352259169, 30822166313, 189736568617, 37394398209, 126223248805, 171062949681, 432846256759, 120941547681, 1199522559057, 927175849731, 6000925117683, 1138595331129]) [2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [896248007847, 5939269941521, 25203223029789, 4777544780495, 16992644509, 156080925, 0]) [4, 1, 0, 3, 0, 7, 0] [true, false, true, false, false, true, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [129086223, 2045513759, 3656236021, 151378983, 1481636039, 3678528781, 209190041, 2348271725, 4039097805, 881247275, 1900016121, 5129535121, 872445809, 4110766275, 6883228205, 3834775559, 3644907739, 11590449573, 3726187665, 11780317393, 19151412797, 26425911267, 11097283069, 49303511729, 26043607681, 64632139927, 101773030677, 570386523703, 63184498431, 698203162061, 568949079865, 1205405187333]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [1837538765629, 13197036757877, 1201082658161, 10790548912383, 946330561, 14189175, 0]) [0, 0, 0, 0, 1, 7, 0] [true, true, true, true, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [48749899, 724158331, 3471013223, 28451509, 986973331, 3450714833, 495398809, 47038115, 3974565151, 500237525, 370593035, 4970201485, 2275941737, 1252847365, 7746380747, 2184984337, 3758313877, 12207306821, 14865577093, 1718915851, 29257868251, 14514281273, 9311945485, 58637726617, 297362700605, 17952112975, 370514708495, 295914514573, 315986591575, 963791923673, 6319180180847, 78466656887]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [5059473742601, 6327478081603, 750399198659, 17706132005051, 1759881561, 14189175, 0]) [0, 0, 4, 0, 0, 7, 0] [false, true, false, true, false, true, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [71527615, 720633787, 1348116339, 77755885, 555954937, 1354344609, 94090359, 876145557, 1526190853, 473484491, 744135655, 2093765703, 470985457, 1823114539, 3038235651, 2889586205, 1686106569, 6398807313, 2858858455, 7602286949, 12147251973, 52143936683, 7403823479, 67150047111, 52036280321, 111890160315, 171330264115, 1003184295507, 111476384121, 779817751071, 1003587719145, 1894478430699]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [2786589765723, 6953424523115, 1895699054169, 3163247038247, 709821977, 4729725, 0]) [0, 0, 0, 0, 0, 7, 0] [false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [1770389, 4585009, 167962177, 1047659, 23207911, 167239447, 33798951, 37727731, 202086057, 34049101, 80214773, 269934109, 207627241, 1121513, 511610451, 204542357, 143921007, 923780049, 3431321233, 276319189, 4559643639, 3419364411, 3719163247, 11410329283, 59472632329, 230980225, 44642938635, 59521397089, 27876734541, 163636968053, 371707043483, 55825713489]) [0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [148548678341, 371431308017, 315953574401, 891687029841, 84866283, 4729725, 0]) [0, 0, 1, 0, 0, 4, 0] [true, false, true, false, false, true, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [46983085, 297339899, 586125233, 49009543, 241802249, 588151691, 1699625, 395358985, 345774617, 91380247, 350578249, 555729111, 364726327, 1126400961, 1841705537, 5467950411, 1080030903, 7674382275, 1364481003, 12062301783, 9300128349, 10503885243, 11995878927, 29986450617, 84066089277, 155999862105, 228070072455, 468483435831, 156136299627, 156347274099, 117088197093, 780967009557]) [0, 0, 0, 0, 0, 0, 5, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [546591749151, 107283778875, 780569277117, 77502087663, 316554159, 14189175, 0]) [1, 4, 0, 1, 0, 4, 0] [true, true, true, true, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [9473961, 138302457, 1221940761, 5664855, 164814243, 1218131655, 411393383, 282269769, 1635189893, 413027267, 741021869, 2459610543, 5821160947, 173824259, 8693798757, 5805500479, 205068213, 20320460183, 78602846481, 6500797515, 52476885819, 78663757725, 72040663665, 209743490025, 384295826355, 36081480105, 95888578605, 384049424715, 156127581345, 864233829675, 1248935285733, 311886464505]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [652031343, 1250314488633, 936680123043, 2499901805709, 615707361, 14189175, 0]) [0, 0, 1, 0, 0, 5, 0] [false, true, false, true, false, true, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [2188394051, 7599648663, 16270083347, 2227957421, 6482040633, 16309646717, 2334178151, 12055563505, 20871782289, 34339919415, 11150396935, 57545879855, 34325007123, 80735402335, 126210806393, 400127771837, 79800411181, 239591958321, 400323265373, 719520141339, 1040042995531, 1681867313907, 720846119565, 241501053003, 1681186443765, 2644214486475, 3604554810675, 4753144282779, 2641526767965, 532596971661, 4755675255909, 6862074079083]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [8976222567027, 10808330348139, 6869823743853, 2923567474797, 9229238699, 156080925, 0]) [0, 0, 0, 0, 0, 5, 0] [false, false, false, true, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [23611665, 1055890873, 4515657217, 14235375, 1190131903, 4506280927, 4563795307, 133765781, 9084311609, 18273794587, 2876963605, 72866222251, 183006772021, 22554299579, 91866755183, 183156336175, 159991063181, 458029863379, 640505717345, 40150509149, 680482209, 319960995823, 120128663541, 639873613391, 768536660073, 239659977525, 191297949141, 769709710611, 528279332991, 1346948421543, 1509771160005, 265024866543]) [2, 3, 2, 2, 3, 2, 2, 6, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [606886972149, 3006516015525, 490745913507, 4812284391237, 2269634441, 156080925, 0]) [1, 0, 3, 0, 2, 5, 0] [false, false, true, false, false, true, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [29443099493, 31920304223, 89921278869, 29559045323, 28557875153, 90037224699, 238989741691, 91038394869, 1195759901867, 2140431527109, 353221242303, 705681883551, 535191185301, 1776277947633, 623359768983, 1487814814603, 1787543498901, 36761988583, 5946690809683, 4174981310779, 10721566433439, 11643148495213, 2079573655391, 5025108747909, 1457378815931, 3734083592217, 285579223043, 2415537170229, 3749941608333, 663237715023, 19265472830019, 5928065088699]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 6, 3, 2, 4, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [27977966751483, 28472539848189, 11765589613353, 18770899733313, 59682189181, 2029052025, 0]) [0, 0, 1, 0, 3, 6, 0] [true, true, true, false, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027]

#time def graph : KernelGraph 27 27 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.6552 s provisional ×3 model; 1092 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C007

namespace C008
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩]

#time def roleTape : List (Fin 15 ⊕ Fin 12) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨9, by decide⟩, .inl ⟨12, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩]

#time def roles : GraphRoles 27 15 12 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [1] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] [true, false, true, false, true, false, true, false, true, false, true, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] [true, false, true, false, true, false, true, false, true, false, true, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]) [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0] [false, true, false, true, false, true, false, true, false, true, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]) [0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0] [false, false, true, false, true, false, true, false, true, false, true, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]) [0, 0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 0] [false, false, false, true, false, true, false, true, false, true, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0]) [0, 0, 0, 1, 2, 2, 2, 2, 2, 2, 2, 0] [false, false, false, false, true, false, true, false, true, false, true, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0]) [0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 2, 0] [false, false, false, false, false, true, false, true, false, true, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0]) [0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 0] [false, false, false, false, false, false, true, false, true, false, true, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0]) [0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 0] [false, false, false, false, false, false, false, true, false, true, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0] [false, false, false, false, false, false, false, false, true, false, true, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0] [false, false, false, false, false, false, false, false, false, true, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0] [false, false, false, false, false, false, false, false, false, false, true, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows014 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [1277156303523, 14344725799, 610912330589, 2734006947, 15156346609, 1890802641059, 1905240913565, 461765232515, 11704265559, 1904261998313, 1420237822077, 3821207177437, 3805798032343, 721248382899, 1919671143407, 3798919125679, 1192780105133, 5685046014615, 5708115629841, 2356422359881, 3775849510453, 5735053208565, 3322555419575, 7667319327953, 7617196189259, 844657712171, 5785176347259, 7509498770171, 1073660192421, 9341518612171, 9507074251077, 4130867921487]) [0, 6, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1] [false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [7343943131265, 10101086847681, 5212433481393, 12264217967493, 333121986467, 2029052025, 0]) [0, 0, 1, 0, 0, 7, 0] [false, false, true, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [5285148865, 495463843029, 734555821369, 2908817215, 931366608789, 725050494769, 65093929339, 542004918469, 100222461621, 63341636715, 1191742326145, 465107629511, 124008370143, 795371465329, 1241573636023, 98382424735, 2183809287289, 1686355225779, 926490271145, 1582430863209, 1404805173197, 730107054969, 5889770371869, 1116551918127, 147956543235, 4502859083085, 9930924110997, 121666668603, 24828207905949, 18558866889813, 41670239664375, 20076192664269]) [3, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 6, 0, 1, 6, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [16030609987371, 36617352644775, 191509166563449, 71205016129317, 755696416829, 2029052025, 0]) [3, 1, 0, 2, 0, 9, 0] [true, false, true, false, false, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [3157943523, 89187677393, 151867520629, 4401860883, 59521899713, 153111437989, 7607914435, 97991399159, 165121213307, 27656511325, 74737728583, 200385639067, 27230323085, 153304421809, 255272473477, 100407944387, 129198374753, 382910740949, 94597274963, 354120310583, 577915960299, 468083447405, 318392924679, 1140596682667, 447478750845, 1290287205393, 2056158880917, 3708804742515, 1213350426369, 6212442374277, 3631452229347, 8707896690423]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [13552699346139, 93078865556733, 8476254885063, 110263017132219, 19378183019, 156080925, 0]) [0, 0, 0, 0, 2, 9, 0] [true, false, true, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [159530795, 12990268409, 16673582919, 91209941, 19718774249, 16536941211, 1831105123, 13719947937, 2318808277, 1842601545, 27043194741, 5556043221, 3663476811, 21090354117, 31393728051, 3335491289, 56351009229, 45391664251, 33346389847, 47774284429, 21352259169, 30822166313, 189736568617, 37394398209, 126223248805, 171062949681, 432846256759, 120941547681, 1199522559057, 927175849731, 6000925117683, 1138595331129]) [2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [896248007847, 5939269941521, 25203223029789, 4777544780495, 16992644509, 156080925, 0]) [4, 1, 0, 3, 0, 7, 0] [true, false, true, false, false, true, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [129086223, 2045513759, 3656236021, 151378983, 1481636039, 3678528781, 209190041, 2348271725, 4039097805, 881247275, 1900016121, 5129535121, 872445809, 4110766275, 6883228205, 3834775559, 3644907739, 11590449573, 3726187665, 11780317393, 19151412797, 26425911267, 11097283069, 49303511729, 26043607681, 64632139927, 101773030677, 570386523703, 63184498431, 698203162061, 568949079865, 1205405187333]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [1837538765629, 13197036757877, 1201082658161, 10790548912383, 946330561, 14189175, 0]) [0, 0, 0, 0, 1, 7, 0] [true, true, true, true, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [48749899, 724158331, 3471013223, 28451509, 986973331, 3450714833, 495398809, 47038115, 3974565151, 500237525, 370593035, 4970201485, 2275941737, 1252847365, 7746380747, 2184984337, 3758313877, 12207306821, 14865577093, 1718915851, 29257868251, 14514281273, 9311945485, 58637726617, 297362700605, 17952112975, 370514708495, 295914514573, 315986591575, 963791923673, 6319180180847, 78466656887]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [5059473742601, 6327478081603, 750399198659, 17706132005051, 1759881561, 14189175, 0]) [0, 0, 4, 0, 0, 7, 0] [false, true, false, true, false, true, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [71527615, 720633787, 1348116339, 77755885, 555954937, 1354344609, 94090359, 876145557, 1526190853, 473484491, 744135655, 2093765703, 470985457, 1823114539, 3038235651, 2889586205, 1686106569, 6398807313, 2858858455, 7602286949, 12147251973, 52143936683, 7403823479, 67150047111, 52036280321, 111890160315, 171330264115, 1003184295507, 111476384121, 779817751071, 1003587719145, 1894478430699]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [2786589765723, 6953424523115, 1895699054169, 3163247038247, 709821977, 4729725, 0]) [0, 0, 0, 0, 0, 7, 0] [false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [1770389, 4585009, 167962177, 1047659, 23207911, 167239447, 33798951, 37727731, 202086057, 34049101, 80214773, 269934109, 207627241, 1121513, 511610451, 204542357, 143921007, 923780049, 3431321233, 276319189, 4559643639, 3419364411, 3719163247, 11410329283, 59472632329, 230980225, 44642938635, 59521397089, 27876734541, 163636968053, 371707043483, 55825713489]) [0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [148548678341, 371431308017, 315953574401, 891687029841, 84866283, 4729725, 0]) [0, 0, 1, 0, 0, 4, 0] [true, false, true, false, false, true, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [46983085, 297339899, 586125233, 49009543, 241802249, 588151691, 1699625, 395358985, 345774617, 91380247, 350578249, 555729111, 364726327, 1126400961, 1841705537, 5467950411, 1080030903, 7674382275, 1364481003, 12062301783, 9300128349, 10503885243, 11995878927, 29986450617, 84066089277, 155999862105, 228070072455, 468483435831, 156136299627, 156347274099, 117088197093, 780967009557]) [0, 0, 0, 0, 0, 0, 5, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [546591749151, 107283778875, 780569277117, 77502087663, 316554159, 14189175, 0]) [1, 4, 0, 1, 0, 4, 0] [true, true, true, true, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [9473961, 138302457, 1221940761, 5664855, 164814243, 1218131655, 411393383, 282269769, 1635189893, 413027267, 741021869, 2459610543, 5821160947, 173824259, 8693798757, 5805500479, 205068213, 20320460183, 78602846481, 6500797515, 52476885819, 78663757725, 72040663665, 209743490025, 384295826355, 36081480105, 95888578605, 384049424715, 156127581345, 864233829675, 1248935285733, 311886464505]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [652031343, 1250314488633, 936680123043, 2499901805709, 615707361, 14189175, 0]) [0, 0, 1, 0, 0, 5, 0] [false, true, false, true, false, true, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [2188394051, 7599648663, 16270083347, 2227957421, 6482040633, 16309646717, 2334178151, 12055563505, 20871782289, 34339919415, 11150396935, 57545879855, 34325007123, 80735402335, 126210806393, 400127771837, 79800411181, 239591958321, 400323265373, 719520141339, 1040042995531, 1681867313907, 720846119565, 241501053003, 1681186443765, 2644214486475, 3604554810675, 4753144282779, 2641526767965, 532596971661, 4755675255909, 6862074079083]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [8976222567027, 10808330348139, 6869823743853, 2923567474797, 9229238699, 156080925, 0]) [0, 0, 0, 0, 0, 5, 0] [false, false, false, true, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [23611665, 1055890873, 4515657217, 14235375, 1190131903, 4506280927, 4563795307, 133765781, 9084311609, 18273794587, 2876963605, 72866222251, 183006772021, 22554299579, 91866755183, 183156336175, 159991063181, 458029863379, 640505717345, 40150509149, 680482209, 319960995823, 120128663541, 639873613391, 768536660073, 239659977525, 191297949141, 769709710611, 528279332991, 1346948421543, 1509771160005, 265024866543]) [2, 3, 2, 2, 3, 2, 2, 6, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [606886972149, 3006516015525, 490745913507, 4812284391237, 2269634441, 156080925, 0]) [1, 0, 3, 0, 2, 5, 0] [false, false, true, false, false, true, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [29443099493, 31920304223, 89921278869, 29559045323, 28557875153, 90037224699, 238989741691, 91038394869, 1195759901867, 2140431527109, 353221242303, 705681883551, 535191185301, 1776277947633, 623359768983, 1487814814603, 1787543498901, 36761988583, 5946690809683, 4174981310779, 10721566433439, 11643148495213, 2079573655391, 5025108747909, 1457378815931, 3734083592217, 285579223043, 2415537170229, 3749941608333, 663237715023, 19265472830019, 5928065088699]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 6, 3, 2, 4, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [27977966751483, 28472539848189, 11765589613353, 18770899733313, 59682189181, 2029052025, 0]) [0, 0, 1, 0, 3, 6, 0] [true, true, true, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015]

#time def graph : KernelGraph 27 15 12 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 13.4856 s provisional ×3 model; 22476 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C008

namespace C009
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩]

#time def roleTape : List (Fin 14 ⊕ Fin 13) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨9, by decide⟩, .inl ⟨12, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inl ⟨13, by decide⟩]

#time def roles : GraphRoles 27 14 13 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549]) [1] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 25248973341690518480929558074228495475777423007206153203055083854432695575378565602963590747098765525]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1] [true, false, true, false, true, false, true, false, true, false, true, false, true]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 2529875405958078746936463413646021603942955091082239225383268399322503534292970155989542080531975]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 5] [true, false, true, false, true, false, true, false, true, false, true, true, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 26657741812981988396979413042842694279571165027654976420829773654134963630922754968133428060995550525]) [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 1] [false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 408893984723613395921686370165302418538836049461773535792844073120428713286906865722802463580511425]) [0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2] [false, false, true, false, true, false, true, false, true, false, true, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 96169232635170189652933375181277295569400806301202511541359517339970916421224681201732715244188275]) [0, 0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2] [false, false, false, true, false, true, false, true, false, true, false, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 13297459119780833010366110887750779529714731573972309656012800603268169327560742788177072601129825]) [0, 0, 0, 1, 2, 2, 2, 2, 2, 2, 2, 0, 4] [false, false, false, false, true, false, true, false, true, false, true, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 3363540253264722708850868197397806901792801322767086882690730566056828629075605902152935982020725]) [0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 2, 0, 4] [false, false, false, false, false, true, false, true, false, true, false, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 6971318644758486505501996536678541460321126044131112201235339836491737669443605366858276335779275]) [0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 0, 2] [false, false, false, false, false, false, true, false, true, false, true, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 1337886472601489572627053155617196726181071661325058916914494672077697671469302973749814162416525]) [0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 0, 2] [false, false, false, false, false, false, false, true, false, true, false, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 1280841936640149443261353353218450622346639551846688682527317744482234418567778514862311841413325]) [0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 1] [false, false, false, false, false, false, false, false, true, false, true, false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 134365871167706937133253303845891919542465377894667024135728980465481142821481770302388249993675]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 1] [false, false, false, false, false, false, false, false, false, true, false, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 7363723529870042291276199632157433136538790509795571761300852158289328304729473293010428224325]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 4] [false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 529369679565838724909339239001181692447339825982000300501071716514504697012598184802588370451234549, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [5285148865, 495463843029, 734555821369, 2908817215, 931366608789, 725050494769, 65093929339, 542004918469, 100222461621, 63341636715, 1191742326145, 465107629511, 124008370143, 795371465329, 1241573636023, 98382424735, 2183809287289, 1686355225779, 926490271145, 1582430863209, 1404805173197, 730107054969, 5889770371869, 1116551918127, 147956543235, 4502859083085, 9930924110997, 121666668603, 24828207905949, 18558866889813, 41670239664375, 20076192664269]) [3, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 6, 0, 1, 6, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [16030609987371, 36617352644775, 191509166563449, 71205016129317, 755696416829, 2029052025, 0]) [3, 1, 0, 2, 0, 9, 0] [true, false, true, false, false, true, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [3157943523, 89187677393, 151867520629, 4401860883, 59521899713, 153111437989, 7607914435, 97991399159, 165121213307, 27656511325, 74737728583, 200385639067, 27230323085, 153304421809, 255272473477, 100407944387, 129198374753, 382910740949, 94597274963, 354120310583, 577915960299, 468083447405, 318392924679, 1140596682667, 447478750845, 1290287205393, 2056158880917, 3708804742515, 1213350426369, 6212442374277, 3631452229347, 8707896690423]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [13552699346139, 93078865556733, 8476254885063, 110263017132219, 19378183019, 156080925, 0]) [0, 0, 0, 0, 2, 9, 0] [true, false, true, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [159530795, 12990268409, 16673582919, 91209941, 19718774249, 16536941211, 1831105123, 13719947937, 2318808277, 1842601545, 27043194741, 5556043221, 3663476811, 21090354117, 31393728051, 3335491289, 56351009229, 45391664251, 33346389847, 47774284429, 21352259169, 30822166313, 189736568617, 37394398209, 126223248805, 171062949681, 432846256759, 120941547681, 1199522559057, 927175849731, 6000925117683, 1138595331129]) [2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [896248007847, 5939269941521, 25203223029789, 4777544780495, 16992644509, 156080925, 0]) [4, 1, 0, 3, 0, 7, 0] [true, false, true, false, false, true, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [129086223, 2045513759, 3656236021, 151378983, 1481636039, 3678528781, 209190041, 2348271725, 4039097805, 881247275, 1900016121, 5129535121, 872445809, 4110766275, 6883228205, 3834775559, 3644907739, 11590449573, 3726187665, 11780317393, 19151412797, 26425911267, 11097283069, 49303511729, 26043607681, 64632139927, 101773030677, 570386523703, 63184498431, 698203162061, 568949079865, 1205405187333]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [1837538765629, 13197036757877, 1201082658161, 10790548912383, 946330561, 14189175, 0]) [0, 0, 0, 0, 1, 7, 0] [true, true, true, true, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [48749899, 724158331, 3471013223, 28451509, 986973331, 3450714833, 495398809, 47038115, 3974565151, 500237525, 370593035, 4970201485, 2275941737, 1252847365, 7746380747, 2184984337, 3758313877, 12207306821, 14865577093, 1718915851, 29257868251, 14514281273, 9311945485, 58637726617, 297362700605, 17952112975, 370514708495, 295914514573, 315986591575, 963791923673, 6319180180847, 78466656887]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [5059473742601, 6327478081603, 750399198659, 17706132005051, 1759881561, 14189175, 0]) [0, 0, 4, 0, 0, 7, 0] [false, true, false, true, false, true, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [71527615, 720633787, 1348116339, 77755885, 555954937, 1354344609, 94090359, 876145557, 1526190853, 473484491, 744135655, 2093765703, 470985457, 1823114539, 3038235651, 2889586205, 1686106569, 6398807313, 2858858455, 7602286949, 12147251973, 52143936683, 7403823479, 67150047111, 52036280321, 111890160315, 171330264115, 1003184295507, 111476384121, 779817751071, 1003587719145, 1894478430699]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [2786589765723, 6953424523115, 1895699054169, 3163247038247, 709821977, 4729725, 0]) [0, 0, 0, 0, 0, 7, 0] [false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [1770389, 4585009, 167962177, 1047659, 23207911, 167239447, 33798951, 37727731, 202086057, 34049101, 80214773, 269934109, 207627241, 1121513, 511610451, 204542357, 143921007, 923780049, 3431321233, 276319189, 4559643639, 3419364411, 3719163247, 11410329283, 59472632329, 230980225, 44642938635, 59521397089, 27876734541, 163636968053, 371707043483, 55825713489]) [0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [148548678341, 371431308017, 315953574401, 891687029841, 84866283, 4729725, 0]) [0, 0, 1, 0, 0, 4, 0] [true, false, true, false, false, true, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [46983085, 297339899, 586125233, 49009543, 241802249, 588151691, 1699625, 395358985, 345774617, 91380247, 350578249, 555729111, 364726327, 1126400961, 1841705537, 5467950411, 1080030903, 7674382275, 1364481003, 12062301783, 9300128349, 10503885243, 11995878927, 29986450617, 84066089277, 155999862105, 228070072455, 468483435831, 156136299627, 156347274099, 117088197093, 780967009557]) [0, 0, 0, 0, 0, 0, 5, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [546591749151, 107283778875, 780569277117, 77502087663, 316554159, 14189175, 0]) [1, 4, 0, 1, 0, 4, 0] [true, true, true, true, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [9473961, 138302457, 1221940761, 5664855, 164814243, 1218131655, 411393383, 282269769, 1635189893, 413027267, 741021869, 2459610543, 5821160947, 173824259, 8693798757, 5805500479, 205068213, 20320460183, 78602846481, 6500797515, 52476885819, 78663757725, 72040663665, 209743490025, 384295826355, 36081480105, 95888578605, 384049424715, 156127581345, 864233829675, 1248935285733, 311886464505]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [652031343, 1250314488633, 936680123043, 2499901805709, 615707361, 14189175, 0]) [0, 0, 1, 0, 0, 5, 0] [false, true, false, true, false, true, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [2188394051, 7599648663, 16270083347, 2227957421, 6482040633, 16309646717, 2334178151, 12055563505, 20871782289, 34339919415, 11150396935, 57545879855, 34325007123, 80735402335, 126210806393, 400127771837, 79800411181, 239591958321, 400323265373, 719520141339, 1040042995531, 1681867313907, 720846119565, 241501053003, 1681186443765, 2644214486475, 3604554810675, 4753144282779, 2641526767965, 532596971661, 4755675255909, 6862074079083]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [8976222567027, 10808330348139, 6869823743853, 2923567474797, 9229238699, 156080925, 0]) [0, 0, 0, 0, 0, 5, 0] [false, false, false, true, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [23611665, 1055890873, 4515657217, 14235375, 1190131903, 4506280927, 4563795307, 133765781, 9084311609, 18273794587, 2876963605, 72866222251, 183006772021, 22554299579, 91866755183, 183156336175, 159991063181, 458029863379, 640505717345, 40150509149, 680482209, 319960995823, 120128663541, 639873613391, 768536660073, 239659977525, 191297949141, 769709710611, 528279332991, 1346948421543, 1509771160005, 265024866543]) [2, 3, 2, 2, 3, 2, 2, 6, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [606886972149, 3006516015525, 490745913507, 4812284391237, 2269634441, 156080925, 0]) [1, 0, 3, 0, 2, 5, 0] [false, false, true, false, false, true, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [29443099493, 31920304223, 89921278869, 29559045323, 28557875153, 90037224699, 238989741691, 91038394869, 1195759901867, 2140431527109, 353221242303, 705681883551, 535191185301, 1776277947633, 623359768983, 1487814814603, 1787543498901, 36761988583, 5946690809683, 4174981310779, 10721566433439, 11643148495213, 2079573655391, 5025108747909, 1457378815931, 3734083592217, 285579223043, 2415537170229, 3749941608333, 663237715023, 19265472830019, 5928065088699]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 6, 3, 2, 4, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [27977966751483, 28472539848189, 11765589613353, 18770899733313, 59682189181, 2029052025, 0]) [0, 0, 1, 0, 3, 6, 0] [true, true, true, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013]

#time def graph : KernelGraph 27 14 13 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 14.1180 s provisional ×3 model; 23530 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C009

namespace C010
#time def pivTape : List (Fin 27) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨26, by decide⟩]

#time def freeTape : List (Fin 27) :=
  [⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩]

#time def roleTape : List (Fin 13 ⊕ Fin 14) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inl ⟨12, by decide⟩]

#time def roles : GraphRoles 27 13 14 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327]) [1] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 159514824901885006751619799712845375304494958134936754604786965942457374266198277900702764403279193405819313, 159516225614057137960885909824471772431253173796116302977582091778219271645626573235499752052107407372435967, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 33404391731056555950269805332204299514453530638533740687641875939414456246225842292720830558411666789575]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1] [true, false, true, false, true, false, true, false, true, false, true, true, false, true]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 273032520346136647766052312522784468999869610416203373041776333993980716315323639793253679832089999426995, 2184960518855158786761473555995474315378064713919401170731773589832794420236736785744523263070826978724287, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 3347025162082538182196941096253686582016529585501802495182064092303672175869599516374164172543802925]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 0, 5] [true, false, true, false, true, false, true, false, true, false, true, true, true, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 116111113446129536003739540086532428067399232355209397232078841809100581826076859570315036663892437674010253, 116113914870473798422271760309785222320915663677568493977669093480624376584933450239909011961548865607243561, 0, 35268192418575170649203763455680884531872651331587533804757790544420556883710804822840525324697113344575]) [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 1] [false, true, false, true, false, true, false, true, false, true, false, false, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 336043210358166092656826620330350105422762943818549576815093784083772830861358135669468690230978403659635, 1343472485346598765994251425508201858311943944684424120862812218454142633731284875279380936509806631330213, 0, 540966741789340522804391067728695099726880093437926387853932708738327187678577783351267659317016615275]) [0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 0, 2] [false, false, true, false, true, false, true, false, true, false, false, false, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 818989434701201416060699403024428262986052572494980153980590914033652381876030489297414592934148067145565, 1637278513316337227488343750235657962592997314400186121563618910186356074037913311196335361454189150982803, 0, 127231894776330160910830855364829862038317266736490922769218641440781522425280253229892382268061087825]) [0, 0, 1, 2, 2, 2, 2, 2, 2, 2, 3, 2, 0, 2] [false, false, false, true, false, true, false, true, false, true, true, true, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 11888926999450805506947530795399010653605000552928945246058057536398359587274872782855168770068014966155, 24478210084967215646950117403996584686317831695632076889679032953745408888697412964204161954243013240637, 0, 17592538415470042072714364704494281317812589872365365674904935198123788020362862708758267051294758475]) [0, 0, 0, 1, 2, 2, 2, 2, 2, 2, 3, 2, 0, 4] [false, false, false, false, true, false, true, false, true, false, true, true, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 10503039105891191460079588034149262446873928901032688921489280206080117821672957659846812355703164675639, 335396895302452522089491761279577834920857894243271859090094048713615080579386977716604170968394286312121, 0, 4449963755069228143809698625157298531071876150020855945799836538893184276267026608548334304213419175]) [0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 7, 2, 0, 4] [false, false, false, false, false, true, false, true, false, true, true, true, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 31700667366535156918144845353914184350760469783699470952880347291339785951345350534855601637643573534659, 33101379538666366184254956980311311108976130963247843748006183053237165379640685331843250465857540151313, 0, 9223054567015477646779141418025710352004849756385461442234354603678568936673889900353499592235980825]) [0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 1, 1, 0, 2] [false, false, false, false, false, false, true, false, true, false, true, true, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 112146240754396636751935028148197546070989687443604506662488659750905432394699086318425781057038534526525, 110745528582265427485824916521800419312774026264056133867362823989008052966403751521438132228824567909871, 0, 1770023803251770704585591324881551268737557807933052947077876451158794019353887834271004136877062575]) [0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 1, 1, 0, 2] [false, false, false, false, false, false, false, true, false, true, true, true, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 9789544144461366393760166520898309715127943440899983615386109363947882038799628121806758821257973899815, 12590968488723784925980389773692563231559265799996729205637780887742640895390297715782056477685907133123, 0, 1694553882174917713434770486308010173364604127093169126983641375949996135765170975162838566189828975]) [0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 1] [false, false, false, false, false, false, false, false, true, false, true, true, false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 25242753605385631167095532293158352863722181502689682161328440552666488111483922042441661356501569206925, 22441329261123212634875309040364099347290859143592936571076769028871729254893252448466363700073635973617, 0, 177766047554876277827294120988115009554681694954644472931569441155831551952820382110059654741632025]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1] [false, false, false, false, false, false, false, false, false, true, true, true, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 700356086065604633055055813198563379107830589774186397562917880948689714147667398493824414106983308327, 318051714294856600985781135302762498728907919255089287494582186201622792695592379324171563417511957613, 1718763886426065867095892761699889256944569098803462082620417948099002220990927176311820391631478574267, 0, 9742206230018065951358412113344284039640819844459541440201027405416781347157093166652796540781975]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 4] [false, false, false, false, false, false, false, false, false, false, true, true, false, false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [5285148865, 495463843029, 734555821369, 2908817215, 931366608789, 725050494769, 65093929339, 542004918469, 100222461621, 63341636715, 1191742326145, 465107629511, 124008370143, 795371465329, 1241573636023, 98382424735, 2183809287289, 1686355225779, 926490271145, 1582430863209, 1404805173197, 730107054969, 5889770371869, 1116551918127, 147956543235, 4502859083085, 9930924110997, 121666668603, 24828207905949, 18558866889813, 41670239664375, 20076192664269]) [3, 0, 1, 3, 0, 1, 1, 0, 4, 1, 0, 2, 2, 0, 1, 2, 0, 1, 1, 0, 2, 1, 0, 3, 6, 0, 1, 6, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [16030609987371, 36617352644775, 191509166563449, 71205016129317, 755696416829, 2029052025, 0]) [3, 1, 0, 2, 0, 9, 0] [true, false, true, false, false, true, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [3157943523, 89187677393, 151867520629, 4401860883, 59521899713, 153111437989, 7607914435, 97991399159, 165121213307, 27656511325, 74737728583, 200385639067, 27230323085, 153304421809, 255272473477, 100407944387, 129198374753, 382910740949, 94597274963, 354120310583, 577915960299, 468083447405, 318392924679, 1140596682667, 447478750845, 1290287205393, 2056158880917, 3708804742515, 1213350426369, 6212442374277, 3631452229347, 8707896690423]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [13552699346139, 93078865556733, 8476254885063, 110263017132219, 19378183019, 156080925, 0]) [0, 0, 0, 0, 2, 9, 0] [true, false, true, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [159530795, 12990268409, 16673582919, 91209941, 19718774249, 16536941211, 1831105123, 13719947937, 2318808277, 1842601545, 27043194741, 5556043221, 3663476811, 21090354117, 31393728051, 3335491289, 56351009229, 45391664251, 33346389847, 47774284429, 21352259169, 30822166313, 189736568617, 37394398209, 126223248805, 171062949681, 432846256759, 120941547681, 1199522559057, 927175849731, 6000925117683, 1138595331129]) [2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [896248007847, 5939269941521, 25203223029789, 4777544780495, 16992644509, 156080925, 0]) [4, 1, 0, 3, 0, 7, 0] [true, false, true, false, false, true, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [129086223, 2045513759, 3656236021, 151378983, 1481636039, 3678528781, 209190041, 2348271725, 4039097805, 881247275, 1900016121, 5129535121, 872445809, 4110766275, 6883228205, 3834775559, 3644907739, 11590449573, 3726187665, 11780317393, 19151412797, 26425911267, 11097283069, 49303511729, 26043607681, 64632139927, 101773030677, 570386523703, 63184498431, 698203162061, 568949079865, 1205405187333]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [1837538765629, 13197036757877, 1201082658161, 10790548912383, 946330561, 14189175, 0]) [0, 0, 0, 0, 1, 7, 0] [true, true, true, true, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [48749899, 724158331, 3471013223, 28451509, 986973331, 3450714833, 495398809, 47038115, 3974565151, 500237525, 370593035, 4970201485, 2275941737, 1252847365, 7746380747, 2184984337, 3758313877, 12207306821, 14865577093, 1718915851, 29257868251, 14514281273, 9311945485, 58637726617, 297362700605, 17952112975, 370514708495, 295914514573, 315986591575, 963791923673, 6319180180847, 78466656887]) [0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [5059473742601, 6327478081603, 750399198659, 17706132005051, 1759881561, 14189175, 0]) [0, 0, 4, 0, 0, 7, 0] [false, true, false, true, false, true, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [71527615, 720633787, 1348116339, 77755885, 555954937, 1354344609, 94090359, 876145557, 1526190853, 473484491, 744135655, 2093765703, 470985457, 1823114539, 3038235651, 2889586205, 1686106569, 6398807313, 2858858455, 7602286949, 12147251973, 52143936683, 7403823479, 67150047111, 52036280321, 111890160315, 171330264115, 1003184295507, 111476384121, 779817751071, 1003587719145, 1894478430699]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [2786589765723, 6953424523115, 1895699054169, 3163247038247, 709821977, 4729725, 0]) [0, 0, 0, 0, 0, 7, 0] [false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [1770389, 4585009, 167962177, 1047659, 23207911, 167239447, 33798951, 37727731, 202086057, 34049101, 80214773, 269934109, 207627241, 1121513, 511610451, 204542357, 143921007, 923780049, 3431321233, 276319189, 4559643639, 3419364411, 3719163247, 11410329283, 59472632329, 230980225, 44642938635, 59521397089, 27876734541, 163636968053, 371707043483, 55825713489]) [0, 4, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [148548678341, 371431308017, 315953574401, 891687029841, 84866283, 4729725, 0]) [0, 0, 1, 0, 0, 4, 0] [true, false, true, false, false, true, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [46983085, 297339899, 586125233, 49009543, 241802249, 588151691, 1699625, 395358985, 345774617, 91380247, 350578249, 555729111, 364726327, 1126400961, 1841705537, 5467950411, 1080030903, 7674382275, 1364481003, 12062301783, 9300128349, 10503885243, 11995878927, 29986450617, 84066089277, 155999862105, 228070072455, 468483435831, 156136299627, 156347274099, 117088197093, 780967009557]) [0, 0, 0, 0, 0, 0, 5, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [546591749151, 107283778875, 780569277117, 77502087663, 316554159, 14189175, 0]) [1, 4, 0, 1, 0, 4, 0] [true, true, true, true, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [9473961, 138302457, 1221940761, 5664855, 164814243, 1218131655, 411393383, 282269769, 1635189893, 413027267, 741021869, 2459610543, 5821160947, 173824259, 8693798757, 5805500479, 205068213, 20320460183, 78602846481, 6500797515, 52476885819, 78663757725, 72040663665, 209743490025, 384295826355, 36081480105, 95888578605, 384049424715, 156127581345, 864233829675, 1248935285733, 311886464505]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [652031343, 1250314488633, 936680123043, 2499901805709, 615707361, 14189175, 0]) [0, 0, 1, 0, 0, 5, 0] [false, true, false, true, false, true, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [2188394051, 7599648663, 16270083347, 2227957421, 6482040633, 16309646717, 2334178151, 12055563505, 20871782289, 34339919415, 11150396935, 57545879855, 34325007123, 80735402335, 126210806393, 400127771837, 79800411181, 239591958321, 400323265373, 719520141339, 1040042995531, 1681867313907, 720846119565, 241501053003, 1681186443765, 2644214486475, 3604554810675, 4753144282779, 2641526767965, 532596971661, 4755675255909, 6862074079083]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [8976222567027, 10808330348139, 6869823743853, 2923567474797, 9229238699, 156080925, 0]) [0, 0, 0, 0, 0, 5, 0] [false, false, false, true, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [23611665, 1055890873, 4515657217, 14235375, 1190131903, 4506280927, 4563795307, 133765781, 9084311609, 18273794587, 2876963605, 72866222251, 183006772021, 22554299579, 91866755183, 183156336175, 159991063181, 458029863379, 640505717345, 40150509149, 680482209, 319960995823, 120128663541, 639873613391, 768536660073, 239659977525, 191297949141, 769709710611, 528279332991, 1346948421543, 1509771160005, 265024866543]) [2, 3, 2, 2, 3, 2, 2, 6, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 3] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [606886972149, 3006516015525, 490745913507, 4812284391237, 2269634441, 156080925, 0]) [1, 0, 3, 0, 2, 5, 0] [false, false, true, false, false, true, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [29443099493, 31920304223, 89921278869, 29559045323, 28557875153, 90037224699, 238989741691, 91038394869, 1195759901867, 2140431527109, 353221242303, 705681883551, 535191185301, 1776277947633, 623359768983, 1487814814603, 1787543498901, 36761988583, 5946690809683, 4174981310779, 10721566433439, 11643148495213, 2079573655391, 5025108747909, 1457378815931, 3734083592217, 285579223043, 2415537170229, 3749941608333, 663237715023, 19265472830019, 5928065088699]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 6, 3, 2, 4, 0, 2] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [27977966751483, 28472539848189, 11765589613353, 18770899733313, 59682189181, 2029052025, 0]) [0, 0, 1, 0, 3, 6, 0] [true, true, true, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012]

#time def graph : KernelGraph 27 13 14 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 15.0546 s provisional ×3 model; 25091 exact original rank units.
#time theorem checked : chart.check 39 27 basis.matrix = true := by decide +kernel
end C010

#time def delta : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj000 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj001 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj002 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj003 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj004 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj005 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj006 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj007 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj008 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj009 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj010 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj011 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj012 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj013 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj014 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj015 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj016 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj017 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj018 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj019 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj020 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj021 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj022 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj023 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj024 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj025 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
#time def adj026 : Int := signedLit (wordMag (raw_ints% [2029052025])) 10 false
def pivots : List (Fin 39) := [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩]
def adjTape : List Int := [adj000, adj001, adj002, adj003, adj004, adj005, adj006, adj007, adj008, adj009, adj010, adj011, adj012, adj013, adj014, adj015, adj016, adj017, adj018, adj019, adj020, adj021, adj022, adj023, adj024, adj025, adj026]
def head : DiagHead 27 39 := ⟨fun i => pivots.getD i.val ⟨0, by decide⟩,
  fun i => adjTape.getD i.val 0, delta⟩
def input : PackedPacketInput := ⟨39, 27, basis, head, []⟩
#time def packet : Packet := { input.packet with charts := [C000.chart, C001.chart, C002.chart, C003.chart, C004.chart, C005.chart, C006.chart, C007.chart, C008.chart, C009.chart, C010.chart] }
-- kcost: 11.8098 s provisional ×3 model; 19683 original head product units.
#time theorem headChecked : packet.checkHead = true := by decide +kernel
#time theorem checked : packet.check = true := by
  apply Packet.check_of_parts headChecked
  intro c hc
  change c ∈ [C000.chart, C001.chart, C002.chart, C003.chart, C004.chart, C005.chart, C006.chart, C007.chart, C008.chart, C009.chart, C010.chart] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact C000.checked
  · exact C001.checked
  · exact C002.checked
  · exact C003.checked
  · exact C004.checked
  · exact C005.checked
  · exact C006.checked
  · exact C007.checked
  · exact C008.checked
  · exact C009.checked
  · exact C010.checked
#time theorem sound : packet.Sound := Packet.check_sound checked
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P029
