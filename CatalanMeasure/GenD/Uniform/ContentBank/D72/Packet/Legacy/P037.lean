module
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCert
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P037
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

#time def basisScales : List Int :=
  decoded (raw_ints% [1, 36940413802179130710908583402876220098614293166813367487160505, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def ambientRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows001 : List Int :=
  decoded (raw_ints% [106773573434310750255820213158852658788818245381178481007041375, 13907430031201355777423265372975715313711943000054559112716875, 1778657321994499617621951575064247641121597349521786199156025, 2771823036028706079791423125427033937238346471561903923124775, 298615654213272292949476047204044333510509637721534635775705, 139852786303723730128026524741917949383638997867672301351655, 1303603385650035560759992849375669408620495468180515090475, 30105504332037347893948751269713585590478031688746190988225, 5248252966588562756437191194536194731579323261941937169625, 490007633387696136148699820635022739399116977923417862208863]) [0, 2, 2, 1, 1, 2, 2, 0, 0, 7] [false, false, false, false, false, false, true, false, true, true]

#time def ambientRows002 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows003 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows004 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows012 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows013 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows014 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows015 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows016 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows017 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows018 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows019 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows020 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows021 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows022 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false]

#time def ambientRows : List (List Int) :=
  [ambientRows000, ambientRows001, ambientRows002, ambientRows003, ambientRows004, ambientRows005, ambientRows006, ambientRows007, ambientRows008, ambientRows009, ambientRows010, ambientRows011, ambientRows012, ambientRows013, ambientRows014, ambientRows015, ambientRows016, ambientRows017, ambientRows018, ambientRows019, ambientRows020, ambientRows021, ambientRows022]

#time def ambientIndex : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 4, 0, 0, 5, 0, 0, 6, 0, 0, 7, 0, 0, 8, 0, 0, 9, 0]

#time def colTags : List (Option (Fin 23)) :=
  [some ⟨0, by decide⟩, some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, none, some ⟨4, by decide⟩, some ⟨5, by decide⟩, none, some ⟨6, by decide⟩, some ⟨7, by decide⟩, none, some ⟨8, by decide⟩, some ⟨9, by decide⟩, none, some ⟨10, by decide⟩, some ⟨11, by decide⟩, none, some ⟨12, by decide⟩, some ⟨13, by decide⟩, none, some ⟨14, by decide⟩, some ⟨15, by decide⟩, none, some ⟨16, by decide⟩, some ⟨17, by decide⟩, none, some ⟨18, by decide⟩, some ⟨19, by decide⟩, none, some ⟨20, by decide⟩, some ⟨21, by decide⟩, none, some ⟨22, by decide⟩]

#time def basis : DiagView 23 33 :=
  ⟨fun x => colTags.getD x.val none, fun a => basisScales.getD a.val 0,
    fun a x => Mx ambientRows a.val (ambientIndex.getD x.val 0)⟩

namespace C000
#time def pivTape : List (Fin 23) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨21, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩]

#time def roleTape : List (Fin 11 ⊕ Fin 12) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨11, by decide⟩]

#time def roles : GraphRoles 23 11 12 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [5248252966588562756437191194536194731579323261941937169625]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36940413802179130710908583402876220098614293166813367487160505, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106773573434310750255820213158852658788818245381178481007041375, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13907430031201355777423265372975715313711943000054559112716875, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1778657321994499617621951575064247641121597349521786199156025, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2771823036028706079791423125427033937238346471561903923124775, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 298615654213272292949476047204044333510509637721534635775705, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 139852786303723730128026524741917949383638997867672301351655, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1303603385650035560759992849375669408620495468180515090475, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0] [false, false, false, false, false, false, false, false, false, false, true, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30105504332037347893948751269713585590478031688746190988225, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010]

#time def graph : KernelGraph 23 11 12 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 9.3330 s provisional ×3 model; 15555 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C000

namespace C001
#time def pivTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

#time def roleTape : List (Fin 11 ⊕ Fin 12) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩]

#time def roles : GraphRoles 23 11 12 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725]) [9] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 1448518868940476153573539931944144708998419688997594211646483971840227702903386533404264135396175367562415247073527728902045728816793395, 1448528373940633400327906348450651729616601216646396435652137755849143866184916643974136341741153655264396176083618982463373343688500995, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 22293360186681855026474338467690379618140558505157209605798379905130707024315737174448819402737185328856943107950856281692910473125]) [9, 9, 9, 9, 9, 9, 9, 9, 5, 5, 8, 4] [true, false, true, false, true, false, true, false, true, true, false, true]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 358668523801146064962043995392445188628429733076815841587772485305722614673, 358668523801146064962043995392445188628429733076815841587772485305722614673, 0, 6386982903310976309370269396521753017417114047032596429701633047266375]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0] [false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 272053226787308063499773173167123903807318105940629570762174541820355972434927411544697067632467268669753375746670969610825055847643595, 272043721787150816745406756660616883189136578291827346756520757811439809153397300974824861287488980967772446736579716049497440975935995, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 4953066799747747795953938592926619098946566430529849947766883725107205623708830851344906748949648283376894353151014227538930448125]) [9, 9, 9, 9, 9, 9, 9, 9, 5, 5, 8, 4] [true, false, true, false, true, false, true, false, false, false, true, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 15338891039015612331046134147163605476038757640442740826339495442125630908382060725961841738383763715196027945948835861251880678586875835, 15339043119018128279115996811267717805929662082823576410429955986268289520886542495079797039903416318427722810110295918233122516534197435, 0, 253050877013855318880989412446246556676219152780625369823241991982287312342491271994146818030374081899241372591749579245502463098125]) [9, 10, 10, 10, 10, 10, 10, 10, 2, 2, 0, 1] [false, true, false, true, false, true, false, true, false, false, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 8739745697959853343047412158007966383173405996706563863847740480475038726750913348085999150895492279882626096353200757418048890449368595, 8739897777962369291117274822112078713064310439087399447938201024617697339255395117203954452415144883114320960514660814399290728396690195, 0, 156530168610764213290833256600205413884625377989135534194444895767986839054398834935633830242798035238711094571084836630199960523125]) [0, 9, 10, 10, 10, 10, 10, 10, 2, 2, 0, 1] [false, false, true, false, true, false, true, false, true, true, false, true]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 78692025036671090127322973824249795961597229873631010209102402440917167883880193068300845018093152772496281280356565382558975850751105, 78539945034155142057460309720137466070692787492795426118641858298258555379398423950345543498440549540801417118896508401317137903429505, 0, 346891968577462209500533479355459529368092729355789208375932558905230428596817853498340105251159135204329002117266653606401564375]) [0, 0, 9, 10, 10, 10, 10, 10, 2, 2, 0, 1] [false, false, false, true, false, true, false, true, true, true, false, true]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 1003703837838072967872459005441885228452748209636141049982260131624501137404651782311420669775639848916880273677176786584937390253234695, 1003855917840588915942321669545997558343652652016976634072720675767159749909133551429375971295292452148575137838636843566179228200556295, 0, 17862052315259451572467750863908480937942507615177114966392323894815262800152410631100442305838846681850777057514564302682081110625]) [0, 0, 0, 9, 10, 10, 10, 10, 2, 2, 0, 1] [false, false, false, false, true, false, true, false, true, true, false, true]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 26914425242890528363639325390126190428961531768448977692003662023744114373493913739212179287486403102896937796678154976074769139807255, 26762345240374580293776661286013860538057089387613393601543117881085501869012144621256877767833799871202073635218097994832931192485655, 0, 299568347402981184547231076821439997327331315609054208638051661070080743213504207265658002506504836501989949786166711023696860625]) [0, 0, 0, 0, 9, 10, 10, 10, 2, 2, 0, 1] [false, false, false, false, false, true, false, true, true, true, false, true]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 119489285494988630894380799780788612842140894962701394978766529054859488142694190926554357475269884173766860427520293702612866503930065, 119641365497504578964243463884900942733045337343536979069227073197518100647175960044509658994922487405461724588980350683854704451251665, 0, 2121657053984422481976550318594669713328706378847473908455353136015670933518812894940452599383814515478536275670574994705016954375]) [0, 0, 0, 0, 0, 9, 10, 10, 2, 2, 0, 1] [false, false, false, false, false, false, true, false, true, true, false, true]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 2910191425913730973103709991589150396815114301057103979181478096996688292768734079505692058955035134923851826272566968925526044009475, 2758111423397782903241045887476820505910671920221519888720933954338075788286964961550390539302431903228987664812509987683688096687875, 0, 29825246085974413738855697586864180645268691078294209848029400721853463619222666956062467325546900939480446288727913101622853125]) [0, 0, 0, 0, 0, 0, 9, 10, 2, 2, 0, 1] [false, false, false, false, false, false, false, true, true, true, false, true]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 594062509827922147901031656688788636345478050139000353361500557260205095631910617012896561142981373808063130703347582975929481725, 7674187403420595122410483805658838476444623622259788083065117370854707075649959104465813200350931719408445918061969838303595776128325, 7826267405936543192273147909771168367349066003095372173525661513513319580131728222421114720003534951103310079522026819545433723449925, 0, 136134998557272042084120691371722480445863310929368634389229886716935892354511304328944528967321895513758246255540662917106021875]) [0, 0, 0, 0, 0, 0, 0, 9, 2, 2, 0, 1] [false, false, false, false, false, false, false, false, true, true, false, true]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [31144655, 1236513293, 1739558163, 18711857, 2118024413, 1714692567, 166311151, 1386208149, 239803429, 189633765, 2783269017, 568593087, 346442907, 2144743209, 3156891927, 321002153, 5554812273, 4491782047, 3053143099, 4712760433, 2046732363, 2826034301, 17767384669, 3516526713, 10929629785, 16016897637, 38751400723, 10520142357, 105204422949, 81650945007, 1801847473, 12006225]) [2, 0, 1, 2, 0, 1, 1, 0, 4, 1, 0, 3, 2, 0, 1, 2, 0, 1, 1, 0, 3, 1, 0, 3, 2, 0, 1, 2, 0, 1, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [5077443, 143531603, 224945857, 8662731, 76336811, 228531145, 13018589, 160857065, 250212465, 62018615, 102373989, 325249669, 51172061, 284894295, 438440345, 279828683, 204718111, 769441089, 226509237, 844551661, 1275779009, 1980283599, 657736585, 3482571845, 1704022285, 4805118859, 7166877729, 43600754971, 4065781155, 52471654985, 57505825, 1091475]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [7526083, 60820927, 309947471, 4499773, 90389767, 306921161, 40422673, 16330175, 351843607, 42822125, 16351555, 435088405, 187211249, 108142825, 665121779, 179320249, 318023689, 1031653277, 1189234141, 143731537, 2400207667, 1154919281, 753628915, 4744361089, 23100948005, 1442382355, 29000228375, 22961271733, 24608205835, 75062448113, 158736777, 1091475]) [0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [4469275, 52711639, 92081823, 5350465, 34900909, 92963013, 6616483, 63412569, 104929961, 35257287, 48133875, 146803731, 32951829, 133927143, 215012847, 219287665, 114037533, 467252341, 207578755, 572502473, 894118761, 4000950311, 529195043, 5102647827, 3941757989, 8574403095, 13045356127, 77219767167, 8412711021, 60232653051, 48275549, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [491571, 5926963, 28290283, 294861, 7972393, 28093573, 5330069, 1519, 33718503, 5482379, 6651231, 44530951, 32632499, 11704203, 82645829, 32090303, 45934961, 147368631, 530488647, 21897253, 709947581, 528149769, 72052951, 1768585997, 9136830671, 571944275, 6840094905, 9146522231, 8560407063, 25123447807, 14390927, 363825]) [0, 1, 0, 0, 1, 0, 0, 13, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [316975, 2108601, 3990967, 342457, 1565391, 4016449, 191205, 2793515, 1185329, 1323881, 2330211, 242859, 2586813, 8089039, 13006063, 39981989, 7503837, 55574865, 19832449, 88053017, 16902719, 307933803, 86833633, 110245239, 617445823, 1143682195, 1674294385, 3430827049, 1148058013, 1139086841, 2153971, 51975]) [0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 5, 0, 0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [823067, 7306631, 66406203, 495845, 9089153, 66078981, 21294533, 15109107, 87869359, 21550761, 39472839, 130714653, 299571657, 9164967, 451837071, 298653377, 21190281, 1050062105, 4026972319, 335313245, 2678256837, 4030919795, 3687927823, 10736148951, 19726889581, 1847803275, 4959820835, 19710473565, 8019480879, 44397183981, 33614635, 363825]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [4949919, 17332727, 36250543, 5101329, 13967897, 36401953, 5352839, 27535385, 46856121, 79881335, 24673575, 132090295, 79542047, 187298055, 291513677, 933115153, 183757669, 562059429, 934915917, 1678932251, 2430090499, 3919052643, 1686074165, 554046227, 3910187545, 6159173035, 8383286415, 11086496759, 6134300925, 1206977201, 20600231, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [33495, 15026437, 4089433, 20265, 17421067, 4076203, 15987187, 15350677, 32373059, 128236229, 81369815, 515118197, 1278493427, 158937583, 635139001, 1279687505, 1115753797, 3193319933, 4483837735, 560374961, 10830297, 2239355951, 1684041969, 4486689967, 5362648557, 839490495, 1363397361, 5373304443, 919651647, 9372555639, 257683, 1091475]) [5, 2, 5, 5, 2, 5, 3, 2, 3, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 2, 1, 1, 3, 1, 1, 4, 1, 8, 5] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [31488119, 33869519, 94662807, 31686569, 29305169, 94861257, 128122409, 97242657, 634313713, 1152204951, 186732747, 389768829, 72118401, 957719637, 673967049, 199954523, 967161669, 162622561, 3190147697, 2241552731, 5738929821, 6269907407, 555746507, 2659170111, 1578615323, 1007088669, 2481299647, 2590342437, 63929301, 1469572533, 63075463, 1091475]) [2, 2, 2, 2, 2, 2, 0, 2, 0, 0, 1, 0, 4, 1, 2, 4, 1, 2, 0, 1, 0, 0, 3, 0, 2, 3, 2, 2, 7, 2, 2, 6] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [7541879007, 341905759, 3783304481, 25456863, 365918209, 11350640351, 11264799425, 2760702935, 111297789, 11251311677, 8337453753, 22404813313, 22566604387, 4245304371, 11089520603, 22520224891, 7114575317, 33997308675, 33599451429, 14029616149, 22918082137, 33798488985, 19370300795, 44479858277, 45937371911, 4942218209, 32340975351, 45111030839, 6641767779, 58707427399, 1879287263, 12006225]) [0, 4, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 7] [false, true, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [12006225]) [7] [false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010]

#time def graph : KernelGraph 23 11 12 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 9.3330 s provisional ×3 model; 15555 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C001

namespace C002
#time def pivTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

#time def roleTape : List (Fin 10 ⊕ Fin 13) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩]

#time def roles : GraphRoles 23 10 13 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375]) [13] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 651641514927708006338315750799186323750441240356811724310580478261034243140501607751337506506804880433685820104619314335825, 1302434838828598670191942017308795473410465745887836380869099159991939032412786744281440118545397202588495365822155702050275, 145331975561741545495852052651944244763432265878808998556504213991344480029775355744572826323996916950727269553133516050615925, 312097919157518485199440757862003004501758552381302427643880861448240961226177913170756194743773362611902757939142753216819125, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 22009644113928837846369466256734841285243980839823702511365154304270969835406446899604477051898978038374194291549310271875]) [13, 13, 13, 13, 13, 13, 13, 14, 13, 7, 7, 12, 6] [true, false, true, false, true, false, true, true, true, false, false, false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 620267236276814091559334828796492164958085982730956744278192579, 620267236276814091559334828796492164958085982730956744278192579, 180896391661490198692858756750203675387296469934738395772803816757, 22107979174625791253669040578301681158026458355613469237586516533, 0, 3767324212004965875044030156242574794283203306215210082207875]) [0, 0, 0, 0, 0, 0, 0, 8, 8, 1, 1, 0, 0] [false, false, false, false, false, false, false, true, true, true, true, false, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 30795149296780461134302590854417029686355434717600328761509489692150680237699524871358270860114521767520429158563860342325, 247209385401061031559110211124913411581260212566589697844137714067334895769812670192101061349128732419039707655593809359975, 2345982514418309658195733765085649126085621846504878631020772874573178303516127242379840707794980014651300407705401154153625, 4320264833519528540729857516926647722374036607734447942765627400991339654201762719031709620715159640888112971401819922547925, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 3724022951435169171526003973637178634882620576378691256874433346644202594073887066518192925200001737857526734663190625]) [13, 13, 13, 13, 13, 13, 13, 16, 13, 11, 11, 12, 10] [true, false, true, false, true, false, true, false, false, true, true, true, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 1760702269951177776776940683270307422539146525993882436606253666742833596781590189238248670592395702662786459946472781017075, 1759005887897543091807561714691153074358313056342308301102130073682574689045157246795778881655970586105033911172306927774325, 422219406470120758987869528264795792768901504661954493179458350345432610261415286858856593447151331395337454024754332495492225, 647480728572438894577277681734329264570338917931470700392794909732658740554327122765034356791046773876477957776356233858141825, 0, 21090135594852210902610212691582844281510364450349650856192149705216980628892231400508018712212952862277318199315779884375]) [13, 14, 14, 14, 14, 14, 14, 13, 13, 7, 7, 0, 6] [false, true, false, true, false, true, false, false, false, true, true, false, true]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 976254202051525802836467588509825805364340318223447408315104181055538632981513915918252695571634669870714484124183068497325, 974557819997891117867088619930671457183506848571873272810980587995279725245080973475782906635209553312961935350017215254575, 33238851525954285183865052695696703764000229548647151058506273172940898014606915826333625455669839593630149746142190181518625, 95664836231535626646378851365792616165531338886097412854540985782567085477857952286942764726288854735507795169316599261579425, 0, 56761680685107486627587733580458109131202605796945994413880172218575850153521816446802155779186969719272666100092684375]) [0, 13, 14, 14, 14, 14, 14, 13, 13, 8, 8, 0, 7] [false, false, true, false, true, false, true, true, true, false, false, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 3042565294753773755080103626418209603215817304822458058560210993614825952904815141666171857392213412566752236063250866075, 4738947348388458724459072205572557784049286956396593562683804053873733689337757584135960793817329970319301010229104108825, 9131331413186718628923383211314801063116313520384950478626619856723692023615962669255143213550261599118677691252053952105275, 9006827210896442909250756398002948784920071852205445652686715615963875069340081505642309091130908904992500839311376272506875, 0, 25243338243995264814862277220528114053011549521878622216031266356047435058626378238678310872290450659229238293079371875]) [0, 0, 13, 14, 14, 14, 14, 13, 13, 9, 9, 0, 8] [false, false, false, true, false, true, false, true, true, true, true, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 111425009968342737948663758155183774295597584319797455128668505551904915043801374903152885032705834729134832909554020176375, 109728627914708052979284789576029426114764114668223319624544912491646007307368432460683096096280718171382284135388166933625, 3167864514609583348957051529536903835842916702923668300143690874141689958027422949542277445280667451774803563327449775245425, 17321697339124833968345758584334548662106065438156997884349349628928948988502290620827780237535806837407899054203749750285425, 0, 15495908793075191030101997986235224157887614585489792503054145057374365247974753256156471890559563646262241424397534375]) [0, 0, 0, 13, 14, 14, 14, 13, 13, 7, 7, 0, 6] [false, false, false, false, true, false, true, true, true, false, false, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 1965754427184164521889115359030103676168224204748476161930411002211991129126255226283015973994069619112838985929797317475, 3662136480818849491268083938184451857001693856322611666054004062470898865559197668752804910419186176865387760095650560225, 6516996100203157226400337388370768612944374034715469978608233577840587352019633171021470070401559614780399640855977456885825, 6156811082090964329558276633349037058821499278806920357617231013700882392359764185739177533799111243837793129110348792713025, 0, 11376573760624698960827371742263364800561904152454092664373580745975975053517439711035507737340969515024727922790115625]) [0, 0, 0, 0, 13, 14, 14, 13, 13, 7, 7, 0, 6] [false, false, false, false, false, true, false, true, true, true, true, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 13227966229514341677721947110198422374244012466733670300645707905874568160768283833445213370644716174284597279746746485275, 11531584175879656708342978531044074193410542815159534796522114845615660424335341390975424434219599616532048505580893242525, 34540147507907110824374731345933709402972883427928965672107499769882303648690935660252320573807983228107905953410893222375, 430692953994211085001413541605813654485445767938220247226792663793725961010348939250982525451637035881174238518653128867175, 0, 256431010439050054973359414679925508667889284086165119189893022709840679207995967652491430003567159327419091418640625]) [0, 0, 0, 0, 0, 13, 14, 13, 13, 9, 9, 0, 8] [false, false, false, false, false, false, true, true, true, false, false, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 848191026817342484689484289577174090416734825787067752061796530129453868216471221234894468212558278876274387082926621375, 191723650349164643025938125774173251434551281065467111166291273829575104741008523705455473797331981466701477893216258525, 1888105703983849612404906704928521432268020932639602615289884334088482841173950966175244410222448539219250252059069501275, 419600216659958596514265871996817298352449171124937093046212210674914617890999489763982815936480993270868924592817914079175, 353045677321302140340478837414331068473966860286374861799614591221536763621720786087800419647848016608918469234344769765575, 0, 337840188387091806422447438097190774860894346922729298330203231761464006435200043863373813790129360296107795282709375]) [0, 0, 0, 0, 0, 0, 13, 13, 13, 8, 8, 0, 7] [false, false, false, false, false, false, false, true, true, true, true, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [5077443, 143531603, 224945857, 8662731, 76336811, 228531145, 13018589, 160857065, 250212465, 62018615, 102373989, 325249669, 51172061, 284894295, 438440345, 279828683, 204718111, 769441089, 226509237, 844551661, 1275779009, 1980283599, 657736585, 3482571845, 1704022285, 4805118859, 7166877729, 43600754971, 4065781155, 52471654985, 57505825, 1091475]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [7526083, 60820927, 309947471, 4499773, 90389767, 306921161, 40422673, 16330175, 351843607, 42822125, 16351555, 435088405, 187211249, 108142825, 665121779, 179320249, 318023689, 1031653277, 1189234141, 143731537, 2400207667, 1154919281, 753628915, 4744361089, 23100948005, 1442382355, 29000228375, 22961271733, 24608205835, 75062448113, 158736777, 1091475]) [0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [4469275, 52711639, 92081823, 5350465, 34900909, 92963013, 6616483, 63412569, 104929961, 35257287, 48133875, 146803731, 32951829, 133927143, 215012847, 219287665, 114037533, 467252341, 207578755, 572502473, 894118761, 4000950311, 529195043, 5102647827, 3941757989, 8574403095, 13045356127, 77219767167, 8412711021, 60232653051, 48275549, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [491571, 5926963, 28290283, 294861, 7972393, 28093573, 5330069, 1519, 33718503, 5482379, 6651231, 44530951, 32632499, 11704203, 82645829, 32090303, 45934961, 147368631, 530488647, 21897253, 709947581, 528149769, 72052951, 1768585997, 9136830671, 571944275, 6840094905, 9146522231, 8560407063, 25123447807, 14390927, 363825]) [0, 1, 0, 0, 1, 0, 0, 13, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [316975, 2108601, 3990967, 342457, 1565391, 4016449, 191205, 2793515, 1185329, 1323881, 2330211, 242859, 2586813, 8089039, 13006063, 39981989, 7503837, 55574865, 19832449, 88053017, 16902719, 307933803, 86833633, 110245239, 617445823, 1143682195, 1674294385, 3430827049, 1148058013, 1139086841, 2153971, 51975]) [0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 5, 0, 0, 0, 0, 0, 0, 1, 0, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [823067, 7306631, 66406203, 495845, 9089153, 66078981, 21294533, 15109107, 87869359, 21550761, 39472839, 130714653, 299571657, 9164967, 451837071, 298653377, 21190281, 1050062105, 4026972319, 335313245, 2678256837, 4030919795, 3687927823, 10736148951, 19726889581, 1847803275, 4959820835, 19710473565, 8019480879, 44397183981, 33614635, 363825]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [4949919, 17332727, 36250543, 5101329, 13967897, 36401953, 5352839, 27535385, 46856121, 79881335, 24673575, 132090295, 79542047, 187298055, 291513677, 933115153, 183757669, 562059429, 934915917, 1678932251, 2430090499, 3919052643, 1686074165, 554046227, 3910187545, 6159173035, 8383286415, 11086496759, 6134300925, 1206977201, 20600231, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [33495, 15026437, 4089433, 20265, 17421067, 4076203, 15987187, 15350677, 32373059, 128236229, 81369815, 515118197, 1278493427, 158937583, 635139001, 1279687505, 1115753797, 3193319933, 4483837735, 560374961, 10830297, 2239355951, 1684041969, 4486689967, 5362648557, 839490495, 1363397361, 5373304443, 919651647, 9372555639, 257683, 1091475]) [5, 2, 5, 5, 2, 5, 3, 2, 3, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1, 2, 1, 1, 3, 1, 1, 4, 1, 8, 5] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [31488119, 33869519, 94662807, 31686569, 29305169, 94861257, 128122409, 97242657, 634313713, 1152204951, 186732747, 389768829, 72118401, 957719637, 673967049, 199954523, 967161669, 162622561, 3190147697, 2241552731, 5738929821, 6269907407, 555746507, 2659170111, 1578615323, 1007088669, 2481299647, 2590342437, 63929301, 1469572533, 63075463, 1091475]) [2, 2, 2, 2, 2, 2, 0, 2, 0, 0, 1, 0, 4, 1, 2, 4, 1, 2, 0, 1, 0, 0, 3, 0, 2, 3, 2, 2, 7, 2, 2, 6] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [7541879007, 341905759, 3783304481, 25456863, 365918209, 11350640351, 11264799425, 2760702935, 111297789, 11251311677, 8337453753, 22404813313, 22566604387, 4245304371, 11089520603, 22520224891, 7114575317, 33997308675, 33599451429, 14029616149, 22918082137, 33798488985, 19370300795, 44479858277, 45937371911, 4942218209, 32340975351, 45111030839, 6641767779, 58707427399, 1879287263, 12006225]) [0, 4, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 7] [false, true, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [12006225]) [7] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009]

#time def graph : KernelGraph 23 10 13 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 10.0104 s provisional ×3 model; 16684 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C002

namespace C003
#time def pivTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨2, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨22, by decide⟩]

#time def roleTape : List (Fin 12 ⊕ Fin 11) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨9, by decide⟩, .inl ⟨11, by decide⟩, .inr ⟨10, by decide⟩]

#time def roles : GraphRoles 23 12 11 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021]

#time def graph : KernelGraph 23 12 11 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 11.0352 s provisional ×3 model; 18392 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C003

namespace C004
#time def pivTape : List (Fin 23) :=
  [⟨1, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 22) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩]

#time def roles : GraphRoles 23 1 22 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010]

#time def graph : KernelGraph 23 1 22 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 21.4170 s provisional ×3 model; 35695 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C004

namespace C005
#time def pivTape : List (Fin 23) :=
  [⟨1, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 22) :=
  [.inr ⟨0, by decide⟩, .inl ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩]

#time def roles : GraphRoles 23 1 22 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009]

#time def graph : KernelGraph 23 1 22 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 20.9616 s provisional ×3 model; 34936 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C005

namespace C006
#time def pivTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨1, by decide⟩]

#time def roleTape : List (Fin 22 ⊕ Fin 1) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩]

#time def roles : GraphRoles 23 22 1 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows012 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows013 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows014 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows015 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows016 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows017 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows018 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows019 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows020 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows021 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [4283643, 203873003, 327371257, 9456531, 119214611, 332544145, 20641589, 222786065, 362642265, 78108815, 160497789, 461392669, 75603461, 379003695, 615104945, 340548083, 311704711, 1031256489, 315276237, 1060099861, 1687080809, 2264763879, 942257185, 4267120925, 2169665365, 5589627619, 8701550169, 45842090851, 5281587915, 56713306385, 82913725, 1091475]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [8055283, 40707127, 241663871, 3970573, 76097167, 237579161, 35340673, 11169425, 276890407, 32095325, 6964865, 344326405, 170923649, 76773025, 547345379, 138840649, 282361489, 857109677, 1130056141, 107806837, 2126006467, 965265761, 706208815, 4221328369, 22790519285, 1180879435, 27977113415, 21467047813, 24202936915, 72234680513, 124859577, 1091475]) [0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [4336975, 62768539, 109152723, 5482765, 42047209, 110298513, 7886983, 73734069, 123668261, 37938987, 57821175, 169494231, 37023729, 149612043, 244456947, 229407565, 131868633, 510888241, 222373255, 608427173, 962669061, 4048363691, 576615143, 5233406007, 4019365169, 8705154555, 13301134867, 76846211187, 8615345481, 59525711151, 56744849, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [518031, 4921273, 24876103, 268401, 7257763, 24626473, 5075969, 2594837, 29970843, 4946039, 3083433, 39992851, 31818119, 10135713, 76757009, 30066323, 44151851, 138641451, 527529747, 10050509, 696237521, 518667093, 285840799, 1742434361, 9152352107, 558869129, 6891250653, 9221233427, 8580670509, 25264836187, 12697067, 363825]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [313825, 2348051, 4397417, 345607, 1735541, 4429199, 103165, 3039265, 2593733, 677903, 2560861, 4155869, 2683763, 8462489, 13707113, 40222939, 7928387, 56613815, 10004287, 88908367, 68426951, 153684679, 87962683, 218933833, 615598033, 1140569065, 1668204415, 3439721239, 1143233383, 1155918791, 2355621, 51975]) [0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [122981, 941183, 8789829, 65435, 1225529, 8732283, 2990219, 1947801, 11787937, 2969223, 5441277, 17747379, 42629751, 153657, 63346353, 42251711, 12017757, 148227815, 575885617, 47168735, 385406091, 577780925, 527814589, 1539072633, 2814959443, 265306095, 698105885, 2800534755, 1143572427, 6313600083, 4456405, 51975]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [9866763, 37179679, 76768811, 10235733, 29722369, 77137781, 11023303, 57651145, 98396817, 160433095, 51768975, 269853215, 160102069, 378517335, 590388379, 1863700331, 371973113, 1113209883, 1866133209, 3348883327, 4843043423, 7849958631, 3360293305, 1140781999, 7839776885, 12351033935, 16830517515, 22079604523, 12319260465, 2590689877, 43317787, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [92995, 2364727, 10430963, 50365, 2804257, 10388333, 10622833, 603773, 21061531, 42447443, 6713545, 169184899, 426616909, 52107811, 214984567, 427686935, 372908549, 1069288411, 1492968745, 93894781, 4006601, 743817907, 280015049, 1488298979, 1791861029, 556028345, 440255857, 1811854591, 1231830931, 3163459763, 5261979, 363825]) [2, 3, 2, 2, 3, 2, 2, 5, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [15734137, 17689027, 48611721, 15853207, 15188557, 48730791, 128884709, 49395441, 645556693, 1150595931, 189638937, 376154529, 287862819, 953014167, 334775217, 801336077, 961812339, 19509647, 3199024397, 2252330141, 5780060001, 6241459379, 1118606029, 2737625019, 783487123, 1994564619, 610733209, 1323187917, 2015342463, 85220703, 32172929, 1091475]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 6, 3, 6] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [685481037, 7599161, 325313971, 2169933, 8194511, 1012964941, 1025458675, 245343085, 10323801, 1025772007, 763234323, 2061554483, 2047067417, 390214461, 1040259073, 2036253281, 641916547, 3043061625, 3070635039, 1255824359, 2008679867, 3124313595, 1786801945, 4186268767, 4091462341, 467122309, 3219120021, 3693487189, 576165099, 4565829509, 180083533, 1091475]) [0, 6, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 7] [false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033]

#time def graph : KernelGraph 23 22 1 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 1.8024 s provisional ×3 model; 3004 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C006

namespace C007
#time def pivTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

#time def freeTape : List (Fin 23) :=
  []

#time def roleTape : List (Fin 23 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inl ⟨3, by decide⟩, .inl ⟨4, by decide⟩, .inl ⟨5, by decide⟩, .inl ⟨6, by decide⟩, .inl ⟨7, by decide⟩, .inl ⟨8, by decide⟩, .inl ⟨9, by decide⟩, .inl ⟨10, by decide⟩, .inl ⟨11, by decide⟩, .inl ⟨12, by decide⟩, .inl ⟨13, by decide⟩, .inl ⟨14, by decide⟩, .inl ⟨15, by decide⟩, .inl ⟨16, by decide⟩, .inl ⟨17, by decide⟩, .inl ⟨18, by decide⟩, .inl ⟨19, by decide⟩, .inl ⟨20, by decide⟩, .inl ⟨21, by decide⟩, .inl ⟨22, by decide⟩]

#time def roles : GraphRoles 23 23 0 :=
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

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011, tailRows012, tailRows013, tailRows014, tailRows015, tailRows016, tailRows017, tailRows018, tailRows019, tailRows020, tailRows021, tailRows022]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [4283643, 203873003, 327371257, 9456531, 119214611, 332544145, 20641589, 222786065, 362642265, 78108815, 160497789, 461392669, 75603461, 379003695, 615104945, 340548083, 311704711, 1031256489, 315276237, 1060099861, 1687080809, 2264763879, 942257185, 4267120925, 2169665365, 5589627619, 8701550169, 45842090851, 5281587915, 56713306385, 82913725, 1091475]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [8055283, 40707127, 241663871, 3970573, 76097167, 237579161, 35340673, 11169425, 276890407, 32095325, 6964865, 344326405, 170923649, 76773025, 547345379, 138840649, 282361489, 857109677, 1130056141, 107806837, 2126006467, 965265761, 706208815, 4221328369, 22790519285, 1180879435, 27977113415, 21467047813, 24202936915, 72234680513, 124859577, 1091475]) [0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [4336975, 62768539, 109152723, 5482765, 42047209, 110298513, 7886983, 73734069, 123668261, 37938987, 57821175, 169494231, 37023729, 149612043, 244456947, 229407565, 131868633, 510888241, 222373255, 608427173, 962669061, 4048363691, 576615143, 5233406007, 4019365169, 8705154555, 13301134867, 76846211187, 8615345481, 59525711151, 56744849, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [518031, 4921273, 24876103, 268401, 7257763, 24626473, 5075969, 2594837, 29970843, 4946039, 3083433, 39992851, 31818119, 10135713, 76757009, 30066323, 44151851, 138641451, 527529747, 10050509, 696237521, 518667093, 285840799, 1742434361, 9152352107, 558869129, 6891250653, 9221233427, 8580670509, 25264836187, 12697067, 363825]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [313825, 2348051, 4397417, 345607, 1735541, 4429199, 103165, 3039265, 2593733, 677903, 2560861, 4155869, 2683763, 8462489, 13707113, 40222939, 7928387, 56613815, 10004287, 88908367, 68426951, 153684679, 87962683, 218933833, 615598033, 1140569065, 1668204415, 3439721239, 1143233383, 1155918791, 2355621, 51975]) [0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [122981, 941183, 8789829, 65435, 1225529, 8732283, 2990219, 1947801, 11787937, 2969223, 5441277, 17747379, 42629751, 153657, 63346353, 42251711, 12017757, 148227815, 575885617, 47168735, 385406091, 577780925, 527814589, 1539072633, 2814959443, 265306095, 698105885, 2800534755, 1143572427, 6313600083, 4456405, 51975]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [9866763, 37179679, 76768811, 10235733, 29722369, 77137781, 11023303, 57651145, 98396817, 160433095, 51768975, 269853215, 160102069, 378517335, 590388379, 1863700331, 371973113, 1113209883, 1866133209, 3348883327, 4843043423, 7849958631, 3360293305, 1140781999, 7839776885, 12351033935, 16830517515, 22079604523, 12319260465, 2590689877, 43317787, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [92995, 2364727, 10430963, 50365, 2804257, 10388333, 10622833, 603773, 21061531, 42447443, 6713545, 169184899, 426616909, 52107811, 214984567, 427686935, 372908549, 1069288411, 1492968745, 93894781, 4006601, 743817907, 280015049, 1488298979, 1791861029, 556028345, 440255857, 1811854591, 1231830931, 3163459763, 5261979, 363825]) [2, 3, 2, 2, 3, 2, 2, 5, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [15734137, 17689027, 48611721, 15853207, 15188557, 48730791, 128884709, 49395441, 645556693, 1150595931, 189638937, 376154529, 287862819, 953014167, 334775217, 801336077, 961812339, 19509647, 3199024397, 2252330141, 5780060001, 6241459379, 1118606029, 2737625019, 783487123, 1994564619, 610733209, 1323187917, 2015342463, 85220703, 32172929, 1091475]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 6, 3, 6] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [685481037, 7599161, 325313971, 2169933, 8194511, 1012964941, 1025458675, 245343085, 10323801, 1025772007, 763234323, 2061554483, 2047067417, 390214461, 1040259073, 2036253281, 641916547, 3043061625, 3070635039, 1255824359, 2008679867, 3124313595, 1786801945, 4186268767, 4091462341, 467122309, 3219120021, 3693487189, 576165099, 4565829509, 180083533, 1091475]) [0, 6, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 7] [false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022]

#time def graph : KernelGraph 23 23 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 0.4554 s provisional ×3 model; 759 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C007

namespace C008
#time def pivTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨1, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩]

#time def roleTape : List (Fin 12 ⊕ Fin 11) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inl ⟨1, by decide⟩, .inl ⟨2, by decide⟩, .inr ⟨1, by decide⟩, .inl ⟨3, by decide⟩, .inr ⟨2, by decide⟩, .inl ⟨4, by decide⟩, .inr ⟨3, by decide⟩, .inl ⟨5, by decide⟩, .inr ⟨4, by decide⟩, .inl ⟨6, by decide⟩, .inr ⟨5, by decide⟩, .inl ⟨7, by decide⟩, .inr ⟨6, by decide⟩, .inl ⟨8, by decide⟩, .inr ⟨7, by decide⟩, .inl ⟨9, by decide⟩, .inr ⟨8, by decide⟩, .inl ⟨10, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inl ⟨11, by decide⟩]

#time def roles : GraphRoles 23 12 11 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [1] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] [false, true, false, true, false, true, false, true, false, true, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] [false, true, false, true, false, true, false, true, false, true, true]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]) [0, 1, 2, 2, 2, 2, 2, 2, 2, 2, 0] [false, false, true, false, true, false, true, false, true, false, false]

#time def tailRows003 : List Int :=
  decoded (raw_ints% [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0]) [0, 0, 1, 2, 2, 2, 2, 2, 2, 2, 0] [false, false, false, true, false, true, false, true, false, true, false]

#time def tailRows004 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0]) [0, 0, 0, 1, 2, 2, 2, 2, 2, 2, 0] [false, false, false, false, true, false, true, false, true, false, false]

#time def tailRows005 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0]) [0, 0, 0, 0, 1, 2, 2, 2, 2, 2, 0] [false, false, false, false, false, true, false, true, false, true, false]

#time def tailRows006 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0]) [0, 0, 0, 0, 0, 1, 2, 2, 2, 2, 0] [false, false, false, false, false, false, true, false, true, false, false]

#time def tailRows007 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0]) [0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0] [false, false, false, false, false, false, false, true, false, true, false]

#time def tailRows008 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0] [false, false, false, false, false, false, false, false, true, false, false]

#time def tailRows009 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0] [false, false, false, false, false, false, false, false, false, true, false]

#time def tailRows010 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows011 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002, tailRows003, tailRows004, tailRows005, tailRows006, tailRows007, tailRows008, tailRows009, tailRows010, tailRows011]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [4283643, 203873003, 327371257, 9456531, 119214611, 332544145, 20641589, 222786065, 362642265, 78108815, 160497789, 461392669, 75603461, 379003695, 615104945, 340548083, 311704711, 1031256489, 315276237, 1060099861, 1687080809, 2264763879, 942257185, 4267120925, 2169665365, 5589627619, 8701550169, 45842090851, 5281587915, 56713306385, 82913725, 1091475]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [8055283, 40707127, 241663871, 3970573, 76097167, 237579161, 35340673, 11169425, 276890407, 32095325, 6964865, 344326405, 170923649, 76773025, 547345379, 138840649, 282361489, 857109677, 1130056141, 107806837, 2126006467, 965265761, 706208815, 4221328369, 22790519285, 1180879435, 27977113415, 21467047813, 24202936915, 72234680513, 124859577, 1091475]) [0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 5, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [4336975, 62768539, 109152723, 5482765, 42047209, 110298513, 7886983, 73734069, 123668261, 37938987, 57821175, 169494231, 37023729, 149612043, 244456947, 229407565, 131868633, 510888241, 222373255, 608427173, 962669061, 4048363691, 576615143, 5233406007, 4019365169, 8705154555, 13301134867, 76846211187, 8615345481, 59525711151, 56744849, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [518031, 4921273, 24876103, 268401, 7257763, 24626473, 5075969, 2594837, 29970843, 4946039, 3083433, 39992851, 31818119, 10135713, 76757009, 30066323, 44151851, 138641451, 527529747, 10050509, 696237521, 518667093, 285840799, 1742434361, 9152352107, 558869129, 6891250653, 9221233427, 8580670509, 25264836187, 12697067, 363825]) [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, false, true]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [313825, 2348051, 4397417, 345607, 1735541, 4429199, 103165, 3039265, 2593733, 677903, 2560861, 4155869, 2683763, 8462489, 13707113, 40222939, 7928387, 56613815, 10004287, 88908367, 68426951, 153684679, 87962683, 218933833, 615598033, 1140569065, 1668204415, 3439721239, 1143233383, 1155918791, 2355621, 51975]) [0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 5] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [122981, 941183, 8789829, 65435, 1225529, 8732283, 2990219, 1947801, 11787937, 2969223, 5441277, 17747379, 42629751, 153657, 63346353, 42251711, 12017757, 148227815, 575885617, 47168735, 385406091, 577780925, 527814589, 1539072633, 2814959443, 265306095, 698105885, 2800534755, 1143572427, 6313600083, 4456405, 51975]) [0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false, false, true]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [9866763, 37179679, 76768811, 10235733, 29722369, 77137781, 11023303, 57651145, 98396817, 160433095, 51768975, 269853215, 160102069, 378517335, 590388379, 1863700331, 371973113, 1113209883, 1866133209, 3348883327, 4843043423, 7849958631, 3360293305, 1140781999, 7839776885, 12351033935, 16830517515, 22079604523, 12319260465, 2590689877, 43317787, 363825]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6] [false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, true, true, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [92995, 2364727, 10430963, 50365, 2804257, 10388333, 10622833, 603773, 21061531, 42447443, 6713545, 169184899, 426616909, 52107811, 214984567, 427686935, 372908549, 1069288411, 1492968745, 93894781, 4006601, 743817907, 280015049, 1488298979, 1791861029, 556028345, 440255857, 1811854591, 1231830931, 3163459763, 5261979, 363825]) [2, 3, 2, 2, 3, 2, 2, 5, 2, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 5] [false, false, true, false, true, false, true, false, true, false, true, false, false, false, false, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, true]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [15734137, 17689027, 48611721, 15853207, 15188557, 48730791, 128884709, 49395441, 645556693, 1150595931, 189638937, 376154529, 287862819, 953014167, 334775217, 801336077, 961812339, 19509647, 3199024397, 2252330141, 5780060001, 6241459379, 1118606029, 2737625019, 783487123, 1994564619, 610733209, 1323187917, 2015342463, 85220703, 32172929, 1091475]) [3, 3, 3, 3, 3, 3, 0, 3, 0, 0, 1, 0, 2, 1, 3, 2, 1, 5, 0, 1, 0, 0, 2, 0, 3, 2, 4, 3, 2, 6, 3, 6] [false, false, true, false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [685481037, 7599161, 325313971, 2169933, 8194511, 1012964941, 1025458675, 245343085, 10323801, 1025772007, 763234323, 2061554483, 2047067417, 390214461, 1040259073, 2036253281, 641916547, 3043061625, 3070635039, 1255824359, 2008679867, 3124313595, 1786801945, 4186268767, 4091462341, 467122309, 3219120021, 3693487189, 576165099, 4565829509, 180083533, 1091475]) [0, 6, 0, 0, 6, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 7] [false, true, false, true, false, true, true, true, true, false, true, false, false, false, true, true, false, true, true, true, false, false, true, false, false, false, true, true, false, true, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012]

#time def graph : KernelGraph 23 12 11 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 8.8968 s provisional ×3 model; 14828 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C008

namespace C009
#time def pivTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩]

#time def roleTape : List (Fin 3 ⊕ Fin 20) :=
  [.inl ⟨0, by decide⟩, .inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inl ⟨1, by decide⟩, .inr ⟨18, by decide⟩, .inr ⟨19, by decide⟩, .inl ⟨2, by decide⟩]

#time def roles : GraphRoles 23 3 20 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows001 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows002 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000, tailRows001, tailRows002]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002]

#time def graph : KernelGraph 23 3 20 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 15.1554 s provisional ×3 model; 25259 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C009

namespace C010
#time def pivTape : List (Fin 23) :=
  [⟨19, by decide⟩]

#time def freeTape : List (Fin 23) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩]

#time def roleTape : List (Fin 1 ⊕ Fin 22) :=
  [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩, .inr ⟨2, by decide⟩, .inr ⟨3, by decide⟩, .inr ⟨4, by decide⟩, .inr ⟨5, by decide⟩, .inr ⟨6, by decide⟩, .inr ⟨7, by decide⟩, .inr ⟨8, by decide⟩, .inr ⟨9, by decide⟩, .inr ⟨10, by decide⟩, .inr ⟨11, by decide⟩, .inr ⟨12, by decide⟩, .inr ⟨13, by decide⟩, .inr ⟨14, by decide⟩, .inr ⟨15, by decide⟩, .inr ⟨16, by decide⟩, .inr ⟨17, by decide⟩, .inr ⟨18, by decide⟩, .inl ⟨0, by decide⟩, .inr ⟨19, by decide⟩, .inr ⟨20, by decide⟩, .inr ⟨21, by decide⟩]

#time def roles : GraphRoles 23 1 22 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0]) [0] [false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01

#time def chartRows : List (List Int) :=
  [chartRows000]

#time def graph : KernelGraph 23 1 22 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

#time def chart : Chart := graph.chart chartRows
-- kcost: 16.8630 s provisional ×3 model; 28105 exact original rank units.
#time theorem checked : chart.check 33 23 basis.matrix = true := by decide +kernel
end C010

#time def delta : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj000 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj001 : Int := signedLit (wordMag (raw_ints% [266805])) 7 false
#time def adj002 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj003 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj004 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj005 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj006 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj007 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj008 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj009 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj010 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj011 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj012 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj013 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj014 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj015 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj016 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj017 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj018 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj019 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj020 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj021 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
#time def adj022 : Int := signedLit (wordMag (raw_ints% [114412425480269, 175275855202506, 206973623788723, 90024351125575, 1570133402])) 7 false
def pivots : List (Fin 33) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩]
def adjTape : List Int := [adj000, adj001, adj002, adj003, adj004, adj005, adj006, adj007, adj008, adj009, adj010, adj011, adj012, adj013, adj014, adj015, adj016, adj017, adj018, adj019, adj020, adj021, adj022]
def head : DiagHead 23 33 := ⟨fun i => pivots.getD i.val ⟨0, by decide⟩,
  fun i => adjTape.getD i.val 0, delta⟩
def input : PackedPacketInput := ⟨33, 23, basis, head, []⟩
#time def packet : Packet := { input.packet with charts := [C000.chart, C001.chart, C002.chart, C003.chart, C004.chart, C005.chart, C006.chart, C007.chart, C008.chart, C009.chart, C010.chart] }
-- kcost: 7.3002 s provisional ×3 model; 12167 original head product units.
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
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P037
