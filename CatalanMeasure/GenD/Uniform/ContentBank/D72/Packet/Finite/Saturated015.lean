module
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.Bases002
public import CatalanMeasure.GenD.Uniform.W.Prof.PacketGraphCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart267
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis022 (basis)

#time def pivTape : List (Fin 1) :=
  [⟨0, by decide⟩]

#time def freeTape : List (Fin 1) :=
  []

#time def roleTape : List (Fin 1 ⊕ Fin 0) :=
  [.inl ⟨0, by decide⟩]

#time def roles : GraphRoles 1 1 0 :=
  fun a => roleTape.getD a.val (.inl ⟨0, by decide⟩)

#time def graphScale : List Int :=
  decoded (raw_ints% [1]) [0] [false]

#time def tailRows000 : List Int :=
  decoded (raw_ints% []) [] []

#time def tailRows : List (List Int) :=
  [tailRows000]

#time def chartRows000_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows000 : List Int := chartRows000_p00 ++ chartRows000_p01 ++ chartRows000_p02

#time def chartRows001_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows001 : List Int := chartRows001_p00 ++ chartRows001_p01 ++ chartRows001_p02

#time def chartRows002_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows002 : List Int := chartRows002_p00 ++ chartRows002_p01 ++ chartRows002_p02

#time def chartRows003_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows003 : List Int := chartRows003_p00 ++ chartRows003_p01 ++ chartRows003_p02

#time def chartRows004_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows004 : List Int := chartRows004_p00 ++ chartRows004_p01 ++ chartRows004_p02

#time def chartRows005_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows005 : List Int := chartRows005_p00 ++ chartRows005_p01 ++ chartRows005_p02

#time def chartRows006_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows006 : List Int := chartRows006_p00 ++ chartRows006_p01 ++ chartRows006_p02

#time def chartRows007_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows007 : List Int := chartRows007_p00 ++ chartRows007_p01 ++ chartRows007_p02

#time def chartRows008_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows008 : List Int := chartRows008_p00 ++ chartRows008_p01 ++ chartRows008_p02

#time def chartRows009_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows009 : List Int := chartRows009_p00 ++ chartRows009_p01 ++ chartRows009_p02

#time def chartRows010_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows010 : List Int := chartRows010_p00 ++ chartRows010_p01 ++ chartRows010_p02

#time def chartRows011_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows011 : List Int := chartRows011_p00 ++ chartRows011_p01 ++ chartRows011_p02

#time def chartRows012_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows012 : List Int := chartRows012_p00 ++ chartRows012_p01 ++ chartRows012_p02

#time def chartRows013_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows013 : List Int := chartRows013_p00 ++ chartRows013_p01 ++ chartRows013_p02

#time def chartRows014_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows014 : List Int := chartRows014_p00 ++ chartRows014_p01 ++ chartRows014_p02

#time def chartRows015_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows015 : List Int := chartRows015_p00 ++ chartRows015_p01 ++ chartRows015_p02

#time def chartRows016_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows016 : List Int := chartRows016_p00 ++ chartRows016_p01 ++ chartRows016_p02

#time def chartRows017_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows017 : List Int := chartRows017_p00 ++ chartRows017_p01 ++ chartRows017_p02

#time def chartRows018_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows018 : List Int := chartRows018_p00 ++ chartRows018_p01 ++ chartRows018_p02

#time def chartRows019_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows019 : List Int := chartRows019_p00 ++ chartRows019_p01 ++ chartRows019_p02

#time def chartRows020_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows020 : List Int := chartRows020_p00 ++ chartRows020_p01 ++ chartRows020_p02

#time def chartRows021_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows021 : List Int := chartRows021_p00 ++ chartRows021_p01 ++ chartRows021_p02

#time def chartRows022_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows022 : List Int := chartRows022_p00 ++ chartRows022_p01 ++ chartRows022_p02

#time def chartRows023_p00 : List Int :=
  decoded (raw_ints% [100856230518113474244279, 201053043349732122978255, 2971218211280223785938263, 6014336281728897321454367, 28296953663168899156135, 64290943477686100548527, 2842065027098941412537849, 5748992294901479097927585, 28868250889079071459495, 64253707204755640982447, 2842636324324851584841209, 5748955058628548638361505, 99067866294522038202039, 201172477985801909610447, 2970572441508452694502743, 6014381243819106188954399, 175340972493480671357321, 368390445140075318320849, 3244981280296455404062103, 6583944166944983416885695, 287031078998667255725017, 592058391383056865788785, 3707353331788603331144441, 7544393003468115600995329, 434713652275298548770215, 919103211527593357491791, 4429098063062569135639673, 9055554606378765824275905, 681748039505922361718135, 1418255702987572644978159, 5545559754843790046128023, 11392913520893931826745855]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows023_p01 : List Int :=
  decoded (raw_ints% [1038301674688002017749833, 2234284544604403161516529, 7265609469037714425595991, 15045453768485907633240543, 1710217700326879925815257, 3592596151919493630313233, 10014128844052596369161081, 20872334465009804425070305, 2726455228497225391246119, 6035002044668654549080175, 14450801772876701686222457, 30499932661597952604463713, 4906875932015978389852855, 10433934202583003639572367, 22084132933389905467321431, 46968868908849610793116255, 8327661312636825108192905, 19223870074304647118871953, 35318670178042708965367191, 76626673185737261551560575, 16885541591319665631505241, 36447308514222669081425713, 60531873081999199705065337, 132297851774264577751858241, 30795872533169181791648039, 75652048091844274598637071, 108213287206488047128218617, 244397208380331521431921025, 72826809526030519982472823, 160058259728975338746132655, 211835969265687748902339479, 480107516201151134776690751]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows023_p02 : List Int :=
  decoded (raw_ints% [143667027872720455735671625, 388114078106104938290728369, 428329806664438724620483927, 1028279854036231411813551775, 416067290940738445127640665, 934198349773961306572612561, 988064125477897625483796217, 2350592281916297656676892705, 892595089793725267154272167, 2818109163979445039051002671, 2296726506212361337765709049, 6102899795669704002300507937, 3434960857430701098665820343, 7908575502527553684720325967, 6624282453436787703585801559, 16829584462176702726071836575, 8054634200399979904954739081, 34172353876937087646822874705, 18113877511267468707206360983, 58910513841641344057615037247, 48800478495643514385070450905, 115695733796554641341225434353, 74968990207310962997231550969, 208778601515133073045663346305, 1536037220899168630091271, 3107694662539314722216311, 559917322254415125, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, false, true, false, false, false]

#time def chartRows023 : List Int := chartRows023_p00 ++ chartRows023_p01 ++ chartRows023_p02

#time def chartRows024_p00 : List Int :=
  decoded (raw_ints% [12735099575650539974435, 3415522685280409794165, 385257765339018824002489, 390307535730710945532107, 4489541123208495319649, 4320323044750451142241, 368033124640159788708405, 186162560972419427606603, 4432889643065726044769, 4322145004859620124257, 367976473160017019433525, 186163471952474012097611, 12912341856515523727139, 3414062685021111979125, 385321704659598269205433, 390305339649892092235979, 24367429604241018166953, 12516728611407079043245, 422601476120354811099525, 428995047612790698238969, 38486627826259072284915, 40620515528368891264745, 485455533550854901551393, 123662255090993436897551, 61141376856716402322197, 63397907783942446719243, 585083538233830376158505, 37416715229767817848387, 92822249596077909947663, 49701831299858569521697, 739047164686624688428365, 761469014059944671336829]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 5, 0, 2, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows024_p01 : List Int :=
  decoded (raw_ints% [150828774349996333956053, 19732500252392136986465, 982698188632698932332081, 1018732678678798906271943, 236960209780477805707111, 260366206678347769807635, 1370487172763173071995245, 718479443688141885985649, 416715632802439133860265, 441317311773992534652245, 2024163015346090011562621, 1069321202914312038215589, 694877771710614065181339, 49637434025746137505851, 3135756419859143210604225, 3374158662014554811177039, 1370324601424085536151521, 736453459347068773672059, 5200958792993842811937085, 5641264525120630558614773, 2456100700217765051892091, 2978687510811685089127005, 9027384094635693399980697, 1261607369328306649385737, 5632224041387124716572317, 6164733162294666570614655, 17115708836240583168445105, 4809069906933201213706889, 10938383866186651797421895, 7269423095346017715022575, 33686316743814359682439317, 39939858980719506855487361]) [0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 5, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows024_p02 : List Int :=
  decoded (raw_ints% [30646392989007713408764493, 8570480245075326383886393, 75271093599008724888625705, 88760626151712847821078083, 64896514077003143527231407, 100381000697787594772257031, 170814000665019581824621605, 111711773914900874064440343, 241084581648136378625800817, 276717868122234389731025865, 476795096390159103977653829, 300261208324911866316081791, 559805795115661658145270419, 289224161526910614575144995, 1277685473153957140748725065, 2034136930879700580663769427, 3266890412551110138285978265, 1932384744631321675671770185, 5104381680820728937179973749, 7055803066249986390307889777, 8365491336832691470656934531, 39301896156414241296339671889, 16736763430204530546122886545, 12555617177981717759497775509, 99498216228667340994231, 403969626471832584708767, 559917322254415125, 0, 0]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 1, 0, 18, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, false, true, true, false, false]

#time def chartRows024 : List Int := chartRows024_p00 ++ chartRows024_p01 ++ chartRows024_p02

#time def chartRows025_p00 : List Int :=
  decoded (raw_ints% [627770704892286485955, 1267464755457356728317, 17038267765168623037995, 34535445277908045367881, 180784302994270950471, 403268212743073121541, 16229712757282065601569, 32864712309707615518023, 182802885394682143815, 403139896599552587013, 16231731339682476794913, 32864583993564094983495, 621458325404011836867, 1267875812426283497469, 17035992550481170775595, 34535599702589931067977, 1110032088649861177389, 2344642474091926464075, 18767482964535043789851, 38148117989108141029521, 1847762445480118736505, 3820845760697228460771, 21725277498665023703745, 44313606223897295954367, 2836134541784358271143, 6052256667999996689933, 26409174485929500711393, 54186708652594521105071, 4584481806951158101075, 9566474636121952298341, 33829790834665017083611, 69805439956716470093345]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows025_p01 : List Int :=
  decoded (raw_ints% [7127851116557230123389, 15563231487040631143283, 45542123758173405308075, 94935146079879053534969, 12286278934015643938713, 25930007384573045032875, 64956253808746279370177, 136428384951492729711127, 20159605784557572064935, 45665053886174576643637, 97402138527319495373825, 208023446222240351387639, 38724617269218365218691, 82925327368550840647661, 156286361581095432657451, 336613827476965768678937, 68241814414107378793005, 163549840674694163207547, 263252793264421176669147, 583088995520210772534145, 151891435251955203610393, 331213229103890161311571, 483386042930483759072545, 1077852065298795097053263, 290401773289762536609351, 760145306606079225926525, 925679251472201499292289, 2169210601008764484291359, 787595631380678175023955, 1755683425640438381804949, 2003676656142642210925595, 4685039333255282092022833]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows025_p02 : List Int :=
  decoded (raw_ints% [1645773815229757876952637, 4991148502397590420638307, 4437046102753078262902187, 11431871261293310894466089, 5903153742954986912347385, 13510144595600051472439259, 11985973660937823052202209, 29933164359290952787543655, 13568207890060371243231111, 54640569411552111235892197, 31457335293953181207780705, 98083878366443115495875111, 76241569300028493072974787, 180005992179528795458706525, 121267112484042045523986603, 332730439957524022190473833, 193960637868940233528232365, 1758945350192484091395369003, 391469319653010772125193755, 2271681782329536909044549361, 3053727855347059222661298489, 7478582003910730607336716099, 3639157812869010228314724609, 11509209136432751607776634463, 8833019235030454761975, 17901455016682701048099, 24344231402365875, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, false, true, false, false, false]

#time def chartRows025 : List Int := chartRows025_p00 ++ chartRows025_p01 ++ chartRows025_p02

#time def chartRows026_p00 : List Int :=
  decoded (raw_ints% [322298476816287553821, 172571686026846014901, 8805281379035875358223, 8933711062439134684347, 111128900484577853535, 108568679448296201823, 8371854001735009950867, 4239999505468573226361, 110281559992258453599, 108595325559947117151, 8371006661242690550931, 4240012828524398684025, 324947082739849414941, 172529028094314958773, 8806235303974798419471, 8933679038797374402747, 620056499282562386703, 159735842701561577175, 9751238885997210221115, 9917680465792250628993, 990713401920011046453, 1054111679533667162251, 11362008787199783654271, 1451341939516520512493, 1614963415012084169395, 1680118376483534332169, 13967685604131878870119, 3586241393037341398591, 2499833273989957943433, 169497186591150271667, 18082482293133920982947, 18737038934091304273205]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 5, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows026_p01 : List Int :=
  decoded (raw_ints% [4233189978841617330427, 2225930445897229694161, 24815505545965496256807, 25900854811344168008199, 6841230335504644949001, 7676256953836272670005, 35889925860311758536235, 19014486328487450033263, 12789377165494183451591, 13641717754805736039667, 55520533361310586936827, 29673473682808454388099, 22146886352729932306485, 13104225886921663416379, 90456796879534702694903, 99197116894265971648623, 47750657224419259266471, 6482368871212384068093, 160354340456683894267859, 177264519637808371026125, 89787603077227839339549, 115622783178569475879199, 297892600758330992873879, 86186563446519229862517, 235165269335402965571227, 261140818116659804217245, 622845473170961797784655, 45094365942581637471657, 484445130718605446386977, 179862310647259831328751, 1342455873224970209742859, 1702099915787005329078761]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 4, 0, 1, 0, 1, 0, 3, 0, 1, 0, 5, 0, 3, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows026_p02 : List Int :=
  decoded (raw_ints% [1673741439583543442914835, 954617368175363702280023, 3500642443527119099044671, 4330783894726772058953811, 3805010935517217286023537, 7456136995252417963048393, 8979394818627879827983043, 6848077813164958713281125, 20540784670391693837231663, 24193956365965003920583303, 33325190424536790951238243, 22673124493773669655096973, 51889245187559410721846349, 113354620806457624534797505, 105755220282487895510316255, 296249446966427592300372259, 782517691406150480997455679, 239337090397035449379232157, 940162156876197787229618283, 1480307050167484638886895897, 2212468818352706817350956805, 6400848902353995966253714253, 3935148666635055085578030767, 61924898290599523903904527, 2281894963963040728011, 9278854434492826714149, 24344231402365875, 0, 0]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 7, 1, 0, 17, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, true, false, false]

#time def chartRows026 : List Int := chartRows026_p00 ++ chartRows026_p01 ++ chartRows026_p02

#time def chartRows027_p00 : List Int :=
  decoded (raw_ints% [1098244748294533841189, 2234784803699541351729, 27054139451306132247093, 54926529789204974146393, 318289168812297858333, 707179803056238211873, 25637605534199300547571, 51984565182449194582791, 320463479806653134109, 707044377423120653089, 25639779845193655823347, 51984429756816077024007, 1091450964045232896293, 2235218209788336775473, 27051694289045541853749, 54926692344027534452569, 1967071011679554624251, 4184194394393123774431, 30110216264770329374293, 61346104948208995002473, 3342795801381905404067, 6936188570265850338607, 35420083077831789402611, 72466487912867969115511, 5219714526088335244829, 11266917802864243086129, 43982593405302030051507, 90669594285998062540247, 8751610752169910278533, 18349182629801793779713, 57953918683560275574869, 120285694718664099406089]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows027_p01 : List Int :=
  decoded (raw_ints% [13975429229175431757531, 31095566168248635681071, 80680958664905617610933, 169730443516714528866873, 25488663125976497568547, 54174703289606851699647, 120145051020057546937011, 255000712974570016247591, 43396651098085276504669, 101491721933267630303489, 189030365244119321010227, 410667138197444498250727, 90701478544388210029093, 196237919722752332113553, 323128494886592807543989, 708396779853464460667769, 167676231258642967664251, 425066091607566654069951, 581506204689623985237333, 1329700791183783446851273, 424078242153459162782307, 938248488339536886511247, 1173260678101726115683891, 2693015371130886987432471, 860664261113512479793629, 2503915308025938967386769, 2458003181368697758259827, 6135179167496362841330487, 2862423851671393812403973, 6508618253238785402024673, 6181091294153604050457429, 15147712728761087210741929]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows027_p02 : List Int :=
  decoded (raw_ints% [6431724542021270699447771, 24522062956277929725452431, 15475239687846268562309173, 46178393938277802338219033, 33318252976841924239605347, 78299436112239902780847007, 55225217206709463501362291, 148999893006795634844518471, 83530641728774686383035549, 702475419235491476845043169, 172074111912326074124003187, 929774748354527014470408647, 1204571302036591656684409893, 2944575612771070360189328113, 1460176055677692417191448629, 4576825780361088851504779929, 3396477979740182720626800891, 18522535005248585888334028129, 6061225337454466794502659413, 11001133612116426676639920087, 45042597272014128874606067933, 115400583241526842839782162193, 35584893954819479359476607629, 144924251858891855404756110409, 14076192099800333044141, 28580657296452257749061, 73032694207097625, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, false]

#time def chartRows027 : List Int := chartRows027_p00 ++ chartRows027_p01 ++ chartRows027_p02

#time def chartRows028_p00 : List Int :=
  decoded (raw_ints% [285279024567003012867, 19155550350208347935, 6994554141718920431689, 7109818485115885368823, 97169899845734246785, 95730210284775946273, 6612105217306183172037, 3353799734613887927795, 96697983119367721345, 95744775700544209633, 6611633300579816646597, 3353807017321772059475, 286753036409175642627, 19152638198096226683, 6995084320108360010569, 7109801021513627955511, 555564788740439501113, 287272202515381720563, 7837402145257975154309, 7990787637713931023565, 900295006232999119651, 967794179488934587185, 9293261940231413775073, 2383281555558407262969, 1515021916749300608325, 1583463919215424901459, 11708578863213713503049, 1510548040117248567565, 2403516837130099269535, 1326165382848886830563, 15627117617093113380909, 16320179005851187103105]) [0, 5, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 5, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 2, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows028_p01 : List Int :=
  decoded (raw_ints% [4287267471781595497109, 1134912458731644969839, 22317901926004808147553, 23512159606475540643587, 7180547559013029253671, 8297308771364140082467, 33785716956799432898333, 18174559106383130302705, 14540872495648906325417, 15667029363249565808805, 55507137011461368477421, 30156728173689983248341, 26405824902687421330715, 8234067997844588034327, 96453834409797696133553, 108916757702007884442795, 64392565664489659562385, 35474080914430125785321, 187252224976974777026653, 212801191522246488150745, 128601691083774265827083, 183136419369048075718517, 380246481725238702416121, 14590180397504837982497, 410949729644154111657517, 465559248276333886653079, 919797902453167079900721, 278895360091384194452875, 911735842733253057470199, 844687241267664707866585, 2242483474830574249028437, 3270515171177200080197749]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 6, 0, 1, 0, 3, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows028_p02 : List Int :=
  decoded (raw_ints% [4523076515030657436334765, 662621621695882778174157, 7677295832594484742833401, 10260862627279591721324175, 11246003021473680971433295, 45438356356456317030114279, 23446375369098823150601461, 30500095978651485488415855, 154738342867847248741255761, 188931762214108043860924649, 189430721258419752863290517, 147685155263933665933935319, 435004360099263996989753779, 139218573752086674538217599, 779173424225530998594300057, 629446517274718020576945505, 5479741423133148827943726487, 3514244437247350703148192545, 4265563638808353832359672651, 8771683981786112823179071387, 17589477011811771966287841165, 6534162292055188090058275897, 27334782073753274626591240303, 2316502641056406534854295145, 1819958291571480861139, 7416307290719218935783, 73032694207097625, 0, 0]) [0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 4, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 1, 0, 15, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false, false, true, true, false, false]

#time def chartRows028 : List Int := chartRows028_p00 ++ chartRows028_p01 ++ chartRows028_p02

#time def chartRows029_p00 : List Int :=
  decoded (raw_ints% [17198030414327967055, 35210391268320485245, 379128239705471118439, 771303909373072306849, 4964930891862448219, 11070567097443488917, 356965278399280703165, 725022951007308332687, 4986758003165885659, 11069230883713950229, 356987105510584140605, 725021614793578793999, 17129876652958577359, 35214664140124142845, 379103740166708603623, 771305509817416887073, 31182816971165245313, 66950400163877679035, 427416433790832426295, 873470574121418708953, 54405289732466290085, 113398552908238214915, 513004540494463961693, 1053819527193534602903, 86803709380378604347, 190263475843312163341, 654213539607308856125, 1357481555945084981159, 152514243193400827903, 321866468806239786133, 893531492181088288375, 1869611500594636930633]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows029_p01 : List Int :=
  decoded (raw_ints% [251900741845299312113, 575701959513575787155, 1297946477219788428391, 2767179928914452503921, 495088192143152122181, 1062596231624827178555, 2044935411208239862685, 4405478120052855469631, 883115337118050800635, 2168789764308991921765, 3423138940469442785501, 7636864115986674569951, 2076260662238730120079, 4556419844506393409677, 6382514939826223706215, 14362073724802059901393, 4077203027417275778561, 11368564120168811239691, 12535978629482229604855, 30287057689477264550761, 12506461523264340802181, 28230765727760593213715, 29119643180163846185597, 69886387537406669004167, 27371405381575229044507, 98542002565788301535005, 68997510085003416032285, 196659155830955563752887, 129834732845161804178815, 303480092353986985783525, 226203648311740449255607, 598681250750730851071417]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows029_p02 : List Int :=
  decoded (raw_ints% [319919313636075134164913, 2480366444334279976330019, 675957694792977387599335, 3382527787438997813184961, 4191059528551247880151397, 10222688230210301640187787, 5186936536980300401915645, 16085582461983579429702767, 11743338089682032385907867, 56227032823554203902809035, 21121334155213580667974909, 29918762131360322832918481, 140131801355023720457585201, 359977132292108981178047075, 107267129110128107403702425, 446122927247023507913774591, 451433999963852553826831615, 285283932444869966052970715, 698832930429004381688119241, 520816127094262523038850951, 1613567666172468760217189861, 4415288230009025953986668963, 463300735779611824702239005, 4179756035359633397000788727, 198163135059899542747, 403257150320696396047, 3843826010899875, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0] [true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows029 : List Int := chartRows029_p00 ++ chartRows029_p01 ++ chartRows029_p02

#time def chartRows030_p00 : List Int :=
  decoded (raw_ints% [3008902311684664925, 1627778039740944399, 65520844609138933855, 66763304286924400799, 1017290491708178783, 1007355568113587599, 61494651805746090147, 31250196319664462201, 1014061022646672095, 1007453656362419887, 61491422336684583459, 31250245363788878345, 3018983071864514141, 1627621264640887263, 65524466431195769695, 66763186913221951103, 5968942950751397727, 48438912357688265, 74512392453811681563, 76218610224287823549, 9843854153769082085, 10729802651577582099, 90325189558332161375, 5821787103603093973, 17262559348020766499, 18154752016479628497, 117431603060122009959, 30508287081426678541, 28250035216107898905, 7985797523658599671, 162944197624250675363, 172131090436820741345]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 8, 0, 1, 0, 1, 0, 5, 0, 1, 0, 3, 0, 3, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows030_p01 : List Int :=
  decoded (raw_ints% [54010130598301030427, 28863627725179344271, 245204363438659604695, 261801535981813828571, 94638725388724794409, 114417238482754755765, 393853219425685429531, 216973014957463636439, 214381372555268403815, 234222801567132896243, 702873317369678627755, 391293034982407462443, 413489735769269982933, 282107179147542577917, 1330744425694217014503, 1581023229827032976963, 1215496589086532253655, 341597120432257549167, 2959730750550019251091, 3511626069851148329465, 2621071012973786296429, 4580055999625928190039, 6796298352610337801175, 2364517637801526679043, 11862585383469607913643, 13822063725461703811605, 21279954749053732011247, 3482523784536717339727, 28942013121933813122705, 13432002358268650287747, 62084553254457153047595, 149138272867904644831397]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 4, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows030_p02 : List Int :=
  decoded (raw_ints% [360077463837259575048851, 219296577620382341432109, 451104030213650541219151, 695187446974818529997591, 1005275680166605768236465, 2239438369552002038885639, 1816457174217515884504467, 552828883668209413011915, 11328382302378479267064337, 14573089445608012250927817, 8506649447994357614323405, 8959092791248216557918643, 36640868857841696237819059, 4772034095307889196745755, 56475900608214533119206801, 22947206837488666973273593, 122786392780524985316668495, 21121420641245805385948639, 29669623314468755959642635, 155568226483093554507807029, 466953543816657497954838517, 58882748652571395926657691, 619409559911651239231149647, 47927792533203924190256729, 17132436730205899695, 70018860366406289597, 1281275336966625, 0, 0]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 4, 0, 1, 0, 1, 0, 4, 1, 0, 14, 0, 0] [true, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, false, false]

#time def chartRows030 : List Int := chartRows030_p00 ++ chartRows030_p01 ++ chartRows030_p02

#time def chartRows031_p00 : List Int :=
  decoded (raw_ints% [205671783492081903, 423505261528736767, 3992463206174821359, 8144072382029485087, 58687508356812495, 132094597381343103, 3728103914325926961, 7588472523119405217, 58857605443020687, 132084339416306751, 3728274011412135153, 7588462265154368865, 205140976303384623, 423538041532419391, 3992272593158540463, 8144084646103095007, 377936525015048849, 821856979394812865, 4575350094476973935, 9389479667030327263, 682699932456143409, 1431393006256315201, 5635986551948166193, 11642729652681455329, 1119449622585294735, 2508313565202754559, 7438136106989604337, 15582436224140525089, 2095027952778776239, 4460863789128606207, 10652613682353675311, 22551613578471885855]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows031_p01 : List Int :=
  decoded (raw_ints% [3612222050114365201, 8605324707360388737, 16359863685246816751, 35617802074960880799, 7891177361713270833, 17167219795373181185, 27863263097074452785, 61390346577694450721, 14939862817205455503, 39909836470989203647, 50694303275993179121, 118467402844056835553, 42048769945854225455, 94137881724568173503, 107682936039052860079, 252515121039614212703, 89238360740222440593, 302578679469891011649, 238970066725129526127, 649231682234073397855, 384631867513482916657, 893393662883121306049, 712840294978834883377, 1845204024587085715553, 928285229999054338191, 6590279899863594992255, 2025757392491372138225, 9328877587333802013857, 10939357472215598391471, 26612510593502518088319, 13893400094706024867887, 42531668080699915094431]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows031_p02 : List Int :=
  decoded (raw_ints% [30418021012574785055505, 125411006086858123641599, 55250778579496408314863, 56266827412655690458849, 322597411671081415785679, 831441561805045718530687, 236928612079010222415311, 1013119395304559532631135, 1048106321280503390545521, 429682873697427930108223, 1607632345030595028746511, 1414878083412177321053599, 3278175801626944057093167, 9082248454099480806293055, 622437135315845637801135, 8097053244384731415347679, 12656251626225576888945297, 4025099965351487526287553, 16556864563168366583839599, 21204401663835699747928287, 20540479123375122782408655, 62368354396706909952826303, 8672637066018820690376241, 37138852767519722678610463, 2099067494833451631, 4283788821779110927, 75369137468625, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0] [true, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, false, false]

#time def chartRows031 : List Int := chartRows031_p00 ++ chartRows031_p01 ++ chartRows031_p02

#time def chartRows032_p00 : List Int :=
  decoded (raw_ints% [13632836687943409, 1864756055499469, 259897494057317443, 265705573314736909, 4587101685209163, 4557381951551839, 241677555684164871, 123115071459594659, 4577512252154379, 4557669136957687, 241667966251110087, 123115215052297583, 13662753728731153, 466160343863527, 259908232231995619, 265705230245185717, 27765504304914771, 14502265825934209, 301336490265641543, 309626892900686999, 46824364268912977, 52067399568012991, 375926358839469291, 48837353015071051, 86855365429311239, 92116400249998357, 509606088537693507, 133720655984644939, 147930505872457973, 86862580820301877, 744391959839462719, 800724185829181867]) [0, 4, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 6, 0, 1, 0, 2, 0, 1, 0, 1, 0, 4, 0, 1, 0, 3, 0, 2, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows032_p01 : List Int :=
  decoded (raw_ints% [312184269388187831, 84512239009416467, 1204506735100108523, 1312498303507451489, 579896779501829837, 758218490832112861, 2096587783990126191, 1204382875188615109, 1560896134936603939, 1739401208262250867, 4237380698428559967, 2453192724735796973, 3255915783673965753, 1337951054513747221, 9054192617039129659, 11997590875788833697, 13334489169935420091, 7715431164095945499, 25644597570648515503, 32780257422035713579, 31798555189222758057, 107702112683668184891, 70777641929806693651, 38978308108473947367, 353876851186291803359, 429781828430543497297, 456453048305321255067, 86674646693513433957, 979575056160367624413, 928284923170440254673, 1789904955651980682839, 733390844362229540393]) [0, 3, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3, 0, 1, 0, 2, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 2, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false]

#time def chartRows032_p02 : List Int :=
  decoded (raw_ints% [9739306348870549089569, 98245675285464829049, 6969826337058200782317, 15165407127242608168011, 31802748104577261918363, 4754264097883424728601, 48511880790506011790249, 11493294732949340778841, 92361858949558771840699, 128918890730242620004847, 12047230054475498132087, 55343282681113681587883, 362754593126430198256353, 8700757967155134336713, 467163682130464468229139, 309211519829711057874317, 539446790253454869578589, 416297610161747730564491, 290471485003439796906903, 453777636756543328560961, 2614241893913502303615103, 871413903831734619268169, 2863217199163517376286789, 67430836278492919029941, 68382582686315213, 280623621758732661, 75369137468625, 0, 0]) [0, 8, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 4, 0, 1, 0, 2, 0, 1, 0, 1, 0, 6, 1, 0, 10, 0, 0] [false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, true, true, false, false]

#time def chartRows032 : List Int := chartRows032_p00 ++ chartRows032_p01 ++ chartRows032_p02

#time def chartRows033_p00 : List Int :=
  decoded (raw_ints% [16187448464149279, 33540096544858665, 271147988081275543, 555120232830385157, 4528391412875315, 10353567231559857, 250432148204250949, 511226569053966635, 4537096826780195, 10353049160446017, 250440853618155829, 511226050982852795, 16160296080206959, 33541751100330297, 271138246525142983, 555120851243629109, 30225813213466481, 66947724919352159, 317524355818816423, 655610327263311565, 57283527331564397, 121062891566828375, 405033696363847301, 843620943749492099, 97332915257061475, 225706088983627881, 559650138952473173, 1190389924299948355, 199462820121568415, 430036112659202849, 856445874331103063, 1846132125942779085]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows033_p01 : List Int :=
  decoded (raw_ints% [363813669818207393, 931752725754352519, 1419722364270878871, 3207920964356334453, 936415291750721837, 2077157062104555903, 2719951325839808101, 6216830752215242875, 1917669870889460739, 6109573780730945265, 5574036488479990677, 14403561595050744043, 7447392527932247215, 17169533531891000297, 14939098887301698631, 37682668907672689605, 17526612137028045425, 113052734865982152783, 39913103552261991271, 167904937305545842685, 183604852929975967501, 445210615297325780423, 241044568619266004197, 726168287468853775891, 505684912597671580419, 1748871329326376652839, 930334334146913552117, 577492426560197096525, 4692717336778072434017, 12145671542015863555695, 3256698090033487301481, 14472035297902437305059]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false]

#time def chartRows033_p02 : List Int :=
  decoded (raw_ints% [15411593323073253823775, 2897681271231712612279, 23361008749884813559273, 23720025568686588248475, 41311266525388005306125, 116343416271824784615471, 2538664452429937923077, 95521071974369908979275, 165475892815946812442467, 74360270569011575040801, 209325823793764755671669, 286224758815206268635547, 223542511019258480109457, 703676471513562576982503, 151259205590453088004679, 343091442129344733306155, 1125743813804555006188559, 801808160812719284669505, 1198027119233360398293337, 1848576074455626594958163, 871413817002929923147565, 3192507449762301073444023, 1452357116034985481334331, 542123214493955193816355, 143667718272712411, 294330164687621911, 75369137468625, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0] [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, false, true, false, false, false]

#time def chartRows033 : List Int := chartRows033_p00 ++ chartRows033_p01 ++ chartRows033_p02

#time def chartRows034_p00 : List Int :=
  decoded (raw_ints% [8683241674810425, 4833722676057995, 142146100589315171, 146015790660756863, 2912268886538171, 2899871064562439, 130550590027966575, 66724237122039217, 2908295189637011, 2899988584891463, 130546616331065415, 66724295882203729, 8695632846830001, 4833535064666615, 142150544367532427, 146015650478632151, 18368719634035907, 604175986557315, 169214896848398335, 175016352177799461, 31901454164434505, 36594423061162155, 219485070646868747, 14434025425549731, 64206064281743703, 68906291327470217, 315592589093046955, 84111280299357017, 115311582581958957, 36177655971493369, 495110235956749615, 550062036410871761]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 6, 0, 1, 0, 1, 0, 5, 0, 1, 0, 3, 0, 3, 0, 1] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows034_p01 : List Int :=
  decoded (raw_ints% [284013266098232287, 156720456032555995, 894435084636940859, 1008213572361957227, 570425533482024429, 880229929415897405, 1748873884217197575, 1100942206921483311, 2096055384601308475, 2405934527283603755, 4415354802300530479, 2744024435271233891, 4861201806449773641, 7447724134668662237, 11372611993351612595, 22789431667163396011, 47763334079848442139, 14449444293492611483, 63997147879649828375, 95482657110471166417, 130803238729735125809, 204476870300365960785, 242563720689233396323, 12799109003981087109, 1127277292740782536897, 1462556829287187525075, 753910333321814014765, 214778766950434729287, 3726475970396920152315, 8975172470643957775, 5607663596459516703977, 3037184205360362034971]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 4, 0, 5, 0, 1] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, true, true, false]

#time def chartRows034_p02 : List Int :=
  decoded (raw_ints% [9154640271655836139127, 6512360465334554773249, 179499295200600717165, 10131139484839050835927, 37516079149761686060053, 9657250109816297234689, 46491220126216921482015, 16406555262662228808557, 45557798131914019320477, 73416619378255021837425, 38449501144064588221591, 15473129371557133492811, 240066960398953734768799, 45465477617697854492285, 247175257386803165867685, 195293833356764997807617, 161967897988238652919795, 38887992804775524087935, 325274319797518247716689, 24879153846043485911293, 1160546934175293199743129, 513567685467997399930931, 997240512366013604946235, 106193847719030634818213, 37707335566031399, 155683236012872853, 75369137468625, 0, 0]) [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 4, 0, 1, 0, 1, 0, 4, 1, 0, 9, 0, 0] [true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, false]

#time def chartRows034 : List Int := chartRows034_p00 ++ chartRows034_p01 ++ chartRows034_p02

#time def chartRows035_p00 : List Int :=
  decoded (raw_ints% [180974268983330455, 377825707434494443, 2545653499225969975, 5239066606437068419, 49091830466035519, 115002060797491219, 2315587399776604001, 4746238838205082757, 49153808320419055, 114998416062248707, 2315649377630987537, 4746235193469840245, 180781045949694823, 377837341549580491, 2545584231901101415, 5239070951081669443, 344958782879352281, 786203847145244165, 3071324060730148519, 6403112139776494099, 701709082582088945, 1499697799555483549, 4117991926191589745, 8689013786477221813, 1251018651067436927, 3081618324124816307, 6070719659841115617, 13270329910157521669, 2959490263532669815, 6499054296362119739, 10281228574441222359, 22851002530644457715]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows035_p01 : List Int :=
  decoded (raw_ints% [5828109414591462921, 17422736449542540597, 19068828252565355095, 46772793276549118051, 20229763806369485537, 46227458985771112205, 45126701473526303553, 110422988711862770853, 46167280944211790415, 268183583287779995043, 111523746224107579505, 424834030985413878101, 423802840880766923719, 1023458308266373228139, 581493868049086293639, 1716475922539567101283, 1153143653827000818425, 3222891931637037267547, 2158440362756854035783, 482957700831096938125, 9175874011808843095663, 23880917506140190897091, 5864289995224988241455, 27586767138608325102763, 30563230642489696421281, 1034883479669955723565, 45603394649523527758399, 52502568124418471723419, 68232568337448324491095, 196556744219728584480091, 7934056954564899688585, 143019292615640157033107]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, true, false, true, true, true]

#time def chartRows035_p02 : List Int :=
  decoded (raw_ints% [287211582407050216399273, 166614413595602377083733, 347510093789933641201783, 506190450430971118596931, 309426905960344003122175, 1026662457502537097287379, 325294770236639854478881, 353857593475963601606715, 1721682685491436404729681, 1381653362943716066001597, 1705814821215140553372975, 2762173413922216764895691, 989485551055784680578343, 4040683560667103263152395, 2438011955650792277524313, 103143216198829567744893, 7824078704714073569877785, 7184822309240872326714437, 6375552300119065972931815, 11122362653709146022121939, 2267998342002187166905039, 12999329397827308429220899, 11931632662830952375904561, 5307855565122709919615477, 1363313884104650215, 2808446156935781431, 1281275336966625, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0] [true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, false]

#time def chartRows035 : List Int := chartRows035_p00 ++ chartRows035_p01 ++ chartRows035_p02

#time def chartRows036_p00 : List Int :=
  decoded (raw_ints% [147707755182930311, 338048310923409909, 2021659612555927473, 4184230298331783769, 49429482520550775, 98590037094809311, 1824522374852446387, 3747591950313564549, 49386646034413239, 98592542307936637, 1824479538366308851, 3747594455526691875, 147841275067597571, 338040316089978987, 2021707459468319661, 4184227313924607499, 331011436010349593, 704236702643183935, 2500560170546266825, 5226504332657770421, 598609258198071113, 1450687240692065677, 3430180864754687531, 7381428275993020033, 1373144528977639535, 2999910351953427513, 5401934651930398179, 11832025868638513223, 2654922387753504843, 7689698480999777359, 9430001568661542557, 22521634701591718095]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows036_p01 : List Int :=
  decoded (raw_ints% [8696407657514905497, 19773277785192804899, 20781331613929952897, 49984610967784300353, 19498817867602293961, 107103652223600654505, 48976557139047152355, 176861540976577759757, 166513261054481815591, 401134126780237312229, 234988636061131261907, 685099319980415726491, 449742913583908699315, 1108012436861007732829, 851244810699521776813, 21778990100354694109, 3282023961944314679879, 8571542027796314659017, 1981036237660884203751, 9701333454757677085955, 11028779045287908657591, 1596656699096455337227, 16291839244893107541221, 19869532181650447082199, 22146268654327221320607, 64753450748648241530305, 5174349635853794878205, 43287261867901339110879, 96243143233929949076987, 62092354129317384599463, 113215062252403375519389, 170133066745866965240647]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, false, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true]

#time def chartRows036_p02 : List Int :=
  decoded (raw_ints% [90447846863552350275655, 311289585692193304022213, 119010358622780974320721, 79064164817008954182103, 537926620891211856570103, 455639483409824907783119, 509364109131983232525037, 845993233919027165987435, 255022121826326247849623, 1130258164225956356368461, 792268608196868841245517, 171374553102895717402093, 2288398705690472073607779, 2176188975762788692147675, 1751152219319929480211885, 3135072586885849331114043, 479441581681693010769831, 3359490785792839324359889, 3560109343328708543049833, 1951770776855798698901829, 8048497113912764700787895, 8140304995858039287300771, 4967829352265749168507893, 9548025004795079912758831, 271170920967357223, 2261139304627596839, 3843826010899875, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 7, 0, 0] [false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, false, false]

#time def chartRows036 : List Int := chartRows036_p00 ++ chartRows036_p01 ++ chartRows036_p02

#time def chartRows037_p00 : List Int :=
  decoded (raw_ints% [1807647280605818961, 1906304277510607753, 641588230206750121, 42599555622253599697, 29190774087112787, 568580788433326091, 18256123700616380319, 37649785490365732009, 467428897660123781, 1137139673006879101, 4564125053220674877, 2353110224156622433, 56452310502728601, 3812678440726884857, 20530403046630138521, 21299790850119861443, 3544980111619015469, 4247543592260020167, 12940928547168234611, 54907347325486648077, 4046870104857367249, 8796270067187331939, 37520577415670219189, 80994974644381352289, 15452619737700843291, 43413616492169481041, 30533468681542898489, 17750141408865687151, 23914126649611270501, 108167837404011196537, 124347810400009181271, 146791292583553087393]) [1, 2, 6, 1, 5, 2, 1, 1, 1, 1, 3, 5, 6, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows037_p01 : List Int :=
  decoded (raw_ints% [105226548471876467779, 272630657879756443267, 69350653042777047513, 947011738330630257857, 208060320319012574127, 999649635973951537709, 1214870441919034954339, 3491572326038046219809, 2228889432871829090041, 4754333421543490691139, 534500144508364292611, 92067272055307325511, 3699671747526672464717, 38809464676871059224303, 8293796401167946427939, 21413629960986045655677, 50250444806400567820911, 6423611176376034400453, 36671464098837602053859, 94483946951595219336563, 44802565948701843949439, 133431994621412741422939, 33988241106672084029751, 159532819938478194708409, 404768159497244157714911, 287354429079602365533841, 230192525143987880792019, 2788090774456664230813, 162216296366343636130509, 1171046898836502222846463, 540720617052532647037931, 84970615747996907112247]) [1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 2, 9, 2, 1, 1, 2] [true, false, true, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false]

#time def chartRows037_p02 : List Int :=
  decoded (raw_ints% [2097996771704874058885801, 934674673393859892753393, 235213593423128585513611, 3210337477120215822577743, 97715930320874477377381, 1945049852985886915687749, 3197978076522906923975641, 1189587117936161776709031, 8314741298514430083598701, 8172607959093003600294461, 1474622666139629744660527, 339785017097769239217529, 133249265176231098203441, 10588860230104212400192343, 13147237841663100276613281, 4228434138058703427531523, 27360473515903157312728331, 14164781511080730018380753, 7639614897824952910871289, 30461554976148265581890803, 436092445553378331219411, 12323514106671941926570259, 43511888202659819796909731, 34144089784965841765511791, 22338470647221822833, 46412164177274815203, 73032694207097625, 0, 0]) [1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 3, 6, 4, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 0, 0, 7, 0, 0] [false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true, false, false, false]

#time def chartRows037 : List Int := chartRows037_p00 ++ chartRows037_p01 ++ chartRows037_p02

#time def chartRows038_p00 : List Int :=
  decoded (raw_ints% [2005490473451260043, 9633724811508479185, 22080970589066763671, 92606456648416345903, 167521196557083485, 2675924865316658953, 2425674416173396211, 80296806971591207765, 334867590295634485, 2675965337856551023, 9702522861875052359, 80296847444131099835, 2006579762902347023, 9633595708550607583, 22081360667243720711, 92606408490538258441, 4950701002154644567, 21407682253451958011, 29038641432300712301, 123647686452540824035, 4749850243120160927, 51912588751616154275, 21744521460347839361, 196967957457608936321, 1747655423561304125, 125766165772946052499, 5059451886494804161, 374646711982171143095, 60341491732743998645, 588683583497062500931, 169255208693641731221, 1089096461252179696525]) [1, 0, 1, 0, 3, 0, 4, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 5, 0, 5, 0, 1, 0, 1, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows038_p01 : List Int :=
  decoded (raw_ints% [440038113254593637641, 2107479889509124768631, 669634813680979367507, 3785259934258366966087, 72941385704199593419, 4209052486255775838913, 569183774550691624963, 1683687337511715895805, 3491607471022378232981, 36810135354794703424505, 1769708836287398235703, 39335500503538763367613, 24010767641972383987285, 17601506909615114203337, 34533400256591936924653, 93747142767948580995455, 37403243316374410237195, 228054603688471838214227, 21140924582189910674743, 116705954010908143015435, 88629442348847700863561, 274507345653048402359867, 96760601715939950644787, 619267903352428383589529, 29353416764679202832893, 904182668908572052769381, 63341605267714622921281, 10407419903095266819985, 846614219488833831833359, 1581994453569723703155125, 710661465476692151479807, 2496584542381391022744491]) [1, 0, 1, 0, 5, 0, 3, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 3, 0, 3, 0, 1, 0, 1, 0] [true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false]

#time def chartRows038_p02 : List Int :=
  decoded (raw_ints% [228647652466660771843165, 2719053676004827899220991, 1328628032498865211470001, 1359525319946286826678625, 777093147640085046842005, 6303260488019765015872199, 3922641036187765132307, 7662788844078306088414565, 71066172783788065353503, 6698756690882004693029921, 2487316227760449902201099, 7267292641216066411256843, 9522864590307192618983929, 20156945563277723492447537, 4690364480353868945288737, 19588409612943661774220615, 969084037095762123772673, 14058189451315906930559915, 15182313107756823688045339, 25687165724905478336108237, 12759611057907311898544595, 55362051093340046732045267, 4683912485481018992635589, 43733074819750475326496945, 12043230531259011857, 99843927206957837, 73032694207097625, 0, 0]) [1, 0, 1, 0, 3, 0, 10, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 9, 7, 0, 0] [true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, false]

#time def chartRows038 : List Int := chartRows038_p00 ++ chartRows038_p01 ++ chartRows038_p02

#time def chartRows039_p00 : List Int :=
  decoded (raw_ints% [1873928755450195685, 4013488549119945105, 16140789971517949391, 33975873251795309611, 445266484910338591, 1159489060168271703, 13821594731157415115, 28802895642507092803, 445483604934329461, 1159476553143276381, 13821811851181405985, 28802883135482097481, 1873252381328232431, 4013528437131575715, 16140547837443967877, 33975888125756949577, 3835068506672357107, 10256954395922114655, 21848868725444557415, 48246370958810639947, 10970519397171282665, 24527802981802747385, 36654456629288197187, 83031128336535501987, 23279498662590572333, 106764283050071146509, 70904474689050052185, 214323214368409395881, 155999049377789865687, 372205066774595572827, 250183022729430490205, 693292564193076115217]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true]

#time def chartRows039_p01 : List Int :=
  decoded (raw_ints% [409132536131020841947, 603398671459579198185, 815314608238241197839, 462098959508092489859, 2181061464558989945951, 5783781827881498622775, 956614320189727906165, 5925081539832985331101, 7614573262776038195595, 3635102295382300749315, 10752249047524756047711, 15343965663096784703191, 10140003399346464838511, 31874063318645737377883, 8226818910954329404795, 12894995360166651925377, 51082693101374583274339, 42817615928225692831479, 52995877589766718708055, 87586674607038082134739, 26670157745644245724231, 112688052768393908884775, 77408412945497056258163, 17716237766869866081443, 223118483146873909595427, 217914590573683805011795, 172380227947021099061495, 312886405575207847815127, 37077942892024454891495, 302478361204463583622275, 358420768201870553765427, 228322634944428069204647]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false]

#time def chartRows039_p02 : List Int :=
  decoded (raw_ints% [753919319771752167056987, 786877410368315305720351, 432576494461906068183055, 861033136628350820137979, 28838238301101822435233, 663284401504531732628567, 1215334052534760057675275, 984626145492134393229763, 2138164599383019277184587, 2308948668602647740380835, 893992308547157397074079, 1987606924615045079779639, 370406376740358748827729, 1226569261722730913614195, 3402563284670535423086395, 3069986331494961906546279, 5332115876309198602068435, 5867511113844538411764335, 1559146214898304430154311, 4024094044072307418832251, 1441196851811038368219529, 1914319126393373858727303, 8332458943018541400442275, 7977286031523471971869283, 4503679681742036269, 9497340450228813679, 24344231402365875, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 7, 0, 0] [true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, false, false]

#time def chartRows039 : List Int := chartRows039_p00 ++ chartRows039_p01 ++ chartRows039_p02

#time def chartRows040_p00 : List Int :=
  decoded (raw_ints% [534962493739814025, 2854313930980866837, 4460448513685171145, 19269078401805536311, 22319037277274191, 713565507527674601, 468366715215895449, 15701198963296994873, 11156348915532905, 713571323360090423, 117090093942421767, 15701204779129410695, 535120456281230991, 2854295386396579179, 4460505045087254015, 19269071488886080297, 1605552891185590717, 7135670588417980315, 6601178392554075723, 29259037463700639791, 1694722174882783945, 29255841947527218791, 5798087816752617165, 65650549999645838897, 10435700178405246147, 99184010920027744913, 17928510170040647257, 194090402867200802601, 54051765856641192435, 124157411145218120179, 110780186553532979243, 169117002642010427335]) [1, 0, 1, 0, 4, 0, 4, 0, 5, 0, 6, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, true]

#time def chartRows040_p01 : List Int :=
  decoded (raw_ints% [253132343215310997343, 1352892438307122591947, 88300390805136825665, 1307932846810330284791, 879569841536271279, 1059622552164756874695, 38816007867299675397, 3720447837282209751433, 124358603314604712755, 6522574492117038056477, 143490367871236712545, 1742504102670071430349, 5433516356816504442093, 9795635106832265484361, 5280462240363448443773, 18060713701619374971187, 2066266433317581101865, 20203486515915896576143, 8647712163862371784001, 7652862292535743879405, 10752235003048619407253, 43774224616647616018299, 7461512137776224066185, 56324848840027768715037, 650490914432221356289, 47447610103367989084035, 17563256226392622117149, 52651463353307395649301, 66350116451736342473385, 142240768575133204322439, 32524585827815540951665, 137036915325193797757173]) [1, 0, 1, 0, 11, 0, 6, 0, 4, 0, 4, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0] [false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true]

#time def chartRows040_p02 : List Int :=
  decoded (raw_ints% [8239553842796076663091, 90201390965914804039833, 107114256122347960088141, 189076292934412198039779, 21628826887905412479925, 380517557426006320637661, 7209600642262407886021, 281642655457508926637715, 667123141598684337843, 140821740536211004769867, 17087706331478647534345, 521338472347304242505509, 399244117764085899853171, 889641913590587573591695, 83144935398111741681699, 509125181779494335856053, 133849559124731571507305, 171934523213487041656177, 616238612286929213042175, 1226832572156594867791571, 419438879613518042261979, 1881842852780973793221941, 44394793907687649987239, 826944803837865967086547, 2497705503712492585, 5530848083196600787, 24344231402365875, 0, 0]) [1, 0, 1, 0, 4, 0, 4, 0, 7, 0, 5, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 6, 0, 0] [true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, true, false, false]

#time def chartRows040 : List Int := chartRows040_p00 ++ chartRows040_p01 ++ chartRows040_p02

#time def chartRows041_p00 : List Int :=
  decoded (raw_ints% [41037898796988671961, 90261943602461257869, 237937708480144556703, 516900720295617916279, 8198741470143783035, 24617227308435272941, 188701068213012101707, 402021549384721385469, 8200927120405692149, 24617102545487849827, 188703253863274010821, 402021424621773962355, 41031092320308098391, 90262341353712953667, 237935273303987801361, 516900868520974765849, 90261570946404018403, 369259486932751286315, 369227936570699918155, 976422696807439005831, 516964739652386437433, 611332576520259433311, 976454247169490373991, 160521708548794322423, 1321139255829860839975, 545692354436468414011, 2814558242651737651399, 337453472618536399671, 5342012669057981773427, 14417671820051927488431, 1206315170576383282053, 12809428747976573119085]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1, 0, 3, 0, 0, 0, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true, false, true, true, true, true, false, true, false, true, false]

#time def chartRows041_p01 : List Int :=
  decoded (raw_ints% [19472457557817752269983, 13613506369426379022391, 26020785397452117325463, 40840606937454879629907, 17059915045840728268611, 59451287138354052486315, 28433327909429141326835, 4997173831472793834017, 104255201742844400705391, 100464057870730803289459, 92881788879255987647167, 164912518840557649609791, 24642202790067923100475, 157330628944736639716379, 172494787832032465252083, 108045947766551813182871, 369632054052181833937199, 390754007139820603452467, 221779469010217291785591, 440038688318005429985975, 17601703385209615930061, 156653510658321955639189, 609013226447608741652851, 8085713658455970658751, 1031449503455888888354077, 566182281320611143552375, 404834573623070530771165, 116023238727085509527883, 219431821755876413431407, 491669816075270284042977, 1655715898834835832556649, 1568880656382636079284837]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6, 0, 1, 0, 3, 0, 0, 0, 0] [false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true]

#time def chartRows041_p02 : List Int :=
  decoded (raw_ints% [2453652779118182283302845, 2740185573076187735071593, 578505058527470037314789, 1662974732768821939829733, 792497409671887316968903, 582128620274293759818731, 3824655247317539637586537, 3821031685570715915082595, 5202904839010544436878113, 5854919060777799008978731, 585752182021117482322673, 2616015995481376853714867, 2096525853206396461170139, 357824348671087444854785, 7885182874238058380370925, 8113110707588088417838813, 10111605242765512248927961, 11410372602727089112811929, 129896515321057407386897, 3655086243810088139827901, 4694060573129550188938075, 287603463234410573527553, 14935562331216119845252933, 1955083221625749799961867, 34871950909641653583, 151790665974519793537, 559917322254415125, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 2, 1, 6, 0, 0] [false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false, false, true, false, false, false]

#time def chartRows041 : List Int := chartRows041_p00 ++ chartRows041_p01 ++ chartRows041_p02

#time def chartRows042_p00 : List Int :=
  decoded (raw_ints% [49226837800384087703, 98471139447885945459, 279027603019682856541, 344676145050959590883, 16418357032834334531, 512869122152448779, 213382408186464434307, 14362074605887205281, 16416304230539313053, 128217736311268283, 213380355384169412829, 14362078252072453987, 49233229563125069321, 98470953492438261453, 279029889177833795203, 344676075773439865469, 279001050612963594117, 1312940497141081202579, 607264169353922458641, 3085528614204593710267, 5513321612125226133, 722104717378072756957, 795985193159457498891, 3676364393967602155889, 1206258050347547120561, 13194976117995674274699, 28710137006037574579, 10240716441406144875767, 9075649082957514737479, 14704845418948698479923, 11603005731676759276917, 38140537978350517630389]) [1, 2, 1, 2, 1, 7, 1, 6, 1, 9, 1, 6, 1, 2, 1, 2, 1, 0, 1, 0, 8, 0, 2, 0, 2, 0, 3, 0, 1, 0, 1, 0] [false, true, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false, true, false]

#time def chartRows042_p01 : List Int :=
  decoded (raw_ints% [5858968847661425236157, 22516841384565923531837, 14819685966972848778239, 3905850314083684523319, 42391394156766511328839, 43425327524407189542999, 33430677037455087786757, 62036318594889428551517, 3791102112380068807837, 48939591604241210036807, 72030969081841530307759, 56522054515055408057709, 132688373140488793786779, 145144845686082613902969, 64448506171027332286857, 137562382775268415882067, 21121842978807571424543, 155976809962971404134329, 218258722290323697498179, 409437646959730655435743, 165454434530537670385097, 741611288723002796683313, 5720518986996504490467, 488150451726243545381899, 25228848394914921641867, 178361524476129412377689, 261676283216339549592567, 1051400215973116929687523, 711101180696524126282819, 1607818560815665275872793, 86833220684185340530217, 734779869318677758562959]) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 2, 0, 5, 0, 3, 0, 2, 0, 1, 0, 1, 0] [true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false]

#time def chartRows042_p02 : List Int :=
  decoded (raw_ints% [286531593002276709874623, 2826980934358107950867, 1084465994382986176687659, 281516880029360447501001, 1374627756600537000459809, 778685846826454403241087, 3630169215274113897527, 238267934242598371846021, 652019467107020321919353, 56081125661790720404289, 2030277392922831436276689, 1073034906730843495491397, 2454342188167414762681359, 694425425520608279077391, 227954671862436995514683, 32466852331072792782387, 1298738494937057029175763, 932917971404221348959041, 3525126011242034796342439, 7527260650163416950614553, 1029725301659326868018461, 9298624013561676600382623, 352481649770892176722179, 838445391994038300809029, 82063610205016736061, 221573642249422768171, 559917322254415125, 0, 0]) [1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 1, 0, 1, 0, 3, 0, 2, 0, 2, 2, 7, 0, 0] [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false, true, false, true, false, true, true, true, false, true, true, false, false]

#time def chartRows042 : List Int := chartRows042_p00 ++ chartRows042_p01 ++ chartRows042_p02

#time def chartRows043_p00 : List Int :=
  decoded (raw_ints% [369282178850173053909, 180621505825159248795, 1025663157935908970043, 12947623884629140435221, 41013463214857425675, 205145405434787972067, 615367515870878490459, 1435885268371999488435, 41018294410311961125, 205145131970894319117, 615372347066333025909, 1435884994908105835485, 369267138336022141659, 6892873425340324848411, 1025657779812667128693, 20021114440372326085227, 3774663141010899870639, 1641224142312612872793, 9354362813605656952047, 25272763723400038060845, 10667618977678501180707, 14852591686561100745075, 2461406976938055641979, 4472353395644622224031, 41849791931898300489525, 19283757933144653044453, 50056003932638746028253, 21540528205497499118795, 17232171108896489981945, 159193113189655184136367, 74673624755640556535833, 90266144186903420991805]) [3, 0, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 1, 3, 1, 2, 1, 3, 1, 0, 1, 0] [false, false, true, false, true, false, false, true, true, false, true, false, false, true, false, true, true, true, true, false, true, false, false, false, false, true, false, true, false, true, true, false]

#time def chartRows043_p01 : List Int :=
  decoded (raw_ints% [83289281451880252331001, 360728427601694960025107, 54568554628508219054057, 429655396604446723169669, 5169565342638730359579, 16514278427115278086491, 143027401423027201744637, 65769421171537154226365, 225742639554079937742087, 15893697511209934084985, 77545672788414005637871, 94408715772372874626497, 62282606593196745594925, 290485761120738854618531, 365570918935690688974883, 1481980605775679923832485, 991101466601685712482405, 2256604144916397824721439, 135394415543910843342789, 1065109300261456755507485, 398966424899419890946479, 27982579551130070275569, 1525462307045016446771673, 401222890871666787390831, 1900964634605045775477639, 1082762011765571107876743, 23464097339390562240513, 154149404786683801685325, 928085202751612771498173, 439513209380911373014985, 2805585740017267984735299, 6003756494736666218004557]) [2, 0, 2, 0, 2, 4, 2, 3, 2, 6, 2, 3, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 3, 1, 2, 1, 3, 1, 0, 1, 0] [true, false, true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, false, false, true, false, true, true, true, true, false, true, false]

#time def chartRows043_p02 : List Int :=
  decoded (raw_ints% [414702728840919993182375, 7534581944006750681859467, 52006139005190101346809, 1091312239889173090839925, 228427935662955445304955, 196731048296801670112271, 591124525498685337140521, 1274967821283792141699695, 337413775935014606840007, 1525435776237455438935429, 72362454645805784382731, 53736906656861627123463, 101052152040088114220089, 3543428611401991951878869, 233577812684692525448727, 16176810074556528480350005, 8322529534123881067646939, 18715060652615729203669655, 2385629337069099401755173, 1005178033342791228559219, 5303670449650786723418625, 1660234637615163548795201, 11240570646705568389310391, 3043852646216699021286405, 87184083549130126497, 6383501189401990593213, 2799586611272075625, 0, 0]) [4, 0, 4, 0, 4, 3, 4, 3, 5, 3, 5, 3, 6, 0, 6, 0, 1, 0, 1, 0, 1, 2, 1, 3, 6, 0, 8, 0, 0] [true, false, false, false, false, true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, false, false]

#time def chartRows043 : List Int := chartRows043_p00 ++ chartRows043_p01 ++ chartRows043_p02

#time def chartRows044_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows044 : List Int := chartRows044_p00 ++ chartRows044_p01 ++ chartRows044_p02

#time def chartRows045_p00 : List Int :=
  decoded (raw_ints% [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows045 : List Int := chartRows045_p00 ++ chartRows045_p01 ++ chartRows045_p02

#time def chartRows046_p00 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p01 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046_p02 : List Int :=
  decoded (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

#time def chartRows046 : List Int := chartRows046_p00 ++ chartRows046_p01 ++ chartRows046_p02

#time def chartRows : List (List Int) :=
  [chartRows000, chartRows001, chartRows002, chartRows003, chartRows004, chartRows005, chartRows006, chartRows007, chartRows008, chartRows009, chartRows010, chartRows011, chartRows012, chartRows013, chartRows014, chartRows015, chartRows016, chartRows017, chartRows018, chartRows019, chartRows020, chartRows021, chartRows022, chartRows023, chartRows024, chartRows025, chartRows026, chartRows027, chartRows028, chartRows029, chartRows030, chartRows031, chartRows032, chartRows033, chartRows034, chartRows035, chartRows036, chartRows037, chartRows038, chartRows039, chartRows040, chartRows041, chartRows042, chartRows043, chartRows044, chartRows045, chartRows046]

#time def graph : KernelGraph 1 1 0 :=
  ⟨graphScale.getD 0 0, fun j => pivTape.getD j.val ⟨0, by decide⟩,
    fun i => freeTape.getD i.val ⟨0, by decide⟩, fun j i => Mx tailRows j.val i.val⟩

-- kcost: 0.0282s shape-only conservative projection.
#time theorem check : graph.chartCheckAuto basis roles chartRows (2 ^ 1425) (2 ^ 1318) (2 ^ 0) (2 ^ 98) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 93 1 basis.matrix :=
  graph.chartCheckAuto_sound basis roles chartRows (2 ^ 1425) (2 ^ 1318) (2 ^ 0) (2 ^ 98) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 47 := by decide +kernel

#time def refs000 : List (Fin 47) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 93 1 basis.matrix :=
  verified.pickRows _

#time def refs001 : List (Fin 47) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩]
#time def chart001 : Chart :=
  (graph.chart chartRows).pickRows (refs001.map (Fin.cast unionLength.symm))

#time theorem chartSound001 : chart001.Sound 93 1 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart267

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart268
open CatalanMeasure.GenD.Uniform.W.Prof

def signedLit (m : Int) (e : Nat) (neg : Bool) : Int :=
  if m = 0 then 0 else if neg then -(m * 2 ^ e) else m * 2 ^ e

def decoded (ms : List Int) (es : List Nat) (bs : List Bool) : List Int :=
  List.zipWith (fun q b => signedLit q.1 q.2 b) (ms.zip es) bs

def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + (2 : Int) ^ (48 : Nat) * wordMag as

open CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankBasis023 (basis)

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

-- kcost: 0.0168s shape-only conservative projection.
#time theorem check : graph.chartCheckAuto basis roles chartRows (2 ^ 62) (2 ^ 1) (2 ^ 0) (2 ^ 49) = true := by
  decide +kernel

#time theorem verified : (graph.chart chartRows).Sound 39 27 basis.matrix :=
  graph.chartCheckAuto_sound basis roles chartRows (2 ^ 62) (2 ^ 1) (2 ^ 0) (2 ^ 49) check

#time theorem unionLength : (graph.chart chartRows).rows.length = 28 := by decide +kernel

#time def refs000 : List (Fin 28) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩]
#time def chart000 : Chart :=
  (graph.chart chartRows).pickRows (refs000.map (Fin.cast unionLength.symm))

#time theorem chartSound000 : chart000.Sound 39 27 basis.matrix :=
  verified.pickRows _

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Finite.RankChart268
