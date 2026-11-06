module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.ResponseRow
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostGeneric
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P037
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource037
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6
abbrev packet := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P037.packet
def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + 2 ^ (48 : Nat) * wordMag as
def value (ws : List Int) (e : Nat) (neg : Bool) : Int :=
  if neg then -(wordMag ws * 2 ^ e) else wordMag ws * 2 ^ e
def target (t : RowTerm packet) : List Int :=
  (List.finRange packet.n).map fun i => t.coeff * t.entry i.val
abbrev blockCount : Nat := 10
abbrev slotCount : Nat := 42
abbrev k0 : Int := -1
abbrev ah : Nat := 0
abbrev aq : Nat := 0
theorem slots_eq : slotCount = blockCount * 4 + 2 + 0 := by decide

def slotsTape : List (Option (Fin slotCount)) := [some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨25, by decide⟩, some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨29, by decide⟩, some ⟨30, by decide⟩, some ⟨31, by decide⟩, some ⟨33, by decide⟩, some ⟨34, by decide⟩, some ⟨35, by decide⟩, some ⟨37, by decide⟩, some ⟨38, by decide⟩, some ⟨39, by decide⟩, some ⟨41, by decide⟩, none, none]
def slots (c : Fin packet.n) : Option (Fin slotCount) := slotsTape.getD c.val none
def low : Fin packet.n := ⟨31, by decide⟩

#time def base000 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨0, by decide⟩, value (raw_ints% [15604702432017, 13866941793]) 31 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check000 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 1 12 low none
    (target base000) = true := by decide +kernel

#time def base001 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 31 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check001 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 12 low none
    (target base001) = true := by decide +kernel

#time def base002 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 31 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check002 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 12 low none
    (target base002) = true := by decide +kernel

#time def base003 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 31 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check003 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 12 low none
    (target base003) = true := by decide +kernel

#time def base004 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 33 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check004 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 12 low none
    (target base004) = true := by decide +kernel

#time def base005 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [226986541268055, 3203263554195]) 33 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check005 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 12 low none
    (target base005) = true := by decide +kernel

#time def base006 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 32 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check006 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 12 low none
    (target base006) = true := by decide +kernel

#time def base007 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨7, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 33 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check007 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 12 low none
    (target base007) = true := by decide +kernel

#time def base008 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨8, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 33 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check008 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 12 low none
    (target base008) = true := by decide +kernel

#time def base009 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨9, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 32 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check009 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 12 low none
    (target base009) = true := by decide +kernel

#time def base010 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨10, by decide⟩, value (raw_ints% [15604702432017, 13866941793]) 31 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check010 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 12 low (some ⟨32, by decide⟩)
    (target base010) = true := by decide +kernel

#time def base011 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨0, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 31 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check011 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 1 11 low none
    (target base011) = true := by decide +kernel

#time def base012 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 31 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check012 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 11 low none
    (target base012) = true := by decide +kernel

#time def base013 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 31 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check013 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 11 low none
    (target base013) = true := by decide +kernel

#time def base014 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 33 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check014 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 11 low none
    (target base014) = true := by decide +kernel

#time def base015 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [226986541268055, 3203263554195]) 33 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check015 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 11 low none
    (target base015) = true := by decide +kernel

#time def base016 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [226986541268055, 3203263554195]) 32 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check016 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 11 low none
    (target base016) = true := by decide +kernel

#time def base017 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 32 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check017 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 11 low none
    (target base017) = true := by decide +kernel

#time def base018 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨7, by decide⟩, value (raw_ints% [233480203545905, 457609079170]) 33 false⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check018 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 11 low none
    (target base018) = true := by decide +kernel

#time def base019 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨8, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 32 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check019 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 11 low none
    (target base019) = true := by decide +kernel

#time def base020 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨9, by decide⟩, value (raw_ints% [171651726752187, 152536359723]) 31 true⟩
-- kcost: 0.198 s provisional; 33 ambient coordinates, 1 sparse source calls each.
#time theorem check020 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 11 low none
    (target base020) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource037
