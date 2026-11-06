module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.ResponseRow
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostGeneric
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P031
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource031
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6
abbrev packet := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P031.packet
def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + 2 ^ (48 : Nat) * wordMag as
def value (ws : List Int) (e : Nat) (neg : Bool) : Int :=
  if neg then -(wordMag ws * 2 ^ e) else wordMag ws * 2 ^ e
def target (t : RowTerm packet) : List Int :=
  (List.finRange packet.n).map fun i => t.coeff * t.entry i.val
abbrev blockCount : Nat := 14
abbrev slotCount : Nat := 58
abbrev k0 : Int := -2
abbrev ah : Nat := 0
abbrev aq : Nat := 0
theorem slots_eq : slotCount = blockCount * 4 + 2 + 0 := by decide

def slotsTape : List (Option (Fin slotCount)) := [some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨25, by decide⟩, some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨29, by decide⟩, some ⟨30, by decide⟩, some ⟨31, by decide⟩, some ⟨33, by decide⟩, some ⟨34, by decide⟩, some ⟨35, by decide⟩, some ⟨37, by decide⟩, some ⟨38, by decide⟩, some ⟨39, by decide⟩, some ⟨41, by decide⟩, some ⟨42, by decide⟩, some ⟨43, by decide⟩, some ⟨45, by decide⟩, some ⟨46, by decide⟩, some ⟨47, by decide⟩, some ⟨49, by decide⟩, some ⟨50, by decide⟩, some ⟨51, by decide⟩, some ⟨53, by decide⟩, some ⟨54, by decide⟩, some ⟨55, by decide⟩, some ⟨57, by decide⟩, none, none]
def slots (c : Fin packet.n) : Option (Fin slotCount) := slotsTape.getD c.val none
def low : Fin packet.n := ⟨43, by decide⟩

#time def base000 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨0, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 28 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check000 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 16 low none
    (target base000) = true := by decide +kernel

#time def base001 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 29 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check001 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 16 low none
    (target base001) = true := by decide +kernel

#time def base002 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 29 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check002 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 16 low none
    (target base002) = true := by decide +kernel

#time def base003 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 31 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check003 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 16 low none
    (target base003) = true := by decide +kernel

#time def base004 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 31 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check004 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 16 low none
    (target base004) = true := by decide +kernel

#time def base005 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 31 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check005 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 16 low none
    (target base005) = true := by decide +kernel

#time def base006 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [212827307226293, 35200698397]) 30 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check006 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 16 low none
    (target base006) = true := by decide +kernel

#time def base007 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨7, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 33 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check007 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 16 low none
    (target base007) = true := by decide +kernel

#time def base008 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨8, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 32 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check008 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 16 low none
    (target base008) = true := by decide +kernel

#time def base009 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨9, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 33 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check009 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 16 low none
    (target base009) = true := by decide +kernel

#time def base010 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨10, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 31 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check010 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 16 low none
    (target base010) = true := by decide +kernel

#time def base011 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨11, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 33 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check011 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 16 low none
    (target base011) = true := by decide +kernel

#time def base012 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨12, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 32 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check012 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 16 low none
    (target base012) = true := by decide +kernel

#time def base013 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨13, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 28 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check013 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 1 15 low (some ⟨44, by decide⟩)
    (target base013) = true := by decide +kernel

#time def base014 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 29 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check014 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 15 low none
    (target base014) = true := by decide +kernel

#time def base015 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 29 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check015 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 15 low none
    (target base015) = true := by decide +kernel

#time def base016 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 31 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check016 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 15 low none
    (target base016) = true := by decide +kernel

#time def base017 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 31 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check017 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 15 low none
    (target base017) = true := by decide +kernel

#time def base018 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 31 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check018 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 15 low none
    (target base018) = true := by decide +kernel

#time def base019 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [212827307226293, 35200698397]) 31 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check019 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 15 low none
    (target base019) = true := by decide +kernel

#time def base020 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨7, by decide⟩, value (raw_ints% [212827307226293, 35200698397]) 34 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check020 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 15 low none
    (target base020) = true := by decide +kernel

#time def base021 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨8, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 34 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check021 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 15 low none
    (target base021) = true := by decide +kernel

#time def base022 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨9, by decide⟩, value (raw_ints% [164767427978983, 11733566132]) 33 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check022 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 15 low none
    (target base022) = true := by decide +kernel

#time def base023 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨10, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 33 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check023 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 15 low none
    (target base023) = true := by decide +kernel

#time def base024 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨11, by decide⟩, value (raw_ints% [66156125581845, 1066687830]) 33 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check024 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 15 low none
    (target base024) = true := by decide +kernel

#time def base025 : RowTerm packet := ⟨⟨8, by decide⟩,
  ⟨12, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 32 true⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check025 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 15 low none
    (target base025) = true := by decide +kernel

#time def base026 : RowTerm packet := ⟨⟨7, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [5088932737065, 82052910]) 31 false⟩
-- kcost: 0.270 s provisional; 45 ambient coordinates, 1 sparse source calls each.
#time theorem check026 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 15 low none
    (target base026) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource031
