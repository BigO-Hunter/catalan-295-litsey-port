module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.ResponseRow
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostGeneric
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource038
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6
abbrev packet := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038.packet
def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + 2 ^ (48 : Nat) * wordMag as
def value (ws : List Int) (e : Nat) (neg : Bool) : Int :=
  if neg then -(wordMag ws * 2 ^ e) else wordMag ws * 2 ^ e
def target (t : RowTerm packet) : List Int :=
  (List.finRange packet.n).map fun i => t.coeff * t.entry i.val
abbrev blockCount : Nat := 30
abbrev slotCount : Nat := 122
abbrev k0 : Int := -3
abbrev ah : Nat := 1
abbrev aq : Nat := 1
theorem slots_eq : slotCount = blockCount * 4 + 2 + 0 := by decide

def slotsTape : List (Option (Fin slotCount)) := [some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨25, by decide⟩, some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨29, by decide⟩, some ⟨30, by decide⟩, some ⟨31, by decide⟩, some ⟨33, by decide⟩, some ⟨34, by decide⟩, some ⟨35, by decide⟩, some ⟨37, by decide⟩, some ⟨38, by decide⟩, some ⟨39, by decide⟩, some ⟨41, by decide⟩, some ⟨42, by decide⟩, some ⟨43, by decide⟩, some ⟨45, by decide⟩, some ⟨46, by decide⟩, some ⟨47, by decide⟩, some ⟨49, by decide⟩, some ⟨50, by decide⟩, some ⟨51, by decide⟩, some ⟨53, by decide⟩, some ⟨54, by decide⟩, some ⟨55, by decide⟩, some ⟨57, by decide⟩, some ⟨58, by decide⟩, some ⟨59, by decide⟩, some ⟨61, by decide⟩, some ⟨62, by decide⟩, some ⟨63, by decide⟩, some ⟨65, by decide⟩, some ⟨66, by decide⟩, some ⟨67, by decide⟩, some ⟨69, by decide⟩, some ⟨70, by decide⟩, some ⟨71, by decide⟩, some ⟨73, by decide⟩, some ⟨74, by decide⟩, some ⟨75, by decide⟩, some ⟨77, by decide⟩, some ⟨78, by decide⟩, some ⟨79, by decide⟩, some ⟨81, by decide⟩, some ⟨82, by decide⟩, some ⟨83, by decide⟩, some ⟨85, by decide⟩, some ⟨86, by decide⟩, some ⟨87, by decide⟩, some ⟨89, by decide⟩, some ⟨90, by decide⟩, some ⟨91, by decide⟩, some ⟨93, by decide⟩, some ⟨94, by decide⟩, some ⟨95, by decide⟩, some ⟨97, by decide⟩, some ⟨98, by decide⟩, some ⟨99, by decide⟩, some ⟨101, by decide⟩, some ⟨102, by decide⟩, some ⟨103, by decide⟩, some ⟨105, by decide⟩, some ⟨106, by decide⟩, some ⟨107, by decide⟩, some ⟨109, by decide⟩, some ⟨110, by decide⟩, some ⟨111, by decide⟩, some ⟨113, by decide⟩, some ⟨114, by decide⟩, some ⟨115, by decide⟩, some ⟨117, by decide⟩, some ⟨118, by decide⟩, some ⟨119, by decide⟩, some ⟨121, by decide⟩, none]
def slots (c : Fin packet.n) : Option (Fin slotCount) := slotsTape.getD c.val none
def low : Fin packet.n := ⟨91, by decide⟩

#time def base000 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨0, by decide⟩, value (raw_ints% [62197]) 7 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check000 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 38 low none
    (target base000) = true := by decide +kernel

#time def base001 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [62197]) 8 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check001 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 38 low none
    (target base001) = true := by decide +kernel

#time def base002 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [62197]) 8 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check002 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 38 low none
    (target base002) = true := by decide +kernel

#time def base003 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [62197]) 13 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check003 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 38 low none
    (target base003) = true := by decide +kernel

#time def base004 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [1928107]) 13 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check004 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 38 low none
    (target base004) = true := by decide +kernel

#time def base005 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [1928107]) 14 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check005 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 38 low none
    (target base005) = true := by decide +kernel

#time def base006 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [55915103]) 14 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check006 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 38 low none
    (target base006) = true := by decide +kernel

#time def base007 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨7, by decide⟩, value (raw_ints% [55915103]) 16 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check007 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 38 low none
    (target base007) = true := by decide +kernel

#time def base008 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨8, by decide⟩, value (raw_ints% [167745309]) 16 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check008 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 38 low none
    (target base008) = true := by decide +kernel

#time def base009 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨9, by decide⟩, value (raw_ints% [167745309]) 17 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check009 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 38 low none
    (target base009) = true := by decide +kernel

#time def base010 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨10, by decide⟩, value (raw_ints% [838726545]) 17 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check010 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 38 low none
    (target base010) = true := by decide +kernel

#time def base011 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨11, by decide⟩, value (raw_ints% [838726545]) 20 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check011 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 15 38 low none
    (target base011) = true := by decide +kernel

#time def base012 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨12, by decide⟩, value (raw_ints% [19290710535]) 20 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check012 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 16 38 low none
    (target base012) = true := by decide +kernel

#time def base013 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨13, by decide⟩, value (raw_ints% [19290710535]) 21 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check013 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 17 38 low none
    (target base013) = true := by decide +kernel

#time def base014 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨14, by decide⟩, value (raw_ints% [19290710535]) 21 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check014 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 18 38 low none
    (target base014) = true := by decide +kernel

#time def base015 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨15, by decide⟩, value (raw_ints% [19290710535]) 23 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check015 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 19 38 low none
    (target base015) = true := by decide +kernel

#time def base016 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨16, by decide⟩, value (raw_ints% [19290710535]) 23 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check016 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 20 38 low none
    (target base016) = true := by decide +kernel

#time def base017 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨17, by decide⟩, value (raw_ints% [19290710535]) 24 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check017 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 21 38 low none
    (target base017) = true := by decide +kernel

#time def base018 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨18, by decide⟩, value (raw_ints% [838726545]) 24 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check018 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 22 38 low none
    (target base018) = true := by decide +kernel

#time def base019 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨19, by decide⟩, value (raw_ints% [838726545]) 28 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check019 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 23 38 low none
    (target base019) = true := by decide +kernel

#time def base020 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨20, by decide⟩, value (raw_ints% [167745309]) 28 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check020 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 24 38 low none
    (target base020) = true := by decide +kernel

#time def base021 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨21, by decide⟩, value (raw_ints% [167745309]) 29 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check021 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 25 38 low none
    (target base021) = true := by decide +kernel

#time def base022 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨22, by decide⟩, value (raw_ints% [55915103]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check022 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 26 38 low none
    (target base022) = true := by decide +kernel

#time def base023 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨23, by decide⟩, value (raw_ints% [55915103]) 29 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check023 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 27 38 low none
    (target base023) = true := by decide +kernel

#time def base024 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨24, by decide⟩, value (raw_ints% [1928107]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check024 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 28 38 low none
    (target base024) = true := by decide +kernel

#time def base025 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨25, by decide⟩, value (raw_ints% [1928107]) 29 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check025 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 29 38 low none
    (target base025) = true := by decide +kernel

#time def base026 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨26, by decide⟩, value (raw_ints% [62197]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check026 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 30 38 low none
    (target base026) = true := by decide +kernel

#time def base027 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨27, by decide⟩, value (raw_ints% [62197]) 31 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check027 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 31 38 low none
    (target base027) = true := by decide +kernel

#time def base028 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨28, by decide⟩, value (raw_ints% [62197]) 30 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check028 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 32 38 low none
    (target base028) = true := by decide +kernel

#time def base029 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨29, by decide⟩, value (raw_ints% [62197]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check029 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 33 38 low none
    (target base029) = true := by decide +kernel

#time def base030 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨0, by decide⟩, value (raw_ints% [62197]) 8 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check030 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 37 low none
    (target base030) = true := by decide +kernel

#time def base031 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [62197]) 8 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check031 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 37 low none
    (target base031) = true := by decide +kernel

#time def base032 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [62197]) 13 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check032 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 37 low none
    (target base032) = true := by decide +kernel

#time def base033 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [1928107]) 13 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check033 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 37 low none
    (target base033) = true := by decide +kernel

#time def base034 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [1928107]) 14 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check034 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 37 low none
    (target base034) = true := by decide +kernel

#time def base035 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [55915103]) 14 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check035 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 9 37 low none
    (target base035) = true := by decide +kernel

#time def base036 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [55915103]) 16 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check036 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 10 37 low none
    (target base036) = true := by decide +kernel

#time def base037 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨7, by decide⟩, value (raw_ints% [167745309]) 16 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check037 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 11 37 low none
    (target base037) = true := by decide +kernel

#time def base038 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨8, by decide⟩, value (raw_ints% [167745309]) 17 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check038 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 12 37 low none
    (target base038) = true := by decide +kernel

#time def base039 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨9, by decide⟩, value (raw_ints% [838726545]) 17 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check039 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 13 37 low none
    (target base039) = true := by decide +kernel

#time def base040 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨10, by decide⟩, value (raw_ints% [838726545]) 20 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check040 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 14 37 low none
    (target base040) = true := by decide +kernel

#time def base041 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨11, by decide⟩, value (raw_ints% [19290710535]) 20 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check041 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 15 37 low none
    (target base041) = true := by decide +kernel

#time def base042 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨12, by decide⟩, value (raw_ints% [19290710535]) 21 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check042 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 16 37 low none
    (target base042) = true := by decide +kernel

#time def base043 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨13, by decide⟩, value (raw_ints% [19290710535]) 21 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check043 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 17 37 low none
    (target base043) = true := by decide +kernel

#time def base044 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨14, by decide⟩, value (raw_ints% [19290710535]) 23 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check044 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 18 37 low none
    (target base044) = true := by decide +kernel

#time def base045 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨15, by decide⟩, value (raw_ints% [19290710535]) 23 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check045 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 19 37 low none
    (target base045) = true := by decide +kernel

#time def base046 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨16, by decide⟩, value (raw_ints% [19290710535]) 24 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check046 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 20 37 low none
    (target base046) = true := by decide +kernel

#time def base047 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨17, by decide⟩, value (raw_ints% [19290710535]) 24 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check047 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 21 37 low none
    (target base047) = true := by decide +kernel

#time def base048 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨18, by decide⟩, value (raw_ints% [838726545]) 28 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check048 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 22 37 low none
    (target base048) = true := by decide +kernel

#time def base049 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨19, by decide⟩, value (raw_ints% [838726545]) 28 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check049 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 23 37 low none
    (target base049) = true := by decide +kernel

#time def base050 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨20, by decide⟩, value (raw_ints% [167745309]) 29 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check050 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 24 37 low none
    (target base050) = true := by decide +kernel

#time def base051 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨21, by decide⟩, value (raw_ints% [167745309]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check051 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 25 37 low none
    (target base051) = true := by decide +kernel

#time def base052 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨22, by decide⟩, value (raw_ints% [55915103]) 29 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check052 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 26 37 low none
    (target base052) = true := by decide +kernel

#time def base053 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨23, by decide⟩, value (raw_ints% [55915103]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check053 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 27 37 low none
    (target base053) = true := by decide +kernel

#time def base054 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨24, by decide⟩, value (raw_ints% [1928107]) 29 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check054 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 28 37 low none
    (target base054) = true := by decide +kernel

#time def base055 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨25, by decide⟩, value (raw_ints% [1928107]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check055 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 29 37 low none
    (target base055) = true := by decide +kernel

#time def base056 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨26, by decide⟩, value (raw_ints% [62197]) 30 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check056 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 30 37 low none
    (target base056) = true := by decide +kernel

#time def base057 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨27, by decide⟩, value (raw_ints% [62197]) 30 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check057 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 31 37 low none
    (target base057) = true := by decide +kernel

#time def base058 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨28, by decide⟩, value (raw_ints% [62197]) 29 true⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check058 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 32 37 low none
    (target base058) = true := by decide +kernel

#time def base059 : RowTerm packet := ⟨⟨7, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [62197]) 28 false⟩
-- kcost: 1.104 s provisional; 92 ambient coordinates, 2 sparse source calls each.
#time theorem check059 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 33 37 low none
    (target base059) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource038
