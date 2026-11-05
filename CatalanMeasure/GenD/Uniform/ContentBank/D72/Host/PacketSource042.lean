module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.ResponseRow
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostGeneric
public import CatalanMeasure.CellCert.RawInts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P042
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042
open CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD.Uniform.W.Charts6
abbrev packet := CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P042.packet
def wordMag : List Int → Int
  | [] => 0
  | a :: as => a + 2 ^ (48 : Nat) * wordMag as
def value (ws : List Int) (e : Nat) (neg : Bool) : Int :=
  if neg then -(wordMag ws * 2 ^ e) else wordMag ws * 2 ^ e
def target (t : RowTerm packet) : List Int :=
  (List.finRange packet.n).map fun i => t.coeff * t.entry i.val
abbrev blockCount : Nat := 8
abbrev slotCount : Nat := 34
abbrev k0 : Int := -1
abbrev ah : Nat := 0
abbrev aq : Nat := 0
theorem slots_eq : slotCount = blockCount * 4 + 2 + 0 := by decide

def slotsTape : List (Option (Fin slotCount)) := [some ⟨0, by decide⟩, some ⟨1, by decide⟩, some ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨4, by decide⟩, some ⟨5, by decide⟩, some ⟨6, by decide⟩, some ⟨7, by decide⟩, some ⟨8, by decide⟩, some ⟨9, by decide⟩, some ⟨10, by decide⟩, some ⟨11, by decide⟩, some ⟨12, by decide⟩, some ⟨13, by decide⟩, some ⟨14, by decide⟩, some ⟨15, by decide⟩, some ⟨16, by decide⟩, some ⟨17, by decide⟩, some ⟨18, by decide⟩, some ⟨19, by decide⟩, some ⟨20, by decide⟩, some ⟨21, by decide⟩, some ⟨22, by decide⟩, some ⟨23, by decide⟩, some ⟨24, by decide⟩, some ⟨25, by decide⟩, some ⟨26, by decide⟩, some ⟨27, by decide⟩, some ⟨28, by decide⟩, some ⟨29, by decide⟩, some ⟨30, by decide⟩, some ⟨31, by decide⟩, some ⟨32, by decide⟩, some ⟨33, by decide⟩, none, none]
def slots (c : Fin packet.n) : Option (Fin slotCount) := slotsTape.getD c.val none
def low : Fin packet.n := ⟨34, by decide⟩

#time def base000 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨0, by decide⟩, value (raw_ints% [105022345827153, 15101099612637]) 31 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check000 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 10 low none
    (target base000) = true := by decide +kernel

#time def base001 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [35007448609051, 5033699870879]) 33 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check001 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 10 low none
    (target base001) = true := by decide +kernel

#time def base002 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [245052140263357, 35235899096153]) 33 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check002 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 10 low none
    (target base002) = true := by decide +kernel

#time def base003 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [172206467368759, 105707697288461]) 32 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check003 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 10 low none
    (target base003) = true := by decide +kernel

#time def base004 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [245052140263357, 35235899096153]) 32 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check004 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 10 low none
    (target base004) = true := by decide +kernel

#time def base005 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [35007448609051, 5033699870879]) 33 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check005 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 10 low none
    (target base005) = true := by decide +kernel

#time def base006 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [105022345827153, 15101099612637]) 32 true⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check006 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 10 low none
    (target base006) = true := by decide +kernel

#time def base007 : RowTerm packet := ⟨⟨1, by decide⟩,
  ⟨7, by decide⟩, value (raw_ints% [105022345827153, 15101099612637]) 31 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check007 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 1 9 low (some ⟨35, by decide⟩)
    (target base007) = true := by decide +kernel

#time def base008 : RowTerm packet := ⟨⟨10, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [105022345827153, 15101099612637]) 33 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check008 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 2 9 low none
    (target base008) = true := by decide +kernel

#time def base009 : RowTerm packet := ⟨⟨10, by decide⟩,
  ⟨2, by decide⟩, value (raw_ints% [245052140263357, 35235899096153]) 33 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check009 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 3 9 low none
    (target base009) = true := by decide +kernel

#time def base010 : RowTerm packet := ⟨⟨10, by decide⟩,
  ⟨3, by decide⟩, value (raw_ints% [172206467368759, 105707697288461]) 32 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check010 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 4 9 low none
    (target base010) = true := by decide +kernel

#time def base011 : RowTerm packet := ⟨⟨10, by decide⟩,
  ⟨4, by decide⟩, value (raw_ints% [172206467368759, 105707697288461]) 32 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check011 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 5 9 low none
    (target base011) = true := by decide +kernel

#time def base012 : RowTerm packet := ⟨⟨10, by decide⟩,
  ⟨5, by decide⟩, value (raw_ints% [245052140263357, 35235899096153]) 33 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check012 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 6 9 low none
    (target base012) = true := by decide +kernel

#time def base013 : RowTerm packet := ⟨⟨10, by decide⟩,
  ⟨6, by decide⟩, value (raw_ints% [105022345827153, 15101099612637]) 33 false⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check013 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 7 9 low none
    (target base013) = true := by decide +kernel

#time def base014 : RowTerm packet := ⟨⟨9, by decide⟩,
  ⟨1, by decide⟩, value (raw_ints% [105022345827153, 15101099612637]) 31 true⟩
-- kcost: 0.216 s provisional; 36 ambient coordinates, 1 sparse source calls each.
#time theorem check014 : foldedTargetCheck (b := blockCount) (ex := 0) slots_eq k0 ah aq slots 8 9 low none
    (target base014) = true := by decide +kernel

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.PacketSource042
