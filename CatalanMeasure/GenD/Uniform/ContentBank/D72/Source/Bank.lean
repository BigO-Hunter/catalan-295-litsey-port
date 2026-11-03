module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table002
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table003
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table004
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table005
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table006
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table007
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table008
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.Table009
public import CatalanMeasure.GenD.Uniform.W.Charts6.SourceProfile
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Charts6

def sourcePair (i : Fin 34) : IntSourceTree × IntSourceTree :=
  match i.val with
  | 0 => (treeG_J001, treeT_J001)
  | 1 => (treeG_J002, treeT_J002)
  | 2 => (treeG_J003, treeT_J003)
  | 3 => (treeG_J004, treeT_J004)
  | 4 => (treeG_J005, treeT_J005)
  | 5 => (treeG_J006, treeT_J006)
  | 6 => (treeG_J007, treeT_J007)
  | 7 => (treeG_J008, treeT_J008)
  | 8 => (treeG_J009, treeT_J009)
  | 9 => (treeG_J010, treeT_J010)
  | 10 => (treeG_J011, treeT_J011)
  | 11 => (treeG_J012, treeT_J012)
  | 12 => (treeG_J013, treeT_J013)
  | 13 => (treeG_J014, treeT_J014)
  | 14 => (treeG_J015, treeT_J015)
  | 15 => (treeG_J016, treeT_J016)
  | 16 => (treeG_J017, treeT_J017)
  | 17 => (treeG_J018, treeT_J018)
  | 18 => (treeG_J019, treeT_J019)
  | 19 => (treeG_J020, treeT_J020)
  | 20 => (treeG_J021, treeT_J021)
  | 21 => (treeG_J022, treeT_J022)
  | 22 => (treeG_J023, treeT_J023)
  | 23 => (treeG_J024, treeT_J024)
  | 24 => (treeG_J025, treeT_J025)
  | 25 => (treeG_J026, treeT_J026)
  | 26 => (treeG_J027, treeT_J027)
  | 27 => (treeG_J028, treeT_J028)
  | 28 => (treeG_J029, treeT_J029)
  | 29 => (treeG_J030, treeT_J030)
  | 30 => (treeG_J031, treeT_J031)
  | 31 => (treeG_J032, treeT_J032)
  | 32 => (treeG_J033, treeT_J033)
  | 33 => (treeG_J034, treeT_J034)
  | _ => (treeG_J001, treeT_J001)

theorem sourcePair_check (i : Fin 34) :
    (sourcePair i).1.check momentData.H (sourceBaseG momentData (i.val + 1)) = true ∧
    (sourcePair i).2.check momentData.H (sourceBaseT momentData (i.val + 1)) = true := by
  fin_cases i
  · exact ⟨treeG_J001_check, treeT_J001_check⟩
  · exact ⟨treeG_J002_check, treeT_J002_check⟩
  · exact ⟨treeG_J003_check, treeT_J003_check⟩
  · exact ⟨treeG_J004_check, treeT_J004_check⟩
  · exact ⟨treeG_J005_check, treeT_J005_check⟩
  · exact ⟨treeG_J006_check, treeT_J006_check⟩
  · exact ⟨treeG_J007_check, treeT_J007_check⟩
  · exact ⟨treeG_J008_check, treeT_J008_check⟩
  · exact ⟨treeG_J009_check, treeT_J009_check⟩
  · exact ⟨treeG_J010_check, treeT_J010_check⟩
  · exact ⟨treeG_J011_check, treeT_J011_check⟩
  · exact ⟨treeG_J012_check, treeT_J012_check⟩
  · exact ⟨treeG_J013_check, treeT_J013_check⟩
  · exact ⟨treeG_J014_check, treeT_J014_check⟩
  · exact ⟨treeG_J015_check, treeT_J015_check⟩
  · exact ⟨treeG_J016_check, treeT_J016_check⟩
  · exact ⟨treeG_J017_check, treeT_J017_check⟩
  · exact ⟨treeG_J018_check, treeT_J018_check⟩
  · exact ⟨treeG_J019_check, treeT_J019_check⟩
  · exact ⟨treeG_J020_check, treeT_J020_check⟩
  · exact ⟨treeG_J021_check, treeT_J021_check⟩
  · exact ⟨treeG_J022_check, treeT_J022_check⟩
  · exact ⟨treeG_J023_check, treeT_J023_check⟩
  · exact ⟨treeG_J024_check, treeT_J024_check⟩
  · exact ⟨treeG_J025_check, treeT_J025_check⟩
  · exact ⟨treeG_J026_check, treeT_J026_check⟩
  · exact ⟨treeG_J027_check, treeT_J027_check⟩
  · exact ⟨treeG_J028_check, treeT_J028_check⟩
  · exact ⟨treeG_J029_check, treeT_J029_check⟩
  · exact ⟨treeG_J030_check, treeT_J030_check⟩
  · exact ⟨treeG_J031_check, treeT_J031_check⟩
  · exact ⟨treeG_J032_check, treeT_J032_check⟩
  · exact ⟨treeG_J033_check, treeT_J033_check⟩
  · exact ⟨treeG_J034_check, treeT_J034_check⟩

def sourceCoeff? (e : SourceExpr) (J : Nat) (S : Int) : Option Int :=
  if h : 1 ≤ J ∧ J ≤ 34 then
    let t := sourcePair ⟨J - 1, by omega⟩
    e.eval? t.1 t.2 momentData.H S
  else none

theorem sourceCoeff?_index (e : SourceExpr) {J : Nat} {S v : Int}
    (h : sourceCoeff? e J S = some v) :
    ∃ i : Fin 34, i.val + 1 = J ∧
      e.eval? (sourcePair i).1 (sourcePair i).2 momentData.H S = some v := by
  unfold sourceCoeff? at h
  split at h
  · rename_i hj
    refine ⟨⟨J - 1, by omega⟩, ?_, h⟩
    change J - 1 + 1 = J
    omega
  · contradiction

end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
