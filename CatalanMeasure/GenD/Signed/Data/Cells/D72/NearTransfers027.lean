module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers027
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers027
open D72.LogTransfer
def d2Transfer216Lo : ℚ := (d2LitsNearTransfers027.q2 (38503635) 1 (-26))
def d2Transfer216Hi : ℚ := (d2LitsNearTransfers027.q2 (78684991) 1 (-27))
def d2Transfer216Cap : ℚ := (d2LitsNearTransfers027.q2 (16281318465) 1 (-40))
def d2Transfer216C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 1 (-5))
def d2Transfer216S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer216Arithmetic : weightedUpper d2Transfer216C0 d2Log123Lo d2Log123Hi ≤ d2Transfer216Cap := by decide +kernel
theorem d2Transfer216Bound : ∀ x ∈ Set.Icc ((d2Transfer216Lo:ℚ):ℝ) ((d2Transfer216Hi:ℚ):ℝ), ((d2Transfer216C0:ℚ):ℝ)*Real.log |x-((d2Transfer216S0:ℚ):ℝ)| ≤ ((d2Transfer216Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer216S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer216S0,d2Transfer216Lo,d2Transfer216Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer216C0 then |x-((d2Transfer216S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2Transfer216S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer216S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer216S0,d2Transfer216Lo,d2Transfer216Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer216C0,d2Log123Q,d2Transfer216S0,d2Transfer216Lo,d2Transfer216Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer216C0 d2Transfer216S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have har : (((weightedUpper d2Transfer216C0 d2Log123Lo d2Log123Hi:ℚ):ℝ)) ≤ ((d2Transfer216Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer216Arithmetic
  linarith
#print axioms d2Transfer216Arithmetic
#print axioms d2Transfer216Bound
def d2Transfer217Lo : ℚ := (d2LitsNearTransfers027.q2 (38503635) 1 (-26))
def d2Transfer217Hi : ℚ := (d2LitsNearTransfers027.q2 (78684991) 1 (-27))
def d2Transfer217Cap : ℚ := (d2LitsNearTransfers027.q2 (31165051305) 1 (-40))
def d2Transfer217C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 11 (-5))
def d2Transfer217S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
def d2Transfer217C1 : ℚ := (d2LitsNearTransfers027.q2 (-5) 11 (-4))
def d2Transfer217S1 : ℚ := (d2LitsNearTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer217Arithmetic : weightedUpper d2Transfer217C0 d2Log123Lo d2Log123Hi + weightedUpper d2Transfer217C1 d2Log51Lo d2Log51Hi ≤ d2Transfer217Cap := by decide +kernel
theorem d2Transfer217Bound : ∀ x ∈ Set.Icc ((d2Transfer217Lo:ℚ):ℝ) ((d2Transfer217Hi:ℚ):ℝ), ((d2Transfer217C0:ℚ):ℝ)*Real.log |x-((d2Transfer217S0:ℚ):ℝ)| + ((d2Transfer217C1:ℚ):ℝ)*Real.log |x-((d2Transfer217S1:ℚ):ℝ)| ≤ ((d2Transfer217Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer217S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer217S0,d2Transfer217Lo,d2Transfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer217C0 then |x-((d2Transfer217S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2Transfer217S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer217S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer217S0,d2Transfer217Lo,d2Transfer217Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer217C0,d2Log123Q,d2Transfer217S0,d2Transfer217Lo,d2Transfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer217C0 d2Transfer217S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have hn1 : x-((d2Transfer217S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer217S1,d2Transfer217Lo,d2Transfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer217C1 then |x-((d2Transfer217S1:ℚ):ℝ)| ≤ ((d2Log51Q:ℚ):ℝ) else ((d2Log51Q:ℚ):ℝ) ≤ |x-((d2Transfer217S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer217S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer217S1,d2Transfer217Lo,d2Transfer217Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer217C1,d2Log51Q,d2Transfer217S1,d2Transfer217Lo,d2Transfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer217C1 d2Transfer217S1 d2Log51Q d2Log51Lo d2Log51Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log51Bounds
  have har : (((weightedUpper d2Transfer217C0 d2Log123Lo d2Log123Hi:ℚ):ℝ) + ((weightedUpper d2Transfer217C1 d2Log51Lo d2Log51Hi:ℚ):ℝ)) ≤ ((d2Transfer217Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer217Arithmetic
  linarith
#print axioms d2Transfer217Arithmetic
#print axioms d2Transfer217Bound
def d2Transfer218Lo : ℚ := (d2LitsNearTransfers027.q2 (78684991) 1 (-27))
def d2Transfer218Hi : ℚ := (d2LitsNearTransfers027.q2 (10045339) 1 (-24))
def d2Transfer218Cap : ℚ := (d2LitsNearTransfers027.q2 (649441385) 1 (-39))
def d2Transfer218C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 25 (-4))
def d2Transfer218S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer218Arithmetic : weightedUpper d2Transfer218C0 d2Log124Lo d2Log124Hi ≤ d2Transfer218Cap := by decide +kernel
theorem d2Transfer218Bound : ∀ x ∈ Set.Icc ((d2Transfer218Lo:ℚ):ℝ) ((d2Transfer218Hi:ℚ):ℝ), ((d2Transfer218C0:ℚ):ℝ)*Real.log |x-((d2Transfer218S0:ℚ):ℝ)| ≤ ((d2Transfer218Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer218S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer218S0,d2Transfer218Lo,d2Transfer218Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer218C0 then |x-((d2Transfer218S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer218S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer218S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer218S0,d2Transfer218Lo,d2Transfer218Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer218C0,d2Log124Q,d2Transfer218S0,d2Transfer218Lo,d2Transfer218Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer218C0 d2Transfer218S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2Transfer218C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2Transfer218Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer218Arithmetic
  linarith
#print axioms d2Transfer218Arithmetic
#print axioms d2Transfer218Bound
def d2Transfer219Lo : ℚ := (d2LitsNearTransfers027.q2 (78684991) 1 (-27))
def d2Transfer219Hi : ℚ := (d2LitsNearTransfers027.q2 (10045339) 1 (-24))
def d2Transfer219Cap : ℚ := (d2LitsNearTransfers027.q2 (2436024149) 1 (-40))
def d2Transfer219C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 275 (-4))
def d2Transfer219S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
def d2Transfer219C1 : ℚ := (d2LitsNearTransfers027.q2 (-1) 55 (-3))
def d2Transfer219S1 : ℚ := (d2LitsNearTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer219Arithmetic : weightedUpper d2Transfer219C0 d2Log124Lo d2Log124Hi + weightedUpper d2Transfer219C1 d2Log50Lo d2Log50Hi ≤ d2Transfer219Cap := by decide +kernel
theorem d2Transfer219Bound : ∀ x ∈ Set.Icc ((d2Transfer219Lo:ℚ):ℝ) ((d2Transfer219Hi:ℚ):ℝ), ((d2Transfer219C0:ℚ):ℝ)*Real.log |x-((d2Transfer219S0:ℚ):ℝ)| + ((d2Transfer219C1:ℚ):ℝ)*Real.log |x-((d2Transfer219S1:ℚ):ℝ)| ≤ ((d2Transfer219Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer219S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer219S0,d2Transfer219Lo,d2Transfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer219C0 then |x-((d2Transfer219S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer219S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer219S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer219S0,d2Transfer219Lo,d2Transfer219Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer219C0,d2Log124Q,d2Transfer219S0,d2Transfer219Lo,d2Transfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer219C0 d2Transfer219S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2Transfer219S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer219S1,d2Transfer219Lo,d2Transfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer219C1 then |x-((d2Transfer219S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2Transfer219S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer219S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer219S1,d2Transfer219Lo,d2Transfer219Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer219C1,d2Log50Q,d2Transfer219S1,d2Transfer219Lo,d2Transfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer219C1 d2Transfer219S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2Transfer219C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2Transfer219C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2Transfer219Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer219Arithmetic
  linarith
#print axioms d2Transfer219Arithmetic
#print axioms d2Transfer219Bound
def d2Transfer220Lo : ℚ := (d2LitsNearTransfers027.q2 (78684991) 1 (-27))
def d2Transfer220Hi : ℚ := (d2LitsNearTransfers027.q2 (10045339) 1 (-24))
def d2Transfer220Cap : ℚ := (d2LitsNearTransfers027.q2 (16281318465) 1 (-40))
def d2Transfer220C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 1 (-5))
def d2Transfer220S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer220Arithmetic : weightedUpper d2Transfer220C0 d2Log124Lo d2Log124Hi ≤ d2Transfer220Cap := by decide +kernel
theorem d2Transfer220Bound : ∀ x ∈ Set.Icc ((d2Transfer220Lo:ℚ):ℝ) ((d2Transfer220Hi:ℚ):ℝ), ((d2Transfer220C0:ℚ):ℝ)*Real.log |x-((d2Transfer220S0:ℚ):ℝ)| ≤ ((d2Transfer220Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer220S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer220S0,d2Transfer220Lo,d2Transfer220Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer220C0 then |x-((d2Transfer220S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer220S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer220S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer220S0,d2Transfer220Lo,d2Transfer220Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer220C0,d2Log124Q,d2Transfer220S0,d2Transfer220Lo,d2Transfer220Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer220C0 d2Transfer220S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2Transfer220C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2Transfer220Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer220Arithmetic
  linarith
#print axioms d2Transfer220Arithmetic
#print axioms d2Transfer220Bound
def d2Transfer221Lo : ℚ := (d2LitsNearTransfers027.q2 (78684991) 1 (-27))
def d2Transfer221Hi : ℚ := (d2LitsNearTransfers027.q2 (10045339) 1 (-24))
def d2Transfer221Cap : ℚ := (d2LitsNearTransfers027.q2 (31165051305) 1 (-40))
def d2Transfer221C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 11 (-5))
def d2Transfer221S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
def d2Transfer221C1 : ℚ := (d2LitsNearTransfers027.q2 (-5) 11 (-4))
def d2Transfer221S1 : ℚ := (d2LitsNearTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer221Arithmetic : weightedUpper d2Transfer221C0 d2Log124Lo d2Log124Hi + weightedUpper d2Transfer221C1 d2Log50Lo d2Log50Hi ≤ d2Transfer221Cap := by decide +kernel
theorem d2Transfer221Bound : ∀ x ∈ Set.Icc ((d2Transfer221Lo:ℚ):ℝ) ((d2Transfer221Hi:ℚ):ℝ), ((d2Transfer221C0:ℚ):ℝ)*Real.log |x-((d2Transfer221S0:ℚ):ℝ)| + ((d2Transfer221C1:ℚ):ℝ)*Real.log |x-((d2Transfer221S1:ℚ):ℝ)| ≤ ((d2Transfer221Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer221S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer221S0,d2Transfer221Lo,d2Transfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer221C0 then |x-((d2Transfer221S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer221S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer221S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer221S0,d2Transfer221Lo,d2Transfer221Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer221C0,d2Log124Q,d2Transfer221S0,d2Transfer221Lo,d2Transfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer221C0 d2Transfer221S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2Transfer221S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer221S1,d2Transfer221Lo,d2Transfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer221C1 then |x-((d2Transfer221S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2Transfer221S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer221S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer221S1,d2Transfer221Lo,d2Transfer221Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer221C1,d2Log50Q,d2Transfer221S1,d2Transfer221Lo,d2Transfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer221C1 d2Transfer221S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2Transfer221C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2Transfer221C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2Transfer221Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer221Arithmetic
  linarith
#print axioms d2Transfer221Arithmetic
#print axioms d2Transfer221Bound
def d2Transfer222Lo : ℚ := (d2LitsNearTransfers027.q2 (10045339) 1 (-24))
def d2Transfer222Hi : ℚ := (d2LitsNearTransfers027.q2 (162403145) 1 (-28))
def d2Transfer222Cap : ℚ := (d2LitsNearTransfers027.q2 (357952183878138426799) 1 (-78))
def d2Transfer222C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 25 (-4))
def d2Transfer222S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer222Arithmetic : weightedUpper d2Transfer222C0 d2Log125Lo d2Log125Hi ≤ d2Transfer222Cap := by decide +kernel
theorem d2Transfer222Bound : ∀ x ∈ Set.Icc ((d2Transfer222Lo:ℚ):ℝ) ((d2Transfer222Hi:ℚ):ℝ), ((d2Transfer222C0:ℚ):ℝ)*Real.log |x-((d2Transfer222S0:ℚ):ℝ)| ≤ ((d2Transfer222Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer222S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer222S0,d2Transfer222Lo,d2Transfer222Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer222C0 then |x-((d2Transfer222S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer222S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer222S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer222S0,d2Transfer222Lo,d2Transfer222Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer222C0,d2Log125Q,d2Transfer222S0,d2Transfer222Lo,d2Transfer222Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer222C0 d2Transfer222S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2Transfer222C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2Transfer222Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer222Arithmetic
  linarith
#print axioms d2Transfer222Arithmetic
#print axioms d2Transfer222Bound
def d2Transfer223Lo : ℚ := (d2LitsNearTransfers027.q2 (10045339) 1 (-24))
def d2Transfer223Hi : ℚ := (d2LitsNearTransfers027.q2 (162403145) 1 (-28))
def d2Transfer223Cap : ℚ := (d2LitsNearTransfers027.q2 (670527226037072262575) 1 (-78))
def d2Transfer223C0 : ℚ := (d2LitsNearTransfers027.q2 (1) 275 (-4))
def d2Transfer223S0 : ℚ := (d2LitsNearTransfers027.q2 (-1) 1 (0))
def d2Transfer223C1 : ℚ := (d2LitsNearTransfers027.q2 (-1) 55 (-3))
def d2Transfer223S1 : ℚ := (d2LitsNearTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer223Arithmetic : weightedUpper d2Transfer223C0 d2Log125Lo d2Log125Hi + weightedUpper d2Transfer223C1 d2Log49Lo d2Log49Hi ≤ d2Transfer223Cap := by decide +kernel
theorem d2Transfer223Bound : ∀ x ∈ Set.Icc ((d2Transfer223Lo:ℚ):ℝ) ((d2Transfer223Hi:ℚ):ℝ), ((d2Transfer223C0:ℚ):ℝ)*Real.log |x-((d2Transfer223S0:ℚ):ℝ)| + ((d2Transfer223C1:ℚ):ℝ)*Real.log |x-((d2Transfer223S1:ℚ):ℝ)| ≤ ((d2Transfer223Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer223S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer223S0,d2Transfer223Lo,d2Transfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer223C0 then |x-((d2Transfer223S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer223S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer223S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer223S0,d2Transfer223Lo,d2Transfer223Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer223C0,d2Log125Q,d2Transfer223S0,d2Transfer223Lo,d2Transfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer223C0 d2Transfer223S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2Transfer223S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer223S1,d2Transfer223Lo,d2Transfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer223C1 then |x-((d2Transfer223S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2Transfer223S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer223S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer223S1,d2Transfer223Lo,d2Transfer223Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers027.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer223C1,d2Log49Q,d2Transfer223S1,d2Transfer223Lo,d2Transfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer223C1 d2Transfer223S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2Transfer223C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2Transfer223C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2Transfer223Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer223Arithmetic
  linarith
#print axioms d2Transfer223Arithmetic
#print axioms d2Transfer223Bound
end CatalanMeasure.GenD.Signed.Data.Cells
