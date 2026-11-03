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
namespace d2LitsNearTransfers025
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers025
open D72.LogTransfer
def d2Transfer200Lo : ℚ := (d2LitsNearTransfers025.q2 (6689897) 1 (-24))
def d2Transfer200Hi : ℚ := (d2LitsNearTransfers025.q2 (15057515) 1 (-25))
def d2Transfer200Cap : ℚ := (d2LitsNearTransfers025.q2 (16281318465) 1 (-40))
def d2Transfer200C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 1 (-5))
def d2Transfer200S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer200Arithmetic : weightedUpper d2Transfer200C0 d2Log119Lo d2Log119Hi ≤ d2Transfer200Cap := by decide +kernel
theorem d2Transfer200Bound : ∀ x ∈ Set.Icc ((d2Transfer200Lo:ℚ):ℝ) ((d2Transfer200Hi:ℚ):ℝ), ((d2Transfer200C0:ℚ):ℝ)*Real.log |x-((d2Transfer200S0:ℚ):ℝ)| ≤ ((d2Transfer200Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer200S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer200S0,d2Transfer200Lo,d2Transfer200Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer200C0 then |x-((d2Transfer200S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer200S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer200S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer200S0,d2Transfer200Lo,d2Transfer200Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer200C0,d2Log119Q,d2Transfer200S0,d2Transfer200Lo,d2Transfer200Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer200C0 d2Transfer200S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have har : (((weightedUpper d2Transfer200C0 d2Log119Lo d2Log119Hi:ℚ):ℝ)) ≤ ((d2Transfer200Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer200Arithmetic
  linarith
#print axioms d2Transfer200Arithmetic
#print axioms d2Transfer200Bound
def d2Transfer201Lo : ℚ := (d2LitsNearTransfers025.q2 (6689897) 1 (-24))
def d2Transfer201Hi : ℚ := (d2LitsNearTransfers025.q2 (15057515) 1 (-25))
def d2Transfer201Cap : ℚ := (d2LitsNearTransfers025.q2 (31165051305) 1 (-40))
def d2Transfer201C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 11 (-5))
def d2Transfer201S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
def d2Transfer201C1 : ℚ := (d2LitsNearTransfers025.q2 (-5) 11 (-4))
def d2Transfer201S1 : ℚ := (d2LitsNearTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer201Arithmetic : weightedUpper d2Transfer201C0 d2Log119Lo d2Log119Hi + weightedUpper d2Transfer201C1 d2Log55Lo d2Log55Hi ≤ d2Transfer201Cap := by decide +kernel
theorem d2Transfer201Bound : ∀ x ∈ Set.Icc ((d2Transfer201Lo:ℚ):ℝ) ((d2Transfer201Hi:ℚ):ℝ), ((d2Transfer201C0:ℚ):ℝ)*Real.log |x-((d2Transfer201S0:ℚ):ℝ)| + ((d2Transfer201C1:ℚ):ℝ)*Real.log |x-((d2Transfer201S1:ℚ):ℝ)| ≤ ((d2Transfer201Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer201S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer201S0,d2Transfer201Lo,d2Transfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer201C0 then |x-((d2Transfer201S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer201S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer201S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer201S0,d2Transfer201Lo,d2Transfer201Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer201C0,d2Log119Q,d2Transfer201S0,d2Transfer201Lo,d2Transfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer201C0 d2Transfer201S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have hn1 : x-((d2Transfer201S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer201S1,d2Transfer201Lo,d2Transfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer201C1 then |x-((d2Transfer201S1:ℚ):ℝ)| ≤ ((d2Log55Q:ℚ):ℝ) else ((d2Log55Q:ℚ):ℝ) ≤ |x-((d2Transfer201S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer201S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer201S1,d2Transfer201Lo,d2Transfer201Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer201C1,d2Log55Q,d2Transfer201S1,d2Transfer201Lo,d2Transfer201Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer201C1 d2Transfer201S1 d2Log55Q d2Log55Lo d2Log55Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log55Bounds
  have har : (((weightedUpper d2Transfer201C0 d2Log119Lo d2Log119Hi:ℚ):ℝ) + ((weightedUpper d2Transfer201C1 d2Log55Lo d2Log55Hi:ℚ):ℝ)) ≤ ((d2Transfer201Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer201Arithmetic
  linarith
#print axioms d2Transfer201Arithmetic
#print axioms d2Transfer201Bound
def d2Transfer202Lo : ℚ := (d2LitsNearTransfers025.q2 (15057515) 1 (-25))
def d2Transfer202Hi : ℚ := (d2LitsNearTransfers025.q2 (4183809) 1 (-23))
def d2Transfer202Cap : ℚ := (d2LitsNearTransfers025.q2 (649441385) 1 (-39))
def d2Transfer202C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 25 (-4))
def d2Transfer202S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer202Arithmetic : weightedUpper d2Transfer202C0 d2Log120Lo d2Log120Hi ≤ d2Transfer202Cap := by decide +kernel
theorem d2Transfer202Bound : ∀ x ∈ Set.Icc ((d2Transfer202Lo:ℚ):ℝ) ((d2Transfer202Hi:ℚ):ℝ), ((d2Transfer202C0:ℚ):ℝ)*Real.log |x-((d2Transfer202S0:ℚ):ℝ)| ≤ ((d2Transfer202Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer202S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer202S0,d2Transfer202Lo,d2Transfer202Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer202C0 then |x-((d2Transfer202S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer202S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer202S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer202S0,d2Transfer202Lo,d2Transfer202Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer202C0,d2Log120Q,d2Transfer202S0,d2Transfer202Lo,d2Transfer202Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer202C0 d2Transfer202S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2Transfer202C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2Transfer202Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer202Arithmetic
  linarith
#print axioms d2Transfer202Arithmetic
#print axioms d2Transfer202Bound
def d2Transfer203Lo : ℚ := (d2LitsNearTransfers025.q2 (15057515) 1 (-25))
def d2Transfer203Hi : ℚ := (d2LitsNearTransfers025.q2 (4183809) 1 (-23))
def d2Transfer203Cap : ℚ := (d2LitsNearTransfers025.q2 (2436024149) 1 (-40))
def d2Transfer203C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 275 (-4))
def d2Transfer203S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
def d2Transfer203C1 : ℚ := (d2LitsNearTransfers025.q2 (-1) 55 (-3))
def d2Transfer203S1 : ℚ := (d2LitsNearTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer203Arithmetic : weightedUpper d2Transfer203C0 d2Log120Lo d2Log120Hi + weightedUpper d2Transfer203C1 d2Log54Lo d2Log54Hi ≤ d2Transfer203Cap := by decide +kernel
theorem d2Transfer203Bound : ∀ x ∈ Set.Icc ((d2Transfer203Lo:ℚ):ℝ) ((d2Transfer203Hi:ℚ):ℝ), ((d2Transfer203C0:ℚ):ℝ)*Real.log |x-((d2Transfer203S0:ℚ):ℝ)| + ((d2Transfer203C1:ℚ):ℝ)*Real.log |x-((d2Transfer203S1:ℚ):ℝ)| ≤ ((d2Transfer203Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer203S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer203S0,d2Transfer203Lo,d2Transfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer203C0 then |x-((d2Transfer203S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer203S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer203S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer203S0,d2Transfer203Lo,d2Transfer203Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer203C0,d2Log120Q,d2Transfer203S0,d2Transfer203Lo,d2Transfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer203C0 d2Transfer203S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2Transfer203S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer203S1,d2Transfer203Lo,d2Transfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer203C1 then |x-((d2Transfer203S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2Transfer203S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer203S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer203S1,d2Transfer203Lo,d2Transfer203Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer203C1,d2Log54Q,d2Transfer203S1,d2Transfer203Lo,d2Transfer203Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer203C1 d2Transfer203S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2Transfer203C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2Transfer203C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2Transfer203Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer203Arithmetic
  linarith
#print axioms d2Transfer203Arithmetic
#print axioms d2Transfer203Bound
def d2Transfer204Lo : ℚ := (d2LitsNearTransfers025.q2 (15057515) 1 (-25))
def d2Transfer204Hi : ℚ := (d2LitsNearTransfers025.q2 (4183809) 1 (-23))
def d2Transfer204Cap : ℚ := (d2LitsNearTransfers025.q2 (16281318465) 1 (-40))
def d2Transfer204C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 1 (-5))
def d2Transfer204S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer204Arithmetic : weightedUpper d2Transfer204C0 d2Log120Lo d2Log120Hi ≤ d2Transfer204Cap := by decide +kernel
theorem d2Transfer204Bound : ∀ x ∈ Set.Icc ((d2Transfer204Lo:ℚ):ℝ) ((d2Transfer204Hi:ℚ):ℝ), ((d2Transfer204C0:ℚ):ℝ)*Real.log |x-((d2Transfer204S0:ℚ):ℝ)| ≤ ((d2Transfer204Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer204S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer204S0,d2Transfer204Lo,d2Transfer204Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer204C0 then |x-((d2Transfer204S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer204S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer204S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer204S0,d2Transfer204Lo,d2Transfer204Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer204C0,d2Log120Q,d2Transfer204S0,d2Transfer204Lo,d2Transfer204Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer204C0 d2Transfer204S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2Transfer204C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2Transfer204Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer204Arithmetic
  linarith
#print axioms d2Transfer204Arithmetic
#print axioms d2Transfer204Bound
def d2Transfer205Lo : ℚ := (d2LitsNearTransfers025.q2 (15057515) 1 (-25))
def d2Transfer205Hi : ℚ := (d2LitsNearTransfers025.q2 (4183809) 1 (-23))
def d2Transfer205Cap : ℚ := (d2LitsNearTransfers025.q2 (31165051305) 1 (-40))
def d2Transfer205C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 11 (-5))
def d2Transfer205S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
def d2Transfer205C1 : ℚ := (d2LitsNearTransfers025.q2 (-5) 11 (-4))
def d2Transfer205S1 : ℚ := (d2LitsNearTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer205Arithmetic : weightedUpper d2Transfer205C0 d2Log120Lo d2Log120Hi + weightedUpper d2Transfer205C1 d2Log54Lo d2Log54Hi ≤ d2Transfer205Cap := by decide +kernel
theorem d2Transfer205Bound : ∀ x ∈ Set.Icc ((d2Transfer205Lo:ℚ):ℝ) ((d2Transfer205Hi:ℚ):ℝ), ((d2Transfer205C0:ℚ):ℝ)*Real.log |x-((d2Transfer205S0:ℚ):ℝ)| + ((d2Transfer205C1:ℚ):ℝ)*Real.log |x-((d2Transfer205S1:ℚ):ℝ)| ≤ ((d2Transfer205Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer205S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer205S0,d2Transfer205Lo,d2Transfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer205C0 then |x-((d2Transfer205S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer205S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer205S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer205S0,d2Transfer205Lo,d2Transfer205Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer205C0,d2Log120Q,d2Transfer205S0,d2Transfer205Lo,d2Transfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer205C0 d2Transfer205S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2Transfer205S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer205S1,d2Transfer205Lo,d2Transfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer205C1 then |x-((d2Transfer205S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2Transfer205S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer205S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer205S1,d2Transfer205Lo,d2Transfer205Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer205C1,d2Log54Q,d2Transfer205S1,d2Transfer205Lo,d2Transfer205Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer205C1 d2Transfer205S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2Transfer205C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2Transfer205C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2Transfer205Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer205Arithmetic
  linarith
#print axioms d2Transfer205Arithmetic
#print axioms d2Transfer205Bound
def d2Transfer206Lo : ℚ := (d2LitsNearTransfers025.q2 (4183809) 1 (-23))
def d2Transfer206Hi : ℚ := (d2LitsNearTransfers025.q2 (18412957) 1 (-25))
def d2Transfer206Cap : ℚ := (d2LitsNearTransfers025.q2 (649441385) 1 (-39))
def d2Transfer206C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 25 (-4))
def d2Transfer206S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer206Arithmetic : weightedUpper d2Transfer206C0 d2Log121Lo d2Log121Hi ≤ d2Transfer206Cap := by decide +kernel
theorem d2Transfer206Bound : ∀ x ∈ Set.Icc ((d2Transfer206Lo:ℚ):ℝ) ((d2Transfer206Hi:ℚ):ℝ), ((d2Transfer206C0:ℚ):ℝ)*Real.log |x-((d2Transfer206S0:ℚ):ℝ)| ≤ ((d2Transfer206Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer206S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer206S0,d2Transfer206Lo,d2Transfer206Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer206C0 then |x-((d2Transfer206S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer206S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer206S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer206S0,d2Transfer206Lo,d2Transfer206Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer206C0,d2Log121Q,d2Transfer206S0,d2Transfer206Lo,d2Transfer206Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer206C0 d2Transfer206S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2Transfer206C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2Transfer206Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer206Arithmetic
  linarith
#print axioms d2Transfer206Arithmetic
#print axioms d2Transfer206Bound
def d2Transfer207Lo : ℚ := (d2LitsNearTransfers025.q2 (4183809) 1 (-23))
def d2Transfer207Hi : ℚ := (d2LitsNearTransfers025.q2 (18412957) 1 (-25))
def d2Transfer207Cap : ℚ := (d2LitsNearTransfers025.q2 (2436024149) 1 (-40))
def d2Transfer207C0 : ℚ := (d2LitsNearTransfers025.q2 (1) 275 (-4))
def d2Transfer207S0 : ℚ := (d2LitsNearTransfers025.q2 (-1) 1 (0))
def d2Transfer207C1 : ℚ := (d2LitsNearTransfers025.q2 (-1) 55 (-3))
def d2Transfer207S1 : ℚ := (d2LitsNearTransfers025.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer207Arithmetic : weightedUpper d2Transfer207C0 d2Log121Lo d2Log121Hi + weightedUpper d2Transfer207C1 d2Log53Lo d2Log53Hi ≤ d2Transfer207Cap := by decide +kernel
theorem d2Transfer207Bound : ∀ x ∈ Set.Icc ((d2Transfer207Lo:ℚ):ℝ) ((d2Transfer207Hi:ℚ):ℝ), ((d2Transfer207C0:ℚ):ℝ)*Real.log |x-((d2Transfer207S0:ℚ):ℝ)| + ((d2Transfer207C1:ℚ):ℝ)*Real.log |x-((d2Transfer207S1:ℚ):ℝ)| ≤ ((d2Transfer207Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer207S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer207S0,d2Transfer207Lo,d2Transfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer207C0 then |x-((d2Transfer207S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer207S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer207S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer207S0,d2Transfer207Lo,d2Transfer207Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer207C0,d2Log121Q,d2Transfer207S0,d2Transfer207Lo,d2Transfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer207C0 d2Transfer207S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2Transfer207S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer207S1,d2Transfer207Lo,d2Transfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer207C1 then |x-((d2Transfer207S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2Transfer207S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer207S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer207S1,d2Transfer207Lo,d2Transfer207Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers025.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer207C1,d2Log53Q,d2Transfer207S1,d2Transfer207Lo,d2Transfer207Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer207C1 d2Transfer207S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2Transfer207C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2Transfer207C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2Transfer207Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer207Arithmetic
  linarith
#print axioms d2Transfer207Arithmetic
#print axioms d2Transfer207Bound
end CatalanMeasure.GenD.Signed.Data.Cells
