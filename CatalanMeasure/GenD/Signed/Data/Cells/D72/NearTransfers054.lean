module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers054
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers054
open D72.LogTransfer
def d2Transfer432Lo : ℚ := (d2LitsNearTransfers054.q2 (11660099) 1 (-26))
def d2Transfer432Hi : ℚ := (d2LitsNearTransfers054.q2 (48318117) 1 (-28))
def d2Transfer432Cap : ℚ := (d2LitsNearTransfers054.q2 (30439539927) 1 (-40))
def d2Transfer432C0 : ℚ := (d2LitsNearTransfers054.q2 (3) 275 (-5))
def d2Transfer432S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
def d2Transfer432C1 : ℚ := (d2LitsNearTransfers054.q2 (-5) 11 (-4))
def d2Transfer432S1 : ℚ := (d2LitsNearTransfers054.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer432Arithmetic : weightedUpper d2Transfer432C0 d2Log104Lo d2Log104Hi + weightedUpper d2Transfer432C1 d2Log70Lo d2Log70Hi ≤ d2Transfer432Cap := by decide +kernel
theorem d2Transfer432Bound : ∀ x ∈ Set.Icc ((d2Transfer432Lo:ℚ):ℝ) ((d2Transfer432Hi:ℚ):ℝ), ((d2Transfer432C0:ℚ):ℝ)*Real.log |x-((d2Transfer432S0:ℚ):ℝ)| + ((d2Transfer432C1:ℚ):ℝ)*Real.log |x-((d2Transfer432S1:ℚ):ℝ)| ≤ ((d2Transfer432Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer432S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer432S0,d2Transfer432Lo,d2Transfer432Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer432C0 then |x-((d2Transfer432S0:ℚ):ℝ)| ≤ ((d2Log104Q:ℚ):ℝ) else ((d2Log104Q:ℚ):ℝ) ≤ |x-((d2Transfer432S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer432S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer432S0,d2Transfer432Lo,d2Transfer432Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer432C0,d2Log104Q,d2Transfer432S0,d2Transfer432Lo,d2Transfer432Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer432C0 d2Transfer432S0 d2Log104Q d2Log104Lo d2Log104Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log104Bounds
  have hn1 : x-((d2Transfer432S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer432S1,d2Transfer432Lo,d2Transfer432Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer432C1 then |x-((d2Transfer432S1:ℚ):ℝ)| ≤ ((d2Log70Q:ℚ):ℝ) else ((d2Log70Q:ℚ):ℝ) ≤ |x-((d2Transfer432S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer432S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer432S1,d2Transfer432Lo,d2Transfer432Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer432C1,d2Log70Q,d2Transfer432S1,d2Transfer432Lo,d2Transfer432Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer432C1 d2Transfer432S1 d2Log70Q d2Log70Lo d2Log70Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log70Bounds
  have har : (((weightedUpper d2Transfer432C0 d2Log104Lo d2Log104Hi:ℚ):ℝ) + ((weightedUpper d2Transfer432C1 d2Log70Lo d2Log70Hi:ℚ):ℝ)) ≤ ((d2Transfer432Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer432Arithmetic
  linarith
#print axioms d2Transfer432Arithmetic
#print axioms d2Transfer432Bound
def d2Transfer433Lo : ℚ := (d2LitsNearTransfers054.q2 (48318117) 1 (-28))
def d2Transfer433Hi : ℚ := (d2LitsNearTransfers054.q2 (24997919) 1 (-27))
def d2Transfer433Cap : ℚ := (d2LitsNearTransfers054.q2 (1169469059) 1 (-40))
def d2Transfer433C0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 55 (-3))
def d2Transfer433S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
def d2Transfer433C1 : ℚ := (d2LitsNearTransfers054.q2 (-1) 55 (-3))
def d2Transfer433S1 : ℚ := (d2LitsNearTransfers054.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer433Arithmetic : weightedUpper d2Transfer433C0 d2Log104Lo d2Log104Hi + weightedUpper d2Transfer433C1 d2Log69Lo d2Log69Hi ≤ d2Transfer433Cap := by decide +kernel
theorem d2Transfer433Bound : ∀ x ∈ Set.Icc ((d2Transfer433Lo:ℚ):ℝ) ((d2Transfer433Hi:ℚ):ℝ), ((d2Transfer433C0:ℚ):ℝ)*Real.log |x-((d2Transfer433S0:ℚ):ℝ)| + ((d2Transfer433C1:ℚ):ℝ)*Real.log |x-((d2Transfer433S1:ℚ):ℝ)| ≤ ((d2Transfer433Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer433S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer433S0,d2Transfer433Lo,d2Transfer433Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer433C0 then |x-((d2Transfer433S0:ℚ):ℝ)| ≤ ((d2Log104Q:ℚ):ℝ) else ((d2Log104Q:ℚ):ℝ) ≤ |x-((d2Transfer433S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer433S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer433S0,d2Transfer433Lo,d2Transfer433Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer433C0,d2Log104Q,d2Transfer433S0,d2Transfer433Lo,d2Transfer433Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer433C0 d2Transfer433S0 d2Log104Q d2Log104Lo d2Log104Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log104Bounds
  have hn1 : x-((d2Transfer433S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer433S1,d2Transfer433Lo,d2Transfer433Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer433C1 then |x-((d2Transfer433S1:ℚ):ℝ)| ≤ ((d2Log69Q:ℚ):ℝ) else ((d2Log69Q:ℚ):ℝ) ≤ |x-((d2Transfer433S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer433S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer433S1,d2Transfer433Lo,d2Transfer433Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer433C1,d2Log69Q,d2Transfer433S1,d2Transfer433Lo,d2Transfer433Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer433C1 d2Transfer433S1 d2Log69Q d2Log69Lo d2Log69Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log69Bounds
  have har : (((weightedUpper d2Transfer433C0 d2Log104Lo d2Log104Hi:ℚ):ℝ) + ((weightedUpper d2Transfer433C1 d2Log69Lo d2Log69Hi:ℚ):ℝ)) ≤ ((d2Transfer433Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer433Arithmetic
  linarith
#print axioms d2Transfer433Arithmetic
#print axioms d2Transfer433Bound
def d2Transfer434Lo : ℚ := (d2LitsNearTransfers054.q2 (48318117) 1 (-28))
def d2Transfer434Hi : ℚ := (d2LitsNearTransfers054.q2 (24997919) 1 (-27))
def d2Transfer434Cap : ℚ := (d2LitsNearTransfers054.q2 (15113656175) 1 (-40))
def d2Transfer434C0 : ℚ := (d2LitsNearTransfers054.q2 (23) 25 (-5))
def d2Transfer434S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer434Arithmetic : weightedUpper d2Transfer434C0 d2Log105Lo d2Log105Hi ≤ d2Transfer434Cap := by decide +kernel
theorem d2Transfer434Bound : ∀ x ∈ Set.Icc ((d2Transfer434Lo:ℚ):ℝ) ((d2Transfer434Hi:ℚ):ℝ), ((d2Transfer434C0:ℚ):ℝ)*Real.log |x-((d2Transfer434S0:ℚ):ℝ)| ≤ ((d2Transfer434Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer434S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer434S0,d2Transfer434Lo,d2Transfer434Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer434C0 then |x-((d2Transfer434S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer434S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer434S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer434S0,d2Transfer434Lo,d2Transfer434Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer434C0,d2Log105Q,d2Transfer434S0,d2Transfer434Lo,d2Transfer434Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer434C0 d2Transfer434S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have har : (((weightedUpper d2Transfer434C0 d2Log105Lo d2Log105Hi:ℚ):ℝ)) ≤ ((d2Transfer434Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer434Arithmetic
  linarith
#print axioms d2Transfer434Arithmetic
#print axioms d2Transfer434Bound
def d2Transfer435Lo : ℚ := (d2LitsNearTransfers054.q2 (48318117) 1 (-28))
def d2Transfer435Hi : ℚ := (d2LitsNearTransfers054.q2 (24997919) 1 (-27))
def d2Transfer435Cap : ℚ := (d2LitsNearTransfers054.q2 (30439539927) 1 (-40))
def d2Transfer435C0 : ℚ := (d2LitsNearTransfers054.q2 (3) 275 (-5))
def d2Transfer435S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
def d2Transfer435C1 : ℚ := (d2LitsNearTransfers054.q2 (-5) 11 (-4))
def d2Transfer435S1 : ℚ := (d2LitsNearTransfers054.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer435Arithmetic : weightedUpper d2Transfer435C0 d2Log105Lo d2Log105Hi + weightedUpper d2Transfer435C1 d2Log69Lo d2Log69Hi ≤ d2Transfer435Cap := by decide +kernel
theorem d2Transfer435Bound : ∀ x ∈ Set.Icc ((d2Transfer435Lo:ℚ):ℝ) ((d2Transfer435Hi:ℚ):ℝ), ((d2Transfer435C0:ℚ):ℝ)*Real.log |x-((d2Transfer435S0:ℚ):ℝ)| + ((d2Transfer435C1:ℚ):ℝ)*Real.log |x-((d2Transfer435S1:ℚ):ℝ)| ≤ ((d2Transfer435Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer435S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer435S0,d2Transfer435Lo,d2Transfer435Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer435C0 then |x-((d2Transfer435S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer435S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer435S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer435S0,d2Transfer435Lo,d2Transfer435Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer435C0,d2Log105Q,d2Transfer435S0,d2Transfer435Lo,d2Transfer435Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer435C0 d2Transfer435S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have hn1 : x-((d2Transfer435S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer435S1,d2Transfer435Lo,d2Transfer435Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer435C1 then |x-((d2Transfer435S1:ℚ):ℝ)| ≤ ((d2Log69Q:ℚ):ℝ) else ((d2Log69Q:ℚ):ℝ) ≤ |x-((d2Transfer435S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer435S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer435S1,d2Transfer435Lo,d2Transfer435Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer435C1,d2Log69Q,d2Transfer435S1,d2Transfer435Lo,d2Transfer435Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer435C1 d2Transfer435S1 d2Log69Q d2Log69Lo d2Log69Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log69Bounds
  have har : (((weightedUpper d2Transfer435C0 d2Log105Lo d2Log105Hi:ℚ):ℝ) + ((weightedUpper d2Transfer435C1 d2Log69Lo d2Log69Hi:ℚ):ℝ)) ≤ ((d2Transfer435Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer435Arithmetic
  linarith
#print axioms d2Transfer435Arithmetic
#print axioms d2Transfer435Bound
def d2Transfer436Lo : ℚ := (d2LitsNearTransfers054.q2 (24997919) 1 (-27))
def d2Transfer436Hi : ℚ := (d2LitsNearTransfers054.q2 (3334455) 1 (-24))
def d2Transfer436Cap : ℚ := (d2LitsNearTransfers054.q2 (1169469059) 1 (-40))
def d2Transfer436C0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 55 (-3))
def d2Transfer436S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
def d2Transfer436C1 : ℚ := (d2LitsNearTransfers054.q2 (-1) 55 (-3))
def d2Transfer436S1 : ℚ := (d2LitsNearTransfers054.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer436Arithmetic : weightedUpper d2Transfer436C0 d2Log105Lo d2Log105Hi + weightedUpper d2Transfer436C1 d2Log68Lo d2Log68Hi ≤ d2Transfer436Cap := by decide +kernel
theorem d2Transfer436Bound : ∀ x ∈ Set.Icc ((d2Transfer436Lo:ℚ):ℝ) ((d2Transfer436Hi:ℚ):ℝ), ((d2Transfer436C0:ℚ):ℝ)*Real.log |x-((d2Transfer436S0:ℚ):ℝ)| + ((d2Transfer436C1:ℚ):ℝ)*Real.log |x-((d2Transfer436S1:ℚ):ℝ)| ≤ ((d2Transfer436Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer436S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer436S0,d2Transfer436Lo,d2Transfer436Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer436C0 then |x-((d2Transfer436S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer436S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer436S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer436S0,d2Transfer436Lo,d2Transfer436Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer436C0,d2Log105Q,d2Transfer436S0,d2Transfer436Lo,d2Transfer436Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer436C0 d2Transfer436S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have hn1 : x-((d2Transfer436S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer436S1,d2Transfer436Lo,d2Transfer436Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer436C1 then |x-((d2Transfer436S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2Transfer436S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer436S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer436S1,d2Transfer436Lo,d2Transfer436Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer436C1,d2Log68Q,d2Transfer436S1,d2Transfer436Lo,d2Transfer436Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer436C1 d2Transfer436S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2Transfer436C0 d2Log105Lo d2Log105Hi:ℚ):ℝ) + ((weightedUpper d2Transfer436C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2Transfer436Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer436Arithmetic
  linarith
#print axioms d2Transfer436Arithmetic
#print axioms d2Transfer436Bound
def d2Transfer437Lo : ℚ := (d2LitsNearTransfers054.q2 (24997919) 1 (-27))
def d2Transfer437Hi : ℚ := (d2LitsNearTransfers054.q2 (3334455) 1 (-24))
def d2Transfer437Cap : ℚ := (d2LitsNearTransfers054.q2 (15113656175) 1 (-40))
def d2Transfer437C0 : ℚ := (d2LitsNearTransfers054.q2 (23) 25 (-5))
def d2Transfer437S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer437Arithmetic : weightedUpper d2Transfer437C0 d2Log106Lo d2Log106Hi ≤ d2Transfer437Cap := by decide +kernel
theorem d2Transfer437Bound : ∀ x ∈ Set.Icc ((d2Transfer437Lo:ℚ):ℝ) ((d2Transfer437Hi:ℚ):ℝ), ((d2Transfer437C0:ℚ):ℝ)*Real.log |x-((d2Transfer437S0:ℚ):ℝ)| ≤ ((d2Transfer437Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer437S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer437S0,d2Transfer437Lo,d2Transfer437Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer437C0 then |x-((d2Transfer437S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer437S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer437S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer437S0,d2Transfer437Lo,d2Transfer437Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer437C0,d2Log106Q,d2Transfer437S0,d2Transfer437Lo,d2Transfer437Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer437C0 d2Transfer437S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2Transfer437C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2Transfer437Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer437Arithmetic
  linarith
#print axioms d2Transfer437Arithmetic
#print axioms d2Transfer437Bound
def d2Transfer438Lo : ℚ := (d2LitsNearTransfers054.q2 (24997919) 1 (-27))
def d2Transfer438Hi : ℚ := (d2LitsNearTransfers054.q2 (3334455) 1 (-24))
def d2Transfer438Cap : ℚ := (d2LitsNearTransfers054.q2 (30439539927) 1 (-40))
def d2Transfer438C0 : ℚ := (d2LitsNearTransfers054.q2 (3) 275 (-5))
def d2Transfer438S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
def d2Transfer438C1 : ℚ := (d2LitsNearTransfers054.q2 (-5) 11 (-4))
def d2Transfer438S1 : ℚ := (d2LitsNearTransfers054.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer438Arithmetic : weightedUpper d2Transfer438C0 d2Log106Lo d2Log106Hi + weightedUpper d2Transfer438C1 d2Log68Lo d2Log68Hi ≤ d2Transfer438Cap := by decide +kernel
theorem d2Transfer438Bound : ∀ x ∈ Set.Icc ((d2Transfer438Lo:ℚ):ℝ) ((d2Transfer438Hi:ℚ):ℝ), ((d2Transfer438C0:ℚ):ℝ)*Real.log |x-((d2Transfer438S0:ℚ):ℝ)| + ((d2Transfer438C1:ℚ):ℝ)*Real.log |x-((d2Transfer438S1:ℚ):ℝ)| ≤ ((d2Transfer438Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer438S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer438S0,d2Transfer438Lo,d2Transfer438Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer438C0 then |x-((d2Transfer438S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer438S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer438S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer438S0,d2Transfer438Lo,d2Transfer438Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer438C0,d2Log106Q,d2Transfer438S0,d2Transfer438Lo,d2Transfer438Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer438C0 d2Transfer438S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2Transfer438S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer438S1,d2Transfer438Lo,d2Transfer438Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer438C1 then |x-((d2Transfer438S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2Transfer438S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer438S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer438S1,d2Transfer438Lo,d2Transfer438Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer438C1,d2Log68Q,d2Transfer438S1,d2Transfer438Lo,d2Transfer438Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer438C1 d2Transfer438S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2Transfer438C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2Transfer438C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2Transfer438Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer438Arithmetic
  linarith
#print axioms d2Transfer438Arithmetic
#print axioms d2Transfer438Bound
def d2Transfer439Lo : ℚ := (d2LitsNearTransfers054.q2 (3334455) 1 (-24))
def d2Transfer439Hi : ℚ := (d2LitsNearTransfers054.q2 (28353361) 1 (-27))
def d2Transfer439Cap : ℚ := (d2LitsNearTransfers054.q2 (1169469059) 1 (-40))
def d2Transfer439C0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 55 (-3))
def d2Transfer439S0 : ℚ := (d2LitsNearTransfers054.q2 (-1) 1 (0))
def d2Transfer439C1 : ℚ := (d2LitsNearTransfers054.q2 (-1) 55 (-3))
def d2Transfer439S1 : ℚ := (d2LitsNearTransfers054.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer439Arithmetic : weightedUpper d2Transfer439C0 d2Log106Lo d2Log106Hi + weightedUpper d2Transfer439C1 d2Log67Lo d2Log67Hi ≤ d2Transfer439Cap := by decide +kernel
theorem d2Transfer439Bound : ∀ x ∈ Set.Icc ((d2Transfer439Lo:ℚ):ℝ) ((d2Transfer439Hi:ℚ):ℝ), ((d2Transfer439C0:ℚ):ℝ)*Real.log |x-((d2Transfer439S0:ℚ):ℝ)| + ((d2Transfer439C1:ℚ):ℝ)*Real.log |x-((d2Transfer439S1:ℚ):ℝ)| ≤ ((d2Transfer439Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer439S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer439S0,d2Transfer439Lo,d2Transfer439Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer439C0 then |x-((d2Transfer439S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer439S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer439S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer439S0,d2Transfer439Lo,d2Transfer439Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer439C0,d2Log106Q,d2Transfer439S0,d2Transfer439Lo,d2Transfer439Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer439C0 d2Transfer439S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2Transfer439S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer439S1,d2Transfer439Lo,d2Transfer439Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer439C1 then |x-((d2Transfer439S1:ℚ):ℝ)| ≤ ((d2Log67Q:ℚ):ℝ) else ((d2Log67Q:ℚ):ℝ) ≤ |x-((d2Transfer439S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer439S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer439S1,d2Transfer439Lo,d2Transfer439Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers054.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer439C1,d2Log67Q,d2Transfer439S1,d2Transfer439Lo,d2Transfer439Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer439C1 d2Transfer439S1 d2Log67Q d2Log67Lo d2Log67Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log67Bounds
  have har : (((weightedUpper d2Transfer439C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2Transfer439C1 d2Log67Lo d2Log67Hi:ℚ):ℝ)) ≤ ((d2Transfer439Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer439Arithmetic
  linarith
#print axioms d2Transfer439Arithmetic
#print axioms d2Transfer439Bound
end CatalanMeasure.GenD.Signed.Data.Cells
