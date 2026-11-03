module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers015
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers015
open D72.LogTransfer
def d2Transfer120Lo : ℚ := (d2LitsNearTransfers015.q2 (34896349) 1 (-28))
def d2Transfer120Hi : ℚ := (d2LitsNearTransfers015.q2 (18287035) 1 (-27))
def d2Transfer120Cap : ℚ := (d2LitsNearTransfers015.q2 (16281318465) 1 (-40))
def d2Transfer120C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 1 (-5))
def d2Transfer120S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer120Arithmetic : weightedUpper d2Transfer120C0 d2Log97Lo d2Log97Hi ≤ d2Transfer120Cap := by decide +kernel
theorem d2Transfer120Bound : ∀ x ∈ Set.Icc ((d2Transfer120Lo:ℚ):ℝ) ((d2Transfer120Hi:ℚ):ℝ), ((d2Transfer120C0:ℚ):ℝ)*Real.log |x-((d2Transfer120S0:ℚ):ℝ)| ≤ ((d2Transfer120Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer120S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer120S0,d2Transfer120Lo,d2Transfer120Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer120C0 then |x-((d2Transfer120S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer120S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer120S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer120S0,d2Transfer120Lo,d2Transfer120Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer120C0,d2Log97Q,d2Transfer120S0,d2Transfer120Lo,d2Transfer120Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer120C0 d2Transfer120S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have har : (((weightedUpper d2Transfer120C0 d2Log97Lo d2Log97Hi:ℚ):ℝ)) ≤ ((d2Transfer120Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer120Arithmetic
  linarith
#print axioms d2Transfer120Arithmetic
#print axioms d2Transfer120Bound
def d2Transfer121Lo : ℚ := (d2LitsNearTransfers015.q2 (34896349) 1 (-28))
def d2Transfer121Hi : ℚ := (d2LitsNearTransfers015.q2 (18287035) 1 (-27))
def d2Transfer121Cap : ℚ := (d2LitsNearTransfers015.q2 (31165051305) 1 (-40))
def d2Transfer121C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 11 (-5))
def d2Transfer121S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
def d2Transfer121C1 : ℚ := (d2LitsNearTransfers015.q2 (-5) 11 (-4))
def d2Transfer121S1 : ℚ := (d2LitsNearTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer121Arithmetic : weightedUpper d2Transfer121C0 d2Log97Lo d2Log97Hi + weightedUpper d2Transfer121C1 d2Log77Lo d2Log77Hi ≤ d2Transfer121Cap := by decide +kernel
theorem d2Transfer121Bound : ∀ x ∈ Set.Icc ((d2Transfer121Lo:ℚ):ℝ) ((d2Transfer121Hi:ℚ):ℝ), ((d2Transfer121C0:ℚ):ℝ)*Real.log |x-((d2Transfer121S0:ℚ):ℝ)| + ((d2Transfer121C1:ℚ):ℝ)*Real.log |x-((d2Transfer121S1:ℚ):ℝ)| ≤ ((d2Transfer121Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer121S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer121S0,d2Transfer121Lo,d2Transfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer121C0 then |x-((d2Transfer121S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer121S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer121S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer121S0,d2Transfer121Lo,d2Transfer121Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer121C0,d2Log97Q,d2Transfer121S0,d2Transfer121Lo,d2Transfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer121C0 d2Transfer121S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have hn1 : x-((d2Transfer121S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer121S1,d2Transfer121Lo,d2Transfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer121C1 then |x-((d2Transfer121S1:ℚ):ℝ)| ≤ ((d2Log77Q:ℚ):ℝ) else ((d2Log77Q:ℚ):ℝ) ≤ |x-((d2Transfer121S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer121S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer121S1,d2Transfer121Lo,d2Transfer121Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer121C1,d2Log77Q,d2Transfer121S1,d2Transfer121Lo,d2Transfer121Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer121C1 d2Transfer121S1 d2Log77Q d2Log77Lo d2Log77Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log77Bounds
  have har : (((weightedUpper d2Transfer121C0 d2Log97Lo d2Log97Hi:ℚ):ℝ) + ((weightedUpper d2Transfer121C1 d2Log77Lo d2Log77Hi:ℚ):ℝ)) ≤ ((d2Transfer121Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer121Arithmetic
  linarith
#print axioms d2Transfer121Arithmetic
#print axioms d2Transfer121Bound
def d2Transfer122Lo : ℚ := (d2LitsNearTransfers015.q2 (18287035) 1 (-27))
def d2Transfer122Hi : ℚ := (d2LitsNearTransfers015.q2 (38251791) 1 (-28))
def d2Transfer122Cap : ℚ := (d2LitsNearTransfers015.q2 (649441385) 1 (-39))
def d2Transfer122C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 25 (-4))
def d2Transfer122S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer122Arithmetic : weightedUpper d2Transfer122C0 d2Log98Lo d2Log98Hi ≤ d2Transfer122Cap := by decide +kernel
theorem d2Transfer122Bound : ∀ x ∈ Set.Icc ((d2Transfer122Lo:ℚ):ℝ) ((d2Transfer122Hi:ℚ):ℝ), ((d2Transfer122C0:ℚ):ℝ)*Real.log |x-((d2Transfer122S0:ℚ):ℝ)| ≤ ((d2Transfer122Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer122S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer122S0,d2Transfer122Lo,d2Transfer122Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer122C0 then |x-((d2Transfer122S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer122S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer122S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer122S0,d2Transfer122Lo,d2Transfer122Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer122C0,d2Log98Q,d2Transfer122S0,d2Transfer122Lo,d2Transfer122Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer122C0 d2Transfer122S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have har : (((weightedUpper d2Transfer122C0 d2Log98Lo d2Log98Hi:ℚ):ℝ)) ≤ ((d2Transfer122Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer122Arithmetic
  linarith
#print axioms d2Transfer122Arithmetic
#print axioms d2Transfer122Bound
def d2Transfer123Lo : ℚ := (d2LitsNearTransfers015.q2 (18287035) 1 (-27))
def d2Transfer123Hi : ℚ := (d2LitsNearTransfers015.q2 (38251791) 1 (-28))
def d2Transfer123Cap : ℚ := (d2LitsNearTransfers015.q2 (2436024149) 1 (-40))
def d2Transfer123C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 275 (-4))
def d2Transfer123S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
def d2Transfer123C1 : ℚ := (d2LitsNearTransfers015.q2 (-1) 55 (-3))
def d2Transfer123S1 : ℚ := (d2LitsNearTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer123Arithmetic : weightedUpper d2Transfer123C0 d2Log98Lo d2Log98Hi + weightedUpper d2Transfer123C1 d2Log76Lo d2Log76Hi ≤ d2Transfer123Cap := by decide +kernel
theorem d2Transfer123Bound : ∀ x ∈ Set.Icc ((d2Transfer123Lo:ℚ):ℝ) ((d2Transfer123Hi:ℚ):ℝ), ((d2Transfer123C0:ℚ):ℝ)*Real.log |x-((d2Transfer123S0:ℚ):ℝ)| + ((d2Transfer123C1:ℚ):ℝ)*Real.log |x-((d2Transfer123S1:ℚ):ℝ)| ≤ ((d2Transfer123Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer123S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer123S0,d2Transfer123Lo,d2Transfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer123C0 then |x-((d2Transfer123S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer123S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer123S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer123S0,d2Transfer123Lo,d2Transfer123Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer123C0,d2Log98Q,d2Transfer123S0,d2Transfer123Lo,d2Transfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer123C0 d2Transfer123S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have hn1 : x-((d2Transfer123S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer123S1,d2Transfer123Lo,d2Transfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer123C1 then |x-((d2Transfer123S1:ℚ):ℝ)| ≤ ((d2Log76Q:ℚ):ℝ) else ((d2Log76Q:ℚ):ℝ) ≤ |x-((d2Transfer123S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer123S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer123S1,d2Transfer123Lo,d2Transfer123Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer123C1,d2Log76Q,d2Transfer123S1,d2Transfer123Lo,d2Transfer123Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer123C1 d2Transfer123S1 d2Log76Q d2Log76Lo d2Log76Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log76Bounds
  have har : (((weightedUpper d2Transfer123C0 d2Log98Lo d2Log98Hi:ℚ):ℝ) + ((weightedUpper d2Transfer123C1 d2Log76Lo d2Log76Hi:ℚ):ℝ)) ≤ ((d2Transfer123Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer123Arithmetic
  linarith
#print axioms d2Transfer123Arithmetic
#print axioms d2Transfer123Bound
def d2Transfer124Lo : ℚ := (d2LitsNearTransfers015.q2 (18287035) 1 (-27))
def d2Transfer124Hi : ℚ := (d2LitsNearTransfers015.q2 (38251791) 1 (-28))
def d2Transfer124Cap : ℚ := (d2LitsNearTransfers015.q2 (16281318465) 1 (-40))
def d2Transfer124C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 1 (-5))
def d2Transfer124S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer124Arithmetic : weightedUpper d2Transfer124C0 d2Log98Lo d2Log98Hi ≤ d2Transfer124Cap := by decide +kernel
theorem d2Transfer124Bound : ∀ x ∈ Set.Icc ((d2Transfer124Lo:ℚ):ℝ) ((d2Transfer124Hi:ℚ):ℝ), ((d2Transfer124C0:ℚ):ℝ)*Real.log |x-((d2Transfer124S0:ℚ):ℝ)| ≤ ((d2Transfer124Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer124S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer124S0,d2Transfer124Lo,d2Transfer124Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer124C0 then |x-((d2Transfer124S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer124S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer124S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer124S0,d2Transfer124Lo,d2Transfer124Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer124C0,d2Log98Q,d2Transfer124S0,d2Transfer124Lo,d2Transfer124Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer124C0 d2Transfer124S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have har : (((weightedUpper d2Transfer124C0 d2Log98Lo d2Log98Hi:ℚ):ℝ)) ≤ ((d2Transfer124Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer124Arithmetic
  linarith
#print axioms d2Transfer124Arithmetic
#print axioms d2Transfer124Bound
def d2Transfer125Lo : ℚ := (d2LitsNearTransfers015.q2 (18287035) 1 (-27))
def d2Transfer125Hi : ℚ := (d2LitsNearTransfers015.q2 (38251791) 1 (-28))
def d2Transfer125Cap : ℚ := (d2LitsNearTransfers015.q2 (31165051305) 1 (-40))
def d2Transfer125C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 11 (-5))
def d2Transfer125S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
def d2Transfer125C1 : ℚ := (d2LitsNearTransfers015.q2 (-5) 11 (-4))
def d2Transfer125S1 : ℚ := (d2LitsNearTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer125Arithmetic : weightedUpper d2Transfer125C0 d2Log98Lo d2Log98Hi + weightedUpper d2Transfer125C1 d2Log76Lo d2Log76Hi ≤ d2Transfer125Cap := by decide +kernel
theorem d2Transfer125Bound : ∀ x ∈ Set.Icc ((d2Transfer125Lo:ℚ):ℝ) ((d2Transfer125Hi:ℚ):ℝ), ((d2Transfer125C0:ℚ):ℝ)*Real.log |x-((d2Transfer125S0:ℚ):ℝ)| + ((d2Transfer125C1:ℚ):ℝ)*Real.log |x-((d2Transfer125S1:ℚ):ℝ)| ≤ ((d2Transfer125Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer125S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer125S0,d2Transfer125Lo,d2Transfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer125C0 then |x-((d2Transfer125S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer125S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer125S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer125S0,d2Transfer125Lo,d2Transfer125Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer125C0,d2Log98Q,d2Transfer125S0,d2Transfer125Lo,d2Transfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer125C0 d2Transfer125S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have hn1 : x-((d2Transfer125S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer125S1,d2Transfer125Lo,d2Transfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer125C1 then |x-((d2Transfer125S1:ℚ):ℝ)| ≤ ((d2Log76Q:ℚ):ℝ) else ((d2Log76Q:ℚ):ℝ) ≤ |x-((d2Transfer125S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer125S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer125S1,d2Transfer125Lo,d2Transfer125Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer125C1,d2Log76Q,d2Transfer125S1,d2Transfer125Lo,d2Transfer125Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer125C1 d2Transfer125S1 d2Log76Q d2Log76Lo d2Log76Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log76Bounds
  have har : (((weightedUpper d2Transfer125C0 d2Log98Lo d2Log98Hi:ℚ):ℝ) + ((weightedUpper d2Transfer125C1 d2Log76Lo d2Log76Hi:ℚ):ℝ)) ≤ ((d2Transfer125Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer125Arithmetic
  linarith
#print axioms d2Transfer125Arithmetic
#print axioms d2Transfer125Bound
def d2Transfer126Lo : ℚ := (d2LitsNearTransfers015.q2 (38251791) 1 (-28))
def d2Transfer126Hi : ℚ := (d2LitsNearTransfers015.q2 (4991189) 1 (-25))
def d2Transfer126Cap : ℚ := (d2LitsNearTransfers015.q2 (649441385) 1 (-39))
def d2Transfer126C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 25 (-4))
def d2Transfer126S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer126Arithmetic : weightedUpper d2Transfer126C0 d2Log99Lo d2Log99Hi ≤ d2Transfer126Cap := by decide +kernel
theorem d2Transfer126Bound : ∀ x ∈ Set.Icc ((d2Transfer126Lo:ℚ):ℝ) ((d2Transfer126Hi:ℚ):ℝ), ((d2Transfer126C0:ℚ):ℝ)*Real.log |x-((d2Transfer126S0:ℚ):ℝ)| ≤ ((d2Transfer126Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer126S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer126S0,d2Transfer126Lo,d2Transfer126Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer126C0 then |x-((d2Transfer126S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer126S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer126S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer126S0,d2Transfer126Lo,d2Transfer126Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer126C0,d2Log99Q,d2Transfer126S0,d2Transfer126Lo,d2Transfer126Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer126C0 d2Transfer126S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2Transfer126C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2Transfer126Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer126Arithmetic
  linarith
#print axioms d2Transfer126Arithmetic
#print axioms d2Transfer126Bound
def d2Transfer127Lo : ℚ := (d2LitsNearTransfers015.q2 (38251791) 1 (-28))
def d2Transfer127Hi : ℚ := (d2LitsNearTransfers015.q2 (4991189) 1 (-25))
def d2Transfer127Cap : ℚ := (d2LitsNearTransfers015.q2 (2436024149) 1 (-40))
def d2Transfer127C0 : ℚ := (d2LitsNearTransfers015.q2 (1) 275 (-4))
def d2Transfer127S0 : ℚ := (d2LitsNearTransfers015.q2 (-1) 1 (0))
def d2Transfer127C1 : ℚ := (d2LitsNearTransfers015.q2 (-1) 55 (-3))
def d2Transfer127S1 : ℚ := (d2LitsNearTransfers015.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer127Arithmetic : weightedUpper d2Transfer127C0 d2Log99Lo d2Log99Hi + weightedUpper d2Transfer127C1 d2Log75Lo d2Log75Hi ≤ d2Transfer127Cap := by decide +kernel
theorem d2Transfer127Bound : ∀ x ∈ Set.Icc ((d2Transfer127Lo:ℚ):ℝ) ((d2Transfer127Hi:ℚ):ℝ), ((d2Transfer127C0:ℚ):ℝ)*Real.log |x-((d2Transfer127S0:ℚ):ℝ)| + ((d2Transfer127C1:ℚ):ℝ)*Real.log |x-((d2Transfer127S1:ℚ):ℝ)| ≤ ((d2Transfer127Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer127S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer127S0,d2Transfer127Lo,d2Transfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer127C0 then |x-((d2Transfer127S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2Transfer127S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer127S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer127S0,d2Transfer127Lo,d2Transfer127Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer127C0,d2Log99Q,d2Transfer127S0,d2Transfer127Lo,d2Transfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer127C0 d2Transfer127S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2Transfer127S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer127S1,d2Transfer127Lo,d2Transfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer127C1 then |x-((d2Transfer127S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2Transfer127S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer127S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer127S1,d2Transfer127Lo,d2Transfer127Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers015.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer127C1,d2Log75Q,d2Transfer127S1,d2Transfer127Lo,d2Transfer127Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer127C1 d2Transfer127S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2Transfer127C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2Transfer127C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2Transfer127Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer127Arithmetic
  linarith
#print axioms d2Transfer127Arithmetic
#print axioms d2Transfer127Bound
end CatalanMeasure.GenD.Signed.Data.Cells
