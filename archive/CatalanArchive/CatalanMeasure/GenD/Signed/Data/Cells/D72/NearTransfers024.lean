module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers024
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers024
open D72.LogTransfer
def d2Transfer192Lo : ℚ := (d2LitsNearTransfers024.q2 (11702073) 1 (-25))
def d2Transfer192Hi : ℚ := (d2LitsNearTransfers024.q2 (25081867) 1 (-26))
def d2Transfer192Cap : ℚ := (d2LitsNearTransfers024.q2 (16281318465) 1 (-40))
def d2Transfer192C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 1 (-5))
def d2Transfer192S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer192Arithmetic : weightedUpper d2Transfer192C0 d2Log116Lo d2Log116Hi ≤ d2Transfer192Cap := by decide +kernel
theorem d2Transfer192Bound : ∀ x ∈ Set.Icc ((d2Transfer192Lo:ℚ):ℝ) ((d2Transfer192Hi:ℚ):ℝ), ((d2Transfer192C0:ℚ):ℝ)*Real.log |x-((d2Transfer192S0:ℚ):ℝ)| ≤ ((d2Transfer192Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer192S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer192S0,d2Transfer192Lo,d2Transfer192Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer192C0 then |x-((d2Transfer192S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer192S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer192S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer192S0,d2Transfer192Lo,d2Transfer192Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer192C0,d2Log116Q,d2Transfer192S0,d2Transfer192Lo,d2Transfer192Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer192C0 d2Transfer192S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have har : (((weightedUpper d2Transfer192C0 d2Log116Lo d2Log116Hi:ℚ):ℝ)) ≤ ((d2Transfer192Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer192Arithmetic
  linarith
#print axioms d2Transfer192Arithmetic
#print axioms d2Transfer192Bound
def d2Transfer193Lo : ℚ := (d2LitsNearTransfers024.q2 (11702073) 1 (-25))
def d2Transfer193Hi : ℚ := (d2LitsNearTransfers024.q2 (25081867) 1 (-26))
def d2Transfer193Cap : ℚ := (d2LitsNearTransfers024.q2 (31165051305) 1 (-40))
def d2Transfer193C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 11 (-5))
def d2Transfer193S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
def d2Transfer193C1 : ℚ := (d2LitsNearTransfers024.q2 (-5) 11 (-4))
def d2Transfer193S1 : ℚ := (d2LitsNearTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer193Arithmetic : weightedUpper d2Transfer193C0 d2Log116Lo d2Log116Hi + weightedUpper d2Transfer193C1 d2Log58Lo d2Log58Hi ≤ d2Transfer193Cap := by decide +kernel
theorem d2Transfer193Bound : ∀ x ∈ Set.Icc ((d2Transfer193Lo:ℚ):ℝ) ((d2Transfer193Hi:ℚ):ℝ), ((d2Transfer193C0:ℚ):ℝ)*Real.log |x-((d2Transfer193S0:ℚ):ℝ)| + ((d2Transfer193C1:ℚ):ℝ)*Real.log |x-((d2Transfer193S1:ℚ):ℝ)| ≤ ((d2Transfer193Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer193S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer193S0,d2Transfer193Lo,d2Transfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer193C0 then |x-((d2Transfer193S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer193S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer193S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer193S0,d2Transfer193Lo,d2Transfer193Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer193C0,d2Log116Q,d2Transfer193S0,d2Transfer193Lo,d2Transfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer193C0 d2Transfer193S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have hn1 : x-((d2Transfer193S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer193S1,d2Transfer193Lo,d2Transfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer193C1 then |x-((d2Transfer193S1:ℚ):ℝ)| ≤ ((d2Log58Q:ℚ):ℝ) else ((d2Log58Q:ℚ):ℝ) ≤ |x-((d2Transfer193S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer193S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer193S1,d2Transfer193Lo,d2Transfer193Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer193C1,d2Log58Q,d2Transfer193S1,d2Transfer193Lo,d2Transfer193Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer193C1 d2Transfer193S1 d2Log58Q d2Log58Lo d2Log58Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log58Bounds
  have har : (((weightedUpper d2Transfer193C0 d2Log116Lo d2Log116Hi:ℚ):ℝ) + ((weightedUpper d2Transfer193C1 d2Log58Lo d2Log58Hi:ℚ):ℝ)) ≤ ((d2Transfer193Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer193Arithmetic
  linarith
#print axioms d2Transfer193Arithmetic
#print axioms d2Transfer193Bound
def d2Transfer194Lo : ℚ := (d2LitsNearTransfers024.q2 (25081867) 1 (-26))
def d2Transfer194Hi : ℚ := (d2LitsNearTransfers024.q2 (6689897) 1 (-24))
def d2Transfer194Cap : ℚ := (d2LitsNearTransfers024.q2 (649441385) 1 (-39))
def d2Transfer194C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 25 (-4))
def d2Transfer194S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer194Arithmetic : weightedUpper d2Transfer194C0 d2Log117Lo d2Log117Hi ≤ d2Transfer194Cap := by decide +kernel
theorem d2Transfer194Bound : ∀ x ∈ Set.Icc ((d2Transfer194Lo:ℚ):ℝ) ((d2Transfer194Hi:ℚ):ℝ), ((d2Transfer194C0:ℚ):ℝ)*Real.log |x-((d2Transfer194S0:ℚ):ℝ)| ≤ ((d2Transfer194Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer194S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer194S0,d2Transfer194Lo,d2Transfer194Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer194C0 then |x-((d2Transfer194S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer194S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer194S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer194S0,d2Transfer194Lo,d2Transfer194Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer194C0,d2Log117Q,d2Transfer194S0,d2Transfer194Lo,d2Transfer194Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer194C0 d2Transfer194S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2Transfer194C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2Transfer194Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer194Arithmetic
  linarith
#print axioms d2Transfer194Arithmetic
#print axioms d2Transfer194Bound
def d2Transfer195Lo : ℚ := (d2LitsNearTransfers024.q2 (25081867) 1 (-26))
def d2Transfer195Hi : ℚ := (d2LitsNearTransfers024.q2 (6689897) 1 (-24))
def d2Transfer195Cap : ℚ := (d2LitsNearTransfers024.q2 (2436024149) 1 (-40))
def d2Transfer195C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 275 (-4))
def d2Transfer195S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
def d2Transfer195C1 : ℚ := (d2LitsNearTransfers024.q2 (-1) 55 (-3))
def d2Transfer195S1 : ℚ := (d2LitsNearTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer195Arithmetic : weightedUpper d2Transfer195C0 d2Log117Lo d2Log117Hi + weightedUpper d2Transfer195C1 d2Log57Lo d2Log57Hi ≤ d2Transfer195Cap := by decide +kernel
theorem d2Transfer195Bound : ∀ x ∈ Set.Icc ((d2Transfer195Lo:ℚ):ℝ) ((d2Transfer195Hi:ℚ):ℝ), ((d2Transfer195C0:ℚ):ℝ)*Real.log |x-((d2Transfer195S0:ℚ):ℝ)| + ((d2Transfer195C1:ℚ):ℝ)*Real.log |x-((d2Transfer195S1:ℚ):ℝ)| ≤ ((d2Transfer195Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer195S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer195S0,d2Transfer195Lo,d2Transfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer195C0 then |x-((d2Transfer195S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer195S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer195S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer195S0,d2Transfer195Lo,d2Transfer195Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer195C0,d2Log117Q,d2Transfer195S0,d2Transfer195Lo,d2Transfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer195C0 d2Transfer195S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2Transfer195S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer195S1,d2Transfer195Lo,d2Transfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer195C1 then |x-((d2Transfer195S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2Transfer195S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer195S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer195S1,d2Transfer195Lo,d2Transfer195Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer195C1,d2Log57Q,d2Transfer195S1,d2Transfer195Lo,d2Transfer195Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer195C1 d2Transfer195S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2Transfer195C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2Transfer195C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2Transfer195Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer195Arithmetic
  linarith
#print axioms d2Transfer195Arithmetic
#print axioms d2Transfer195Bound
def d2Transfer196Lo : ℚ := (d2LitsNearTransfers024.q2 (25081867) 1 (-26))
def d2Transfer196Hi : ℚ := (d2LitsNearTransfers024.q2 (6689897) 1 (-24))
def d2Transfer196Cap : ℚ := (d2LitsNearTransfers024.q2 (16281318465) 1 (-40))
def d2Transfer196C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 1 (-5))
def d2Transfer196S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer196Arithmetic : weightedUpper d2Transfer196C0 d2Log117Lo d2Log117Hi ≤ d2Transfer196Cap := by decide +kernel
theorem d2Transfer196Bound : ∀ x ∈ Set.Icc ((d2Transfer196Lo:ℚ):ℝ) ((d2Transfer196Hi:ℚ):ℝ), ((d2Transfer196C0:ℚ):ℝ)*Real.log |x-((d2Transfer196S0:ℚ):ℝ)| ≤ ((d2Transfer196Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer196S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer196S0,d2Transfer196Lo,d2Transfer196Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer196C0 then |x-((d2Transfer196S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer196S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer196S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer196S0,d2Transfer196Lo,d2Transfer196Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer196C0,d2Log117Q,d2Transfer196S0,d2Transfer196Lo,d2Transfer196Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer196C0 d2Transfer196S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2Transfer196C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2Transfer196Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer196Arithmetic
  linarith
#print axioms d2Transfer196Arithmetic
#print axioms d2Transfer196Bound
def d2Transfer197Lo : ℚ := (d2LitsNearTransfers024.q2 (25081867) 1 (-26))
def d2Transfer197Hi : ℚ := (d2LitsNearTransfers024.q2 (6689897) 1 (-24))
def d2Transfer197Cap : ℚ := (d2LitsNearTransfers024.q2 (31165051305) 1 (-40))
def d2Transfer197C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 11 (-5))
def d2Transfer197S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
def d2Transfer197C1 : ℚ := (d2LitsNearTransfers024.q2 (-5) 11 (-4))
def d2Transfer197S1 : ℚ := (d2LitsNearTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer197Arithmetic : weightedUpper d2Transfer197C0 d2Log117Lo d2Log117Hi + weightedUpper d2Transfer197C1 d2Log57Lo d2Log57Hi ≤ d2Transfer197Cap := by decide +kernel
theorem d2Transfer197Bound : ∀ x ∈ Set.Icc ((d2Transfer197Lo:ℚ):ℝ) ((d2Transfer197Hi:ℚ):ℝ), ((d2Transfer197C0:ℚ):ℝ)*Real.log |x-((d2Transfer197S0:ℚ):ℝ)| + ((d2Transfer197C1:ℚ):ℝ)*Real.log |x-((d2Transfer197S1:ℚ):ℝ)| ≤ ((d2Transfer197Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer197S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer197S0,d2Transfer197Lo,d2Transfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer197C0 then |x-((d2Transfer197S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer197S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer197S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer197S0,d2Transfer197Lo,d2Transfer197Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer197C0,d2Log117Q,d2Transfer197S0,d2Transfer197Lo,d2Transfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer197C0 d2Transfer197S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2Transfer197S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer197S1,d2Transfer197Lo,d2Transfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer197C1 then |x-((d2Transfer197S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2Transfer197S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer197S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer197S1,d2Transfer197Lo,d2Transfer197Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer197C1,d2Log57Q,d2Transfer197S1,d2Transfer197Lo,d2Transfer197Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer197C1 d2Transfer197S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2Transfer197C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2Transfer197C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2Transfer197Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer197Arithmetic
  linarith
#print axioms d2Transfer197Arithmetic
#print axioms d2Transfer197Bound
def d2Transfer198Lo : ℚ := (d2LitsNearTransfers024.q2 (6689897) 1 (-24))
def d2Transfer198Hi : ℚ := (d2LitsNearTransfers024.q2 (15057515) 1 (-25))
def d2Transfer198Cap : ℚ := (d2LitsNearTransfers024.q2 (649441385) 1 (-39))
def d2Transfer198C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 25 (-4))
def d2Transfer198S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer198Arithmetic : weightedUpper d2Transfer198C0 d2Log119Lo d2Log119Hi ≤ d2Transfer198Cap := by decide +kernel
theorem d2Transfer198Bound : ∀ x ∈ Set.Icc ((d2Transfer198Lo:ℚ):ℝ) ((d2Transfer198Hi:ℚ):ℝ), ((d2Transfer198C0:ℚ):ℝ)*Real.log |x-((d2Transfer198S0:ℚ):ℝ)| ≤ ((d2Transfer198Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer198S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer198S0,d2Transfer198Lo,d2Transfer198Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer198C0 then |x-((d2Transfer198S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer198S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer198S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer198S0,d2Transfer198Lo,d2Transfer198Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer198C0,d2Log119Q,d2Transfer198S0,d2Transfer198Lo,d2Transfer198Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer198C0 d2Transfer198S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have har : (((weightedUpper d2Transfer198C0 d2Log119Lo d2Log119Hi:ℚ):ℝ)) ≤ ((d2Transfer198Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer198Arithmetic
  linarith
#print axioms d2Transfer198Arithmetic
#print axioms d2Transfer198Bound
def d2Transfer199Lo : ℚ := (d2LitsNearTransfers024.q2 (6689897) 1 (-24))
def d2Transfer199Hi : ℚ := (d2LitsNearTransfers024.q2 (15057515) 1 (-25))
def d2Transfer199Cap : ℚ := (d2LitsNearTransfers024.q2 (2436024149) 1 (-40))
def d2Transfer199C0 : ℚ := (d2LitsNearTransfers024.q2 (1) 275 (-4))
def d2Transfer199S0 : ℚ := (d2LitsNearTransfers024.q2 (-1) 1 (0))
def d2Transfer199C1 : ℚ := (d2LitsNearTransfers024.q2 (-1) 55 (-3))
def d2Transfer199S1 : ℚ := (d2LitsNearTransfers024.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer199Arithmetic : weightedUpper d2Transfer199C0 d2Log119Lo d2Log119Hi + weightedUpper d2Transfer199C1 d2Log55Lo d2Log55Hi ≤ d2Transfer199Cap := by decide +kernel
theorem d2Transfer199Bound : ∀ x ∈ Set.Icc ((d2Transfer199Lo:ℚ):ℝ) ((d2Transfer199Hi:ℚ):ℝ), ((d2Transfer199C0:ℚ):ℝ)*Real.log |x-((d2Transfer199S0:ℚ):ℝ)| + ((d2Transfer199C1:ℚ):ℝ)*Real.log |x-((d2Transfer199S1:ℚ):ℝ)| ≤ ((d2Transfer199Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer199S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer199S0,d2Transfer199Lo,d2Transfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer199C0 then |x-((d2Transfer199S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer199S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer199S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer199S0,d2Transfer199Lo,d2Transfer199Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer199C0,d2Log119Q,d2Transfer199S0,d2Transfer199Lo,d2Transfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer199C0 d2Transfer199S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have hn1 : x-((d2Transfer199S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer199S1,d2Transfer199Lo,d2Transfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer199C1 then |x-((d2Transfer199S1:ℚ):ℝ)| ≤ ((d2Log55Q:ℚ):ℝ) else ((d2Log55Q:ℚ):ℝ) ≤ |x-((d2Transfer199S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer199S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer199S1,d2Transfer199Lo,d2Transfer199Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers024.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer199C1,d2Log55Q,d2Transfer199S1,d2Transfer199Lo,d2Transfer199Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer199C1 d2Transfer199S1 d2Log55Q d2Log55Lo d2Log55Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log55Bounds
  have har : (((weightedUpper d2Transfer199C0 d2Log119Lo d2Log119Hi:ℚ):ℝ) + ((weightedUpper d2Transfer199C1 d2Log55Lo d2Log55Hi:ℚ):ℝ)) ≤ ((d2Transfer199Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer199Arithmetic
  linarith
#print axioms d2Transfer199Arithmetic
#print axioms d2Transfer199Bound
end CatalanMeasure.GenD.Signed.Data.Cells
