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
namespace d2LitsNearTransfers020
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers020
open D72.LogTransfer
def d2Transfer160Lo : ℚ := (d2LitsNearTransfers020.q2 (28353361) 1 (-27))
def d2Transfer160Hi : ℚ := (d2LitsNearTransfers020.q2 (15015541) 1 (-26))
def d2Transfer160Cap : ℚ := (d2LitsNearTransfers020.q2 (16281318465) 1 (-40))
def d2Transfer160C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 1 (-5))
def d2Transfer160S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer160Arithmetic : weightedUpper d2Transfer160C0 d2Log108Lo d2Log108Hi ≤ d2Transfer160Cap := by decide +kernel
theorem d2Transfer160Bound : ∀ x ∈ Set.Icc ((d2Transfer160Lo:ℚ):ℝ) ((d2Transfer160Hi:ℚ):ℝ), ((d2Transfer160C0:ℚ):ℝ)*Real.log |x-((d2Transfer160S0:ℚ):ℝ)| ≤ ((d2Transfer160Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer160S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer160S0,d2Transfer160Lo,d2Transfer160Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer160C0 then |x-((d2Transfer160S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer160S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer160S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer160S0,d2Transfer160Lo,d2Transfer160Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer160C0,d2Log108Q,d2Transfer160S0,d2Transfer160Lo,d2Transfer160Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer160C0 d2Transfer160S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have har : (((weightedUpper d2Transfer160C0 d2Log108Lo d2Log108Hi:ℚ):ℝ)) ≤ ((d2Transfer160Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer160Arithmetic
  linarith
#print axioms d2Transfer160Arithmetic
#print axioms d2Transfer160Bound
def d2Transfer161Lo : ℚ := (d2LitsNearTransfers020.q2 (28353361) 1 (-27))
def d2Transfer161Hi : ℚ := (d2LitsNearTransfers020.q2 (15015541) 1 (-26))
def d2Transfer161Cap : ℚ := (d2LitsNearTransfers020.q2 (31165051305) 1 (-40))
def d2Transfer161C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 11 (-5))
def d2Transfer161S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
def d2Transfer161C1 : ℚ := (d2LitsNearTransfers020.q2 (-5) 11 (-4))
def d2Transfer161S1 : ℚ := (d2LitsNearTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer161Arithmetic : weightedUpper d2Transfer161C0 d2Log108Lo d2Log108Hi + weightedUpper d2Transfer161C1 d2Log66Lo d2Log66Hi ≤ d2Transfer161Cap := by decide +kernel
theorem d2Transfer161Bound : ∀ x ∈ Set.Icc ((d2Transfer161Lo:ℚ):ℝ) ((d2Transfer161Hi:ℚ):ℝ), ((d2Transfer161C0:ℚ):ℝ)*Real.log |x-((d2Transfer161S0:ℚ):ℝ)| + ((d2Transfer161C1:ℚ):ℝ)*Real.log |x-((d2Transfer161S1:ℚ):ℝ)| ≤ ((d2Transfer161Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer161S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer161S0,d2Transfer161Lo,d2Transfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer161C0 then |x-((d2Transfer161S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer161S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer161S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer161S0,d2Transfer161Lo,d2Transfer161Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer161C0,d2Log108Q,d2Transfer161S0,d2Transfer161Lo,d2Transfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer161C0 d2Transfer161S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have hn1 : x-((d2Transfer161S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer161S1,d2Transfer161Lo,d2Transfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer161C1 then |x-((d2Transfer161S1:ℚ):ℝ)| ≤ ((d2Log66Q:ℚ):ℝ) else ((d2Log66Q:ℚ):ℝ) ≤ |x-((d2Transfer161S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer161S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer161S1,d2Transfer161Lo,d2Transfer161Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer161C1,d2Log66Q,d2Transfer161S1,d2Transfer161Lo,d2Transfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer161C1 d2Transfer161S1 d2Log66Q d2Log66Lo d2Log66Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log66Bounds
  have har : (((weightedUpper d2Transfer161C0 d2Log108Lo d2Log108Hi:ℚ):ℝ) + ((weightedUpper d2Transfer161C1 d2Log66Lo d2Log66Hi:ℚ):ℝ)) ≤ ((d2Transfer161Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer161Arithmetic
  linarith
#print axioms d2Transfer161Arithmetic
#print axioms d2Transfer161Bound
def d2Transfer162Lo : ℚ := (d2LitsNearTransfers020.q2 (15015541) 1 (-26))
def d2Transfer162Hi : ℚ := (d2LitsNearTransfers020.q2 (31708803) 1 (-27))
def d2Transfer162Cap : ℚ := (d2LitsNearTransfers020.q2 (649441385) 1 (-39))
def d2Transfer162C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 25 (-4))
def d2Transfer162S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer162Arithmetic : weightedUpper d2Transfer162C0 d2Log109Lo d2Log109Hi ≤ d2Transfer162Cap := by decide +kernel
theorem d2Transfer162Bound : ∀ x ∈ Set.Icc ((d2Transfer162Lo:ℚ):ℝ) ((d2Transfer162Hi:ℚ):ℝ), ((d2Transfer162C0:ℚ):ℝ)*Real.log |x-((d2Transfer162S0:ℚ):ℝ)| ≤ ((d2Transfer162Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer162S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer162S0,d2Transfer162Lo,d2Transfer162Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer162C0 then |x-((d2Transfer162S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer162S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer162S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer162S0,d2Transfer162Lo,d2Transfer162Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer162C0,d2Log109Q,d2Transfer162S0,d2Transfer162Lo,d2Transfer162Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer162C0 d2Transfer162S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have har : (((weightedUpper d2Transfer162C0 d2Log109Lo d2Log109Hi:ℚ):ℝ)) ≤ ((d2Transfer162Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer162Arithmetic
  linarith
#print axioms d2Transfer162Arithmetic
#print axioms d2Transfer162Bound
def d2Transfer163Lo : ℚ := (d2LitsNearTransfers020.q2 (15015541) 1 (-26))
def d2Transfer163Hi : ℚ := (d2LitsNearTransfers020.q2 (31708803) 1 (-27))
def d2Transfer163Cap : ℚ := (d2LitsNearTransfers020.q2 (2436024149) 1 (-40))
def d2Transfer163C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 275 (-4))
def d2Transfer163S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
def d2Transfer163C1 : ℚ := (d2LitsNearTransfers020.q2 (-1) 55 (-3))
def d2Transfer163S1 : ℚ := (d2LitsNearTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer163Arithmetic : weightedUpper d2Transfer163C0 d2Log109Lo d2Log109Hi + weightedUpper d2Transfer163C1 d2Log65Lo d2Log65Hi ≤ d2Transfer163Cap := by decide +kernel
theorem d2Transfer163Bound : ∀ x ∈ Set.Icc ((d2Transfer163Lo:ℚ):ℝ) ((d2Transfer163Hi:ℚ):ℝ), ((d2Transfer163C0:ℚ):ℝ)*Real.log |x-((d2Transfer163S0:ℚ):ℝ)| + ((d2Transfer163C1:ℚ):ℝ)*Real.log |x-((d2Transfer163S1:ℚ):ℝ)| ≤ ((d2Transfer163Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer163S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer163S0,d2Transfer163Lo,d2Transfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer163C0 then |x-((d2Transfer163S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer163S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer163S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer163S0,d2Transfer163Lo,d2Transfer163Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer163C0,d2Log109Q,d2Transfer163S0,d2Transfer163Lo,d2Transfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer163C0 d2Transfer163S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have hn1 : x-((d2Transfer163S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer163S1,d2Transfer163Lo,d2Transfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer163C1 then |x-((d2Transfer163S1:ℚ):ℝ)| ≤ ((d2Log65Q:ℚ):ℝ) else ((d2Log65Q:ℚ):ℝ) ≤ |x-((d2Transfer163S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer163S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer163S1,d2Transfer163Lo,d2Transfer163Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer163C1,d2Log65Q,d2Transfer163S1,d2Transfer163Lo,d2Transfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer163C1 d2Transfer163S1 d2Log65Q d2Log65Lo d2Log65Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log65Bounds
  have har : (((weightedUpper d2Transfer163C0 d2Log109Lo d2Log109Hi:ℚ):ℝ) + ((weightedUpper d2Transfer163C1 d2Log65Lo d2Log65Hi:ℚ):ℝ)) ≤ ((d2Transfer163Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer163Arithmetic
  linarith
#print axioms d2Transfer163Arithmetic
#print axioms d2Transfer163Bound
def d2Transfer164Lo : ℚ := (d2LitsNearTransfers020.q2 (15015541) 1 (-26))
def d2Transfer164Hi : ℚ := (d2LitsNearTransfers020.q2 (31708803) 1 (-27))
def d2Transfer164Cap : ℚ := (d2LitsNearTransfers020.q2 (16281318465) 1 (-40))
def d2Transfer164C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 1 (-5))
def d2Transfer164S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer164Arithmetic : weightedUpper d2Transfer164C0 d2Log109Lo d2Log109Hi ≤ d2Transfer164Cap := by decide +kernel
theorem d2Transfer164Bound : ∀ x ∈ Set.Icc ((d2Transfer164Lo:ℚ):ℝ) ((d2Transfer164Hi:ℚ):ℝ), ((d2Transfer164C0:ℚ):ℝ)*Real.log |x-((d2Transfer164S0:ℚ):ℝ)| ≤ ((d2Transfer164Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer164S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer164S0,d2Transfer164Lo,d2Transfer164Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer164C0 then |x-((d2Transfer164S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer164S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer164S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer164S0,d2Transfer164Lo,d2Transfer164Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer164C0,d2Log109Q,d2Transfer164S0,d2Transfer164Lo,d2Transfer164Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer164C0 d2Transfer164S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have har : (((weightedUpper d2Transfer164C0 d2Log109Lo d2Log109Hi:ℚ):ℝ)) ≤ ((d2Transfer164Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer164Arithmetic
  linarith
#print axioms d2Transfer164Arithmetic
#print axioms d2Transfer164Bound
def d2Transfer165Lo : ℚ := (d2LitsNearTransfers020.q2 (15015541) 1 (-26))
def d2Transfer165Hi : ℚ := (d2LitsNearTransfers020.q2 (31708803) 1 (-27))
def d2Transfer165Cap : ℚ := (d2LitsNearTransfers020.q2 (31165051305) 1 (-40))
def d2Transfer165C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 11 (-5))
def d2Transfer165S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
def d2Transfer165C1 : ℚ := (d2LitsNearTransfers020.q2 (-5) 11 (-4))
def d2Transfer165S1 : ℚ := (d2LitsNearTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer165Arithmetic : weightedUpper d2Transfer165C0 d2Log109Lo d2Log109Hi + weightedUpper d2Transfer165C1 d2Log65Lo d2Log65Hi ≤ d2Transfer165Cap := by decide +kernel
theorem d2Transfer165Bound : ∀ x ∈ Set.Icc ((d2Transfer165Lo:ℚ):ℝ) ((d2Transfer165Hi:ℚ):ℝ), ((d2Transfer165C0:ℚ):ℝ)*Real.log |x-((d2Transfer165S0:ℚ):ℝ)| + ((d2Transfer165C1:ℚ):ℝ)*Real.log |x-((d2Transfer165S1:ℚ):ℝ)| ≤ ((d2Transfer165Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer165S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer165S0,d2Transfer165Lo,d2Transfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer165C0 then |x-((d2Transfer165S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer165S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer165S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer165S0,d2Transfer165Lo,d2Transfer165Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer165C0,d2Log109Q,d2Transfer165S0,d2Transfer165Lo,d2Transfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer165C0 d2Transfer165S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have hn1 : x-((d2Transfer165S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer165S1,d2Transfer165Lo,d2Transfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer165C1 then |x-((d2Transfer165S1:ℚ):ℝ)| ≤ ((d2Log65Q:ℚ):ℝ) else ((d2Log65Q:ℚ):ℝ) ≤ |x-((d2Transfer165S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer165S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer165S1,d2Transfer165Lo,d2Transfer165Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer165C1,d2Log65Q,d2Transfer165S1,d2Transfer165Lo,d2Transfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer165C1 d2Transfer165S1 d2Log65Q d2Log65Lo d2Log65Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log65Bounds
  have har : (((weightedUpper d2Transfer165C0 d2Log109Lo d2Log109Hi:ℚ):ℝ) + ((weightedUpper d2Transfer165C1 d2Log65Lo d2Log65Hi:ℚ):ℝ)) ≤ ((d2Transfer165Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer165Arithmetic
  linarith
#print axioms d2Transfer165Arithmetic
#print axioms d2Transfer165Bound
def d2Transfer166Lo : ℚ := (d2LitsNearTransfers020.q2 (31708803) 1 (-27))
def d2Transfer166Hi : ℚ := (d2LitsNearTransfers020.q2 (8346631) 1 (-25))
def d2Transfer166Cap : ℚ := (d2LitsNearTransfers020.q2 (649441385) 1 (-39))
def d2Transfer166C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 25 (-4))
def d2Transfer166S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer166Arithmetic : weightedUpper d2Transfer166C0 d2Log110Lo d2Log110Hi ≤ d2Transfer166Cap := by decide +kernel
theorem d2Transfer166Bound : ∀ x ∈ Set.Icc ((d2Transfer166Lo:ℚ):ℝ) ((d2Transfer166Hi:ℚ):ℝ), ((d2Transfer166C0:ℚ):ℝ)*Real.log |x-((d2Transfer166S0:ℚ):ℝ)| ≤ ((d2Transfer166Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer166S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer166S0,d2Transfer166Lo,d2Transfer166Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer166C0 then |x-((d2Transfer166S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer166S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer166S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer166S0,d2Transfer166Lo,d2Transfer166Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer166C0,d2Log110Q,d2Transfer166S0,d2Transfer166Lo,d2Transfer166Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer166C0 d2Transfer166S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have har : (((weightedUpper d2Transfer166C0 d2Log110Lo d2Log110Hi:ℚ):ℝ)) ≤ ((d2Transfer166Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer166Arithmetic
  linarith
#print axioms d2Transfer166Arithmetic
#print axioms d2Transfer166Bound
def d2Transfer167Lo : ℚ := (d2LitsNearTransfers020.q2 (31708803) 1 (-27))
def d2Transfer167Hi : ℚ := (d2LitsNearTransfers020.q2 (8346631) 1 (-25))
def d2Transfer167Cap : ℚ := (d2LitsNearTransfers020.q2 (2436024149) 1 (-40))
def d2Transfer167C0 : ℚ := (d2LitsNearTransfers020.q2 (1) 275 (-4))
def d2Transfer167S0 : ℚ := (d2LitsNearTransfers020.q2 (-1) 1 (0))
def d2Transfer167C1 : ℚ := (d2LitsNearTransfers020.q2 (-1) 55 (-3))
def d2Transfer167S1 : ℚ := (d2LitsNearTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer167Arithmetic : weightedUpper d2Transfer167C0 d2Log110Lo d2Log110Hi + weightedUpper d2Transfer167C1 d2Log64Lo d2Log64Hi ≤ d2Transfer167Cap := by decide +kernel
theorem d2Transfer167Bound : ∀ x ∈ Set.Icc ((d2Transfer167Lo:ℚ):ℝ) ((d2Transfer167Hi:ℚ):ℝ), ((d2Transfer167C0:ℚ):ℝ)*Real.log |x-((d2Transfer167S0:ℚ):ℝ)| + ((d2Transfer167C1:ℚ):ℝ)*Real.log |x-((d2Transfer167S1:ℚ):ℝ)| ≤ ((d2Transfer167Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer167S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer167S0,d2Transfer167Lo,d2Transfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer167C0 then |x-((d2Transfer167S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer167S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer167S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer167S0,d2Transfer167Lo,d2Transfer167Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer167C0,d2Log110Q,d2Transfer167S0,d2Transfer167Lo,d2Transfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer167C0 d2Transfer167S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have hn1 : x-((d2Transfer167S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer167S1,d2Transfer167Lo,d2Transfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer167C1 then |x-((d2Transfer167S1:ℚ):ℝ)| ≤ ((d2Log64Q:ℚ):ℝ) else ((d2Log64Q:ℚ):ℝ) ≤ |x-((d2Transfer167S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer167S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer167S1,d2Transfer167Lo,d2Transfer167Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers020.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer167C1,d2Log64Q,d2Transfer167S1,d2Transfer167Lo,d2Transfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer167C1 d2Transfer167S1 d2Log64Q d2Log64Lo d2Log64Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log64Bounds
  have har : (((weightedUpper d2Transfer167C0 d2Log110Lo d2Log110Hi:ℚ):ℝ) + ((weightedUpper d2Transfer167C1 d2Log64Lo d2Log64Hi:ℚ):ℝ)) ≤ ((d2Transfer167Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer167Arithmetic
  linarith
#print axioms d2Transfer167Arithmetic
#print axioms d2Transfer167Bound
end CatalanMeasure.GenD.Signed.Data.Cells
