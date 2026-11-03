module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers004
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers004
open D72.LogTransfer
def d2Transfer32Lo : ℚ := (d2LitsNearTransfers004.q2 (28353361) 1 (-27))
def d2Transfer32Hi : ℚ := (d2LitsNearTransfers004.q2 (15015541) 1 (-26))
def d2Transfer32Cap : ℚ := (d2LitsNearTransfers004.q2 (648894057) 1 (-39))
def d2Transfer32C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 25 (-4))
def d2Transfer32S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer32Arithmetic : weightedUpper d2Transfer32C0 d2Log108Lo d2Log108Hi ≤ d2Transfer32Cap := by decide +kernel
theorem d2Transfer32Bound : ∀ x ∈ Set.Icc ((d2Transfer32Lo:ℚ):ℝ) ((d2Transfer32Hi:ℚ):ℝ), ((d2Transfer32C0:ℚ):ℝ)*Real.log |x-((d2Transfer32S0:ℚ):ℝ)| ≤ ((d2Transfer32Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer32S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer32S0,d2Transfer32Lo,d2Transfer32Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer32C0 then |x-((d2Transfer32S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer32S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer32S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer32S0,d2Transfer32Lo,d2Transfer32Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer32C0,d2Log108Q,d2Transfer32S0,d2Transfer32Lo,d2Transfer32Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer32C0 d2Transfer32S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have har : (((weightedUpper d2Transfer32C0 d2Log108Lo d2Log108Hi:ℚ):ℝ)) ≤ ((d2Transfer32Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer32Arithmetic
  linarith
#print axioms d2Transfer32Arithmetic
#print axioms d2Transfer32Bound
def d2Transfer33Lo : ℚ := (d2LitsNearTransfers004.q2 (28353361) 1 (-27))
def d2Transfer33Hi : ℚ := (d2LitsNearTransfers004.q2 (15015541) 1 (-26))
def d2Transfer33Cap : ℚ := (d2LitsNearTransfers004.q2 (2432512853) 1 (-40))
def d2Transfer33C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 275 (-4))
def d2Transfer33S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
def d2Transfer33C1 : ℚ := (d2LitsNearTransfers004.q2 (-1) 55 (-3))
def d2Transfer33S1 : ℚ := (d2LitsNearTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer33Arithmetic : weightedUpper d2Transfer33C0 d2Log108Lo d2Log108Hi + weightedUpper d2Transfer33C1 d2Log66Lo d2Log66Hi ≤ d2Transfer33Cap := by decide +kernel
theorem d2Transfer33Bound : ∀ x ∈ Set.Icc ((d2Transfer33Lo:ℚ):ℝ) ((d2Transfer33Hi:ℚ):ℝ), ((d2Transfer33C0:ℚ):ℝ)*Real.log |x-((d2Transfer33S0:ℚ):ℝ)| + ((d2Transfer33C1:ℚ):ℝ)*Real.log |x-((d2Transfer33S1:ℚ):ℝ)| ≤ ((d2Transfer33Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer33S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer33S0,d2Transfer33Lo,d2Transfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer33C0 then |x-((d2Transfer33S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer33S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer33S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer33S0,d2Transfer33Lo,d2Transfer33Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer33C0,d2Log108Q,d2Transfer33S0,d2Transfer33Lo,d2Transfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer33C0 d2Transfer33S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have hn1 : x-((d2Transfer33S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer33S1,d2Transfer33Lo,d2Transfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer33C1 then |x-((d2Transfer33S1:ℚ):ℝ)| ≤ ((d2Log66Q:ℚ):ℝ) else ((d2Log66Q:ℚ):ℝ) ≤ |x-((d2Transfer33S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer33S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer33S1,d2Transfer33Lo,d2Transfer33Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer33C1,d2Log66Q,d2Transfer33S1,d2Transfer33Lo,d2Transfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer33C1 d2Transfer33S1 d2Log66Q d2Log66Lo d2Log66Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log66Bounds
  have har : (((weightedUpper d2Transfer33C0 d2Log108Lo d2Log108Hi:ℚ):ℝ) + ((weightedUpper d2Transfer33C1 d2Log66Lo d2Log66Hi:ℚ):ℝ)) ≤ ((d2Transfer33Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer33Arithmetic
  linarith
#print axioms d2Transfer33Arithmetic
#print axioms d2Transfer33Bound
def d2Transfer34Lo : ℚ := (d2LitsNearTransfers004.q2 (15015541) 1 (-26))
def d2Transfer34Hi : ℚ := (d2LitsNearTransfers004.q2 (31708803) 1 (-27))
def d2Transfer34Cap : ℚ := (d2LitsNearTransfers004.q2 (648894057) 1 (-39))
def d2Transfer34C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 25 (-4))
def d2Transfer34S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer34Arithmetic : weightedUpper d2Transfer34C0 d2Log109Lo d2Log109Hi ≤ d2Transfer34Cap := by decide +kernel
theorem d2Transfer34Bound : ∀ x ∈ Set.Icc ((d2Transfer34Lo:ℚ):ℝ) ((d2Transfer34Hi:ℚ):ℝ), ((d2Transfer34C0:ℚ):ℝ)*Real.log |x-((d2Transfer34S0:ℚ):ℝ)| ≤ ((d2Transfer34Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer34S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer34S0,d2Transfer34Lo,d2Transfer34Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer34C0 then |x-((d2Transfer34S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer34S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer34S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer34S0,d2Transfer34Lo,d2Transfer34Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer34C0,d2Log109Q,d2Transfer34S0,d2Transfer34Lo,d2Transfer34Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer34C0 d2Transfer34S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have har : (((weightedUpper d2Transfer34C0 d2Log109Lo d2Log109Hi:ℚ):ℝ)) ≤ ((d2Transfer34Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer34Arithmetic
  linarith
#print axioms d2Transfer34Arithmetic
#print axioms d2Transfer34Bound
def d2Transfer35Lo : ℚ := (d2LitsNearTransfers004.q2 (15015541) 1 (-26))
def d2Transfer35Hi : ℚ := (d2LitsNearTransfers004.q2 (31708803) 1 (-27))
def d2Transfer35Cap : ℚ := (d2LitsNearTransfers004.q2 (2432512853) 1 (-40))
def d2Transfer35C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 275 (-4))
def d2Transfer35S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
def d2Transfer35C1 : ℚ := (d2LitsNearTransfers004.q2 (-1) 55 (-3))
def d2Transfer35S1 : ℚ := (d2LitsNearTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer35Arithmetic : weightedUpper d2Transfer35C0 d2Log109Lo d2Log109Hi + weightedUpper d2Transfer35C1 d2Log65Lo d2Log65Hi ≤ d2Transfer35Cap := by decide +kernel
theorem d2Transfer35Bound : ∀ x ∈ Set.Icc ((d2Transfer35Lo:ℚ):ℝ) ((d2Transfer35Hi:ℚ):ℝ), ((d2Transfer35C0:ℚ):ℝ)*Real.log |x-((d2Transfer35S0:ℚ):ℝ)| + ((d2Transfer35C1:ℚ):ℝ)*Real.log |x-((d2Transfer35S1:ℚ):ℝ)| ≤ ((d2Transfer35Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer35S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer35S0,d2Transfer35Lo,d2Transfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer35C0 then |x-((d2Transfer35S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer35S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer35S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer35S0,d2Transfer35Lo,d2Transfer35Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer35C0,d2Log109Q,d2Transfer35S0,d2Transfer35Lo,d2Transfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer35C0 d2Transfer35S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have hn1 : x-((d2Transfer35S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer35S1,d2Transfer35Lo,d2Transfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer35C1 then |x-((d2Transfer35S1:ℚ):ℝ)| ≤ ((d2Log65Q:ℚ):ℝ) else ((d2Log65Q:ℚ):ℝ) ≤ |x-((d2Transfer35S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer35S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer35S1,d2Transfer35Lo,d2Transfer35Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer35C1,d2Log65Q,d2Transfer35S1,d2Transfer35Lo,d2Transfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer35C1 d2Transfer35S1 d2Log65Q d2Log65Lo d2Log65Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log65Bounds
  have har : (((weightedUpper d2Transfer35C0 d2Log109Lo d2Log109Hi:ℚ):ℝ) + ((weightedUpper d2Transfer35C1 d2Log65Lo d2Log65Hi:ℚ):ℝ)) ≤ ((d2Transfer35Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer35Arithmetic
  linarith
#print axioms d2Transfer35Arithmetic
#print axioms d2Transfer35Bound
def d2Transfer36Lo : ℚ := (d2LitsNearTransfers004.q2 (31708803) 1 (-27))
def d2Transfer36Hi : ℚ := (d2LitsNearTransfers004.q2 (8346631) 1 (-25))
def d2Transfer36Cap : ℚ := (d2LitsNearTransfers004.q2 (648894057) 1 (-39))
def d2Transfer36C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 25 (-4))
def d2Transfer36S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer36Arithmetic : weightedUpper d2Transfer36C0 d2Log110Lo d2Log110Hi ≤ d2Transfer36Cap := by decide +kernel
theorem d2Transfer36Bound : ∀ x ∈ Set.Icc ((d2Transfer36Lo:ℚ):ℝ) ((d2Transfer36Hi:ℚ):ℝ), ((d2Transfer36C0:ℚ):ℝ)*Real.log |x-((d2Transfer36S0:ℚ):ℝ)| ≤ ((d2Transfer36Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer36S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer36S0,d2Transfer36Lo,d2Transfer36Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer36C0 then |x-((d2Transfer36S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer36S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer36S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer36S0,d2Transfer36Lo,d2Transfer36Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer36C0,d2Log110Q,d2Transfer36S0,d2Transfer36Lo,d2Transfer36Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer36C0 d2Transfer36S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have har : (((weightedUpper d2Transfer36C0 d2Log110Lo d2Log110Hi:ℚ):ℝ)) ≤ ((d2Transfer36Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer36Arithmetic
  linarith
#print axioms d2Transfer36Arithmetic
#print axioms d2Transfer36Bound
def d2Transfer37Lo : ℚ := (d2LitsNearTransfers004.q2 (31708803) 1 (-27))
def d2Transfer37Hi : ℚ := (d2LitsNearTransfers004.q2 (8346631) 1 (-25))
def d2Transfer37Cap : ℚ := (d2LitsNearTransfers004.q2 (2432512853) 1 (-40))
def d2Transfer37C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 275 (-4))
def d2Transfer37S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
def d2Transfer37C1 : ℚ := (d2LitsNearTransfers004.q2 (-1) 55 (-3))
def d2Transfer37S1 : ℚ := (d2LitsNearTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer37Arithmetic : weightedUpper d2Transfer37C0 d2Log110Lo d2Log110Hi + weightedUpper d2Transfer37C1 d2Log64Lo d2Log64Hi ≤ d2Transfer37Cap := by decide +kernel
theorem d2Transfer37Bound : ∀ x ∈ Set.Icc ((d2Transfer37Lo:ℚ):ℝ) ((d2Transfer37Hi:ℚ):ℝ), ((d2Transfer37C0:ℚ):ℝ)*Real.log |x-((d2Transfer37S0:ℚ):ℝ)| + ((d2Transfer37C1:ℚ):ℝ)*Real.log |x-((d2Transfer37S1:ℚ):ℝ)| ≤ ((d2Transfer37Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer37S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer37S0,d2Transfer37Lo,d2Transfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer37C0 then |x-((d2Transfer37S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer37S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer37S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer37S0,d2Transfer37Lo,d2Transfer37Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer37C0,d2Log110Q,d2Transfer37S0,d2Transfer37Lo,d2Transfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer37C0 d2Transfer37S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have hn1 : x-((d2Transfer37S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer37S1,d2Transfer37Lo,d2Transfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer37C1 then |x-((d2Transfer37S1:ℚ):ℝ)| ≤ ((d2Log64Q:ℚ):ℝ) else ((d2Log64Q:ℚ):ℝ) ≤ |x-((d2Transfer37S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer37S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer37S1,d2Transfer37Lo,d2Transfer37Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer37C1,d2Log64Q,d2Transfer37S1,d2Transfer37Lo,d2Transfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer37C1 d2Transfer37S1 d2Log64Q d2Log64Lo d2Log64Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log64Bounds
  have har : (((weightedUpper d2Transfer37C0 d2Log110Lo d2Log110Hi:ℚ):ℝ) + ((weightedUpper d2Transfer37C1 d2Log64Lo d2Log64Hi:ℚ):ℝ)) ≤ ((d2Transfer37Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer37Arithmetic
  linarith
#print axioms d2Transfer37Arithmetic
#print axioms d2Transfer37Bound
def d2Transfer38Lo : ℚ := (d2LitsNearTransfers004.q2 (8346631) 1 (-25))
def d2Transfer38Hi : ℚ := (d2LitsNearTransfers004.q2 (18370983) 1 (-26))
def d2Transfer38Cap : ℚ := (d2LitsNearTransfers004.q2 (648894057) 1 (-39))
def d2Transfer38C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 25 (-4))
def d2Transfer38S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer38Arithmetic : weightedUpper d2Transfer38C0 d2Log112Lo d2Log112Hi ≤ d2Transfer38Cap := by decide +kernel
theorem d2Transfer38Bound : ∀ x ∈ Set.Icc ((d2Transfer38Lo:ℚ):ℝ) ((d2Transfer38Hi:ℚ):ℝ), ((d2Transfer38C0:ℚ):ℝ)*Real.log |x-((d2Transfer38S0:ℚ):ℝ)| ≤ ((d2Transfer38Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer38S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer38S0,d2Transfer38Lo,d2Transfer38Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer38C0 then |x-((d2Transfer38S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer38S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer38S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer38S0,d2Transfer38Lo,d2Transfer38Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer38C0,d2Log112Q,d2Transfer38S0,d2Transfer38Lo,d2Transfer38Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer38C0 d2Transfer38S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have har : (((weightedUpper d2Transfer38C0 d2Log112Lo d2Log112Hi:ℚ):ℝ)) ≤ ((d2Transfer38Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer38Arithmetic
  linarith
#print axioms d2Transfer38Arithmetic
#print axioms d2Transfer38Bound
def d2Transfer39Lo : ℚ := (d2LitsNearTransfers004.q2 (8346631) 1 (-25))
def d2Transfer39Hi : ℚ := (d2LitsNearTransfers004.q2 (18370983) 1 (-26))
def d2Transfer39Cap : ℚ := (d2LitsNearTransfers004.q2 (2432512853) 1 (-40))
def d2Transfer39C0 : ℚ := (d2LitsNearTransfers004.q2 (1) 275 (-4))
def d2Transfer39S0 : ℚ := (d2LitsNearTransfers004.q2 (-1) 1 (0))
def d2Transfer39C1 : ℚ := (d2LitsNearTransfers004.q2 (-1) 55 (-3))
def d2Transfer39S1 : ℚ := (d2LitsNearTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer39Arithmetic : weightedUpper d2Transfer39C0 d2Log112Lo d2Log112Hi + weightedUpper d2Transfer39C1 d2Log62Lo d2Log62Hi ≤ d2Transfer39Cap := by decide +kernel
theorem d2Transfer39Bound : ∀ x ∈ Set.Icc ((d2Transfer39Lo:ℚ):ℝ) ((d2Transfer39Hi:ℚ):ℝ), ((d2Transfer39C0:ℚ):ℝ)*Real.log |x-((d2Transfer39S0:ℚ):ℝ)| + ((d2Transfer39C1:ℚ):ℝ)*Real.log |x-((d2Transfer39S1:ℚ):ℝ)| ≤ ((d2Transfer39Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer39S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer39S0,d2Transfer39Lo,d2Transfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer39C0 then |x-((d2Transfer39S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer39S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer39S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer39S0,d2Transfer39Lo,d2Transfer39Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer39C0,d2Log112Q,d2Transfer39S0,d2Transfer39Lo,d2Transfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer39C0 d2Transfer39S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have hn1 : x-((d2Transfer39S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer39S1,d2Transfer39Lo,d2Transfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer39C1 then |x-((d2Transfer39S1:ℚ):ℝ)| ≤ ((d2Log62Q:ℚ):ℝ) else ((d2Log62Q:ℚ):ℝ) ≤ |x-((d2Transfer39S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer39S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer39S1,d2Transfer39Lo,d2Transfer39Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers004.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer39C1,d2Log62Q,d2Transfer39S1,d2Transfer39Lo,d2Transfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer39C1 d2Transfer39S1 d2Log62Q d2Log62Lo d2Log62Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log62Bounds
  have har : (((weightedUpper d2Transfer39C0 d2Log112Lo d2Log112Hi:ℚ):ℝ) + ((weightedUpper d2Transfer39C1 d2Log62Lo d2Log62Hi:ℚ):ℝ)) ≤ ((d2Transfer39Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer39Arithmetic
  linarith
#print axioms d2Transfer39Arithmetic
#print axioms d2Transfer39Bound
end CatalanMeasure.GenD.Signed.Data.Cells
