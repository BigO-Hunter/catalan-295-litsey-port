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
namespace d2LitsNearTransfers003
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers003
open D72.LogTransfer
def d2Transfer24Lo : ℚ := (d2LitsNearTransfers003.q2 (21642477) 1 (-27))
def d2Transfer24Hi : ℚ := (d2LitsNearTransfers003.q2 (11660099) 1 (-26))
def d2Transfer24Cap : ℚ := (d2LitsNearTransfers003.q2 (648894057) 1 (-39))
def d2Transfer24C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 25 (-4))
def d2Transfer24S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer24Arithmetic : weightedUpper d2Transfer24C0 d2Log103Lo d2Log103Hi ≤ d2Transfer24Cap := by decide +kernel
theorem d2Transfer24Bound : ∀ x ∈ Set.Icc ((d2Transfer24Lo:ℚ):ℝ) ((d2Transfer24Hi:ℚ):ℝ), ((d2Transfer24C0:ℚ):ℝ)*Real.log |x-((d2Transfer24S0:ℚ):ℝ)| ≤ ((d2Transfer24Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer24S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer24S0,d2Transfer24Lo,d2Transfer24Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer24C0 then |x-((d2Transfer24S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer24S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer24S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer24S0,d2Transfer24Lo,d2Transfer24Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer24C0,d2Log103Q,d2Transfer24S0,d2Transfer24Lo,d2Transfer24Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer24C0 d2Transfer24S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have har : (((weightedUpper d2Transfer24C0 d2Log103Lo d2Log103Hi:ℚ):ℝ)) ≤ ((d2Transfer24Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer24Arithmetic
  linarith
#print axioms d2Transfer24Arithmetic
#print axioms d2Transfer24Bound
def d2Transfer25Lo : ℚ := (d2LitsNearTransfers003.q2 (21642477) 1 (-27))
def d2Transfer25Hi : ℚ := (d2LitsNearTransfers003.q2 (11660099) 1 (-26))
def d2Transfer25Cap : ℚ := (d2LitsNearTransfers003.q2 (2432512853) 1 (-40))
def d2Transfer25C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 275 (-4))
def d2Transfer25S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
def d2Transfer25C1 : ℚ := (d2LitsNearTransfers003.q2 (-1) 55 (-3))
def d2Transfer25S1 : ℚ := (d2LitsNearTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer25Arithmetic : weightedUpper d2Transfer25C0 d2Log103Lo d2Log103Hi + weightedUpper d2Transfer25C1 d2Log71Lo d2Log71Hi ≤ d2Transfer25Cap := by decide +kernel
theorem d2Transfer25Bound : ∀ x ∈ Set.Icc ((d2Transfer25Lo:ℚ):ℝ) ((d2Transfer25Hi:ℚ):ℝ), ((d2Transfer25C0:ℚ):ℝ)*Real.log |x-((d2Transfer25S0:ℚ):ℝ)| + ((d2Transfer25C1:ℚ):ℝ)*Real.log |x-((d2Transfer25S1:ℚ):ℝ)| ≤ ((d2Transfer25Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer25S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer25S0,d2Transfer25Lo,d2Transfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer25C0 then |x-((d2Transfer25S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer25S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer25S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer25S0,d2Transfer25Lo,d2Transfer25Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer25C0,d2Log103Q,d2Transfer25S0,d2Transfer25Lo,d2Transfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer25C0 d2Transfer25S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have hn1 : x-((d2Transfer25S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer25S1,d2Transfer25Lo,d2Transfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer25C1 then |x-((d2Transfer25S1:ℚ):ℝ)| ≤ ((d2Log71Q:ℚ):ℝ) else ((d2Log71Q:ℚ):ℝ) ≤ |x-((d2Transfer25S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer25S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer25S1,d2Transfer25Lo,d2Transfer25Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer25C1,d2Log71Q,d2Transfer25S1,d2Transfer25Lo,d2Transfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer25C1 d2Transfer25S1 d2Log71Q d2Log71Lo d2Log71Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log71Bounds
  have har : (((weightedUpper d2Transfer25C0 d2Log103Lo d2Log103Hi:ℚ):ℝ) + ((weightedUpper d2Transfer25C1 d2Log71Lo d2Log71Hi:ℚ):ℝ)) ≤ ((d2Transfer25Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer25Arithmetic
  linarith
#print axioms d2Transfer25Arithmetic
#print axioms d2Transfer25Bound
def d2Transfer26Lo : ℚ := (d2LitsNearTransfers003.q2 (11660099) 1 (-26))
def d2Transfer26Hi : ℚ := (d2LitsNearTransfers003.q2 (24997919) 1 (-27))
def d2Transfer26Cap : ℚ := (d2LitsNearTransfers003.q2 (648894057) 1 (-39))
def d2Transfer26C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 25 (-4))
def d2Transfer26S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer26Arithmetic : weightedUpper d2Transfer26C0 d2Log105Lo d2Log105Hi ≤ d2Transfer26Cap := by decide +kernel
theorem d2Transfer26Bound : ∀ x ∈ Set.Icc ((d2Transfer26Lo:ℚ):ℝ) ((d2Transfer26Hi:ℚ):ℝ), ((d2Transfer26C0:ℚ):ℝ)*Real.log |x-((d2Transfer26S0:ℚ):ℝ)| ≤ ((d2Transfer26Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer26S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer26S0,d2Transfer26Lo,d2Transfer26Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer26C0 then |x-((d2Transfer26S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer26S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer26S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer26S0,d2Transfer26Lo,d2Transfer26Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer26C0,d2Log105Q,d2Transfer26S0,d2Transfer26Lo,d2Transfer26Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer26C0 d2Transfer26S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have har : (((weightedUpper d2Transfer26C0 d2Log105Lo d2Log105Hi:ℚ):ℝ)) ≤ ((d2Transfer26Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer26Arithmetic
  linarith
#print axioms d2Transfer26Arithmetic
#print axioms d2Transfer26Bound
def d2Transfer27Lo : ℚ := (d2LitsNearTransfers003.q2 (11660099) 1 (-26))
def d2Transfer27Hi : ℚ := (d2LitsNearTransfers003.q2 (24997919) 1 (-27))
def d2Transfer27Cap : ℚ := (d2LitsNearTransfers003.q2 (2432512853) 1 (-40))
def d2Transfer27C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 275 (-4))
def d2Transfer27S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
def d2Transfer27C1 : ℚ := (d2LitsNearTransfers003.q2 (-1) 55 (-3))
def d2Transfer27S1 : ℚ := (d2LitsNearTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer27Arithmetic : weightedUpper d2Transfer27C0 d2Log105Lo d2Log105Hi + weightedUpper d2Transfer27C1 d2Log69Lo d2Log69Hi ≤ d2Transfer27Cap := by decide +kernel
theorem d2Transfer27Bound : ∀ x ∈ Set.Icc ((d2Transfer27Lo:ℚ):ℝ) ((d2Transfer27Hi:ℚ):ℝ), ((d2Transfer27C0:ℚ):ℝ)*Real.log |x-((d2Transfer27S0:ℚ):ℝ)| + ((d2Transfer27C1:ℚ):ℝ)*Real.log |x-((d2Transfer27S1:ℚ):ℝ)| ≤ ((d2Transfer27Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer27S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer27S0,d2Transfer27Lo,d2Transfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer27C0 then |x-((d2Transfer27S0:ℚ):ℝ)| ≤ ((d2Log105Q:ℚ):ℝ) else ((d2Log105Q:ℚ):ℝ) ≤ |x-((d2Transfer27S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer27S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer27S0,d2Transfer27Lo,d2Transfer27Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer27C0,d2Log105Q,d2Transfer27S0,d2Transfer27Lo,d2Transfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer27C0 d2Transfer27S0 d2Log105Q d2Log105Lo d2Log105Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log105Bounds
  have hn1 : x-((d2Transfer27S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer27S1,d2Transfer27Lo,d2Transfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer27C1 then |x-((d2Transfer27S1:ℚ):ℝ)| ≤ ((d2Log69Q:ℚ):ℝ) else ((d2Log69Q:ℚ):ℝ) ≤ |x-((d2Transfer27S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer27S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer27S1,d2Transfer27Lo,d2Transfer27Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer27C1,d2Log69Q,d2Transfer27S1,d2Transfer27Lo,d2Transfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer27C1 d2Transfer27S1 d2Log69Q d2Log69Lo d2Log69Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log69Bounds
  have har : (((weightedUpper d2Transfer27C0 d2Log105Lo d2Log105Hi:ℚ):ℝ) + ((weightedUpper d2Transfer27C1 d2Log69Lo d2Log69Hi:ℚ):ℝ)) ≤ ((d2Transfer27Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer27Arithmetic
  linarith
#print axioms d2Transfer27Arithmetic
#print axioms d2Transfer27Bound
def d2Transfer28Lo : ℚ := (d2LitsNearTransfers003.q2 (24997919) 1 (-27))
def d2Transfer28Hi : ℚ := (d2LitsNearTransfers003.q2 (3334455) 1 (-24))
def d2Transfer28Cap : ℚ := (d2LitsNearTransfers003.q2 (648894057) 1 (-39))
def d2Transfer28C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 25 (-4))
def d2Transfer28S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer28Arithmetic : weightedUpper d2Transfer28C0 d2Log106Lo d2Log106Hi ≤ d2Transfer28Cap := by decide +kernel
theorem d2Transfer28Bound : ∀ x ∈ Set.Icc ((d2Transfer28Lo:ℚ):ℝ) ((d2Transfer28Hi:ℚ):ℝ), ((d2Transfer28C0:ℚ):ℝ)*Real.log |x-((d2Transfer28S0:ℚ):ℝ)| ≤ ((d2Transfer28Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer28S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer28S0,d2Transfer28Lo,d2Transfer28Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer28C0 then |x-((d2Transfer28S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer28S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer28S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer28S0,d2Transfer28Lo,d2Transfer28Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer28C0,d2Log106Q,d2Transfer28S0,d2Transfer28Lo,d2Transfer28Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer28C0 d2Transfer28S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2Transfer28C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2Transfer28Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer28Arithmetic
  linarith
#print axioms d2Transfer28Arithmetic
#print axioms d2Transfer28Bound
def d2Transfer29Lo : ℚ := (d2LitsNearTransfers003.q2 (24997919) 1 (-27))
def d2Transfer29Hi : ℚ := (d2LitsNearTransfers003.q2 (3334455) 1 (-24))
def d2Transfer29Cap : ℚ := (d2LitsNearTransfers003.q2 (2432512853) 1 (-40))
def d2Transfer29C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 275 (-4))
def d2Transfer29S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
def d2Transfer29C1 : ℚ := (d2LitsNearTransfers003.q2 (-1) 55 (-3))
def d2Transfer29S1 : ℚ := (d2LitsNearTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer29Arithmetic : weightedUpper d2Transfer29C0 d2Log106Lo d2Log106Hi + weightedUpper d2Transfer29C1 d2Log68Lo d2Log68Hi ≤ d2Transfer29Cap := by decide +kernel
theorem d2Transfer29Bound : ∀ x ∈ Set.Icc ((d2Transfer29Lo:ℚ):ℝ) ((d2Transfer29Hi:ℚ):ℝ), ((d2Transfer29C0:ℚ):ℝ)*Real.log |x-((d2Transfer29S0:ℚ):ℝ)| + ((d2Transfer29C1:ℚ):ℝ)*Real.log |x-((d2Transfer29S1:ℚ):ℝ)| ≤ ((d2Transfer29Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer29S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer29S0,d2Transfer29Lo,d2Transfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer29C0 then |x-((d2Transfer29S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer29S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer29S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer29S0,d2Transfer29Lo,d2Transfer29Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer29C0,d2Log106Q,d2Transfer29S0,d2Transfer29Lo,d2Transfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer29C0 d2Transfer29S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2Transfer29S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer29S1,d2Transfer29Lo,d2Transfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer29C1 then |x-((d2Transfer29S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2Transfer29S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer29S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer29S1,d2Transfer29Lo,d2Transfer29Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer29C1,d2Log68Q,d2Transfer29S1,d2Transfer29Lo,d2Transfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer29C1 d2Transfer29S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2Transfer29C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2Transfer29C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2Transfer29Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer29Arithmetic
  linarith
#print axioms d2Transfer29Arithmetic
#print axioms d2Transfer29Bound
def d2Transfer30Lo : ℚ := (d2LitsNearTransfers003.q2 (3334455) 1 (-24))
def d2Transfer30Hi : ℚ := (d2LitsNearTransfers003.q2 (28353361) 1 (-27))
def d2Transfer30Cap : ℚ := (d2LitsNearTransfers003.q2 (648894057) 1 (-39))
def d2Transfer30C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 25 (-4))
def d2Transfer30S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer30Arithmetic : weightedUpper d2Transfer30C0 d2Log107Lo d2Log107Hi ≤ d2Transfer30Cap := by decide +kernel
theorem d2Transfer30Bound : ∀ x ∈ Set.Icc ((d2Transfer30Lo:ℚ):ℝ) ((d2Transfer30Hi:ℚ):ℝ), ((d2Transfer30C0:ℚ):ℝ)*Real.log |x-((d2Transfer30S0:ℚ):ℝ)| ≤ ((d2Transfer30Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer30S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer30S0,d2Transfer30Lo,d2Transfer30Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer30C0 then |x-((d2Transfer30S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer30S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer30S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer30S0,d2Transfer30Lo,d2Transfer30Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer30C0,d2Log107Q,d2Transfer30S0,d2Transfer30Lo,d2Transfer30Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer30C0 d2Transfer30S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have har : (((weightedUpper d2Transfer30C0 d2Log107Lo d2Log107Hi:ℚ):ℝ)) ≤ ((d2Transfer30Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer30Arithmetic
  linarith
#print axioms d2Transfer30Arithmetic
#print axioms d2Transfer30Bound
def d2Transfer31Lo : ℚ := (d2LitsNearTransfers003.q2 (3334455) 1 (-24))
def d2Transfer31Hi : ℚ := (d2LitsNearTransfers003.q2 (28353361) 1 (-27))
def d2Transfer31Cap : ℚ := (d2LitsNearTransfers003.q2 (2432512853) 1 (-40))
def d2Transfer31C0 : ℚ := (d2LitsNearTransfers003.q2 (1) 275 (-4))
def d2Transfer31S0 : ℚ := (d2LitsNearTransfers003.q2 (-1) 1 (0))
def d2Transfer31C1 : ℚ := (d2LitsNearTransfers003.q2 (-1) 55 (-3))
def d2Transfer31S1 : ℚ := (d2LitsNearTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer31Arithmetic : weightedUpper d2Transfer31C0 d2Log107Lo d2Log107Hi + weightedUpper d2Transfer31C1 d2Log67Lo d2Log67Hi ≤ d2Transfer31Cap := by decide +kernel
theorem d2Transfer31Bound : ∀ x ∈ Set.Icc ((d2Transfer31Lo:ℚ):ℝ) ((d2Transfer31Hi:ℚ):ℝ), ((d2Transfer31C0:ℚ):ℝ)*Real.log |x-((d2Transfer31S0:ℚ):ℝ)| + ((d2Transfer31C1:ℚ):ℝ)*Real.log |x-((d2Transfer31S1:ℚ):ℝ)| ≤ ((d2Transfer31Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer31S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer31S0,d2Transfer31Lo,d2Transfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer31C0 then |x-((d2Transfer31S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer31S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer31S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer31S0,d2Transfer31Lo,d2Transfer31Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer31C0,d2Log107Q,d2Transfer31S0,d2Transfer31Lo,d2Transfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer31C0 d2Transfer31S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have hn1 : x-((d2Transfer31S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer31S1,d2Transfer31Lo,d2Transfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer31C1 then |x-((d2Transfer31S1:ℚ):ℝ)| ≤ ((d2Log67Q:ℚ):ℝ) else ((d2Log67Q:ℚ):ℝ) ≤ |x-((d2Transfer31S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer31S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer31S1,d2Transfer31Lo,d2Transfer31Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer31C1,d2Log67Q,d2Transfer31S1,d2Transfer31Lo,d2Transfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer31C1 d2Transfer31S1 d2Log67Q d2Log67Lo d2Log67Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log67Bounds
  have har : (((weightedUpper d2Transfer31C0 d2Log107Lo d2Log107Hi:ℚ):ℝ) + ((weightedUpper d2Transfer31C1 d2Log67Lo d2Log67Hi:ℚ):ℝ)) ≤ ((d2Transfer31Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer31Arithmetic
  linarith
#print axioms d2Transfer31Arithmetic
#print axioms d2Transfer31Bound
end CatalanMeasure.GenD.Signed.Data.Cells
