module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers047
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers047
open D72.LogTransfer
def d2WiderTransfer376Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (45214519) 1 (-26))
def d2WiderTransfer376Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (2930765) 1 (-22))
def d2WiderTransfer376Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (4621244410980826169991) 1 (-79))
def d2WiderTransfer376C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 55 (-3))
def d2WiderTransfer376S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
def d2WiderTransfer376C1 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 55 (-3))
def d2WiderTransfer376S1 : ℚ := (d2LitsNearWiderTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer376Arithmetic : weightedUpper d2WiderTransfer376C0 d2Log165Lo d2Log165Hi + weightedUpper d2WiderTransfer376C1 d2Log8Lo d2Log8Hi ≤ d2WiderTransfer376Cap := by decide +kernel
theorem d2WiderTransfer376Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer376Lo:ℚ):ℝ) ((d2WiderTransfer376Hi:ℚ):ℝ), ((d2WiderTransfer376C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer376S0:ℚ):ℝ)| + ((d2WiderTransfer376C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer376S1:ℚ):ℝ)| ≤ ((d2WiderTransfer376Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer376S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer376S0,d2WiderTransfer376Lo,d2WiderTransfer376Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer376C0 then |x-((d2WiderTransfer376S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer376S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer376S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer376S0,d2WiderTransfer376Lo,d2WiderTransfer376Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer376C0,d2Log165Q,d2WiderTransfer376S0,d2WiderTransfer376Lo,d2WiderTransfer376Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer376C0 d2WiderTransfer376S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2WiderTransfer376S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer376S1,d2WiderTransfer376Lo,d2WiderTransfer376Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer376C1 then |x-((d2WiderTransfer376S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer376S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer376S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer376S1,d2WiderTransfer376Lo,d2WiderTransfer376Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer376C1,d2Log8Q,d2WiderTransfer376S1,d2WiderTransfer376Lo,d2WiderTransfer376Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer376C1 d2WiderTransfer376S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2WiderTransfer376C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer376C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer376Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer376Arithmetic
  linarith
#print axioms d2WiderTransfer376Arithmetic
#print axioms d2WiderTransfer376Bound
def d2WiderTransfer377Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (45214519) 1 (-26))
def d2WiderTransfer377Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (2930765) 1 (-22))
def d2WiderTransfer377Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (12287142347943969636999) 1 (-79))
def d2WiderTransfer377C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (23) 25 (-5))
def d2WiderTransfer377S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer377Arithmetic : weightedUpper d2WiderTransfer377C0 d2Log166Lo d2Log166Hi ≤ d2WiderTransfer377Cap := by decide +kernel
theorem d2WiderTransfer377Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer377Lo:ℚ):ℝ) ((d2WiderTransfer377Hi:ℚ):ℝ), ((d2WiderTransfer377C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer377S0:ℚ):ℝ)| ≤ ((d2WiderTransfer377Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer377S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer377S0,d2WiderTransfer377Lo,d2WiderTransfer377Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer377C0 then |x-((d2WiderTransfer377S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer377S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer377S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer377S0,d2WiderTransfer377Lo,d2WiderTransfer377Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer377C0,d2Log166Q,d2WiderTransfer377S0,d2WiderTransfer377Lo,d2WiderTransfer377Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer377C0 d2WiderTransfer377S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2WiderTransfer377C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer377Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer377Arithmetic
  linarith
#print axioms d2WiderTransfer377Arithmetic
#print axioms d2WiderTransfer377Bound
def d2WiderTransfer378Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (45214519) 1 (-26))
def d2WiderTransfer378Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (2930765) 1 (-22))
def d2WiderTransfer378Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (20712636043577604784775) 1 (-79))
def d2WiderTransfer378C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (3) 275 (-5))
def d2WiderTransfer378S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
def d2WiderTransfer378C1 : ℚ := (d2LitsNearWiderTransfers047.q2 (-5) 11 (-4))
def d2WiderTransfer378S1 : ℚ := (d2LitsNearWiderTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer378Arithmetic : weightedUpper d2WiderTransfer378C0 d2Log166Lo d2Log166Hi + weightedUpper d2WiderTransfer378C1 d2Log8Lo d2Log8Hi ≤ d2WiderTransfer378Cap := by decide +kernel
theorem d2WiderTransfer378Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer378Lo:ℚ):ℝ) ((d2WiderTransfer378Hi:ℚ):ℝ), ((d2WiderTransfer378C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer378S0:ℚ):ℝ)| + ((d2WiderTransfer378C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer378S1:ℚ):ℝ)| ≤ ((d2WiderTransfer378Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer378S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer378S0,d2WiderTransfer378Lo,d2WiderTransfer378Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer378C0 then |x-((d2WiderTransfer378S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer378S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer378S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer378S0,d2WiderTransfer378Lo,d2WiderTransfer378Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer378C0,d2Log166Q,d2WiderTransfer378S0,d2WiderTransfer378Lo,d2WiderTransfer378Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer378C0 d2WiderTransfer378S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2WiderTransfer378S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer378S1,d2WiderTransfer378Lo,d2WiderTransfer378Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer378C1 then |x-((d2WiderTransfer378S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer378S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer378S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer378S1,d2WiderTransfer378Lo,d2WiderTransfer378Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer378C1,d2Log8Q,d2WiderTransfer378S1,d2WiderTransfer378Lo,d2WiderTransfer378Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer378C1 d2WiderTransfer378S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2WiderTransfer378C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer378C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer378Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer378Arithmetic
  linarith
#print axioms d2WiderTransfer378Arithmetic
#print axioms d2WiderTransfer378Bound
def d2WiderTransfer379Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (2930765) 1 (-22))
def d2WiderTransfer379Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (25123841) 1 (-25))
def d2WiderTransfer379Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (15487665051695413563023) 1 (-80))
def d2WiderTransfer379C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 55 (-3))
def d2WiderTransfer379S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
def d2WiderTransfer379C1 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 55 (-3))
def d2WiderTransfer379S1 : ℚ := (d2LitsNearWiderTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer379Arithmetic : weightedUpper d2WiderTransfer379C0 d2Log166Lo d2Log166Hi + weightedUpper d2WiderTransfer379C1 d2Log7Lo d2Log7Hi ≤ d2WiderTransfer379Cap := by decide +kernel
theorem d2WiderTransfer379Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer379Lo:ℚ):ℝ) ((d2WiderTransfer379Hi:ℚ):ℝ), ((d2WiderTransfer379C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer379S0:ℚ):ℝ)| + ((d2WiderTransfer379C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer379S1:ℚ):ℝ)| ≤ ((d2WiderTransfer379Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer379S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer379S0,d2WiderTransfer379Lo,d2WiderTransfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer379C0 then |x-((d2WiderTransfer379S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer379S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer379S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer379S0,d2WiderTransfer379Lo,d2WiderTransfer379Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer379C0,d2Log166Q,d2WiderTransfer379S0,d2WiderTransfer379Lo,d2WiderTransfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer379C0 d2WiderTransfer379S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2WiderTransfer379S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer379S1,d2WiderTransfer379Lo,d2WiderTransfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer379C1 then |x-((d2WiderTransfer379S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer379S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer379S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer379S1,d2WiderTransfer379Lo,d2WiderTransfer379Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer379C1,d2Log7Q,d2WiderTransfer379S1,d2WiderTransfer379Lo,d2WiderTransfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer379C1 d2WiderTransfer379S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2WiderTransfer379C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer379C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer379Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer379Arithmetic
  linarith
#print axioms d2WiderTransfer379Arithmetic
#print axioms d2WiderTransfer379Bound
def d2WiderTransfer380Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (2930765) 1 (-22))
def d2WiderTransfer380Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (25123841) 1 (-25))
def d2WiderTransfer380Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (30819460925621700497039) 1 (-80))
def d2WiderTransfer380C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (23) 25 (-5))
def d2WiderTransfer380S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer380Arithmetic : weightedUpper d2WiderTransfer380C0 d2Log167Lo d2Log167Hi ≤ d2WiderTransfer380Cap := by decide +kernel
theorem d2WiderTransfer380Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer380Lo:ℚ):ℝ) ((d2WiderTransfer380Hi:ℚ):ℝ), ((d2WiderTransfer380C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer380S0:ℚ):ℝ)| ≤ ((d2WiderTransfer380Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer380S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer380S0,d2WiderTransfer380Lo,d2WiderTransfer380Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer380C0 then |x-((d2WiderTransfer380S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer380S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer380S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer380S0,d2WiderTransfer380Lo,d2WiderTransfer380Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer380C0,d2Log167Q,d2WiderTransfer380S0,d2WiderTransfer380Lo,d2WiderTransfer380Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer380C0 d2WiderTransfer380S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have har : (((weightedUpper d2WiderTransfer380C0 d2Log167Lo d2Log167Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer380Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer380Arithmetic
  linarith
#print axioms d2WiderTransfer380Arithmetic
#print axioms d2WiderTransfer380Bound
def d2WiderTransfer381Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (2930765) 1 (-22))
def d2WiderTransfer381Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (25123841) 1 (-25))
def d2WiderTransfer381Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (47670448316888970792591) 1 (-80))
def d2WiderTransfer381C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (3) 275 (-5))
def d2WiderTransfer381S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
def d2WiderTransfer381C1 : ℚ := (d2LitsNearWiderTransfers047.q2 (-5) 11 (-4))
def d2WiderTransfer381S1 : ℚ := (d2LitsNearWiderTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer381Arithmetic : weightedUpper d2WiderTransfer381C0 d2Log167Lo d2Log167Hi + weightedUpper d2WiderTransfer381C1 d2Log7Lo d2Log7Hi ≤ d2WiderTransfer381Cap := by decide +kernel
theorem d2WiderTransfer381Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer381Lo:ℚ):ℝ) ((d2WiderTransfer381Hi:ℚ):ℝ), ((d2WiderTransfer381C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer381S0:ℚ):ℝ)| + ((d2WiderTransfer381C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer381S1:ℚ):ℝ)| ≤ ((d2WiderTransfer381Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer381S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer381S0,d2WiderTransfer381Lo,d2WiderTransfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer381C0 then |x-((d2WiderTransfer381S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer381S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer381S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer381S0,d2WiderTransfer381Lo,d2WiderTransfer381Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer381C0,d2Log167Q,d2WiderTransfer381S0,d2WiderTransfer381Lo,d2WiderTransfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer381C0 d2WiderTransfer381S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2WiderTransfer381S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer381S1,d2WiderTransfer381Lo,d2WiderTransfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer381C1 then |x-((d2WiderTransfer381S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer381S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer381S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer381S1,d2WiderTransfer381Lo,d2WiderTransfer381Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer381C1,d2Log7Q,d2WiderTransfer381S1,d2WiderTransfer381Lo,d2WiderTransfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer381C1 d2WiderTransfer381S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2WiderTransfer381C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer381C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer381Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer381Arithmetic
  linarith
#print axioms d2WiderTransfer381Arithmetic
#print axioms d2WiderTransfer381Bound
def d2WiderTransfer382Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (25123841) 1 (-25))
def d2WiderTransfer382Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (13400781) 1 (-24))
def d2WiderTransfer382Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (23120299455999289732387) 1 (-80))
def d2WiderTransfer382C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 55 (-3))
def d2WiderTransfer382S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
def d2WiderTransfer382C1 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 55 (-3))
def d2WiderTransfer382S1 : ℚ := (d2LitsNearWiderTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer382Arithmetic : weightedUpper d2WiderTransfer382C0 d2Log167Lo d2Log167Hi + weightedUpper d2WiderTransfer382C1 d2Log6Lo d2Log6Hi ≤ d2WiderTransfer382Cap := by decide +kernel
theorem d2WiderTransfer382Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer382Lo:ℚ):ℝ) ((d2WiderTransfer382Hi:ℚ):ℝ), ((d2WiderTransfer382C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer382S0:ℚ):ℝ)| + ((d2WiderTransfer382C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer382S1:ℚ):ℝ)| ≤ ((d2WiderTransfer382Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer382S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer382S0,d2WiderTransfer382Lo,d2WiderTransfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer382C0 then |x-((d2WiderTransfer382S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer382S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer382S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer382S0,d2WiderTransfer382Lo,d2WiderTransfer382Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer382C0,d2Log167Q,d2WiderTransfer382S0,d2WiderTransfer382Lo,d2WiderTransfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer382C0 d2WiderTransfer382S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2WiderTransfer382S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer382S1,d2WiderTransfer382Lo,d2WiderTransfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer382C1 then |x-((d2WiderTransfer382S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer382S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer382S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer382S1,d2WiderTransfer382Lo,d2WiderTransfer382Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer382C1,d2Log6Q,d2WiderTransfer382S1,d2WiderTransfer382Lo,d2WiderTransfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer382C1 d2WiderTransfer382S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2WiderTransfer382C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer382C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer382Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer382Arithmetic
  linarith
#print axioms d2WiderTransfer382Arithmetic
#print axioms d2WiderTransfer382Bound
def d2WiderTransfer383Lo : ℚ := (d2LitsNearWiderTransfers047.q2 (25123841) 1 (-25))
def d2WiderTransfer383Hi : ℚ := (d2LitsNearWiderTransfers047.q2 (13400781) 1 (-24))
def d2WiderTransfer383Cap : ℚ := (d2LitsNearWiderTransfers047.q2 (38452095329925576666403) 1 (-80))
def d2WiderTransfer383C0 : ℚ := (d2LitsNearWiderTransfers047.q2 (23) 25 (-5))
def d2WiderTransfer383S0 : ℚ := (d2LitsNearWiderTransfers047.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer383Arithmetic : weightedUpper d2WiderTransfer383C0 d2Log168Lo d2Log168Hi ≤ d2WiderTransfer383Cap := by decide +kernel
theorem d2WiderTransfer383Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer383Lo:ℚ):ℝ) ((d2WiderTransfer383Hi:ℚ):ℝ), ((d2WiderTransfer383C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer383S0:ℚ):ℝ)| ≤ ((d2WiderTransfer383Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer383S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer383S0,d2WiderTransfer383Lo,d2WiderTransfer383Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer383C0 then |x-((d2WiderTransfer383S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer383S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer383S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer383S0,d2WiderTransfer383Lo,d2WiderTransfer383Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer383C0,d2Log168Q,d2WiderTransfer383S0,d2WiderTransfer383Lo,d2WiderTransfer383Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer383C0 d2WiderTransfer383S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2WiderTransfer383C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer383Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer383Arithmetic
  linarith
#print axioms d2WiderTransfer383Arithmetic
#print axioms d2WiderTransfer383Bound
end CatalanMeasure.GenD.Signed.Data.Cells
