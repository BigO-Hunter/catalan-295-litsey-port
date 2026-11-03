module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers060
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers060
open D72.LogTransfer
def d2WiderTransfer480Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (8191) 1 (-13))
def d2WiderTransfer480Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (16383) 1 (-14))
def d2WiderTransfer480Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (1505649412060978558719) 1 (-76))
def d2WiderTransfer480C0 : ℚ := (d2LitsNearWiderTransfers060.q2 (23) 25 (-5))
def d2WiderTransfer480S0 : ℚ := (d2LitsNearWiderTransfers060.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer480Arithmetic : weightedUpper d2WiderTransfer480C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer480Cap := by decide +kernel
theorem d2WiderTransfer480Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer480Lo:ℚ):ℝ) ((d2WiderTransfer480Hi:ℚ):ℝ), ((d2WiderTransfer480C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer480S0:ℚ):ℝ)| ≤ ((d2WiderTransfer480Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer480S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer480S0,d2WiderTransfer480Lo,d2WiderTransfer480Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer480C0 then |x-((d2WiderTransfer480S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer480S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer480S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer480S0,d2WiderTransfer480Lo,d2WiderTransfer480Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer480C0,d2Log180Q,d2WiderTransfer480S0,d2WiderTransfer480Lo,d2WiderTransfer480Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer480C0 d2WiderTransfer480S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer480C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer480Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer480Arithmetic
  linarith
#print axioms d2WiderTransfer480Arithmetic
#print axioms d2WiderTransfer480Bound
def d2WiderTransfer481Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (16383) 1 (-14))
def d2WiderTransfer481Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (32767) 1 (-15))
def d2WiderTransfer481Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (16853050294997609245) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer481Arithmetic : (0 : ℚ) ≤ d2WiderTransfer481Cap := by decide +kernel
theorem d2WiderTransfer481Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer481Lo:ℚ):ℝ) ((d2WiderTransfer481Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer481Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer481Arithmetic
#print axioms d2WiderTransfer481Arithmetic
#print axioms d2WiderTransfer481Bound
def d2WiderTransfer482Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (16383) 1 (-14))
def d2WiderTransfer482Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (32767) 1 (-15))
def d2WiderTransfer482Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (24090921679082393430813) 1 (-80))
def d2WiderTransfer482C0 : ℚ := (d2LitsNearWiderTransfers060.q2 (23) 25 (-5))
def d2WiderTransfer482S0 : ℚ := (d2LitsNearWiderTransfers060.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer482Arithmetic : weightedUpper d2WiderTransfer482C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer482Cap := by decide +kernel
theorem d2WiderTransfer482Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer482Lo:ℚ):ℝ) ((d2WiderTransfer482Hi:ℚ):ℝ), ((d2WiderTransfer482C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer482S0:ℚ):ℝ)| ≤ ((d2WiderTransfer482Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer482S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer482S0,d2WiderTransfer482Lo,d2WiderTransfer482Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer482C0 then |x-((d2WiderTransfer482S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer482S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer482S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer482S0,d2WiderTransfer482Lo,d2WiderTransfer482Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer482C0,d2Log181Q,d2WiderTransfer482S0,d2WiderTransfer482Lo,d2WiderTransfer482Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer482C0 d2WiderTransfer482S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer482C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer482Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer482Arithmetic
  linarith
#print axioms d2WiderTransfer482Arithmetic
#print axioms d2WiderTransfer482Bound
def d2WiderTransfer483Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (16383) 1 (-14))
def d2WiderTransfer483Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (32767) 1 (-15))
def d2WiderTransfer483Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (24090920949006672587549) 1 (-80))
def d2WiderTransfer483C0 : ℚ := (d2LitsNearWiderTransfers060.q2 (23) 25 (-5))
def d2WiderTransfer483S0 : ℚ := (d2LitsNearWiderTransfers060.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer483Arithmetic : weightedUpper d2WiderTransfer483C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer483Cap := by decide +kernel
theorem d2WiderTransfer483Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer483Lo:ℚ):ℝ) ((d2WiderTransfer483Hi:ℚ):ℝ), ((d2WiderTransfer483C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer483S0:ℚ):ℝ)| ≤ ((d2WiderTransfer483Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer483S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer483S0,d2WiderTransfer483Lo,d2WiderTransfer483Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer483C0 then |x-((d2WiderTransfer483S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer483S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer483S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer483S0,d2WiderTransfer483Lo,d2WiderTransfer483Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer483C0,d2Log181Q,d2WiderTransfer483S0,d2WiderTransfer483Lo,d2WiderTransfer483Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer483C0 d2WiderTransfer483S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer483C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer483Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer483Arithmetic
  linarith
#print axioms d2WiderTransfer483Arithmetic
#print axioms d2WiderTransfer483Bound
def d2WiderTransfer484Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (32767) 1 (-15))
def d2WiderTransfer484Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (65535) 1 (-16))
def d2WiderTransfer484Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (17118225275745292243) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer484Arithmetic : (0 : ℚ) ≤ d2WiderTransfer484Cap := by decide +kernel
theorem d2WiderTransfer484Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer484Lo:ℚ):ℝ) ((d2WiderTransfer484Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer484Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer484Arithmetic
#print axioms d2WiderTransfer484Arithmetic
#print axioms d2WiderTransfer484Bound
def d2WiderTransfer485Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (32767) 1 (-15))
def d2WiderTransfer485Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (65535) 1 (-16))
def d2WiderTransfer485Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (24091186854063141113811) 1 (-80))
def d2WiderTransfer485C0 : ℚ := (d2LitsNearWiderTransfers060.q2 (23) 25 (-5))
def d2WiderTransfer485S0 : ℚ := (d2LitsNearWiderTransfers060.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer485Arithmetic : weightedUpper d2WiderTransfer485C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer485Cap := by decide +kernel
theorem d2WiderTransfer485Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer485Lo:ℚ):ℝ) ((d2WiderTransfer485Hi:ℚ):ℝ), ((d2WiderTransfer485C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer485S0:ℚ):ℝ)| ≤ ((d2WiderTransfer485Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer485S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer485S0,d2WiderTransfer485Lo,d2WiderTransfer485Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer485C0 then |x-((d2WiderTransfer485S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer485S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer485S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer485S0,d2WiderTransfer485Lo,d2WiderTransfer485Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer485C0,d2Log182Q,d2WiderTransfer485S0,d2WiderTransfer485Lo,d2WiderTransfer485Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer485C0 d2WiderTransfer485S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer485C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer485Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer485Arithmetic
  linarith
#print axioms d2WiderTransfer485Arithmetic
#print axioms d2WiderTransfer485Bound
def d2WiderTransfer486Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (32767) 1 (-15))
def d2WiderTransfer486Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (65535) 1 (-16))
def d2WiderTransfer486Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (24091186123987420270547) 1 (-80))
def d2WiderTransfer486C0 : ℚ := (d2LitsNearWiderTransfers060.q2 (23) 25 (-5))
def d2WiderTransfer486S0 : ℚ := (d2LitsNearWiderTransfers060.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer486Arithmetic : weightedUpper d2WiderTransfer486C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer486Cap := by decide +kernel
theorem d2WiderTransfer486Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer486Lo:ℚ):ℝ) ((d2WiderTransfer486Hi:ℚ):ℝ), ((d2WiderTransfer486C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer486S0:ℚ):ℝ)| ≤ ((d2WiderTransfer486Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer486S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer486S0,d2WiderTransfer486Lo,d2WiderTransfer486Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer486C0 then |x-((d2WiderTransfer486S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer486S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer486S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer486S0,d2WiderTransfer486Lo,d2WiderTransfer486Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers060.q2, d2LitsNearLogCache011.q2, d2WiderTransfer486C0,d2Log182Q,d2WiderTransfer486S0,d2WiderTransfer486Lo,d2WiderTransfer486Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer486C0 d2WiderTransfer486S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer486C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer486Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer486Arithmetic
  linarith
#print axioms d2WiderTransfer486Arithmetic
#print axioms d2WiderTransfer486Bound
def d2WiderTransfer487Lo : ℚ := (d2LitsNearWiderTransfers060.q2 (65535) 1 (-16))
def d2WiderTransfer487Hi : ℚ := (d2LitsNearWiderTransfers060.q2 (131071) 1 (-17))
def d2WiderTransfer487Cap : ℚ := (d2LitsNearWiderTransfers060.q2 (17250812007442604725) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer487Arithmetic : (0 : ℚ) ≤ d2WiderTransfer487Cap := by decide +kernel
theorem d2WiderTransfer487Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer487Lo:ℚ):ℝ) ((d2WiderTransfer487Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer487Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer487Arithmetic
#print axioms d2WiderTransfer487Arithmetic
#print axioms d2WiderTransfer487Bound
end CatalanMeasure.GenD.Signed.Data.Cells
