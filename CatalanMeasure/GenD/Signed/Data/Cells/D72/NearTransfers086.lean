module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers086
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers086
open D72.LogTransfer
def d2Transfer688Lo : ℚ := (d2LitsNearTransfers086.q2 (8191) 1 (-13))
def d2Transfer688Hi : ℚ := (d2LitsNearTransfers086.q2 (16383) 1 (-14))
def d2Transfer688Cap : ℚ := (d2LitsNearTransfers086.q2 (1020168391498872575) 1 (-76))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer688Arithmetic : (0 : ℚ) ≤ d2Transfer688Cap := by decide +kernel
theorem d2Transfer688Bound : ∀ x ∈ Set.Icc ((d2Transfer688Lo:ℚ):ℝ) ((d2Transfer688Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer688Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer688Arithmetic
#print axioms d2Transfer688Arithmetic
#print axioms d2Transfer688Bound
def d2Transfer689Lo : ℚ := (d2LitsNearTransfers086.q2 (8191) 1 (-13))
def d2Transfer689Hi : ℚ := (d2LitsNearTransfers086.q2 (16383) 1 (-14))
def d2Transfer689Cap : ℚ := (d2LitsNearTransfers086.q2 (1505649457690711111423) 1 (-76))
def d2Transfer689C0 : ℚ := (d2LitsNearTransfers086.q2 (23) 25 (-5))
def d2Transfer689S0 : ℚ := (d2LitsNearTransfers086.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer689Arithmetic : weightedUpper d2Transfer689C0 d2Log180Lo d2Log180Hi ≤ d2Transfer689Cap := by decide +kernel
theorem d2Transfer689Bound : ∀ x ∈ Set.Icc ((d2Transfer689Lo:ℚ):ℝ) ((d2Transfer689Hi:ℚ):ℝ), ((d2Transfer689C0:ℚ):ℝ)*Real.log |x-((d2Transfer689S0:ℚ):ℝ)| ≤ ((d2Transfer689Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer689S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer689S0,d2Transfer689Lo,d2Transfer689Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer689C0 then |x-((d2Transfer689S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer689S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer689S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer689S0,d2Transfer689Lo,d2Transfer689Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer689C0,d2Log180Q,d2Transfer689S0,d2Transfer689Lo,d2Transfer689Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer689C0 d2Transfer689S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer689C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer689Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer689Arithmetic
  linarith
#print axioms d2Transfer689Arithmetic
#print axioms d2Transfer689Bound
def d2Transfer690Lo : ℚ := (d2LitsNearTransfers086.q2 (8191) 1 (-13))
def d2Transfer690Hi : ℚ := (d2LitsNearTransfers086.q2 (16383) 1 (-14))
def d2Transfer690Cap : ℚ := (d2LitsNearTransfers086.q2 (1505649412060978558719) 1 (-76))
def d2Transfer690C0 : ℚ := (d2LitsNearTransfers086.q2 (23) 25 (-5))
def d2Transfer690S0 : ℚ := (d2LitsNearTransfers086.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer690Arithmetic : weightedUpper d2Transfer690C0 d2Log180Lo d2Log180Hi ≤ d2Transfer690Cap := by decide +kernel
theorem d2Transfer690Bound : ∀ x ∈ Set.Icc ((d2Transfer690Lo:ℚ):ℝ) ((d2Transfer690Hi:ℚ):ℝ), ((d2Transfer690C0:ℚ):ℝ)*Real.log |x-((d2Transfer690S0:ℚ):ℝ)| ≤ ((d2Transfer690Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer690S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer690S0,d2Transfer690Lo,d2Transfer690Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer690C0 then |x-((d2Transfer690S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer690S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer690S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer690S0,d2Transfer690Lo,d2Transfer690Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer690C0,d2Log180Q,d2Transfer690S0,d2Transfer690Lo,d2Transfer690Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer690C0 d2Transfer690S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer690C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer690Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer690Arithmetic
  linarith
#print axioms d2Transfer690Arithmetic
#print axioms d2Transfer690Bound
def d2Transfer691Lo : ℚ := (d2LitsNearTransfers086.q2 (16383) 1 (-14))
def d2Transfer691Hi : ℚ := (d2LitsNearTransfers086.q2 (32767) 1 (-15))
def d2Transfer691Cap : ℚ := (d2LitsNearTransfers086.q2 (16853050294997609245) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer691Arithmetic : (0 : ℚ) ≤ d2Transfer691Cap := by decide +kernel
theorem d2Transfer691Bound : ∀ x ∈ Set.Icc ((d2Transfer691Lo:ℚ):ℝ) ((d2Transfer691Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer691Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer691Arithmetic
#print axioms d2Transfer691Arithmetic
#print axioms d2Transfer691Bound
def d2Transfer692Lo : ℚ := (d2LitsNearTransfers086.q2 (16383) 1 (-14))
def d2Transfer692Hi : ℚ := (d2LitsNearTransfers086.q2 (32767) 1 (-15))
def d2Transfer692Cap : ℚ := (d2LitsNearTransfers086.q2 (24090921679082393430813) 1 (-80))
def d2Transfer692C0 : ℚ := (d2LitsNearTransfers086.q2 (23) 25 (-5))
def d2Transfer692S0 : ℚ := (d2LitsNearTransfers086.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer692Arithmetic : weightedUpper d2Transfer692C0 d2Log181Lo d2Log181Hi ≤ d2Transfer692Cap := by decide +kernel
theorem d2Transfer692Bound : ∀ x ∈ Set.Icc ((d2Transfer692Lo:ℚ):ℝ) ((d2Transfer692Hi:ℚ):ℝ), ((d2Transfer692C0:ℚ):ℝ)*Real.log |x-((d2Transfer692S0:ℚ):ℝ)| ≤ ((d2Transfer692Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer692S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer692S0,d2Transfer692Lo,d2Transfer692Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer692C0 then |x-((d2Transfer692S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer692S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer692S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer692S0,d2Transfer692Lo,d2Transfer692Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer692C0,d2Log181Q,d2Transfer692S0,d2Transfer692Lo,d2Transfer692Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer692C0 d2Transfer692S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer692C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer692Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer692Arithmetic
  linarith
#print axioms d2Transfer692Arithmetic
#print axioms d2Transfer692Bound
def d2Transfer693Lo : ℚ := (d2LitsNearTransfers086.q2 (16383) 1 (-14))
def d2Transfer693Hi : ℚ := (d2LitsNearTransfers086.q2 (32767) 1 (-15))
def d2Transfer693Cap : ℚ := (d2LitsNearTransfers086.q2 (24090920949006672587549) 1 (-80))
def d2Transfer693C0 : ℚ := (d2LitsNearTransfers086.q2 (23) 25 (-5))
def d2Transfer693S0 : ℚ := (d2LitsNearTransfers086.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer693Arithmetic : weightedUpper d2Transfer693C0 d2Log181Lo d2Log181Hi ≤ d2Transfer693Cap := by decide +kernel
theorem d2Transfer693Bound : ∀ x ∈ Set.Icc ((d2Transfer693Lo:ℚ):ℝ) ((d2Transfer693Hi:ℚ):ℝ), ((d2Transfer693C0:ℚ):ℝ)*Real.log |x-((d2Transfer693S0:ℚ):ℝ)| ≤ ((d2Transfer693Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer693S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer693S0,d2Transfer693Lo,d2Transfer693Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer693C0 then |x-((d2Transfer693S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer693S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer693S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer693S0,d2Transfer693Lo,d2Transfer693Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer693C0,d2Log181Q,d2Transfer693S0,d2Transfer693Lo,d2Transfer693Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer693C0 d2Transfer693S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer693C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer693Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer693Arithmetic
  linarith
#print axioms d2Transfer693Arithmetic
#print axioms d2Transfer693Bound
def d2Transfer694Lo : ℚ := (d2LitsNearTransfers086.q2 (32767) 1 (-15))
def d2Transfer694Hi : ℚ := (d2LitsNearTransfers086.q2 (65535) 1 (-16))
def d2Transfer694Cap : ℚ := (d2LitsNearTransfers086.q2 (17118225275745292243) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer694Arithmetic : (0 : ℚ) ≤ d2Transfer694Cap := by decide +kernel
theorem d2Transfer694Bound : ∀ x ∈ Set.Icc ((d2Transfer694Lo:ℚ):ℝ) ((d2Transfer694Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer694Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer694Arithmetic
#print axioms d2Transfer694Arithmetic
#print axioms d2Transfer694Bound
def d2Transfer695Lo : ℚ := (d2LitsNearTransfers086.q2 (32767) 1 (-15))
def d2Transfer695Hi : ℚ := (d2LitsNearTransfers086.q2 (65535) 1 (-16))
def d2Transfer695Cap : ℚ := (d2LitsNearTransfers086.q2 (24091186854063141113811) 1 (-80))
def d2Transfer695C0 : ℚ := (d2LitsNearTransfers086.q2 (23) 25 (-5))
def d2Transfer695S0 : ℚ := (d2LitsNearTransfers086.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer695Arithmetic : weightedUpper d2Transfer695C0 d2Log182Lo d2Log182Hi ≤ d2Transfer695Cap := by decide +kernel
theorem d2Transfer695Bound : ∀ x ∈ Set.Icc ((d2Transfer695Lo:ℚ):ℝ) ((d2Transfer695Hi:ℚ):ℝ), ((d2Transfer695C0:ℚ):ℝ)*Real.log |x-((d2Transfer695S0:ℚ):ℝ)| ≤ ((d2Transfer695Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer695S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer695S0,d2Transfer695Lo,d2Transfer695Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer695C0 then |x-((d2Transfer695S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer695S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer695S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer695S0,d2Transfer695Lo,d2Transfer695Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers086.q2, d2LitsNearLogCache011.q2, d2Transfer695C0,d2Log182Q,d2Transfer695S0,d2Transfer695Lo,d2Transfer695Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer695C0 d2Transfer695S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer695C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer695Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer695Arithmetic
  linarith
#print axioms d2Transfer695Arithmetic
#print axioms d2Transfer695Bound
end CatalanMeasure.GenD.Signed.Data.Cells
