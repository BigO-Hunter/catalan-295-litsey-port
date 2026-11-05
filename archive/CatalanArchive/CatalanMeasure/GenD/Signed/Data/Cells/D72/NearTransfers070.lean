module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers070
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers070
open D72.LogTransfer
def d2Transfer560Lo : ℚ := (d2LitsNearTransfers070.q2 (1368011721) 1 (-31))
def d2Transfer560Hi : ℚ := (d2LitsNearTransfers070.q2 (684844721) 1 (-30))
def d2Transfer560Cap : ℚ := (d2LitsNearTransfers070.q2 (9116129790956444707841) 1 (-79))
def d2Transfer560C0 : ℚ := (d2LitsNearTransfers070.q2 (23) 25 (-5))
def d2Transfer560S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer560Arithmetic : weightedUpper d2Transfer560C0 d2Log157Lo d2Log157Hi ≤ d2Transfer560Cap := by decide +kernel
theorem d2Transfer560Bound : ∀ x ∈ Set.Icc ((d2Transfer560Lo:ℚ):ℝ) ((d2Transfer560Hi:ℚ):ℝ), ((d2Transfer560C0:ℚ):ℝ)*Real.log |x-((d2Transfer560S0:ℚ):ℝ)| ≤ ((d2Transfer560Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer560S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer560S0,d2Transfer560Lo,d2Transfer560Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer560C0 then |x-((d2Transfer560S0:ℚ):ℝ)| ≤ ((d2Log157Q:ℚ):ℝ) else ((d2Log157Q:ℚ):ℝ) ≤ |x-((d2Transfer560S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer560S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer560S0,d2Transfer560Lo,d2Transfer560Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer560C0,d2Log157Q,d2Transfer560S0,d2Transfer560Lo,d2Transfer560Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer560C0 d2Transfer560S0 d2Log157Q d2Log157Lo d2Log157Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log157Bounds
  have har : (((weightedUpper d2Transfer560C0 d2Log157Lo d2Log157Hi:ℚ):ℝ)) ≤ ((d2Transfer560Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer560Arithmetic
  linarith
#print axioms d2Transfer560Arithmetic
#print axioms d2Transfer560Bound
def d2Transfer561Lo : ℚ := (d2LitsNearTransfers070.q2 (1368011721) 1 (-31))
def d2Transfer561Hi : ℚ := (d2LitsNearTransfers070.q2 (684844721) 1 (-30))
def d2Transfer561Cap : ℚ := (d2LitsNearTransfers070.q2 (17541623486590079855617) 1 (-79))
def d2Transfer561C0 : ℚ := (d2LitsNearTransfers070.q2 (3) 275 (-5))
def d2Transfer561S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
def d2Transfer561C1 : ℚ := (d2LitsNearTransfers070.q2 (-5) 11 (-4))
def d2Transfer561S1 : ℚ := (d2LitsNearTransfers070.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer561Arithmetic : weightedUpper d2Transfer561C0 d2Log157Lo d2Log157Hi + weightedUpper d2Transfer561C1 d2Log17Lo d2Log17Hi ≤ d2Transfer561Cap := by decide +kernel
theorem d2Transfer561Bound : ∀ x ∈ Set.Icc ((d2Transfer561Lo:ℚ):ℝ) ((d2Transfer561Hi:ℚ):ℝ), ((d2Transfer561C0:ℚ):ℝ)*Real.log |x-((d2Transfer561S0:ℚ):ℝ)| + ((d2Transfer561C1:ℚ):ℝ)*Real.log |x-((d2Transfer561S1:ℚ):ℝ)| ≤ ((d2Transfer561Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer561S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer561S0,d2Transfer561Lo,d2Transfer561Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer561C0 then |x-((d2Transfer561S0:ℚ):ℝ)| ≤ ((d2Log157Q:ℚ):ℝ) else ((d2Log157Q:ℚ):ℝ) ≤ |x-((d2Transfer561S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer561S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer561S0,d2Transfer561Lo,d2Transfer561Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer561C0,d2Log157Q,d2Transfer561S0,d2Transfer561Lo,d2Transfer561Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer561C0 d2Transfer561S0 d2Log157Q d2Log157Lo d2Log157Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log157Bounds
  have hn1 : x-((d2Transfer561S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer561S1,d2Transfer561Lo,d2Transfer561Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer561C1 then |x-((d2Transfer561S1:ℚ):ℝ)| ≤ ((d2Log17Q:ℚ):ℝ) else ((d2Log17Q:ℚ):ℝ) ≤ |x-((d2Transfer561S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer561S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer561S1,d2Transfer561Lo,d2Transfer561Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer561C1,d2Log17Q,d2Transfer561S1,d2Transfer561Lo,d2Transfer561Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer561C1 d2Transfer561S1 d2Log17Q d2Log17Lo d2Log17Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log17Bounds
  have har : (((weightedUpper d2Transfer561C0 d2Log157Lo d2Log157Hi:ℚ):ℝ) + ((weightedUpper d2Transfer561C1 d2Log17Lo d2Log17Hi:ℚ):ℝ)) ≤ ((d2Transfer561Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer561Arithmetic
  linarith
#print axioms d2Transfer561Arithmetic
#print axioms d2Transfer561Bound
def d2Transfer562Lo : ℚ := (d2LitsNearTransfers070.q2 (684844721) 1 (-30))
def d2Transfer562Hi : ℚ := (d2LitsNearTransfers070.q2 (343261221) 1 (-29))
def d2Transfer562Cap : ℚ := (d2LitsNearTransfers070.q2 (3049340988866887689691) 1 (-80))
def d2Transfer562C0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 55 (-3))
def d2Transfer562S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
def d2Transfer562C1 : ℚ := (d2LitsNearTransfers070.q2 (-1) 55 (-3))
def d2Transfer562S1 : ℚ := (d2LitsNearTransfers070.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer562Arithmetic : weightedUpper d2Transfer562C0 d2Log157Lo d2Log157Hi + weightedUpper d2Transfer562C1 d2Log16Lo d2Log16Hi ≤ d2Transfer562Cap := by decide +kernel
theorem d2Transfer562Bound : ∀ x ∈ Set.Icc ((d2Transfer562Lo:ℚ):ℝ) ((d2Transfer562Hi:ℚ):ℝ), ((d2Transfer562C0:ℚ):ℝ)*Real.log |x-((d2Transfer562S0:ℚ):ℝ)| + ((d2Transfer562C1:ℚ):ℝ)*Real.log |x-((d2Transfer562S1:ℚ):ℝ)| ≤ ((d2Transfer562Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer562S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer562S0,d2Transfer562Lo,d2Transfer562Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer562C0 then |x-((d2Transfer562S0:ℚ):ℝ)| ≤ ((d2Log157Q:ℚ):ℝ) else ((d2Log157Q:ℚ):ℝ) ≤ |x-((d2Transfer562S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer562S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer562S0,d2Transfer562Lo,d2Transfer562Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer562C0,d2Log157Q,d2Transfer562S0,d2Transfer562Lo,d2Transfer562Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer562C0 d2Transfer562S0 d2Log157Q d2Log157Lo d2Log157Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log157Bounds
  have hn1 : x-((d2Transfer562S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer562S1,d2Transfer562Lo,d2Transfer562Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer562C1 then |x-((d2Transfer562S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2Transfer562S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer562S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer562S1,d2Transfer562Lo,d2Transfer562Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer562C1,d2Log16Q,d2Transfer562S1,d2Transfer562Lo,d2Transfer562Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer562C1 d2Transfer562S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2Transfer562C0 d2Log157Lo d2Log157Hi:ℚ):ℝ) + ((weightedUpper d2Transfer562C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2Transfer562Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer562Arithmetic
  linarith
#print axioms d2Transfer562Arithmetic
#print axioms d2Transfer562Bound
def d2Transfer563Lo : ℚ := (d2LitsNearTransfers070.q2 (684844721) 1 (-30))
def d2Transfer563Hi : ℚ := (d2LitsNearTransfers070.q2 (343261221) 1 (-29))
def d2Transfer563Cap : ℚ := (d2LitsNearTransfers070.q2 (18381136862793174623707) 1 (-80))
def d2Transfer563C0 : ℚ := (d2LitsNearTransfers070.q2 (23) 25 (-5))
def d2Transfer563S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer563Arithmetic : weightedUpper d2Transfer563C0 d2Log158Lo d2Log158Hi ≤ d2Transfer563Cap := by decide +kernel
theorem d2Transfer563Bound : ∀ x ∈ Set.Icc ((d2Transfer563Lo:ℚ):ℝ) ((d2Transfer563Hi:ℚ):ℝ), ((d2Transfer563C0:ℚ):ℝ)*Real.log |x-((d2Transfer563S0:ℚ):ℝ)| ≤ ((d2Transfer563Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer563S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer563S0,d2Transfer563Lo,d2Transfer563Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer563C0 then |x-((d2Transfer563S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2Transfer563S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer563S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer563S0,d2Transfer563Lo,d2Transfer563Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer563C0,d2Log158Q,d2Transfer563S0,d2Transfer563Lo,d2Transfer563Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer563C0 d2Transfer563S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have har : (((weightedUpper d2Transfer563C0 d2Log158Lo d2Log158Hi:ℚ):ℝ)) ≤ ((d2Transfer563Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer563Arithmetic
  linarith
#print axioms d2Transfer563Arithmetic
#print axioms d2Transfer563Bound
def d2Transfer564Lo : ℚ := (d2LitsNearTransfers070.q2 (684844721) 1 (-30))
def d2Transfer564Hi : ℚ := (d2LitsNearTransfers070.q2 (343261221) 1 (-29))
def d2Transfer564Cap : ℚ := (d2LitsNearTransfers070.q2 (35232124254060444919259) 1 (-80))
def d2Transfer564C0 : ℚ := (d2LitsNearTransfers070.q2 (3) 275 (-5))
def d2Transfer564S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
def d2Transfer564C1 : ℚ := (d2LitsNearTransfers070.q2 (-5) 11 (-4))
def d2Transfer564S1 : ℚ := (d2LitsNearTransfers070.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer564Arithmetic : weightedUpper d2Transfer564C0 d2Log158Lo d2Log158Hi + weightedUpper d2Transfer564C1 d2Log16Lo d2Log16Hi ≤ d2Transfer564Cap := by decide +kernel
theorem d2Transfer564Bound : ∀ x ∈ Set.Icc ((d2Transfer564Lo:ℚ):ℝ) ((d2Transfer564Hi:ℚ):ℝ), ((d2Transfer564C0:ℚ):ℝ)*Real.log |x-((d2Transfer564S0:ℚ):ℝ)| + ((d2Transfer564C1:ℚ):ℝ)*Real.log |x-((d2Transfer564S1:ℚ):ℝ)| ≤ ((d2Transfer564Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer564S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer564S0,d2Transfer564Lo,d2Transfer564Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer564C0 then |x-((d2Transfer564S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2Transfer564S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer564S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer564S0,d2Transfer564Lo,d2Transfer564Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer564C0,d2Log158Q,d2Transfer564S0,d2Transfer564Lo,d2Transfer564Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer564C0 d2Transfer564S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2Transfer564S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer564S1,d2Transfer564Lo,d2Transfer564Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer564C1 then |x-((d2Transfer564S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2Transfer564S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer564S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer564S1,d2Transfer564Lo,d2Transfer564Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer564C1,d2Log16Q,d2Transfer564S1,d2Transfer564Lo,d2Transfer564Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer564C1 d2Transfer564S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2Transfer564C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2Transfer564C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2Transfer564Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer564Arithmetic
  linarith
#print axioms d2Transfer564Arithmetic
#print axioms d2Transfer564Bound
def d2Transfer565Lo : ℚ := (d2LitsNearTransfers070.q2 (343261221) 1 (-29))
def d2Transfer565Hi : ℚ := (d2LitsNearTransfers070.q2 (688200163) 1 (-30))
def d2Transfer565Cap : ℚ := (d2LitsNearTransfers070.q2 (1599431318984013064275) 1 (-79))
def d2Transfer565C0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 55 (-3))
def d2Transfer565S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
def d2Transfer565C1 : ℚ := (d2LitsNearTransfers070.q2 (-1) 55 (-3))
def d2Transfer565S1 : ℚ := (d2LitsNearTransfers070.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer565Arithmetic : weightedUpper d2Transfer565C0 d2Log158Lo d2Log158Hi + weightedUpper d2Transfer565C1 d2Log15Lo d2Log15Hi ≤ d2Transfer565Cap := by decide +kernel
theorem d2Transfer565Bound : ∀ x ∈ Set.Icc ((d2Transfer565Lo:ℚ):ℝ) ((d2Transfer565Hi:ℚ):ℝ), ((d2Transfer565C0:ℚ):ℝ)*Real.log |x-((d2Transfer565S0:ℚ):ℝ)| + ((d2Transfer565C1:ℚ):ℝ)*Real.log |x-((d2Transfer565S1:ℚ):ℝ)| ≤ ((d2Transfer565Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer565S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer565S0,d2Transfer565Lo,d2Transfer565Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer565C0 then |x-((d2Transfer565S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2Transfer565S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer565S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer565S0,d2Transfer565Lo,d2Transfer565Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer565C0,d2Log158Q,d2Transfer565S0,d2Transfer565Lo,d2Transfer565Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer565C0 d2Transfer565S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2Transfer565S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer565S1,d2Transfer565Lo,d2Transfer565Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer565C1 then |x-((d2Transfer565S1:ℚ):ℝ)| ≤ ((d2Log15Q:ℚ):ℝ) else ((d2Log15Q:ℚ):ℝ) ≤ |x-((d2Transfer565S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer565S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer565S1,d2Transfer565Lo,d2Transfer565Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer565C1,d2Log15Q,d2Transfer565S1,d2Transfer565Lo,d2Transfer565Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer565C1 d2Transfer565S1 d2Log15Q d2Log15Lo d2Log15Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log15Bounds
  have har : (((weightedUpper d2Transfer565C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2Transfer565C1 d2Log15Lo d2Log15Hi:ℚ):ℝ)) ≤ ((d2Transfer565Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer565Arithmetic
  linarith
#print axioms d2Transfer565Arithmetic
#print axioms d2Transfer565Bound
def d2Transfer566Lo : ℚ := (d2LitsNearTransfers070.q2 (343261221) 1 (-29))
def d2Transfer566Hi : ℚ := (d2LitsNearTransfers070.q2 (688200163) 1 (-30))
def d2Transfer566Cap : ℚ := (d2LitsNearTransfers070.q2 (9265329255947156531283) 1 (-79))
def d2Transfer566C0 : ℚ := (d2LitsNearTransfers070.q2 (23) 25 (-5))
def d2Transfer566S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer566Arithmetic : weightedUpper d2Transfer566C0 d2Log159Lo d2Log159Hi ≤ d2Transfer566Cap := by decide +kernel
theorem d2Transfer566Bound : ∀ x ∈ Set.Icc ((d2Transfer566Lo:ℚ):ℝ) ((d2Transfer566Hi:ℚ):ℝ), ((d2Transfer566C0:ℚ):ℝ)*Real.log |x-((d2Transfer566S0:ℚ):ℝ)| ≤ ((d2Transfer566Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer566S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer566S0,d2Transfer566Lo,d2Transfer566Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer566C0 then |x-((d2Transfer566S0:ℚ):ℝ)| ≤ ((d2Log159Q:ℚ):ℝ) else ((d2Log159Q:ℚ):ℝ) ≤ |x-((d2Transfer566S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer566S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer566S0,d2Transfer566Lo,d2Transfer566Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer566C0,d2Log159Q,d2Transfer566S0,d2Transfer566Lo,d2Transfer566Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer566C0 d2Transfer566S0 d2Log159Q d2Log159Lo d2Log159Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log159Bounds
  have har : (((weightedUpper d2Transfer566C0 d2Log159Lo d2Log159Hi:ℚ):ℝ)) ≤ ((d2Transfer566Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer566Arithmetic
  linarith
#print axioms d2Transfer566Arithmetic
#print axioms d2Transfer566Bound
def d2Transfer567Lo : ℚ := (d2LitsNearTransfers070.q2 (343261221) 1 (-29))
def d2Transfer567Hi : ℚ := (d2LitsNearTransfers070.q2 (688200163) 1 (-30))
def d2Transfer567Cap : ℚ := (d2LitsNearTransfers070.q2 (17690822951580791679059) 1 (-79))
def d2Transfer567C0 : ℚ := (d2LitsNearTransfers070.q2 (3) 275 (-5))
def d2Transfer567S0 : ℚ := (d2LitsNearTransfers070.q2 (-1) 1 (0))
def d2Transfer567C1 : ℚ := (d2LitsNearTransfers070.q2 (-5) 11 (-4))
def d2Transfer567S1 : ℚ := (d2LitsNearTransfers070.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer567Arithmetic : weightedUpper d2Transfer567C0 d2Log159Lo d2Log159Hi + weightedUpper d2Transfer567C1 d2Log15Lo d2Log15Hi ≤ d2Transfer567Cap := by decide +kernel
theorem d2Transfer567Bound : ∀ x ∈ Set.Icc ((d2Transfer567Lo:ℚ):ℝ) ((d2Transfer567Hi:ℚ):ℝ), ((d2Transfer567C0:ℚ):ℝ)*Real.log |x-((d2Transfer567S0:ℚ):ℝ)| + ((d2Transfer567C1:ℚ):ℝ)*Real.log |x-((d2Transfer567S1:ℚ):ℝ)| ≤ ((d2Transfer567Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer567S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer567S0,d2Transfer567Lo,d2Transfer567Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer567C0 then |x-((d2Transfer567S0:ℚ):ℝ)| ≤ ((d2Log159Q:ℚ):ℝ) else ((d2Log159Q:ℚ):ℝ) ≤ |x-((d2Transfer567S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer567S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer567S0,d2Transfer567Lo,d2Transfer567Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer567C0,d2Log159Q,d2Transfer567S0,d2Transfer567Lo,d2Transfer567Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer567C0 d2Transfer567S0 d2Log159Q d2Log159Lo d2Log159Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log159Bounds
  have hn1 : x-((d2Transfer567S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer567S1,d2Transfer567Lo,d2Transfer567Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer567C1 then |x-((d2Transfer567S1:ℚ):ℝ)| ≤ ((d2Log15Q:ℚ):ℝ) else ((d2Log15Q:ℚ):ℝ) ≤ |x-((d2Transfer567S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer567S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer567S1,d2Transfer567Lo,d2Transfer567Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers070.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer567C1,d2Log15Q,d2Transfer567S1,d2Transfer567Lo,d2Transfer567Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer567C1 d2Transfer567S1 d2Log15Q d2Log15Lo d2Log15Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log15Bounds
  have har : (((weightedUpper d2Transfer567C0 d2Log159Lo d2Log159Hi:ℚ):ℝ) + ((weightedUpper d2Transfer567C1 d2Log15Lo d2Log15Hi:ℚ):ℝ)) ≤ ((d2Transfer567Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer567Arithmetic
  linarith
#print axioms d2Transfer567Arithmetic
#print axioms d2Transfer567Bound
end CatalanMeasure.GenD.Signed.Data.Cells
