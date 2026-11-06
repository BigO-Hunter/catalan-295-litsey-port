module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
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
namespace d2LitsNearWiderTransfers040
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers040
open D72.LogTransfer
def d2WiderTransfer320Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (1351234511) 1 (-31))
def d2WiderTransfer320Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (169114029) 1 (-28))
def d2WiderTransfer320Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (17497346865223007396799) 1 (-80))
def d2WiderTransfer320C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (23) 25 (-5))
def d2WiderTransfer320S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer320Arithmetic : weightedUpper d2WiderTransfer320C0 d2Log147Lo d2Log147Hi ≤ d2WiderTransfer320Cap := by decide +kernel
theorem d2WiderTransfer320Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer320Lo:ℚ):ℝ) ((d2WiderTransfer320Hi:ℚ):ℝ), ((d2WiderTransfer320C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer320S0:ℚ):ℝ)| ≤ ((d2WiderTransfer320Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer320S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer320S0,d2WiderTransfer320Lo,d2WiderTransfer320Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer320C0 then |x-((d2WiderTransfer320S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer320S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer320S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer320S0,d2WiderTransfer320Lo,d2WiderTransfer320Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer320C0,d2Log147Q,d2WiderTransfer320S0,d2WiderTransfer320Lo,d2WiderTransfer320Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer320C0 d2WiderTransfer320S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have har : (((weightedUpper d2WiderTransfer320C0 d2Log147Lo d2Log147Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer320Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer320Arithmetic
  linarith
#print axioms d2WiderTransfer320Arithmetic
#print axioms d2WiderTransfer320Bound
def d2WiderTransfer321Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (1351234511) 1 (-31))
def d2WiderTransfer321Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (169114029) 1 (-28))
def d2WiderTransfer321Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (34348334256490277692351) 1 (-80))
def d2WiderTransfer321C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (3) 275 (-5))
def d2WiderTransfer321S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
def d2WiderTransfer321C1 : ℚ := (d2LitsNearWiderTransfers040.q2 (-5) 11 (-4))
def d2WiderTransfer321S1 : ℚ := (d2LitsNearWiderTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer321Arithmetic : weightedUpper d2WiderTransfer321C0 d2Log147Lo d2Log147Hi + weightedUpper d2WiderTransfer321C1 d2Log27Lo d2Log27Hi ≤ d2WiderTransfer321Cap := by decide +kernel
theorem d2WiderTransfer321Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer321Lo:ℚ):ℝ) ((d2WiderTransfer321Hi:ℚ):ℝ), ((d2WiderTransfer321C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer321S0:ℚ):ℝ)| + ((d2WiderTransfer321C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer321S1:ℚ):ℝ)| ≤ ((d2WiderTransfer321Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer321S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer321S0,d2WiderTransfer321Lo,d2WiderTransfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer321C0 then |x-((d2WiderTransfer321S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer321S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer321S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer321S0,d2WiderTransfer321Lo,d2WiderTransfer321Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer321C0,d2Log147Q,d2WiderTransfer321S0,d2WiderTransfer321Lo,d2WiderTransfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer321C0 d2WiderTransfer321S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2WiderTransfer321S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer321S1,d2WiderTransfer321Lo,d2WiderTransfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer321C1 then |x-((d2WiderTransfer321S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer321S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer321S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer321S1,d2WiderTransfer321Lo,d2WiderTransfer321Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer321C1,d2Log27Q,d2WiderTransfer321S1,d2WiderTransfer321Lo,d2WiderTransfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer321C1 d2WiderTransfer321S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2WiderTransfer321C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer321C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer321Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer321Arithmetic
  linarith
#print axioms d2WiderTransfer321Arithmetic
#print axioms d2WiderTransfer321Bound
def d2WiderTransfer322Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (169114029) 1 (-28))
def d2WiderTransfer322Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (1354589953) 1 (-31))
def d2WiderTransfer322Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (2238342807005286720359) 1 (-80))
def d2WiderTransfer322C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 55 (-3))
def d2WiderTransfer322S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
def d2WiderTransfer322C1 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 55 (-3))
def d2WiderTransfer322S1 : ℚ := (d2LitsNearWiderTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer322Arithmetic : weightedUpper d2WiderTransfer322C0 d2Log147Lo d2Log147Hi + weightedUpper d2WiderTransfer322C1 d2Log26Lo d2Log26Hi ≤ d2WiderTransfer322Cap := by decide +kernel
theorem d2WiderTransfer322Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer322Lo:ℚ):ℝ) ((d2WiderTransfer322Hi:ℚ):ℝ), ((d2WiderTransfer322C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer322S0:ℚ):ℝ)| + ((d2WiderTransfer322C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer322S1:ℚ):ℝ)| ≤ ((d2WiderTransfer322Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer322S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer322S0,d2WiderTransfer322Lo,d2WiderTransfer322Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer322C0 then |x-((d2WiderTransfer322S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer322S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer322S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer322S0,d2WiderTransfer322Lo,d2WiderTransfer322Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer322C0,d2Log147Q,d2WiderTransfer322S0,d2WiderTransfer322Lo,d2WiderTransfer322Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer322C0 d2WiderTransfer322S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2WiderTransfer322S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer322S1,d2WiderTransfer322Lo,d2WiderTransfer322Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer322C1 then |x-((d2WiderTransfer322S1:ℚ):ℝ)| ≤ ((d2Log26Q:ℚ):ℝ) else ((d2Log26Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer322S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer322S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer322S1,d2WiderTransfer322Lo,d2WiderTransfer322Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer322C1,d2Log26Q,d2WiderTransfer322S1,d2WiderTransfer322Lo,d2WiderTransfer322Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer322C1 d2WiderTransfer322S1 d2Log26Q d2Log26Lo d2Log26Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log26Bounds
  have har : (((weightedUpper d2WiderTransfer322C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer322C1 d2Log26Lo d2Log26Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer322Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer322Arithmetic
  linarith
#print axioms d2WiderTransfer322Arithmetic
#print axioms d2WiderTransfer322Bound
def d2WiderTransfer323Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (169114029) 1 (-28))
def d2WiderTransfer323Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (1354589953) 1 (-31))
def d2WiderTransfer323Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (17570138680931573654375) 1 (-80))
def d2WiderTransfer323C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (23) 25 (-5))
def d2WiderTransfer323S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer323Arithmetic : weightedUpper d2WiderTransfer323C0 d2Log148Lo d2Log148Hi ≤ d2WiderTransfer323Cap := by decide +kernel
theorem d2WiderTransfer323Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer323Lo:ℚ):ℝ) ((d2WiderTransfer323Hi:ℚ):ℝ), ((d2WiderTransfer323C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer323S0:ℚ):ℝ)| ≤ ((d2WiderTransfer323Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer323S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer323S0,d2WiderTransfer323Lo,d2WiderTransfer323Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer323C0 then |x-((d2WiderTransfer323S0:ℚ):ℝ)| ≤ ((d2Log148Q:ℚ):ℝ) else ((d2Log148Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer323S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer323S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer323S0,d2WiderTransfer323Lo,d2WiderTransfer323Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer323C0,d2Log148Q,d2WiderTransfer323S0,d2WiderTransfer323Lo,d2WiderTransfer323Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer323C0 d2WiderTransfer323S0 d2Log148Q d2Log148Lo d2Log148Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log148Bounds
  have har : (((weightedUpper d2WiderTransfer323C0 d2Log148Lo d2Log148Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer323Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer323Arithmetic
  linarith
#print axioms d2WiderTransfer323Arithmetic
#print axioms d2WiderTransfer323Bound
def d2WiderTransfer324Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (169114029) 1 (-28))
def d2WiderTransfer324Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (1354589953) 1 (-31))
def d2WiderTransfer324Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (34421126072198843949927) 1 (-80))
def d2WiderTransfer324C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (3) 275 (-5))
def d2WiderTransfer324S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
def d2WiderTransfer324C1 : ℚ := (d2LitsNearWiderTransfers040.q2 (-5) 11 (-4))
def d2WiderTransfer324S1 : ℚ := (d2LitsNearWiderTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer324Arithmetic : weightedUpper d2WiderTransfer324C0 d2Log148Lo d2Log148Hi + weightedUpper d2WiderTransfer324C1 d2Log26Lo d2Log26Hi ≤ d2WiderTransfer324Cap := by decide +kernel
theorem d2WiderTransfer324Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer324Lo:ℚ):ℝ) ((d2WiderTransfer324Hi:ℚ):ℝ), ((d2WiderTransfer324C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer324S0:ℚ):ℝ)| + ((d2WiderTransfer324C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer324S1:ℚ):ℝ)| ≤ ((d2WiderTransfer324Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer324S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer324S0,d2WiderTransfer324Lo,d2WiderTransfer324Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer324C0 then |x-((d2WiderTransfer324S0:ℚ):ℝ)| ≤ ((d2Log148Q:ℚ):ℝ) else ((d2Log148Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer324S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer324S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer324S0,d2WiderTransfer324Lo,d2WiderTransfer324Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer324C0,d2Log148Q,d2WiderTransfer324S0,d2WiderTransfer324Lo,d2WiderTransfer324Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer324C0 d2WiderTransfer324S0 d2Log148Q d2Log148Lo d2Log148Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log148Bounds
  have hn1 : x-((d2WiderTransfer324S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer324S1,d2WiderTransfer324Lo,d2WiderTransfer324Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer324C1 then |x-((d2WiderTransfer324S1:ℚ):ℝ)| ≤ ((d2Log26Q:ℚ):ℝ) else ((d2Log26Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer324S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer324S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer324S1,d2WiderTransfer324Lo,d2WiderTransfer324Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer324C1,d2Log26Q,d2WiderTransfer324S1,d2WiderTransfer324Lo,d2WiderTransfer324Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer324C1 d2WiderTransfer324S1 d2Log26Q d2Log26Lo d2Log26Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log26Bounds
  have har : (((weightedUpper d2WiderTransfer324C0 d2Log148Lo d2Log148Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer324C1 d2Log26Lo d2Log26Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer324Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer324Arithmetic
  linarith
#print axioms d2WiderTransfer324Arithmetic
#print axioms d2WiderTransfer324Bound
def d2WiderTransfer325Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (1354589953) 1 (-31))
def d2WiderTransfer325Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (678133837) 1 (-30))
def d2WiderTransfer325Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (1155644148338036120111) 1 (-79))
def d2WiderTransfer325C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 55 (-3))
def d2WiderTransfer325S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
def d2WiderTransfer325C1 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 55 (-3))
def d2WiderTransfer325S1 : ℚ := (d2LitsNearWiderTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer325Arithmetic : weightedUpper d2WiderTransfer325C0 d2Log148Lo d2Log148Hi + weightedUpper d2WiderTransfer325C1 d2Log25Lo d2Log25Hi ≤ d2WiderTransfer325Cap := by decide +kernel
theorem d2WiderTransfer325Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer325Lo:ℚ):ℝ) ((d2WiderTransfer325Hi:ℚ):ℝ), ((d2WiderTransfer325C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer325S0:ℚ):ℝ)| + ((d2WiderTransfer325C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer325S1:ℚ):ℝ)| ≤ ((d2WiderTransfer325Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer325S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer325S0,d2WiderTransfer325Lo,d2WiderTransfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer325C0 then |x-((d2WiderTransfer325S0:ℚ):ℝ)| ≤ ((d2Log148Q:ℚ):ℝ) else ((d2Log148Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer325S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer325S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer325S0,d2WiderTransfer325Lo,d2WiderTransfer325Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer325C0,d2Log148Q,d2WiderTransfer325S0,d2WiderTransfer325Lo,d2WiderTransfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer325C0 d2WiderTransfer325S0 d2Log148Q d2Log148Lo d2Log148Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log148Bounds
  have hn1 : x-((d2WiderTransfer325S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer325S1,d2WiderTransfer325Lo,d2WiderTransfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer325C1 then |x-((d2WiderTransfer325S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer325S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer325S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer325S1,d2WiderTransfer325Lo,d2WiderTransfer325Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer325C1,d2Log25Q,d2WiderTransfer325S1,d2WiderTransfer325Lo,d2WiderTransfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer325C1 d2WiderTransfer325S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2WiderTransfer325C0 d2Log148Lo d2Log148Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer325C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer325Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer325Arithmetic
  linarith
#print axioms d2WiderTransfer325Arithmetic
#print axioms d2WiderTransfer325Bound
def d2WiderTransfer326Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (1354589953) 1 (-31))
def d2WiderTransfer326Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (678133837) 1 (-30))
def d2WiderTransfer326Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (8821542085301179587119) 1 (-79))
def d2WiderTransfer326C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (23) 25 (-5))
def d2WiderTransfer326S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer326Arithmetic : weightedUpper d2WiderTransfer326C0 d2Log149Lo d2Log149Hi ≤ d2WiderTransfer326Cap := by decide +kernel
theorem d2WiderTransfer326Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer326Lo:ℚ):ℝ) ((d2WiderTransfer326Hi:ℚ):ℝ), ((d2WiderTransfer326C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer326S0:ℚ):ℝ)| ≤ ((d2WiderTransfer326Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer326S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer326S0,d2WiderTransfer326Lo,d2WiderTransfer326Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer326C0 then |x-((d2WiderTransfer326S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer326S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer326S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer326S0,d2WiderTransfer326Lo,d2WiderTransfer326Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer326C0,d2Log149Q,d2WiderTransfer326S0,d2WiderTransfer326Lo,d2WiderTransfer326Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer326C0 d2WiderTransfer326S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have har : (((weightedUpper d2WiderTransfer326C0 d2Log149Lo d2Log149Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer326Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer326Arithmetic
  linarith
#print axioms d2WiderTransfer326Arithmetic
#print axioms d2WiderTransfer326Bound
def d2WiderTransfer327Lo : ℚ := (d2LitsNearWiderTransfers040.q2 (1354589953) 1 (-31))
def d2WiderTransfer327Hi : ℚ := (d2LitsNearWiderTransfers040.q2 (678133837) 1 (-30))
def d2WiderTransfer327Cap : ℚ := (d2LitsNearWiderTransfers040.q2 (17247035780934814734895) 1 (-79))
def d2WiderTransfer327C0 : ℚ := (d2LitsNearWiderTransfers040.q2 (3) 275 (-5))
def d2WiderTransfer327S0 : ℚ := (d2LitsNearWiderTransfers040.q2 (-1) 1 (0))
def d2WiderTransfer327C1 : ℚ := (d2LitsNearWiderTransfers040.q2 (-5) 11 (-4))
def d2WiderTransfer327S1 : ℚ := (d2LitsNearWiderTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer327Arithmetic : weightedUpper d2WiderTransfer327C0 d2Log149Lo d2Log149Hi + weightedUpper d2WiderTransfer327C1 d2Log25Lo d2Log25Hi ≤ d2WiderTransfer327Cap := by decide +kernel
theorem d2WiderTransfer327Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer327Lo:ℚ):ℝ) ((d2WiderTransfer327Hi:ℚ):ℝ), ((d2WiderTransfer327C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer327S0:ℚ):ℝ)| + ((d2WiderTransfer327C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer327S1:ℚ):ℝ)| ≤ ((d2WiderTransfer327Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer327S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer327S0,d2WiderTransfer327Lo,d2WiderTransfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer327C0 then |x-((d2WiderTransfer327S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer327S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer327S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer327S0,d2WiderTransfer327Lo,d2WiderTransfer327Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer327C0,d2Log149Q,d2WiderTransfer327S0,d2WiderTransfer327Lo,d2WiderTransfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer327C0 d2WiderTransfer327S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2WiderTransfer327S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer327S1,d2WiderTransfer327Lo,d2WiderTransfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer327C1 then |x-((d2WiderTransfer327S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer327S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer327S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer327S1,d2WiderTransfer327Lo,d2WiderTransfer327Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer327C1,d2Log25Q,d2WiderTransfer327S1,d2WiderTransfer327Lo,d2WiderTransfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer327C1 d2WiderTransfer327S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2WiderTransfer327C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer327C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer327Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer327Arithmetic
  linarith
#print axioms d2WiderTransfer327Arithmetic
#print axioms d2WiderTransfer327Bound
end CatalanMeasure.GenD.Signed.Data.Cells
