module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers040
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers040
open D72.LogTransfer
def d2Transfer320Lo : ℚ := (d2LitsNearTransfers040.q2 (678133837) 1 (-30))
def d2Transfer320Hi : ℚ := (d2LitsNearTransfers040.q2 (339905779) 1 (-29))
def d2Transfer320Cap : ℚ := (d2LitsNearTransfers040.q2 (19758017983738877923109) 1 (-80))
def d2Transfer320C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 1 (-5))
def d2Transfer320S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer320Arithmetic : weightedUpper d2Transfer320C0 d2Log151Lo d2Log151Hi ≤ d2Transfer320Cap := by decide +kernel
theorem d2Transfer320Bound : ∀ x ∈ Set.Icc ((d2Transfer320Lo:ℚ):ℝ) ((d2Transfer320Hi:ℚ):ℝ), ((d2Transfer320C0:ℚ):ℝ)*Real.log |x-((d2Transfer320S0:ℚ):ℝ)| ≤ ((d2Transfer320Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer320S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer320S0,d2Transfer320Lo,d2Transfer320Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer320C0 then |x-((d2Transfer320S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2Transfer320S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer320S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer320S0,d2Transfer320Lo,d2Transfer320Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer320C0,d2Log151Q,d2Transfer320S0,d2Transfer320Lo,d2Transfer320Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer320C0 d2Transfer320S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have har : (((weightedUpper d2Transfer320C0 d2Log151Lo d2Log151Hi:ℚ):ℝ)) ≤ ((d2Transfer320Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer320Arithmetic
  linarith
#print axioms d2Transfer320Arithmetic
#print axioms d2Transfer320Bound
def d2Transfer321Lo : ℚ := (d2LitsNearTransfers040.q2 (678133837) 1 (-30))
def d2Transfer321Hi : ℚ := (d2LitsNearTransfers040.q2 (339905779) 1 (-29))
def d2Transfer321Cap : ℚ := (d2LitsNearTransfers040.q2 (36122855306030385286949) 1 (-80))
def d2Transfer321C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 11 (-5))
def d2Transfer321S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
def d2Transfer321C1 : ℚ := (d2LitsNearTransfers040.q2 (-5) 11 (-4))
def d2Transfer321S1 : ℚ := (d2LitsNearTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer321Arithmetic : weightedUpper d2Transfer321C0 d2Log151Lo d2Log151Hi + weightedUpper d2Transfer321C1 d2Log23Lo d2Log23Hi ≤ d2Transfer321Cap := by decide +kernel
theorem d2Transfer321Bound : ∀ x ∈ Set.Icc ((d2Transfer321Lo:ℚ):ℝ) ((d2Transfer321Hi:ℚ):ℝ), ((d2Transfer321C0:ℚ):ℝ)*Real.log |x-((d2Transfer321S0:ℚ):ℝ)| + ((d2Transfer321C1:ℚ):ℝ)*Real.log |x-((d2Transfer321S1:ℚ):ℝ)| ≤ ((d2Transfer321Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer321S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer321S0,d2Transfer321Lo,d2Transfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer321C0 then |x-((d2Transfer321S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2Transfer321S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer321S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer321S0,d2Transfer321Lo,d2Transfer321Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer321C0,d2Log151Q,d2Transfer321S0,d2Transfer321Lo,d2Transfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer321C0 d2Transfer321S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2Transfer321S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer321S1,d2Transfer321Lo,d2Transfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer321C1 then |x-((d2Transfer321S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2Transfer321S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer321S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer321S1,d2Transfer321Lo,d2Transfer321Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer321C1,d2Log23Q,d2Transfer321S1,d2Transfer321Lo,d2Transfer321Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer321C1 d2Transfer321S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2Transfer321C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2Transfer321C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2Transfer321Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer321Arithmetic
  linarith
#print axioms d2Transfer321Arithmetic
#print axioms d2Transfer321Bound
def d2Transfer322Lo : ℚ := (d2LitsNearTransfers040.q2 (339905779) 1 (-29))
def d2Transfer322Hi : ℚ := (d2LitsNearTransfers040.q2 (85395875) 1 (-27))
def d2Transfer322Cap : ℚ := (d2LitsNearTransfers040.q2 (3585015757831320625385) 1 (-80))
def d2Transfer322C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 25 (-4))
def d2Transfer322S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer322Arithmetic : weightedUpper d2Transfer322C0 d2Log155Lo d2Log155Hi ≤ d2Transfer322Cap := by decide +kernel
theorem d2Transfer322Bound : ∀ x ∈ Set.Icc ((d2Transfer322Lo:ℚ):ℝ) ((d2Transfer322Hi:ℚ):ℝ), ((d2Transfer322C0:ℚ):ℝ)*Real.log |x-((d2Transfer322S0:ℚ):ℝ)| ≤ ((d2Transfer322Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer322S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer322S0,d2Transfer322Lo,d2Transfer322Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer322C0 then |x-((d2Transfer322S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2Transfer322S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer322S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer322S0,d2Transfer322Lo,d2Transfer322Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer322C0,d2Log155Q,d2Transfer322S0,d2Transfer322Lo,d2Transfer322Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer322C0 d2Transfer322S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have har : (((weightedUpper d2Transfer322C0 d2Log155Lo d2Log155Hi:ℚ):ℝ)) ≤ ((d2Transfer322Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer322Arithmetic
  linarith
#print axioms d2Transfer322Arithmetic
#print axioms d2Transfer322Bound
def d2Transfer323Lo : ℚ := (d2LitsNearTransfers040.q2 (339905779) 1 (-29))
def d2Transfer323Hi : ℚ := (d2LitsNearTransfers040.q2 (85395875) 1 (-27))
def d2Transfer323Cap : ℚ := (d2LitsNearTransfers040.q2 (4835315926467055968489) 1 (-80))
def d2Transfer323C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 275 (-4))
def d2Transfer323S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
def d2Transfer323C1 : ℚ := (d2LitsNearTransfers040.q2 (-1) 55 (-3))
def d2Transfer323S1 : ℚ := (d2LitsNearTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer323Arithmetic : weightedUpper d2Transfer323C0 d2Log155Lo d2Log155Hi + weightedUpper d2Transfer323C1 d2Log19Lo d2Log19Hi ≤ d2Transfer323Cap := by decide +kernel
theorem d2Transfer323Bound : ∀ x ∈ Set.Icc ((d2Transfer323Lo:ℚ):ℝ) ((d2Transfer323Hi:ℚ):ℝ), ((d2Transfer323C0:ℚ):ℝ)*Real.log |x-((d2Transfer323S0:ℚ):ℝ)| + ((d2Transfer323C1:ℚ):ℝ)*Real.log |x-((d2Transfer323S1:ℚ):ℝ)| ≤ ((d2Transfer323Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer323S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer323S0,d2Transfer323Lo,d2Transfer323Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer323C0 then |x-((d2Transfer323S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2Transfer323S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer323S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer323S0,d2Transfer323Lo,d2Transfer323Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer323C0,d2Log155Q,d2Transfer323S0,d2Transfer323Lo,d2Transfer323Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer323C0 d2Transfer323S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2Transfer323S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer323S1,d2Transfer323Lo,d2Transfer323Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer323C1 then |x-((d2Transfer323S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2Transfer323S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer323S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer323S1,d2Transfer323Lo,d2Transfer323Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer323C1,d2Log19Q,d2Transfer323S1,d2Transfer323Lo,d2Transfer323Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer323C1 d2Transfer323S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2Transfer323C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2Transfer323C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2Transfer323Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer323Arithmetic
  linarith
#print axioms d2Transfer323Arithmetic
#print axioms d2Transfer323Bound
def d2Transfer324Lo : ℚ := (d2LitsNearTransfers040.q2 (339905779) 1 (-29))
def d2Transfer324Hi : ℚ := (d2LitsNearTransfers040.q2 (85395875) 1 (-27))
def d2Transfer324Cap : ℚ := (d2LitsNearTransfers040.q2 (20058378016890016489705) 1 (-80))
def d2Transfer324C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 1 (-5))
def d2Transfer324S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer324Arithmetic : weightedUpper d2Transfer324C0 d2Log155Lo d2Log155Hi ≤ d2Transfer324Cap := by decide +kernel
theorem d2Transfer324Bound : ∀ x ∈ Set.Icc ((d2Transfer324Lo:ℚ):ℝ) ((d2Transfer324Hi:ℚ):ℝ), ((d2Transfer324C0:ℚ):ℝ)*Real.log |x-((d2Transfer324S0:ℚ):ℝ)| ≤ ((d2Transfer324Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer324S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer324S0,d2Transfer324Lo,d2Transfer324Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer324C0 then |x-((d2Transfer324S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2Transfer324S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer324S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer324S0,d2Transfer324Lo,d2Transfer324Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer324C0,d2Log155Q,d2Transfer324S0,d2Transfer324Lo,d2Transfer324Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer324C0 d2Transfer324S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have har : (((weightedUpper d2Transfer324C0 d2Log155Lo d2Log155Hi:ℚ):ℝ)) ≤ ((d2Transfer324Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer324Arithmetic
  linarith
#print axioms d2Transfer324Arithmetic
#print axioms d2Transfer324Bound
def d2Transfer325Lo : ℚ := (d2LitsNearTransfers040.q2 (339905779) 1 (-29))
def d2Transfer325Hi : ℚ := (d2LitsNearTransfers040.q2 (85395875) 1 (-27))
def d2Transfer325Cap : ℚ := (d2LitsNearTransfers040.q2 (36423215339181523853545) 1 (-80))
def d2Transfer325C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 11 (-5))
def d2Transfer325S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
def d2Transfer325C1 : ℚ := (d2LitsNearTransfers040.q2 (-5) 11 (-4))
def d2Transfer325S1 : ℚ := (d2LitsNearTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer325Arithmetic : weightedUpper d2Transfer325C0 d2Log155Lo d2Log155Hi + weightedUpper d2Transfer325C1 d2Log19Lo d2Log19Hi ≤ d2Transfer325Cap := by decide +kernel
theorem d2Transfer325Bound : ∀ x ∈ Set.Icc ((d2Transfer325Lo:ℚ):ℝ) ((d2Transfer325Hi:ℚ):ℝ), ((d2Transfer325C0:ℚ):ℝ)*Real.log |x-((d2Transfer325S0:ℚ):ℝ)| + ((d2Transfer325C1:ℚ):ℝ)*Real.log |x-((d2Transfer325S1:ℚ):ℝ)| ≤ ((d2Transfer325Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer325S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer325S0,d2Transfer325Lo,d2Transfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer325C0 then |x-((d2Transfer325S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2Transfer325S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer325S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer325S0,d2Transfer325Lo,d2Transfer325Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer325C0,d2Log155Q,d2Transfer325S0,d2Transfer325Lo,d2Transfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer325C0 d2Transfer325S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2Transfer325S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer325S1,d2Transfer325Lo,d2Transfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer325C1 then |x-((d2Transfer325S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2Transfer325S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer325S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer325S1,d2Transfer325Lo,d2Transfer325Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer325C1,d2Log19Q,d2Transfer325S1,d2Transfer325Lo,d2Transfer325Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer325C1 d2Transfer325S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2Transfer325C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2Transfer325C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2Transfer325Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer325Arithmetic
  linarith
#print axioms d2Transfer325Arithmetic
#print axioms d2Transfer325Bound
def d2Transfer326Lo : ℚ := (d2LitsNearTransfers040.q2 (85395875) 1 (-27))
def d2Transfer326Hi : ℚ := (d2LitsNearTransfers040.q2 (343261221) 1 (-29))
def d2Transfer326Cap : ℚ := (d2LitsNearTransfers040.q2 (3887898182126945858551) 1 (-80))
def d2Transfer326C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 25 (-4))
def d2Transfer326S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer326Arithmetic : weightedUpper d2Transfer326C0 d2Log158Lo d2Log158Hi ≤ d2Transfer326Cap := by decide +kernel
theorem d2Transfer326Bound : ∀ x ∈ Set.Icc ((d2Transfer326Lo:ℚ):ℝ) ((d2Transfer326Hi:ℚ):ℝ), ((d2Transfer326C0:ℚ):ℝ)*Real.log |x-((d2Transfer326S0:ℚ):ℝ)| ≤ ((d2Transfer326Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer326S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer326S0,d2Transfer326Lo,d2Transfer326Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer326C0 then |x-((d2Transfer326S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2Transfer326S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer326S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer326S0,d2Transfer326Lo,d2Transfer326Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer326C0,d2Log158Q,d2Transfer326S0,d2Transfer326Lo,d2Transfer326Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer326C0 d2Transfer326S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have har : (((weightedUpper d2Transfer326C0 d2Log158Lo d2Log158Hi:ℚ):ℝ)) ≤ ((d2Transfer326Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer326Arithmetic
  linarith
#print axioms d2Transfer326Arithmetic
#print axioms d2Transfer326Bound
def d2Transfer327Lo : ℚ := (d2LitsNearTransfers040.q2 (85395875) 1 (-27))
def d2Transfer327Hi : ℚ := (d2LitsNearTransfers040.q2 (343261221) 1 (-29))
def d2Transfer327Cap : ℚ := (d2LitsNearTransfers040.q2 (5138198350762681201655) 1 (-80))
def d2Transfer327C0 : ℚ := (d2LitsNearTransfers040.q2 (1) 275 (-4))
def d2Transfer327S0 : ℚ := (d2LitsNearTransfers040.q2 (-1) 1 (0))
def d2Transfer327C1 : ℚ := (d2LitsNearTransfers040.q2 (-1) 55 (-3))
def d2Transfer327S1 : ℚ := (d2LitsNearTransfers040.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer327Arithmetic : weightedUpper d2Transfer327C0 d2Log158Lo d2Log158Hi + weightedUpper d2Transfer327C1 d2Log16Lo d2Log16Hi ≤ d2Transfer327Cap := by decide +kernel
theorem d2Transfer327Bound : ∀ x ∈ Set.Icc ((d2Transfer327Lo:ℚ):ℝ) ((d2Transfer327Hi:ℚ):ℝ), ((d2Transfer327C0:ℚ):ℝ)*Real.log |x-((d2Transfer327S0:ℚ):ℝ)| + ((d2Transfer327C1:ℚ):ℝ)*Real.log |x-((d2Transfer327S1:ℚ):ℝ)| ≤ ((d2Transfer327Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer327S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer327S0,d2Transfer327Lo,d2Transfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer327C0 then |x-((d2Transfer327S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2Transfer327S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer327S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer327S0,d2Transfer327Lo,d2Transfer327Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer327C0,d2Log158Q,d2Transfer327S0,d2Transfer327Lo,d2Transfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer327C0 d2Transfer327S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2Transfer327S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer327S1,d2Transfer327Lo,d2Transfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer327C1 then |x-((d2Transfer327S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2Transfer327S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer327S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer327S1,d2Transfer327Lo,d2Transfer327Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers040.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer327C1,d2Log16Q,d2Transfer327S1,d2Transfer327Lo,d2Transfer327Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer327C1 d2Transfer327S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2Transfer327C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2Transfer327C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2Transfer327Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer327Arithmetic
  linarith
#print axioms d2Transfer327Arithmetic
#print axioms d2Transfer327Bound
end CatalanMeasure.GenD.Signed.Data.Cells
