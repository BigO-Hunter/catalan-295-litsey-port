module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers043
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers043
open D72.LogTransfer
def d2Transfer344Lo : ℚ := (d2LitsNearTransfers043.q2 (88751317) 1 (-27))
def d2Transfer344Hi : ℚ := (d2LitsNearTransfers043.q2 (45214519) 1 (-26))
def d2Transfer344Cap : ℚ := (d2LitsNearTransfers043.q2 (5968241331627658409123) 1 (-78))
def d2Transfer344C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 1 (-5))
def d2Transfer344S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer344Arithmetic : weightedUpper d2Transfer344C0 d2Log165Lo d2Log165Hi ≤ d2Transfer344Cap := by decide +kernel
theorem d2Transfer344Bound : ∀ x ∈ Set.Icc ((d2Transfer344Lo:ℚ):ℝ) ((d2Transfer344Hi:ℚ):ℝ), ((d2Transfer344C0:ℚ):ℝ)*Real.log |x-((d2Transfer344S0:ℚ):ℝ)| ≤ ((d2Transfer344Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer344S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer344S0,d2Transfer344Lo,d2Transfer344Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer344C0 then |x-((d2Transfer344S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2Transfer344S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer344S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer344S0,d2Transfer344Lo,d2Transfer344Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer344C0,d2Log165Q,d2Transfer344S0,d2Transfer344Lo,d2Transfer344Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer344C0 d2Transfer344S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have har : (((weightedUpper d2Transfer344C0 d2Log165Lo d2Log165Hi:ℚ):ℝ)) ≤ ((d2Transfer344Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer344Arithmetic
  linarith
#print axioms d2Transfer344Arithmetic
#print axioms d2Transfer344Bound
def d2Transfer345Lo : ℚ := (d2LitsNearTransfers043.q2 (88751317) 1 (-27))
def d2Transfer345Hi : ℚ := (d2LitsNearTransfers043.q2 (45214519) 1 (-26))
def d2Transfer345Cap : ℚ := (d2LitsNearTransfers043.q2 (10059450662200535250083) 1 (-78))
def d2Transfer345C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 11 (-5))
def d2Transfer345S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
def d2Transfer345C1 : ℚ := (d2LitsNearTransfers043.q2 (-5) 11 (-4))
def d2Transfer345S1 : ℚ := (d2LitsNearTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer345Arithmetic : weightedUpper d2Transfer345C0 d2Log165Lo d2Log165Hi + weightedUpper d2Transfer345C1 d2Log9Lo d2Log9Hi ≤ d2Transfer345Cap := by decide +kernel
theorem d2Transfer345Bound : ∀ x ∈ Set.Icc ((d2Transfer345Lo:ℚ):ℝ) ((d2Transfer345Hi:ℚ):ℝ), ((d2Transfer345C0:ℚ):ℝ)*Real.log |x-((d2Transfer345S0:ℚ):ℝ)| + ((d2Transfer345C1:ℚ):ℝ)*Real.log |x-((d2Transfer345S1:ℚ):ℝ)| ≤ ((d2Transfer345Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer345S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer345S0,d2Transfer345Lo,d2Transfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer345C0 then |x-((d2Transfer345S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2Transfer345S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer345S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer345S0,d2Transfer345Lo,d2Transfer345Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer345C0,d2Log165Q,d2Transfer345S0,d2Transfer345Lo,d2Transfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer345C0 d2Transfer345S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2Transfer345S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer345S1,d2Transfer345Lo,d2Transfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer345C1 then |x-((d2Transfer345S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2Transfer345S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer345S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer345S1,d2Transfer345Lo,d2Transfer345Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer345C1,d2Log9Q,d2Transfer345S1,d2Transfer345Lo,d2Transfer345Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer345C1 d2Transfer345S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2Transfer345C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2Transfer345C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2Transfer345Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer345Arithmetic
  linarith
#print axioms d2Transfer345Arithmetic
#print axioms d2Transfer345Bound
def d2Transfer346Lo : ℚ := (d2LitsNearTransfers043.q2 (45214519) 1 (-26))
def d2Transfer346Hi : ℚ := (d2LitsNearTransfers043.q2 (2930765) 1 (-22))
def d2Transfer346Cap : ℚ := (d2LitsNearTransfers043.q2 (10188572794624507164743) 1 (-80))
def d2Transfer346C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 25 (-4))
def d2Transfer346S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer346Arithmetic : weightedUpper d2Transfer346C0 d2Log166Lo d2Log166Hi ≤ d2Transfer346Cap := by decide +kernel
theorem d2Transfer346Bound : ∀ x ∈ Set.Icc ((d2Transfer346Lo:ℚ):ℝ) ((d2Transfer346Hi:ℚ):ℝ), ((d2Transfer346C0:ℚ):ℝ)*Real.log |x-((d2Transfer346S0:ℚ):ℝ)| ≤ ((d2Transfer346Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer346S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer346S0,d2Transfer346Lo,d2Transfer346Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer346C0 then |x-((d2Transfer346S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer346S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer346S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer346S0,d2Transfer346Lo,d2Transfer346Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer346C0,d2Log166Q,d2Transfer346S0,d2Transfer346Lo,d2Transfer346Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer346C0 d2Transfer346S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2Transfer346C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2Transfer346Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer346Arithmetic
  linarith
#print axioms d2Transfer346Arithmetic
#print axioms d2Transfer346Bound
def d2Transfer347Lo : ℚ := (d2LitsNearTransfers043.q2 (45214519) 1 (-26))
def d2Transfer347Hi : ℚ := (d2LitsNearTransfers043.q2 (2930765) 1 (-22))
def d2Transfer347Cap : ℚ := (d2LitsNearTransfers043.q2 (11438872963260242507847) 1 (-80))
def d2Transfer347C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 275 (-4))
def d2Transfer347S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
def d2Transfer347C1 : ℚ := (d2LitsNearTransfers043.q2 (-1) 55 (-3))
def d2Transfer347S1 : ℚ := (d2LitsNearTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer347Arithmetic : weightedUpper d2Transfer347C0 d2Log166Lo d2Log166Hi + weightedUpper d2Transfer347C1 d2Log8Lo d2Log8Hi ≤ d2Transfer347Cap := by decide +kernel
theorem d2Transfer347Bound : ∀ x ∈ Set.Icc ((d2Transfer347Lo:ℚ):ℝ) ((d2Transfer347Hi:ℚ):ℝ), ((d2Transfer347C0:ℚ):ℝ)*Real.log |x-((d2Transfer347S0:ℚ):ℝ)| + ((d2Transfer347C1:ℚ):ℝ)*Real.log |x-((d2Transfer347S1:ℚ):ℝ)| ≤ ((d2Transfer347Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer347S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer347S0,d2Transfer347Lo,d2Transfer347Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer347C0 then |x-((d2Transfer347S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer347S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer347S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer347S0,d2Transfer347Lo,d2Transfer347Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer347C0,d2Log166Q,d2Transfer347S0,d2Transfer347Lo,d2Transfer347Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer347C0 d2Transfer347S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2Transfer347S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer347S1,d2Transfer347Lo,d2Transfer347Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer347C1 then |x-((d2Transfer347S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2Transfer347S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer347S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer347S1,d2Transfer347Lo,d2Transfer347Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer347C1,d2Log8Q,d2Transfer347S1,d2Transfer347Lo,d2Transfer347Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer347C1 d2Transfer347S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2Transfer347C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2Transfer347C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2Transfer347Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer347Arithmetic
  linarith
#print axioms d2Transfer347Arithmetic
#print axioms d2Transfer347Bound
def d2Transfer348Lo : ℚ := (d2LitsNearTransfers043.q2 (45214519) 1 (-26))
def d2Transfer348Hi : ℚ := (d2LitsNearTransfers043.q2 (2930765) 1 (-22))
def d2Transfer348Cap : ℚ := (d2LitsNearTransfers043.q2 (26661935053683203029063) 1 (-80))
def d2Transfer348C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 1 (-5))
def d2Transfer348S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer348Arithmetic : weightedUpper d2Transfer348C0 d2Log166Lo d2Log166Hi ≤ d2Transfer348Cap := by decide +kernel
theorem d2Transfer348Bound : ∀ x ∈ Set.Icc ((d2Transfer348Lo:ℚ):ℝ) ((d2Transfer348Hi:ℚ):ℝ), ((d2Transfer348C0:ℚ):ℝ)*Real.log |x-((d2Transfer348S0:ℚ):ℝ)| ≤ ((d2Transfer348Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer348S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer348S0,d2Transfer348Lo,d2Transfer348Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer348C0 then |x-((d2Transfer348S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer348S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer348S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer348S0,d2Transfer348Lo,d2Transfer348Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer348C0,d2Log166Q,d2Transfer348S0,d2Transfer348Lo,d2Transfer348Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer348C0 d2Transfer348S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2Transfer348C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2Transfer348Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer348Arithmetic
  linarith
#print axioms d2Transfer348Arithmetic
#print axioms d2Transfer348Bound
def d2Transfer349Lo : ℚ := (d2LitsNearTransfers043.q2 (45214519) 1 (-26))
def d2Transfer349Hi : ℚ := (d2LitsNearTransfers043.q2 (2930765) 1 (-22))
def d2Transfer349Cap : ℚ := (d2LitsNearTransfers043.q2 (43026772375974710392903) 1 (-80))
def d2Transfer349C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 11 (-5))
def d2Transfer349S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
def d2Transfer349C1 : ℚ := (d2LitsNearTransfers043.q2 (-5) 11 (-4))
def d2Transfer349S1 : ℚ := (d2LitsNearTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer349Arithmetic : weightedUpper d2Transfer349C0 d2Log166Lo d2Log166Hi + weightedUpper d2Transfer349C1 d2Log8Lo d2Log8Hi ≤ d2Transfer349Cap := by decide +kernel
theorem d2Transfer349Bound : ∀ x ∈ Set.Icc ((d2Transfer349Lo:ℚ):ℝ) ((d2Transfer349Hi:ℚ):ℝ), ((d2Transfer349C0:ℚ):ℝ)*Real.log |x-((d2Transfer349S0:ℚ):ℝ)| + ((d2Transfer349C1:ℚ):ℝ)*Real.log |x-((d2Transfer349S1:ℚ):ℝ)| ≤ ((d2Transfer349Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer349S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer349S0,d2Transfer349Lo,d2Transfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer349C0 then |x-((d2Transfer349S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer349S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer349S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer349S0,d2Transfer349Lo,d2Transfer349Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer349C0,d2Log166Q,d2Transfer349S0,d2Transfer349Lo,d2Transfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer349C0 d2Transfer349S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2Transfer349S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer349S1,d2Transfer349Lo,d2Transfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer349C1 then |x-((d2Transfer349S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2Transfer349S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer349S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer349S1,d2Transfer349Lo,d2Transfer349Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer349C1,d2Log8Q,d2Transfer349S1,d2Transfer349Lo,d2Transfer349Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer349C1 d2Transfer349S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2Transfer349C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2Transfer349C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2Transfer349Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer349Arithmetic
  linarith
#print axioms d2Transfer349Arithmetic
#print axioms d2Transfer349Bound
def d2Transfer350Lo : ℚ := (d2LitsNearTransfers043.q2 (2930765) 1 (-22))
def d2Transfer350Hi : ℚ := (d2LitsNearTransfers043.q2 (25123841) 1 (-25))
def d2Transfer350Cap : ℚ := (d2LitsNearTransfers043.q2 (4130355511903425424277) 1 (-78))
def d2Transfer350C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 25 (-4))
def d2Transfer350S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer350Arithmetic : weightedUpper d2Transfer350C0 d2Log167Lo d2Log167Hi ≤ d2Transfer350Cap := by decide +kernel
theorem d2Transfer350Bound : ∀ x ∈ Set.Icc ((d2Transfer350Lo:ℚ):ℝ) ((d2Transfer350Hi:ℚ):ℝ), ((d2Transfer350C0:ℚ):ℝ)*Real.log |x-((d2Transfer350S0:ℚ):ℝ)| ≤ ((d2Transfer350Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer350S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer350S0,d2Transfer350Lo,d2Transfer350Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer350C0 then |x-((d2Transfer350S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2Transfer350S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer350S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer350S0,d2Transfer350Lo,d2Transfer350Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer350C0,d2Log167Q,d2Transfer350S0,d2Transfer350Lo,d2Transfer350Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer350C0 d2Transfer350S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have har : (((weightedUpper d2Transfer350C0 d2Log167Lo d2Log167Hi:ℚ):ℝ)) ≤ ((d2Transfer350Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer350Arithmetic
  linarith
#print axioms d2Transfer350Arithmetic
#print axioms d2Transfer350Bound
def d2Transfer351Lo : ℚ := (d2LitsNearTransfers043.q2 (2930765) 1 (-22))
def d2Transfer351Hi : ℚ := (d2LitsNearTransfers043.q2 (25123841) 1 (-25))
def d2Transfer351Cap : ℚ := (d2LitsNearTransfers043.q2 (4442930554062359260053) 1 (-78))
def d2Transfer351C0 : ℚ := (d2LitsNearTransfers043.q2 (1) 275 (-4))
def d2Transfer351S0 : ℚ := (d2LitsNearTransfers043.q2 (-1) 1 (0))
def d2Transfer351C1 : ℚ := (d2LitsNearTransfers043.q2 (-1) 55 (-3))
def d2Transfer351S1 : ℚ := (d2LitsNearTransfers043.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer351Arithmetic : weightedUpper d2Transfer351C0 d2Log167Lo d2Log167Hi + weightedUpper d2Transfer351C1 d2Log7Lo d2Log7Hi ≤ d2Transfer351Cap := by decide +kernel
theorem d2Transfer351Bound : ∀ x ∈ Set.Icc ((d2Transfer351Lo:ℚ):ℝ) ((d2Transfer351Hi:ℚ):ℝ), ((d2Transfer351C0:ℚ):ℝ)*Real.log |x-((d2Transfer351S0:ℚ):ℝ)| + ((d2Transfer351C1:ℚ):ℝ)*Real.log |x-((d2Transfer351S1:ℚ):ℝ)| ≤ ((d2Transfer351Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer351S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer351S0,d2Transfer351Lo,d2Transfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer351C0 then |x-((d2Transfer351S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2Transfer351S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer351S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer351S0,d2Transfer351Lo,d2Transfer351Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer351C0,d2Log167Q,d2Transfer351S0,d2Transfer351Lo,d2Transfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer351C0 d2Transfer351S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2Transfer351S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer351S1,d2Transfer351Lo,d2Transfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer351C1 then |x-((d2Transfer351S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2Transfer351S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer351S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer351S1,d2Transfer351Lo,d2Transfer351Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers043.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer351C1,d2Log7Q,d2Transfer351S1,d2Transfer351Lo,d2Transfer351Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer351C1 d2Transfer351S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2Transfer351C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2Transfer351C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2Transfer351Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer351Arithmetic
  linarith
#print axioms d2Transfer351Arithmetic
#print axioms d2Transfer351Bound
end CatalanMeasure.GenD.Signed.Data.Cells
