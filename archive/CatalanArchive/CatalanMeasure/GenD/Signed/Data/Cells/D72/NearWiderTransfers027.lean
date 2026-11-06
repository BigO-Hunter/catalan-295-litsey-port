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
namespace d2LitsNearWiderTransfers027
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers027
open D72.LogTransfer
def d2WiderTransfer216Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (45214519) 1 (-26))
def d2WiderTransfer216Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (2930765) 1 (-22))
def d2WiderTransfer216Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (26661935053683203029063) 1 (-80))
def d2WiderTransfer216C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 1 (-5))
def d2WiderTransfer216S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer216Arithmetic : weightedUpper d2WiderTransfer216C0 d2Log166Lo d2Log166Hi ≤ d2WiderTransfer216Cap := by decide +kernel
theorem d2WiderTransfer216Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer216Lo:ℚ):ℝ) ((d2WiderTransfer216Hi:ℚ):ℝ), ((d2WiderTransfer216C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer216S0:ℚ):ℝ)| ≤ ((d2WiderTransfer216Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer216S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer216S0,d2WiderTransfer216Lo,d2WiderTransfer216Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer216C0 then |x-((d2WiderTransfer216S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer216S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer216S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer216S0,d2WiderTransfer216Lo,d2WiderTransfer216Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer216C0,d2Log166Q,d2WiderTransfer216S0,d2WiderTransfer216Lo,d2WiderTransfer216Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer216C0 d2WiderTransfer216S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2WiderTransfer216C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer216Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer216Arithmetic
  linarith
#print axioms d2WiderTransfer216Arithmetic
#print axioms d2WiderTransfer216Bound
def d2WiderTransfer217Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (45214519) 1 (-26))
def d2WiderTransfer217Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (2930765) 1 (-22))
def d2WiderTransfer217Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (43026772375974710392903) 1 (-80))
def d2WiderTransfer217C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 11 (-5))
def d2WiderTransfer217S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
def d2WiderTransfer217C1 : ℚ := (d2LitsNearWiderTransfers027.q2 (-5) 11 (-4))
def d2WiderTransfer217S1 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer217Arithmetic : weightedUpper d2WiderTransfer217C0 d2Log166Lo d2Log166Hi + weightedUpper d2WiderTransfer217C1 d2Log8Lo d2Log8Hi ≤ d2WiderTransfer217Cap := by decide +kernel
theorem d2WiderTransfer217Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer217Lo:ℚ):ℝ) ((d2WiderTransfer217Hi:ℚ):ℝ), ((d2WiderTransfer217C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer217S0:ℚ):ℝ)| + ((d2WiderTransfer217C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer217S1:ℚ):ℝ)| ≤ ((d2WiderTransfer217Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer217S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer217S0,d2WiderTransfer217Lo,d2WiderTransfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer217C0 then |x-((d2WiderTransfer217S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer217S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer217S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer217S0,d2WiderTransfer217Lo,d2WiderTransfer217Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer217C0,d2Log166Q,d2WiderTransfer217S0,d2WiderTransfer217Lo,d2WiderTransfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer217C0 d2WiderTransfer217S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2WiderTransfer217S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer217S1,d2WiderTransfer217Lo,d2WiderTransfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer217C1 then |x-((d2WiderTransfer217S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer217S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer217S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer217S1,d2WiderTransfer217Lo,d2WiderTransfer217Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer217C1,d2Log8Q,d2WiderTransfer217S1,d2WiderTransfer217Lo,d2WiderTransfer217Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer217C1 d2WiderTransfer217S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2WiderTransfer217C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer217C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer217Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer217Arithmetic
  linarith
#print axioms d2WiderTransfer217Arithmetic
#print axioms d2WiderTransfer217Bound
def d2WiderTransfer218Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (2930765) 1 (-22))
def d2WiderTransfer218Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (25123841) 1 (-25))
def d2WiderTransfer218Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (4130355511903425424277) 1 (-78))
def d2WiderTransfer218C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 25 (-4))
def d2WiderTransfer218S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer218Arithmetic : weightedUpper d2WiderTransfer218C0 d2Log167Lo d2Log167Hi ≤ d2WiderTransfer218Cap := by decide +kernel
theorem d2WiderTransfer218Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer218Lo:ℚ):ℝ) ((d2WiderTransfer218Hi:ℚ):ℝ), ((d2WiderTransfer218C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer218S0:ℚ):ℝ)| ≤ ((d2WiderTransfer218Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer218S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer218S0,d2WiderTransfer218Lo,d2WiderTransfer218Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer218C0 then |x-((d2WiderTransfer218S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer218S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer218S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer218S0,d2WiderTransfer218Lo,d2WiderTransfer218Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer218C0,d2Log167Q,d2WiderTransfer218S0,d2WiderTransfer218Lo,d2WiderTransfer218Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer218C0 d2WiderTransfer218S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have har : (((weightedUpper d2WiderTransfer218C0 d2Log167Lo d2Log167Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer218Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer218Arithmetic
  linarith
#print axioms d2WiderTransfer218Arithmetic
#print axioms d2WiderTransfer218Bound
def d2WiderTransfer219Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (2930765) 1 (-22))
def d2WiderTransfer219Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (25123841) 1 (-25))
def d2WiderTransfer219Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (4442930554062359260053) 1 (-78))
def d2WiderTransfer219C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 275 (-4))
def d2WiderTransfer219S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
def d2WiderTransfer219C1 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 55 (-3))
def d2WiderTransfer219S1 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer219Arithmetic : weightedUpper d2WiderTransfer219C0 d2Log167Lo d2Log167Hi + weightedUpper d2WiderTransfer219C1 d2Log7Lo d2Log7Hi ≤ d2WiderTransfer219Cap := by decide +kernel
theorem d2WiderTransfer219Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer219Lo:ℚ):ℝ) ((d2WiderTransfer219Hi:ℚ):ℝ), ((d2WiderTransfer219C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer219S0:ℚ):ℝ)| + ((d2WiderTransfer219C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer219S1:ℚ):ℝ)| ≤ ((d2WiderTransfer219Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer219S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer219S0,d2WiderTransfer219Lo,d2WiderTransfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer219C0 then |x-((d2WiderTransfer219S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer219S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer219S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer219S0,d2WiderTransfer219Lo,d2WiderTransfer219Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer219C0,d2Log167Q,d2WiderTransfer219S0,d2WiderTransfer219Lo,d2WiderTransfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer219C0 d2WiderTransfer219S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2WiderTransfer219S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer219S1,d2WiderTransfer219Lo,d2WiderTransfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer219C1 then |x-((d2WiderTransfer219S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer219S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer219S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer219S1,d2WiderTransfer219Lo,d2WiderTransfer219Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer219C1,d2Log7Q,d2WiderTransfer219S1,d2WiderTransfer219Lo,d2WiderTransfer219Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer219C1 d2WiderTransfer219S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2WiderTransfer219C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer219C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer219Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer219Arithmetic
  linarith
#print axioms d2WiderTransfer219Arithmetic
#print axioms d2WiderTransfer219Bound
def d2WiderTransfer220Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (2930765) 1 (-22))
def d2WiderTransfer220Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (25123841) 1 (-25))
def d2WiderTransfer220Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (8248696076668099390357) 1 (-78))
def d2WiderTransfer220C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 1 (-5))
def d2WiderTransfer220S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer220Arithmetic : weightedUpper d2WiderTransfer220C0 d2Log167Lo d2Log167Hi ≤ d2WiderTransfer220Cap := by decide +kernel
theorem d2WiderTransfer220Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer220Lo:ℚ):ℝ) ((d2WiderTransfer220Hi:ℚ):ℝ), ((d2WiderTransfer220C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer220S0:ℚ):ℝ)| ≤ ((d2WiderTransfer220Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer220S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer220S0,d2WiderTransfer220Lo,d2WiderTransfer220Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer220C0 then |x-((d2WiderTransfer220S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer220S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer220S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer220S0,d2WiderTransfer220Lo,d2WiderTransfer220Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer220C0,d2Log167Q,d2WiderTransfer220S0,d2WiderTransfer220Lo,d2WiderTransfer220Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer220C0 d2WiderTransfer220S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have har : (((weightedUpper d2WiderTransfer220C0 d2Log167Lo d2Log167Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer220Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer220Arithmetic
  linarith
#print axioms d2WiderTransfer220Arithmetic
#print axioms d2WiderTransfer220Bound
def d2WiderTransfer221Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (2930765) 1 (-22))
def d2WiderTransfer221Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (25123841) 1 (-25))
def d2WiderTransfer221Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (12339905407240976231317) 1 (-78))
def d2WiderTransfer221C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 11 (-5))
def d2WiderTransfer221S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
def d2WiderTransfer221C1 : ℚ := (d2LitsNearWiderTransfers027.q2 (-5) 11 (-4))
def d2WiderTransfer221S1 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer221Arithmetic : weightedUpper d2WiderTransfer221C0 d2Log167Lo d2Log167Hi + weightedUpper d2WiderTransfer221C1 d2Log7Lo d2Log7Hi ≤ d2WiderTransfer221Cap := by decide +kernel
theorem d2WiderTransfer221Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer221Lo:ℚ):ℝ) ((d2WiderTransfer221Hi:ℚ):ℝ), ((d2WiderTransfer221C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer221S0:ℚ):ℝ)| + ((d2WiderTransfer221C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer221S1:ℚ):ℝ)| ≤ ((d2WiderTransfer221Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer221S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer221S0,d2WiderTransfer221Lo,d2WiderTransfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer221C0 then |x-((d2WiderTransfer221S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer221S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer221S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer221S0,d2WiderTransfer221Lo,d2WiderTransfer221Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer221C0,d2Log167Q,d2WiderTransfer221S0,d2WiderTransfer221Lo,d2WiderTransfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer221C0 d2WiderTransfer221S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2WiderTransfer221S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer221S1,d2WiderTransfer221Lo,d2WiderTransfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer221C1 then |x-((d2WiderTransfer221S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer221S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer221S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer221S1,d2WiderTransfer221Lo,d2WiderTransfer221Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer221C1,d2Log7Q,d2WiderTransfer221S1,d2WiderTransfer221Lo,d2WiderTransfer221Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer221C1 d2WiderTransfer221S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2WiderTransfer221C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer221C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer221Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer221Arithmetic
  linarith
#print axioms d2WiderTransfer221Arithmetic
#print axioms d2WiderTransfer221Bound
def d2WiderTransfer222Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (25123841) 1 (-25))
def d2WiderTransfer222Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (13400781) 1 (-24))
def d2WiderTransfer222Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (24239257739226882297541) 1 (-80))
def d2WiderTransfer222C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 25 (-4))
def d2WiderTransfer222S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer222Arithmetic : weightedUpper d2WiderTransfer222C0 d2Log168Lo d2Log168Hi ≤ d2WiderTransfer222Cap := by decide +kernel
theorem d2WiderTransfer222Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer222Lo:ℚ):ℝ) ((d2WiderTransfer222Hi:ℚ):ℝ), ((d2WiderTransfer222C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer222S0:ℚ):ℝ)| ≤ ((d2WiderTransfer222Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer222S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer222S0,d2WiderTransfer222Lo,d2WiderTransfer222Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer222C0 then |x-((d2WiderTransfer222S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer222S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer222S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer222S0,d2WiderTransfer222Lo,d2WiderTransfer222Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer222C0,d2Log168Q,d2WiderTransfer222S0,d2WiderTransfer222Lo,d2WiderTransfer222Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer222C0 d2WiderTransfer222S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2WiderTransfer222C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer222Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer222Arithmetic
  linarith
#print axioms d2WiderTransfer222Arithmetic
#print axioms d2WiderTransfer222Bound
def d2WiderTransfer223Lo : ℚ := (d2LitsNearWiderTransfers027.q2 (25123841) 1 (-25))
def d2WiderTransfer223Hi : ℚ := (d2LitsNearWiderTransfers027.q2 (13400781) 1 (-24))
def d2WiderTransfer223Cap : ℚ := (d2LitsNearWiderTransfers027.q2 (25489557907862617640645) 1 (-80))
def d2WiderTransfer223C0 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 275 (-4))
def d2WiderTransfer223S0 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 1 (0))
def d2WiderTransfer223C1 : ℚ := (d2LitsNearWiderTransfers027.q2 (-1) 55 (-3))
def d2WiderTransfer223S1 : ℚ := (d2LitsNearWiderTransfers027.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer223Arithmetic : weightedUpper d2WiderTransfer223C0 d2Log168Lo d2Log168Hi + weightedUpper d2WiderTransfer223C1 d2Log6Lo d2Log6Hi ≤ d2WiderTransfer223Cap := by decide +kernel
theorem d2WiderTransfer223Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer223Lo:ℚ):ℝ) ((d2WiderTransfer223Hi:ℚ):ℝ), ((d2WiderTransfer223C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer223S0:ℚ):ℝ)| + ((d2WiderTransfer223C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer223S1:ℚ):ℝ)| ≤ ((d2WiderTransfer223Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer223S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer223S0,d2WiderTransfer223Lo,d2WiderTransfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer223C0 then |x-((d2WiderTransfer223S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer223S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer223S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer223S0,d2WiderTransfer223Lo,d2WiderTransfer223Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer223C0,d2Log168Q,d2WiderTransfer223S0,d2WiderTransfer223Lo,d2WiderTransfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer223C0 d2WiderTransfer223S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2WiderTransfer223S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer223S1,d2WiderTransfer223Lo,d2WiderTransfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer223C1 then |x-((d2WiderTransfer223S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer223S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer223S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer223S1,d2WiderTransfer223Lo,d2WiderTransfer223Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers027.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer223C1,d2Log6Q,d2WiderTransfer223S1,d2WiderTransfer223Lo,d2WiderTransfer223Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer223C1 d2WiderTransfer223S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2WiderTransfer223C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer223C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer223Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer223Arithmetic
  linarith
#print axioms d2WiderTransfer223Arithmetic
#print axioms d2WiderTransfer223Bound
end CatalanMeasure.GenD.Signed.Data.Cells
