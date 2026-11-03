module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers071
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers071
open D72.LogTransfer
def d2Transfer568Lo : ℚ := (d2LitsNearTransfers071.q2 (688200163) 1 (-30))
def d2Transfer568Hi : ℚ := (d2LitsNearTransfers071.q2 (172469471) 1 (-28))
def d2Transfer568Cap : ℚ := (d2LitsNearTransfers071.q2 (837258569895468822063) 1 (-78))
def d2Transfer568C0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 55 (-3))
def d2Transfer568S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
def d2Transfer568C1 : ℚ := (d2LitsNearTransfers071.q2 (-1) 55 (-3))
def d2Transfer568S1 : ℚ := (d2LitsNearTransfers071.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer568Arithmetic : weightedUpper d2Transfer568C0 d2Log159Lo d2Log159Hi + weightedUpper d2Transfer568C1 d2Log14Lo d2Log14Hi ≤ d2Transfer568Cap := by decide +kernel
theorem d2Transfer568Bound : ∀ x ∈ Set.Icc ((d2Transfer568Lo:ℚ):ℝ) ((d2Transfer568Hi:ℚ):ℝ), ((d2Transfer568C0:ℚ):ℝ)*Real.log |x-((d2Transfer568S0:ℚ):ℝ)| + ((d2Transfer568C1:ℚ):ℝ)*Real.log |x-((d2Transfer568S1:ℚ):ℝ)| ≤ ((d2Transfer568Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer568S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer568S0,d2Transfer568Lo,d2Transfer568Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer568C0 then |x-((d2Transfer568S0:ℚ):ℝ)| ≤ ((d2Log159Q:ℚ):ℝ) else ((d2Log159Q:ℚ):ℝ) ≤ |x-((d2Transfer568S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer568S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer568S0,d2Transfer568Lo,d2Transfer568Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer568C0,d2Log159Q,d2Transfer568S0,d2Transfer568Lo,d2Transfer568Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer568C0 d2Transfer568S0 d2Log159Q d2Log159Lo d2Log159Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log159Bounds
  have hn1 : x-((d2Transfer568S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer568S1,d2Transfer568Lo,d2Transfer568Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer568C1 then |x-((d2Transfer568S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2Transfer568S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer568S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer568S1,d2Transfer568Lo,d2Transfer568Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer568C1,d2Log14Q,d2Transfer568S1,d2Transfer568Lo,d2Transfer568Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer568C1 d2Transfer568S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2Transfer568C0 d2Log159Lo d2Log159Hi:ℚ):ℝ) + ((weightedUpper d2Transfer568C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2Transfer568Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer568Arithmetic
  linarith
#print axioms d2Transfer568Arithmetic
#print axioms d2Transfer568Bound
def d2Transfer569Lo : ℚ := (d2LitsNearTransfers071.q2 (688200163) 1 (-30))
def d2Transfer569Hi : ℚ := (d2LitsNearTransfers071.q2 (172469471) 1 (-28))
def d2Transfer569Cap : ℚ := (d2LitsNearTransfers071.q2 (4670207538377040555567) 1 (-78))
def d2Transfer569C0 : ℚ := (d2LitsNearTransfers071.q2 (23) 25 (-5))
def d2Transfer569S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer569Arithmetic : weightedUpper d2Transfer569C0 d2Log160Lo d2Log160Hi ≤ d2Transfer569Cap := by decide +kernel
theorem d2Transfer569Bound : ∀ x ∈ Set.Icc ((d2Transfer569Lo:ℚ):ℝ) ((d2Transfer569Hi:ℚ):ℝ), ((d2Transfer569C0:ℚ):ℝ)*Real.log |x-((d2Transfer569S0:ℚ):ℝ)| ≤ ((d2Transfer569Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer569S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer569S0,d2Transfer569Lo,d2Transfer569Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer569C0 then |x-((d2Transfer569S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2Transfer569S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer569S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer569S0,d2Transfer569Lo,d2Transfer569Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer569C0,d2Log160Q,d2Transfer569S0,d2Transfer569Lo,d2Transfer569Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer569C0 d2Transfer569S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have har : (((weightedUpper d2Transfer569C0 d2Log160Lo d2Log160Hi:ℚ):ℝ)) ≤ ((d2Transfer569Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer569Arithmetic
  linarith
#print axioms d2Transfer569Arithmetic
#print axioms d2Transfer569Bound
def d2Transfer570Lo : ℚ := (d2LitsNearTransfers071.q2 (688200163) 1 (-30))
def d2Transfer570Hi : ℚ := (d2LitsNearTransfers071.q2 (172469471) 1 (-28))
def d2Transfer570Cap : ℚ := (d2LitsNearTransfers071.q2 (8882954386193858129455) 1 (-78))
def d2Transfer570C0 : ℚ := (d2LitsNearTransfers071.q2 (3) 275 (-5))
def d2Transfer570S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
def d2Transfer570C1 : ℚ := (d2LitsNearTransfers071.q2 (-5) 11 (-4))
def d2Transfer570S1 : ℚ := (d2LitsNearTransfers071.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer570Arithmetic : weightedUpper d2Transfer570C0 d2Log160Lo d2Log160Hi + weightedUpper d2Transfer570C1 d2Log14Lo d2Log14Hi ≤ d2Transfer570Cap := by decide +kernel
theorem d2Transfer570Bound : ∀ x ∈ Set.Icc ((d2Transfer570Lo:ℚ):ℝ) ((d2Transfer570Hi:ℚ):ℝ), ((d2Transfer570C0:ℚ):ℝ)*Real.log |x-((d2Transfer570S0:ℚ):ℝ)| + ((d2Transfer570C1:ℚ):ℝ)*Real.log |x-((d2Transfer570S1:ℚ):ℝ)| ≤ ((d2Transfer570Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer570S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer570S0,d2Transfer570Lo,d2Transfer570Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer570C0 then |x-((d2Transfer570S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2Transfer570S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer570S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer570S0,d2Transfer570Lo,d2Transfer570Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer570C0,d2Log160Q,d2Transfer570S0,d2Transfer570Lo,d2Transfer570Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer570C0 d2Transfer570S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2Transfer570S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer570S1,d2Transfer570Lo,d2Transfer570Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer570C1 then |x-((d2Transfer570S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2Transfer570S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer570S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer570S1,d2Transfer570Lo,d2Transfer570Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer570C1,d2Log14Q,d2Transfer570S1,d2Transfer570Lo,d2Transfer570Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer570C1 d2Transfer570S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2Transfer570C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2Transfer570C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2Transfer570Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer570Arithmetic
  linarith
#print axioms d2Transfer570Arithmetic
#print axioms d2Transfer570Bound
def d2Transfer571Lo : ℚ := (d2LitsNearTransfers071.q2 (172469471) 1 (-28))
def d2Transfer571Hi : ℚ := (d2LitsNearTransfers071.q2 (346616663) 1 (-29))
def d2Transfer571Cap : ℚ := (d2LitsNearTransfers071.q2 (3651350408292595360187) 1 (-80))
def d2Transfer571C0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 55 (-3))
def d2Transfer571S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
def d2Transfer571C1 : ℚ := (d2LitsNearTransfers071.q2 (-1) 55 (-3))
def d2Transfer571S1 : ℚ := (d2LitsNearTransfers071.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer571Arithmetic : weightedUpper d2Transfer571C0 d2Log160Lo d2Log160Hi + weightedUpper d2Transfer571C1 d2Log13Lo d2Log13Hi ≤ d2Transfer571Cap := by decide +kernel
theorem d2Transfer571Bound : ∀ x ∈ Set.Icc ((d2Transfer571Lo:ℚ):ℝ) ((d2Transfer571Hi:ℚ):ℝ), ((d2Transfer571C0:ℚ):ℝ)*Real.log |x-((d2Transfer571S0:ℚ):ℝ)| + ((d2Transfer571C1:ℚ):ℝ)*Real.log |x-((d2Transfer571S1:ℚ):ℝ)| ≤ ((d2Transfer571Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer571S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer571S0,d2Transfer571Lo,d2Transfer571Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer571C0 then |x-((d2Transfer571S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2Transfer571S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer571S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer571S0,d2Transfer571Lo,d2Transfer571Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer571C0,d2Log160Q,d2Transfer571S0,d2Transfer571Lo,d2Transfer571Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer571C0 d2Transfer571S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2Transfer571S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer571S1,d2Transfer571Lo,d2Transfer571Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer571C1 then |x-((d2Transfer571S1:ℚ):ℝ)| ≤ ((d2Log13Q:ℚ):ℝ) else ((d2Log13Q:ℚ):ℝ) ≤ |x-((d2Transfer571S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer571S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer571S1,d2Transfer571Lo,d2Transfer571Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer571C1,d2Log13Q,d2Transfer571S1,d2Transfer571Lo,d2Transfer571Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer571C1 d2Transfer571S1 d2Log13Q d2Log13Lo d2Log13Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log13Bounds
  have har : (((weightedUpper d2Transfer571C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2Transfer571C1 d2Log13Lo d2Log13Hi:ℚ):ℝ)) ≤ ((d2Transfer571Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer571Arithmetic
  linarith
#print axioms d2Transfer571Arithmetic
#print axioms d2Transfer571Bound
def d2Transfer572Lo : ℚ := (d2LitsNearTransfers071.q2 (172469471) 1 (-28))
def d2Transfer572Hi : ℚ := (d2LitsNearTransfers071.q2 (346616663) 1 (-29))
def d2Transfer572Cap : ℚ := (d2LitsNearTransfers071.q2 (18983146282218882294203) 1 (-80))
def d2Transfer572C0 : ℚ := (d2LitsNearTransfers071.q2 (23) 25 (-5))
def d2Transfer572S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer572Arithmetic : weightedUpper d2Transfer572C0 d2Log161Lo d2Log161Hi ≤ d2Transfer572Cap := by decide +kernel
theorem d2Transfer572Bound : ∀ x ∈ Set.Icc ((d2Transfer572Lo:ℚ):ℝ) ((d2Transfer572Hi:ℚ):ℝ), ((d2Transfer572C0:ℚ):ℝ)*Real.log |x-((d2Transfer572S0:ℚ):ℝ)| ≤ ((d2Transfer572Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer572S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer572S0,d2Transfer572Lo,d2Transfer572Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer572C0 then |x-((d2Transfer572S0:ℚ):ℝ)| ≤ ((d2Log161Q:ℚ):ℝ) else ((d2Log161Q:ℚ):ℝ) ≤ |x-((d2Transfer572S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer572S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer572S0,d2Transfer572Lo,d2Transfer572Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer572C0,d2Log161Q,d2Transfer572S0,d2Transfer572Lo,d2Transfer572Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer572C0 d2Transfer572S0 d2Log161Q d2Log161Lo d2Log161Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log161Bounds
  have har : (((weightedUpper d2Transfer572C0 d2Log161Lo d2Log161Hi:ℚ):ℝ)) ≤ ((d2Transfer572Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer572Arithmetic
  linarith
#print axioms d2Transfer572Arithmetic
#print axioms d2Transfer572Bound
def d2Transfer573Lo : ℚ := (d2LitsNearTransfers071.q2 (172469471) 1 (-28))
def d2Transfer573Hi : ℚ := (d2LitsNearTransfers071.q2 (346616663) 1 (-29))
def d2Transfer573Cap : ℚ := (d2LitsNearTransfers071.q2 (35834133673486152589755) 1 (-80))
def d2Transfer573C0 : ℚ := (d2LitsNearTransfers071.q2 (3) 275 (-5))
def d2Transfer573S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
def d2Transfer573C1 : ℚ := (d2LitsNearTransfers071.q2 (-5) 11 (-4))
def d2Transfer573S1 : ℚ := (d2LitsNearTransfers071.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer573Arithmetic : weightedUpper d2Transfer573C0 d2Log161Lo d2Log161Hi + weightedUpper d2Transfer573C1 d2Log13Lo d2Log13Hi ≤ d2Transfer573Cap := by decide +kernel
theorem d2Transfer573Bound : ∀ x ∈ Set.Icc ((d2Transfer573Lo:ℚ):ℝ) ((d2Transfer573Hi:ℚ):ℝ), ((d2Transfer573C0:ℚ):ℝ)*Real.log |x-((d2Transfer573S0:ℚ):ℝ)| + ((d2Transfer573C1:ℚ):ℝ)*Real.log |x-((d2Transfer573S1:ℚ):ℝ)| ≤ ((d2Transfer573Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer573S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer573S0,d2Transfer573Lo,d2Transfer573Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer573C0 then |x-((d2Transfer573S0:ℚ):ℝ)| ≤ ((d2Log161Q:ℚ):ℝ) else ((d2Log161Q:ℚ):ℝ) ≤ |x-((d2Transfer573S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer573S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer573S0,d2Transfer573Lo,d2Transfer573Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer573C0,d2Log161Q,d2Transfer573S0,d2Transfer573Lo,d2Transfer573Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer573C0 d2Transfer573S0 d2Log161Q d2Log161Lo d2Log161Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log161Bounds
  have hn1 : x-((d2Transfer573S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer573S1,d2Transfer573Lo,d2Transfer573Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer573C1 then |x-((d2Transfer573S1:ℚ):ℝ)| ≤ ((d2Log13Q:ℚ):ℝ) else ((d2Log13Q:ℚ):ℝ) ≤ |x-((d2Transfer573S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer573S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer573S1,d2Transfer573Lo,d2Transfer573Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer573C1,d2Log13Q,d2Transfer573S1,d2Transfer573Lo,d2Transfer573Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer573C1 d2Transfer573S1 d2Log13Q d2Log13Lo d2Log13Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log13Bounds
  have har : (((weightedUpper d2Transfer573C0 d2Log161Lo d2Log161Hi:ℚ):ℝ) + ((weightedUpper d2Transfer573C1 d2Log13Lo d2Log13Hi:ℚ):ℝ)) ≤ ((d2Transfer573Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer573Arithmetic
  linarith
#print axioms d2Transfer573Arithmetic
#print axioms d2Transfer573Bound
def d2Transfer574Lo : ℚ := (d2LitsNearTransfers071.q2 (346616663) 1 (-29))
def d2Transfer574Hi : ℚ := (d2LitsNearTransfers071.q2 (21768399) 1 (-25))
def d2Transfer574Cap : ℚ := (d2LitsNearTransfers071.q2 (3956335870851972903335) 1 (-80))
def d2Transfer574C0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 55 (-3))
def d2Transfer574S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
def d2Transfer574C1 : ℚ := (d2LitsNearTransfers071.q2 (-1) 55 (-3))
def d2Transfer574S1 : ℚ := (d2LitsNearTransfers071.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer574Arithmetic : weightedUpper d2Transfer574C0 d2Log161Lo d2Log161Hi + weightedUpper d2Transfer574C1 d2Log12Lo d2Log12Hi ≤ d2Transfer574Cap := by decide +kernel
theorem d2Transfer574Bound : ∀ x ∈ Set.Icc ((d2Transfer574Lo:ℚ):ℝ) ((d2Transfer574Hi:ℚ):ℝ), ((d2Transfer574C0:ℚ):ℝ)*Real.log |x-((d2Transfer574S0:ℚ):ℝ)| + ((d2Transfer574C1:ℚ):ℝ)*Real.log |x-((d2Transfer574S1:ℚ):ℝ)| ≤ ((d2Transfer574Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer574S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer574S0,d2Transfer574Lo,d2Transfer574Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer574C0 then |x-((d2Transfer574S0:ℚ):ℝ)| ≤ ((d2Log161Q:ℚ):ℝ) else ((d2Log161Q:ℚ):ℝ) ≤ |x-((d2Transfer574S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer574S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer574S0,d2Transfer574Lo,d2Transfer574Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer574C0,d2Log161Q,d2Transfer574S0,d2Transfer574Lo,d2Transfer574Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer574C0 d2Transfer574S0 d2Log161Q d2Log161Lo d2Log161Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log161Bounds
  have hn1 : x-((d2Transfer574S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer574S1,d2Transfer574Lo,d2Transfer574Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer574C1 then |x-((d2Transfer574S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2Transfer574S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer574S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer574S1,d2Transfer574Lo,d2Transfer574Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer574C1,d2Log12Q,d2Transfer574S1,d2Transfer574Lo,d2Transfer574Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer574C1 d2Transfer574S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2Transfer574C0 d2Log161Lo d2Log161Hi:ℚ):ℝ) + ((weightedUpper d2Transfer574C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2Transfer574Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer574Arithmetic
  linarith
#print axioms d2Transfer574Arithmetic
#print axioms d2Transfer574Bound
def d2Transfer575Lo : ℚ := (d2LitsNearTransfers071.q2 (346616663) 1 (-29))
def d2Transfer575Hi : ℚ := (d2LitsNearTransfers071.q2 (21768399) 1 (-25))
def d2Transfer575Cap : ℚ := (d2LitsNearTransfers071.q2 (19288131744778259837351) 1 (-80))
def d2Transfer575C0 : ℚ := (d2LitsNearTransfers071.q2 (23) 25 (-5))
def d2Transfer575S0 : ℚ := (d2LitsNearTransfers071.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer575Arithmetic : weightedUpper d2Transfer575C0 d2Log162Lo d2Log162Hi ≤ d2Transfer575Cap := by decide +kernel
theorem d2Transfer575Bound : ∀ x ∈ Set.Icc ((d2Transfer575Lo:ℚ):ℝ) ((d2Transfer575Hi:ℚ):ℝ), ((d2Transfer575C0:ℚ):ℝ)*Real.log |x-((d2Transfer575S0:ℚ):ℝ)| ≤ ((d2Transfer575Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer575S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer575S0,d2Transfer575Lo,d2Transfer575Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer575C0 then |x-((d2Transfer575S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer575S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer575S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer575S0,d2Transfer575Lo,d2Transfer575Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers071.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer575C0,d2Log162Q,d2Transfer575S0,d2Transfer575Lo,d2Transfer575Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer575C0 d2Transfer575S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2Transfer575C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2Transfer575Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer575Arithmetic
  linarith
#print axioms d2Transfer575Arithmetic
#print axioms d2Transfer575Bound
end CatalanMeasure.GenD.Signed.Data.Cells
