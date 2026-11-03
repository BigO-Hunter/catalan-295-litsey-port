module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers039
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers039
open D72.LogTransfer
def d2Transfer312Lo : ℚ := (d2LitsNearTransfers039.q2 (1351234511) 1 (-31))
def d2Transfer312Hi : ℚ := (d2LitsNearTransfers039.q2 (169114029) 1 (-28))
def d2Transfer312Cap : ℚ := (d2LitsNearTransfers039.q2 (9730068645975812010747) 1 (-79))
def d2Transfer312C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 1 (-5))
def d2Transfer312S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer312Arithmetic : weightedUpper d2Transfer312C0 d2Log147Lo d2Log147Hi ≤ d2Transfer312Cap := by decide +kernel
theorem d2Transfer312Bound : ∀ x ∈ Set.Icc ((d2Transfer312Lo:ℚ):ℝ) ((d2Transfer312Hi:ℚ):ℝ), ((d2Transfer312C0:ℚ):ℝ)*Real.log |x-((d2Transfer312S0:ℚ):ℝ)| ≤ ((d2Transfer312Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer312S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer312S0,d2Transfer312Lo,d2Transfer312Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer312C0 then |x-((d2Transfer312S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2Transfer312S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer312S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer312S0,d2Transfer312Lo,d2Transfer312Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer312C0,d2Log147Q,d2Transfer312S0,d2Transfer312Lo,d2Transfer312Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer312C0 d2Transfer312S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have har : (((weightedUpper d2Transfer312C0 d2Log147Lo d2Log147Hi:ℚ):ℝ)) ≤ ((d2Transfer312Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer312Arithmetic
  linarith
#print axioms d2Transfer312Arithmetic
#print axioms d2Transfer312Bound
def d2Transfer313Lo : ℚ := (d2LitsNearTransfers039.q2 (1351234511) 1 (-31))
def d2Transfer313Hi : ℚ := (d2LitsNearTransfers039.q2 (169114029) 1 (-28))
def d2Transfer313Cap : ℚ := (d2LitsNearTransfers039.q2 (17912487307121565692667) 1 (-79))
def d2Transfer313C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 11 (-5))
def d2Transfer313S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
def d2Transfer313C1 : ℚ := (d2LitsNearTransfers039.q2 (-5) 11 (-4))
def d2Transfer313S1 : ℚ := (d2LitsNearTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer313Arithmetic : weightedUpper d2Transfer313C0 d2Log147Lo d2Log147Hi + weightedUpper d2Transfer313C1 d2Log27Lo d2Log27Hi ≤ d2Transfer313Cap := by decide +kernel
theorem d2Transfer313Bound : ∀ x ∈ Set.Icc ((d2Transfer313Lo:ℚ):ℝ) ((d2Transfer313Hi:ℚ):ℝ), ((d2Transfer313C0:ℚ):ℝ)*Real.log |x-((d2Transfer313S0:ℚ):ℝ)| + ((d2Transfer313C1:ℚ):ℝ)*Real.log |x-((d2Transfer313S1:ℚ):ℝ)| ≤ ((d2Transfer313Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer313S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer313S0,d2Transfer313Lo,d2Transfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer313C0 then |x-((d2Transfer313S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2Transfer313S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer313S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer313S0,d2Transfer313Lo,d2Transfer313Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer313C0,d2Log147Q,d2Transfer313S0,d2Transfer313Lo,d2Transfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer313C0 d2Transfer313S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2Transfer313S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer313S1,d2Transfer313Lo,d2Transfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer313C1 then |x-((d2Transfer313S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2Transfer313S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer313S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer313S1,d2Transfer313Lo,d2Transfer313Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer313C1,d2Log27Q,d2Transfer313S1,d2Transfer313Lo,d2Transfer313Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer313C1 d2Transfer313S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2Transfer313C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2Transfer313C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2Transfer313Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer313Arithmetic
  linarith
#print axioms d2Transfer313Arithmetic
#print axioms d2Transfer313Bound
def d2Transfer314Lo : ℚ := (d2LitsNearTransfers039.q2 (169114029) 1 (-28))
def d2Transfer314Hi : ℚ := (d2LitsNearTransfers039.q2 (678133837) 1 (-30))
def d2Transfer314Cap : ℚ := (d2LitsNearTransfers039.q2 (1567704054461560565645) 1 (-79))
def d2Transfer314C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 25 (-4))
def d2Transfer314S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer314Arithmetic : weightedUpper d2Transfer314C0 d2Log149Lo d2Log149Hi ≤ d2Transfer314Cap := by decide +kernel
theorem d2Transfer314Bound : ∀ x ∈ Set.Icc ((d2Transfer314Lo:ℚ):ℝ) ((d2Transfer314Hi:ℚ):ℝ), ((d2Transfer314C0:ℚ):ℝ)*Real.log |x-((d2Transfer314S0:ℚ):ℝ)| ≤ ((d2Transfer314Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer314S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer314S0,d2Transfer314Lo,d2Transfer314Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer314C0 then |x-((d2Transfer314S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2Transfer314S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer314S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer314S0,d2Transfer314Lo,d2Transfer314Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer314C0,d2Log149Q,d2Transfer314S0,d2Transfer314Lo,d2Transfer314Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer314C0 d2Transfer314S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have har : (((weightedUpper d2Transfer314C0 d2Log149Lo d2Log149Hi:ℚ):ℝ)) ≤ ((d2Transfer314Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer314Arithmetic
  linarith
#print axioms d2Transfer314Arithmetic
#print axioms d2Transfer314Bound
def d2Transfer315Lo : ℚ := (d2LitsNearTransfers039.q2 (169114029) 1 (-28))
def d2Transfer315Hi : ℚ := (d2LitsNearTransfers039.q2 (678133837) 1 (-30))
def d2Transfer315Cap : ℚ := (d2LitsNearTransfers039.q2 (2192854138779428237197) 1 (-79))
def d2Transfer315C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 275 (-4))
def d2Transfer315S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
def d2Transfer315C1 : ℚ := (d2LitsNearTransfers039.q2 (-1) 55 (-3))
def d2Transfer315S1 : ℚ := (d2LitsNearTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer315Arithmetic : weightedUpper d2Transfer315C0 d2Log149Lo d2Log149Hi + weightedUpper d2Transfer315C1 d2Log25Lo d2Log25Hi ≤ d2Transfer315Cap := by decide +kernel
theorem d2Transfer315Bound : ∀ x ∈ Set.Icc ((d2Transfer315Lo:ℚ):ℝ) ((d2Transfer315Hi:ℚ):ℝ), ((d2Transfer315C0:ℚ):ℝ)*Real.log |x-((d2Transfer315S0:ℚ):ℝ)| + ((d2Transfer315C1:ℚ):ℝ)*Real.log |x-((d2Transfer315S1:ℚ):ℝ)| ≤ ((d2Transfer315Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer315S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer315S0,d2Transfer315Lo,d2Transfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer315C0 then |x-((d2Transfer315S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2Transfer315S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer315S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer315S0,d2Transfer315Lo,d2Transfer315Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer315C0,d2Log149Q,d2Transfer315S0,d2Transfer315Lo,d2Transfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer315C0 d2Transfer315S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2Transfer315S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer315S1,d2Transfer315Lo,d2Transfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer315C1 then |x-((d2Transfer315S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2Transfer315S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer315S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer315S1,d2Transfer315Lo,d2Transfer315Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer315C1,d2Log25Q,d2Transfer315S1,d2Transfer315Lo,d2Transfer315Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer315C1 d2Transfer315S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2Transfer315C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2Transfer315C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2Transfer315Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer315Arithmetic
  linarith
#print axioms d2Transfer315Arithmetic
#print axioms d2Transfer315Bound
def d2Transfer316Lo : ℚ := (d2LitsNearTransfers039.q2 (169114029) 1 (-28))
def d2Transfer316Hi : ℚ := (d2LitsNearTransfers039.q2 (678133837) 1 (-30))
def d2Transfer316Cap : ℚ := (d2LitsNearTransfers039.q2 (9804385183990908497805) 1 (-79))
def d2Transfer316C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 1 (-5))
def d2Transfer316S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer316Arithmetic : weightedUpper d2Transfer316C0 d2Log149Lo d2Log149Hi ≤ d2Transfer316Cap := by decide +kernel
theorem d2Transfer316Bound : ∀ x ∈ Set.Icc ((d2Transfer316Lo:ℚ):ℝ) ((d2Transfer316Hi:ℚ):ℝ), ((d2Transfer316C0:ℚ):ℝ)*Real.log |x-((d2Transfer316S0:ℚ):ℝ)| ≤ ((d2Transfer316Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer316S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer316S0,d2Transfer316Lo,d2Transfer316Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer316C0 then |x-((d2Transfer316S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2Transfer316S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer316S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer316S0,d2Transfer316Lo,d2Transfer316Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer316C0,d2Log149Q,d2Transfer316S0,d2Transfer316Lo,d2Transfer316Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer316C0 d2Transfer316S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have har : (((weightedUpper d2Transfer316C0 d2Log149Lo d2Log149Hi:ℚ):ℝ)) ≤ ((d2Transfer316Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer316Arithmetic
  linarith
#print axioms d2Transfer316Arithmetic
#print axioms d2Transfer316Bound
def d2Transfer317Lo : ℚ := (d2LitsNearTransfers039.q2 (169114029) 1 (-28))
def d2Transfer317Hi : ℚ := (d2LitsNearTransfers039.q2 (678133837) 1 (-30))
def d2Transfer317Cap : ℚ := (d2LitsNearTransfers039.q2 (17986803845136662179725) 1 (-79))
def d2Transfer317C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 11 (-5))
def d2Transfer317S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
def d2Transfer317C1 : ℚ := (d2LitsNearTransfers039.q2 (-5) 11 (-4))
def d2Transfer317S1 : ℚ := (d2LitsNearTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer317Arithmetic : weightedUpper d2Transfer317C0 d2Log149Lo d2Log149Hi + weightedUpper d2Transfer317C1 d2Log25Lo d2Log25Hi ≤ d2Transfer317Cap := by decide +kernel
theorem d2Transfer317Bound : ∀ x ∈ Set.Icc ((d2Transfer317Lo:ℚ):ℝ) ((d2Transfer317Hi:ℚ):ℝ), ((d2Transfer317C0:ℚ):ℝ)*Real.log |x-((d2Transfer317S0:ℚ):ℝ)| + ((d2Transfer317C1:ℚ):ℝ)*Real.log |x-((d2Transfer317S1:ℚ):ℝ)| ≤ ((d2Transfer317Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer317S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer317S0,d2Transfer317Lo,d2Transfer317Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer317C0 then |x-((d2Transfer317S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2Transfer317S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer317S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer317S0,d2Transfer317Lo,d2Transfer317Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer317C0,d2Log149Q,d2Transfer317S0,d2Transfer317Lo,d2Transfer317Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer317C0 d2Transfer317S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2Transfer317S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer317S1,d2Transfer317Lo,d2Transfer317Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer317C1 then |x-((d2Transfer317S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2Transfer317S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer317S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer317S1,d2Transfer317Lo,d2Transfer317Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer317C1,d2Log25Q,d2Transfer317S1,d2Transfer317Lo,d2Transfer317Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer317C1 d2Transfer317S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2Transfer317C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2Transfer317C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2Transfer317Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer317Arithmetic
  linarith
#print axioms d2Transfer317Arithmetic
#print axioms d2Transfer317Bound
def d2Transfer318Lo : ℚ := (d2LitsNearTransfers039.q2 (678133837) 1 (-30))
def d2Transfer318Hi : ℚ := (d2LitsNearTransfers039.q2 (339905779) 1 (-29))
def d2Transfer318Cap : ℚ := (d2LitsNearTransfers039.q2 (3284655724680182058789) 1 (-80))
def d2Transfer318C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 25 (-4))
def d2Transfer318S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer318Arithmetic : weightedUpper d2Transfer318C0 d2Log151Lo d2Log151Hi ≤ d2Transfer318Cap := by decide +kernel
theorem d2Transfer318Bound : ∀ x ∈ Set.Icc ((d2Transfer318Lo:ℚ):ℝ) ((d2Transfer318Hi:ℚ):ℝ), ((d2Transfer318C0:ℚ):ℝ)*Real.log |x-((d2Transfer318S0:ℚ):ℝ)| ≤ ((d2Transfer318Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer318S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer318S0,d2Transfer318Lo,d2Transfer318Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer318C0 then |x-((d2Transfer318S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2Transfer318S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer318S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer318S0,d2Transfer318Lo,d2Transfer318Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer318C0,d2Log151Q,d2Transfer318S0,d2Transfer318Lo,d2Transfer318Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer318C0 d2Transfer318S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have har : (((weightedUpper d2Transfer318C0 d2Log151Lo d2Log151Hi:ℚ):ℝ)) ≤ ((d2Transfer318Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer318Arithmetic
  linarith
#print axioms d2Transfer318Arithmetic
#print axioms d2Transfer318Bound
def d2Transfer319Lo : ℚ := (d2LitsNearTransfers039.q2 (678133837) 1 (-30))
def d2Transfer319Hi : ℚ := (d2LitsNearTransfers039.q2 (339905779) 1 (-29))
def d2Transfer319Cap : ℚ := (d2LitsNearTransfers039.q2 (4534955893315917401893) 1 (-80))
def d2Transfer319C0 : ℚ := (d2LitsNearTransfers039.q2 (1) 275 (-4))
def d2Transfer319S0 : ℚ := (d2LitsNearTransfers039.q2 (-1) 1 (0))
def d2Transfer319C1 : ℚ := (d2LitsNearTransfers039.q2 (-1) 55 (-3))
def d2Transfer319S1 : ℚ := (d2LitsNearTransfers039.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer319Arithmetic : weightedUpper d2Transfer319C0 d2Log151Lo d2Log151Hi + weightedUpper d2Transfer319C1 d2Log23Lo d2Log23Hi ≤ d2Transfer319Cap := by decide +kernel
theorem d2Transfer319Bound : ∀ x ∈ Set.Icc ((d2Transfer319Lo:ℚ):ℝ) ((d2Transfer319Hi:ℚ):ℝ), ((d2Transfer319C0:ℚ):ℝ)*Real.log |x-((d2Transfer319S0:ℚ):ℝ)| + ((d2Transfer319C1:ℚ):ℝ)*Real.log |x-((d2Transfer319S1:ℚ):ℝ)| ≤ ((d2Transfer319Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer319S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer319S0,d2Transfer319Lo,d2Transfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer319C0 then |x-((d2Transfer319S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2Transfer319S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer319S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer319S0,d2Transfer319Lo,d2Transfer319Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer319C0,d2Log151Q,d2Transfer319S0,d2Transfer319Lo,d2Transfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer319C0 d2Transfer319S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2Transfer319S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer319S1,d2Transfer319Lo,d2Transfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer319C1 then |x-((d2Transfer319S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2Transfer319S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer319S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer319S1,d2Transfer319Lo,d2Transfer319Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers039.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer319C1,d2Log23Q,d2Transfer319S1,d2Transfer319Lo,d2Transfer319Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer319C1 d2Transfer319S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2Transfer319C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2Transfer319C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2Transfer319Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer319Arithmetic
  linarith
#print axioms d2Transfer319Arithmetic
#print axioms d2Transfer319Bound
end CatalanMeasure.GenD.Signed.Data.Cells
