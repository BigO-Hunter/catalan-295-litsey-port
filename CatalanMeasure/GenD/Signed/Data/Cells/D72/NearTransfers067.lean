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
namespace d2LitsNearTransfers067
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers067
open D72.LogTransfer
def d2Transfer536Lo : ℚ := (d2LitsNearTransfers067.q2 (1354589953) 1 (-31))
def d2Transfer536Hi : ℚ := (d2LitsNearTransfers067.q2 (678133837) 1 (-30))
def d2Transfer536Cap : ℚ := (d2LitsNearTransfers067.q2 (8821542085301179587119) 1 (-79))
def d2Transfer536C0 : ℚ := (d2LitsNearTransfers067.q2 (23) 25 (-5))
def d2Transfer536S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer536Arithmetic : weightedUpper d2Transfer536C0 d2Log149Lo d2Log149Hi ≤ d2Transfer536Cap := by decide +kernel
theorem d2Transfer536Bound : ∀ x ∈ Set.Icc ((d2Transfer536Lo:ℚ):ℝ) ((d2Transfer536Hi:ℚ):ℝ), ((d2Transfer536C0:ℚ):ℝ)*Real.log |x-((d2Transfer536S0:ℚ):ℝ)| ≤ ((d2Transfer536Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer536S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer536S0,d2Transfer536Lo,d2Transfer536Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer536C0 then |x-((d2Transfer536S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2Transfer536S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer536S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer536S0,d2Transfer536Lo,d2Transfer536Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer536C0,d2Log149Q,d2Transfer536S0,d2Transfer536Lo,d2Transfer536Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer536C0 d2Transfer536S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have har : (((weightedUpper d2Transfer536C0 d2Log149Lo d2Log149Hi:ℚ):ℝ)) ≤ ((d2Transfer536Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer536Arithmetic
  linarith
#print axioms d2Transfer536Arithmetic
#print axioms d2Transfer536Bound
def d2Transfer537Lo : ℚ := (d2LitsNearTransfers067.q2 (1354589953) 1 (-31))
def d2Transfer537Hi : ℚ := (d2LitsNearTransfers067.q2 (678133837) 1 (-30))
def d2Transfer537Cap : ℚ := (d2LitsNearTransfers067.q2 (17247035780934814734895) 1 (-79))
def d2Transfer537C0 : ℚ := (d2LitsNearTransfers067.q2 (3) 275 (-5))
def d2Transfer537S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
def d2Transfer537C1 : ℚ := (d2LitsNearTransfers067.q2 (-5) 11 (-4))
def d2Transfer537S1 : ℚ := (d2LitsNearTransfers067.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer537Arithmetic : weightedUpper d2Transfer537C0 d2Log149Lo d2Log149Hi + weightedUpper d2Transfer537C1 d2Log25Lo d2Log25Hi ≤ d2Transfer537Cap := by decide +kernel
theorem d2Transfer537Bound : ∀ x ∈ Set.Icc ((d2Transfer537Lo:ℚ):ℝ) ((d2Transfer537Hi:ℚ):ℝ), ((d2Transfer537C0:ℚ):ℝ)*Real.log |x-((d2Transfer537S0:ℚ):ℝ)| + ((d2Transfer537C1:ℚ):ℝ)*Real.log |x-((d2Transfer537S1:ℚ):ℝ)| ≤ ((d2Transfer537Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer537S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer537S0,d2Transfer537Lo,d2Transfer537Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer537C0 then |x-((d2Transfer537S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2Transfer537S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer537S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer537S0,d2Transfer537Lo,d2Transfer537Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer537C0,d2Log149Q,d2Transfer537S0,d2Transfer537Lo,d2Transfer537Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer537C0 d2Transfer537S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2Transfer537S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer537S1,d2Transfer537Lo,d2Transfer537Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer537C1 then |x-((d2Transfer537S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2Transfer537S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer537S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer537S1,d2Transfer537Lo,d2Transfer537Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer537C1,d2Log25Q,d2Transfer537S1,d2Transfer537Lo,d2Transfer537Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer537C1 d2Transfer537S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2Transfer537C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2Transfer537C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2Transfer537Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer537Arithmetic
  linarith
#print axioms d2Transfer537Arithmetic
#print axioms d2Transfer537Bound
def d2Transfer538Lo : ℚ := (d2LitsNearTransfers067.q2 (678133837) 1 (-30))
def d2Transfer538Hi : ℚ := (d2LitsNearTransfers067.q2 (1357945395) 1 (-31))
def d2Transfer538Cap : ℚ := (d2LitsNearTransfers067.q2 (1192194056602251574363) 1 (-79))
def d2Transfer538C0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 55 (-3))
def d2Transfer538S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
def d2Transfer538C1 : ℚ := (d2LitsNearTransfers067.q2 (-1) 55 (-3))
def d2Transfer538S1 : ℚ := (d2LitsNearTransfers067.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer538Arithmetic : weightedUpper d2Transfer538C0 d2Log149Lo d2Log149Hi + weightedUpper d2Transfer538C1 d2Log24Lo d2Log24Hi ≤ d2Transfer538Cap := by decide +kernel
theorem d2Transfer538Bound : ∀ x ∈ Set.Icc ((d2Transfer538Lo:ℚ):ℝ) ((d2Transfer538Hi:ℚ):ℝ), ((d2Transfer538C0:ℚ):ℝ)*Real.log |x-((d2Transfer538S0:ℚ):ℝ)| + ((d2Transfer538C1:ℚ):ℝ)*Real.log |x-((d2Transfer538S1:ℚ):ℝ)| ≤ ((d2Transfer538Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer538S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer538S0,d2Transfer538Lo,d2Transfer538Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer538C0 then |x-((d2Transfer538S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2Transfer538S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer538S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer538S0,d2Transfer538Lo,d2Transfer538Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer538C0,d2Log149Q,d2Transfer538S0,d2Transfer538Lo,d2Transfer538Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer538C0 d2Transfer538S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2Transfer538S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer538S1,d2Transfer538Lo,d2Transfer538Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer538C1 then |x-((d2Transfer538S1:ℚ):ℝ)| ≤ ((d2Log24Q:ℚ):ℝ) else ((d2Log24Q:ℚ):ℝ) ≤ |x-((d2Transfer538S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer538S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer538S1,d2Transfer538Lo,d2Transfer538Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer538C1,d2Log24Q,d2Transfer538S1,d2Transfer538Lo,d2Transfer538Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer538C1 d2Transfer538S1 d2Log24Q d2Log24Lo d2Log24Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log24Bounds
  have har : (((weightedUpper d2Transfer538C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2Transfer538C1 d2Log24Lo d2Log24Hi:ℚ):ℝ)) ≤ ((d2Transfer538Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer538Arithmetic
  linarith
#print axioms d2Transfer538Arithmetic
#print axioms d2Transfer538Bound
def d2Transfer539Lo : ℚ := (d2LitsNearTransfers067.q2 (678133837) 1 (-30))
def d2Transfer539Hi : ℚ := (d2LitsNearTransfers067.q2 (1357945395) 1 (-31))
def d2Transfer539Cap : ℚ := (d2LitsNearTransfers067.q2 (8858091993565395041371) 1 (-79))
def d2Transfer539C0 : ℚ := (d2LitsNearTransfers067.q2 (23) 25 (-5))
def d2Transfer539S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer539Arithmetic : weightedUpper d2Transfer539C0 d2Log150Lo d2Log150Hi ≤ d2Transfer539Cap := by decide +kernel
theorem d2Transfer539Bound : ∀ x ∈ Set.Icc ((d2Transfer539Lo:ℚ):ℝ) ((d2Transfer539Hi:ℚ):ℝ), ((d2Transfer539C0:ℚ):ℝ)*Real.log |x-((d2Transfer539S0:ℚ):ℝ)| ≤ ((d2Transfer539Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer539S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer539S0,d2Transfer539Lo,d2Transfer539Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer539C0 then |x-((d2Transfer539S0:ℚ):ℝ)| ≤ ((d2Log150Q:ℚ):ℝ) else ((d2Log150Q:ℚ):ℝ) ≤ |x-((d2Transfer539S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer539S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer539S0,d2Transfer539Lo,d2Transfer539Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer539C0,d2Log150Q,d2Transfer539S0,d2Transfer539Lo,d2Transfer539Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer539C0 d2Transfer539S0 d2Log150Q d2Log150Lo d2Log150Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log150Bounds
  have har : (((weightedUpper d2Transfer539C0 d2Log150Lo d2Log150Hi:ℚ):ℝ)) ≤ ((d2Transfer539Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer539Arithmetic
  linarith
#print axioms d2Transfer539Arithmetic
#print axioms d2Transfer539Bound
def d2Transfer540Lo : ℚ := (d2LitsNearTransfers067.q2 (678133837) 1 (-30))
def d2Transfer540Hi : ℚ := (d2LitsNearTransfers067.q2 (1357945395) 1 (-31))
def d2Transfer540Cap : ℚ := (d2LitsNearTransfers067.q2 (17283585689199030189147) 1 (-79))
def d2Transfer540C0 : ℚ := (d2LitsNearTransfers067.q2 (3) 275 (-5))
def d2Transfer540S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
def d2Transfer540C1 : ℚ := (d2LitsNearTransfers067.q2 (-5) 11 (-4))
def d2Transfer540S1 : ℚ := (d2LitsNearTransfers067.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer540Arithmetic : weightedUpper d2Transfer540C0 d2Log150Lo d2Log150Hi + weightedUpper d2Transfer540C1 d2Log24Lo d2Log24Hi ≤ d2Transfer540Cap := by decide +kernel
theorem d2Transfer540Bound : ∀ x ∈ Set.Icc ((d2Transfer540Lo:ℚ):ℝ) ((d2Transfer540Hi:ℚ):ℝ), ((d2Transfer540C0:ℚ):ℝ)*Real.log |x-((d2Transfer540S0:ℚ):ℝ)| + ((d2Transfer540C1:ℚ):ℝ)*Real.log |x-((d2Transfer540S1:ℚ):ℝ)| ≤ ((d2Transfer540Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer540S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer540S0,d2Transfer540Lo,d2Transfer540Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer540C0 then |x-((d2Transfer540S0:ℚ):ℝ)| ≤ ((d2Log150Q:ℚ):ℝ) else ((d2Log150Q:ℚ):ℝ) ≤ |x-((d2Transfer540S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer540S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer540S0,d2Transfer540Lo,d2Transfer540Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer540C0,d2Log150Q,d2Transfer540S0,d2Transfer540Lo,d2Transfer540Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer540C0 d2Transfer540S0 d2Log150Q d2Log150Lo d2Log150Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log150Bounds
  have hn1 : x-((d2Transfer540S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer540S1,d2Transfer540Lo,d2Transfer540Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer540C1 then |x-((d2Transfer540S1:ℚ):ℝ)| ≤ ((d2Log24Q:ℚ):ℝ) else ((d2Log24Q:ℚ):ℝ) ≤ |x-((d2Transfer540S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer540S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer540S1,d2Transfer540Lo,d2Transfer540Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer540C1,d2Log24Q,d2Transfer540S1,d2Transfer540Lo,d2Transfer540Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer540C1 d2Transfer540S1 d2Log24Q d2Log24Lo d2Log24Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log24Bounds
  have har : (((weightedUpper d2Transfer540C0 d2Log150Lo d2Log150Hi:ℚ):ℝ) + ((weightedUpper d2Transfer540C1 d2Log24Lo d2Log24Hi:ℚ):ℝ)) ≤ ((d2Transfer540Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer540Arithmetic
  linarith
#print axioms d2Transfer540Arithmetic
#print axioms d2Transfer540Bound
def d2Transfer541Lo : ℚ := (d2LitsNearTransfers067.q2 (1357945395) 1 (-31))
def d2Transfer541Hi : ℚ := (d2LitsNearTransfers067.q2 (339905779) 1 (-29))
def d2Transfer541Cap : ℚ := (d2LitsNearTransfers067.q2 (1228821456825910251985) 1 (-79))
def d2Transfer541C0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 55 (-3))
def d2Transfer541S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
def d2Transfer541C1 : ℚ := (d2LitsNearTransfers067.q2 (-1) 55 (-3))
def d2Transfer541S1 : ℚ := (d2LitsNearTransfers067.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer541Arithmetic : weightedUpper d2Transfer541C0 d2Log150Lo d2Log150Hi + weightedUpper d2Transfer541C1 d2Log23Lo d2Log23Hi ≤ d2Transfer541Cap := by decide +kernel
theorem d2Transfer541Bound : ∀ x ∈ Set.Icc ((d2Transfer541Lo:ℚ):ℝ) ((d2Transfer541Hi:ℚ):ℝ), ((d2Transfer541C0:ℚ):ℝ)*Real.log |x-((d2Transfer541S0:ℚ):ℝ)| + ((d2Transfer541C1:ℚ):ℝ)*Real.log |x-((d2Transfer541S1:ℚ):ℝ)| ≤ ((d2Transfer541Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer541S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer541S0,d2Transfer541Lo,d2Transfer541Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer541C0 then |x-((d2Transfer541S0:ℚ):ℝ)| ≤ ((d2Log150Q:ℚ):ℝ) else ((d2Log150Q:ℚ):ℝ) ≤ |x-((d2Transfer541S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer541S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer541S0,d2Transfer541Lo,d2Transfer541Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer541C0,d2Log150Q,d2Transfer541S0,d2Transfer541Lo,d2Transfer541Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer541C0 d2Transfer541S0 d2Log150Q d2Log150Lo d2Log150Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log150Bounds
  have hn1 : x-((d2Transfer541S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer541S1,d2Transfer541Lo,d2Transfer541Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer541C1 then |x-((d2Transfer541S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2Transfer541S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer541S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer541S1,d2Transfer541Lo,d2Transfer541Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer541C1,d2Log23Q,d2Transfer541S1,d2Transfer541Lo,d2Transfer541Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer541C1 d2Transfer541S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2Transfer541C0 d2Log150Lo d2Log150Hi:ℚ):ℝ) + ((weightedUpper d2Transfer541C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2Transfer541Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer541Arithmetic
  linarith
#print axioms d2Transfer541Arithmetic
#print axioms d2Transfer541Bound
def d2Transfer542Lo : ℚ := (d2LitsNearTransfers067.q2 (1357945395) 1 (-31))
def d2Transfer542Hi : ℚ := (d2LitsNearTransfers067.q2 (339905779) 1 (-29))
def d2Transfer542Cap : ℚ := (d2LitsNearTransfers067.q2 (8894719393789053718993) 1 (-79))
def d2Transfer542C0 : ℚ := (d2LitsNearTransfers067.q2 (23) 25 (-5))
def d2Transfer542S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer542Arithmetic : weightedUpper d2Transfer542C0 d2Log151Lo d2Log151Hi ≤ d2Transfer542Cap := by decide +kernel
theorem d2Transfer542Bound : ∀ x ∈ Set.Icc ((d2Transfer542Lo:ℚ):ℝ) ((d2Transfer542Hi:ℚ):ℝ), ((d2Transfer542C0:ℚ):ℝ)*Real.log |x-((d2Transfer542S0:ℚ):ℝ)| ≤ ((d2Transfer542Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer542S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer542S0,d2Transfer542Lo,d2Transfer542Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer542C0 then |x-((d2Transfer542S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2Transfer542S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer542S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer542S0,d2Transfer542Lo,d2Transfer542Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer542C0,d2Log151Q,d2Transfer542S0,d2Transfer542Lo,d2Transfer542Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer542C0 d2Transfer542S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have har : (((weightedUpper d2Transfer542C0 d2Log151Lo d2Log151Hi:ℚ):ℝ)) ≤ ((d2Transfer542Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer542Arithmetic
  linarith
#print axioms d2Transfer542Arithmetic
#print axioms d2Transfer542Bound
def d2Transfer543Lo : ℚ := (d2LitsNearTransfers067.q2 (1357945395) 1 (-31))
def d2Transfer543Hi : ℚ := (d2LitsNearTransfers067.q2 (339905779) 1 (-29))
def d2Transfer543Cap : ℚ := (d2LitsNearTransfers067.q2 (17320213089422688866769) 1 (-79))
def d2Transfer543C0 : ℚ := (d2LitsNearTransfers067.q2 (3) 275 (-5))
def d2Transfer543S0 : ℚ := (d2LitsNearTransfers067.q2 (-1) 1 (0))
def d2Transfer543C1 : ℚ := (d2LitsNearTransfers067.q2 (-5) 11 (-4))
def d2Transfer543S1 : ℚ := (d2LitsNearTransfers067.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer543Arithmetic : weightedUpper d2Transfer543C0 d2Log151Lo d2Log151Hi + weightedUpper d2Transfer543C1 d2Log23Lo d2Log23Hi ≤ d2Transfer543Cap := by decide +kernel
theorem d2Transfer543Bound : ∀ x ∈ Set.Icc ((d2Transfer543Lo:ℚ):ℝ) ((d2Transfer543Hi:ℚ):ℝ), ((d2Transfer543C0:ℚ):ℝ)*Real.log |x-((d2Transfer543S0:ℚ):ℝ)| + ((d2Transfer543C1:ℚ):ℝ)*Real.log |x-((d2Transfer543S1:ℚ):ℝ)| ≤ ((d2Transfer543Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer543S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer543S0,d2Transfer543Lo,d2Transfer543Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer543C0 then |x-((d2Transfer543S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2Transfer543S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer543S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer543S0,d2Transfer543Lo,d2Transfer543Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer543C0,d2Log151Q,d2Transfer543S0,d2Transfer543Lo,d2Transfer543Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer543C0 d2Transfer543S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2Transfer543S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer543S1,d2Transfer543Lo,d2Transfer543Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer543C1 then |x-((d2Transfer543S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2Transfer543S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer543S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer543S1,d2Transfer543Lo,d2Transfer543Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers067.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer543C1,d2Log23Q,d2Transfer543S1,d2Transfer543Lo,d2Transfer543Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer543C1 d2Transfer543S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2Transfer543C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2Transfer543C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2Transfer543Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer543Arithmetic
  linarith
#print axioms d2Transfer543Arithmetic
#print axioms d2Transfer543Bound
end CatalanMeasure.GenD.Signed.Data.Cells
