module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers049
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers049
open D72.LogTransfer
def d2Transfer392Lo : ℚ := (d2LitsNearTransfers049.q2 (28185465) 1 (-28))
def d2Transfer392Hi : ℚ := (d2LitsNearTransfers049.q2 (58048651) 1 (-29))
def d2Transfer392Cap : ℚ := (d2LitsNearTransfers049.q2 (15113656175) 1 (-40))
def d2Transfer392C0 : ℚ := (d2LitsNearTransfers049.q2 (23) 25 (-5))
def d2Transfer392S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer392Arithmetic : weightedUpper d2Transfer392C0 d2Log91Lo d2Log91Hi ≤ d2Transfer392Cap := by decide +kernel
theorem d2Transfer392Bound : ∀ x ∈ Set.Icc ((d2Transfer392Lo:ℚ):ℝ) ((d2Transfer392Hi:ℚ):ℝ), ((d2Transfer392C0:ℚ):ℝ)*Real.log |x-((d2Transfer392S0:ℚ):ℝ)| ≤ ((d2Transfer392Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer392S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer392S0,d2Transfer392Lo,d2Transfer392Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer392C0 then |x-((d2Transfer392S0:ℚ):ℝ)| ≤ ((d2Log91Q:ℚ):ℝ) else ((d2Log91Q:ℚ):ℝ) ≤ |x-((d2Transfer392S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer392S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer392S0,d2Transfer392Lo,d2Transfer392Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer392C0,d2Log91Q,d2Transfer392S0,d2Transfer392Lo,d2Transfer392Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer392C0 d2Transfer392S0 d2Log91Q d2Log91Lo d2Log91Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log91Bounds
  have har : (((weightedUpper d2Transfer392C0 d2Log91Lo d2Log91Hi:ℚ):ℝ)) ≤ ((d2Transfer392Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer392Arithmetic
  linarith
#print axioms d2Transfer392Arithmetic
#print axioms d2Transfer392Bound
def d2Transfer393Lo : ℚ := (d2LitsNearTransfers049.q2 (28185465) 1 (-28))
def d2Transfer393Hi : ℚ := (d2LitsNearTransfers049.q2 (58048651) 1 (-29))
def d2Transfer393Cap : ℚ := (d2LitsNearTransfers049.q2 (30439539927) 1 (-40))
def d2Transfer393C0 : ℚ := (d2LitsNearTransfers049.q2 (3) 275 (-5))
def d2Transfer393S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
def d2Transfer393C1 : ℚ := (d2LitsNearTransfers049.q2 (-5) 11 (-4))
def d2Transfer393S1 : ℚ := (d2LitsNearTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer393Arithmetic : weightedUpper d2Transfer393C0 d2Log91Lo d2Log91Hi + weightedUpper d2Transfer393C1 d2Log83Lo d2Log83Hi ≤ d2Transfer393Cap := by decide +kernel
theorem d2Transfer393Bound : ∀ x ∈ Set.Icc ((d2Transfer393Lo:ℚ):ℝ) ((d2Transfer393Hi:ℚ):ℝ), ((d2Transfer393C0:ℚ):ℝ)*Real.log |x-((d2Transfer393S0:ℚ):ℝ)| + ((d2Transfer393C1:ℚ):ℝ)*Real.log |x-((d2Transfer393S1:ℚ):ℝ)| ≤ ((d2Transfer393Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer393S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer393S0,d2Transfer393Lo,d2Transfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer393C0 then |x-((d2Transfer393S0:ℚ):ℝ)| ≤ ((d2Log91Q:ℚ):ℝ) else ((d2Log91Q:ℚ):ℝ) ≤ |x-((d2Transfer393S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer393S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer393S0,d2Transfer393Lo,d2Transfer393Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer393C0,d2Log91Q,d2Transfer393S0,d2Transfer393Lo,d2Transfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer393C0 d2Transfer393S0 d2Log91Q d2Log91Lo d2Log91Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log91Bounds
  have hn1 : x-((d2Transfer393S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer393S1,d2Transfer393Lo,d2Transfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer393C1 then |x-((d2Transfer393S1:ℚ):ℝ)| ≤ ((d2Log83Q:ℚ):ℝ) else ((d2Log83Q:ℚ):ℝ) ≤ |x-((d2Transfer393S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer393S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer393S1,d2Transfer393Lo,d2Transfer393Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer393C1,d2Log83Q,d2Transfer393S1,d2Transfer393Lo,d2Transfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer393C1 d2Transfer393S1 d2Log83Q d2Log83Lo d2Log83Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log83Bounds
  have har : (((weightedUpper d2Transfer393C0 d2Log91Lo d2Log91Hi:ℚ):ℝ) + ((weightedUpper d2Transfer393C1 d2Log83Lo d2Log83Hi:ℚ):ℝ)) ≤ ((d2Transfer393Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer393Arithmetic
  linarith
#print axioms d2Transfer393Arithmetic
#print axioms d2Transfer393Bound
def d2Transfer394Lo : ℚ := (d2LitsNearTransfers049.q2 (58048651) 1 (-29))
def d2Transfer394Hi : ℚ := (d2LitsNearTransfers049.q2 (14931593) 1 (-27))
def d2Transfer394Cap : ℚ := (d2LitsNearTransfers049.q2 (1169469059) 1 (-40))
def d2Transfer394C0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 55 (-3))
def d2Transfer394S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
def d2Transfer394C1 : ℚ := (d2LitsNearTransfers049.q2 (-1) 55 (-3))
def d2Transfer394S1 : ℚ := (d2LitsNearTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer394Arithmetic : weightedUpper d2Transfer394C0 d2Log91Lo d2Log91Hi + weightedUpper d2Transfer394C1 d2Log82Lo d2Log82Hi ≤ d2Transfer394Cap := by decide +kernel
theorem d2Transfer394Bound : ∀ x ∈ Set.Icc ((d2Transfer394Lo:ℚ):ℝ) ((d2Transfer394Hi:ℚ):ℝ), ((d2Transfer394C0:ℚ):ℝ)*Real.log |x-((d2Transfer394S0:ℚ):ℝ)| + ((d2Transfer394C1:ℚ):ℝ)*Real.log |x-((d2Transfer394S1:ℚ):ℝ)| ≤ ((d2Transfer394Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer394S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer394S0,d2Transfer394Lo,d2Transfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer394C0 then |x-((d2Transfer394S0:ℚ):ℝ)| ≤ ((d2Log91Q:ℚ):ℝ) else ((d2Log91Q:ℚ):ℝ) ≤ |x-((d2Transfer394S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer394S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer394S0,d2Transfer394Lo,d2Transfer394Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer394C0,d2Log91Q,d2Transfer394S0,d2Transfer394Lo,d2Transfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer394C0 d2Transfer394S0 d2Log91Q d2Log91Lo d2Log91Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log91Bounds
  have hn1 : x-((d2Transfer394S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer394S1,d2Transfer394Lo,d2Transfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer394C1 then |x-((d2Transfer394S1:ℚ):ℝ)| ≤ ((d2Log82Q:ℚ):ℝ) else ((d2Log82Q:ℚ):ℝ) ≤ |x-((d2Transfer394S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer394S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer394S1,d2Transfer394Lo,d2Transfer394Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer394C1,d2Log82Q,d2Transfer394S1,d2Transfer394Lo,d2Transfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer394C1 d2Transfer394S1 d2Log82Q d2Log82Lo d2Log82Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log82Bounds
  have har : (((weightedUpper d2Transfer394C0 d2Log91Lo d2Log91Hi:ℚ):ℝ) + ((weightedUpper d2Transfer394C1 d2Log82Lo d2Log82Hi:ℚ):ℝ)) ≤ ((d2Transfer394Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer394Arithmetic
  linarith
#print axioms d2Transfer394Arithmetic
#print axioms d2Transfer394Bound
def d2Transfer395Lo : ℚ := (d2LitsNearTransfers049.q2 (58048651) 1 (-29))
def d2Transfer395Hi : ℚ := (d2LitsNearTransfers049.q2 (14931593) 1 (-27))
def d2Transfer395Cap : ℚ := (d2LitsNearTransfers049.q2 (15113656175) 1 (-40))
def d2Transfer395C0 : ℚ := (d2LitsNearTransfers049.q2 (23) 25 (-5))
def d2Transfer395S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer395Arithmetic : weightedUpper d2Transfer395C0 d2Log92Lo d2Log92Hi ≤ d2Transfer395Cap := by decide +kernel
theorem d2Transfer395Bound : ∀ x ∈ Set.Icc ((d2Transfer395Lo:ℚ):ℝ) ((d2Transfer395Hi:ℚ):ℝ), ((d2Transfer395C0:ℚ):ℝ)*Real.log |x-((d2Transfer395S0:ℚ):ℝ)| ≤ ((d2Transfer395Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer395S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer395S0,d2Transfer395Lo,d2Transfer395Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer395C0 then |x-((d2Transfer395S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer395S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer395S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer395S0,d2Transfer395Lo,d2Transfer395Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer395C0,d2Log92Q,d2Transfer395S0,d2Transfer395Lo,d2Transfer395Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer395C0 d2Transfer395S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have har : (((weightedUpper d2Transfer395C0 d2Log92Lo d2Log92Hi:ℚ):ℝ)) ≤ ((d2Transfer395Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer395Arithmetic
  linarith
#print axioms d2Transfer395Arithmetic
#print axioms d2Transfer395Bound
def d2Transfer396Lo : ℚ := (d2LitsNearTransfers049.q2 (58048651) 1 (-29))
def d2Transfer396Hi : ℚ := (d2LitsNearTransfers049.q2 (14931593) 1 (-27))
def d2Transfer396Cap : ℚ := (d2LitsNearTransfers049.q2 (30439539927) 1 (-40))
def d2Transfer396C0 : ℚ := (d2LitsNearTransfers049.q2 (3) 275 (-5))
def d2Transfer396S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
def d2Transfer396C1 : ℚ := (d2LitsNearTransfers049.q2 (-5) 11 (-4))
def d2Transfer396S1 : ℚ := (d2LitsNearTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer396Arithmetic : weightedUpper d2Transfer396C0 d2Log92Lo d2Log92Hi + weightedUpper d2Transfer396C1 d2Log82Lo d2Log82Hi ≤ d2Transfer396Cap := by decide +kernel
theorem d2Transfer396Bound : ∀ x ∈ Set.Icc ((d2Transfer396Lo:ℚ):ℝ) ((d2Transfer396Hi:ℚ):ℝ), ((d2Transfer396C0:ℚ):ℝ)*Real.log |x-((d2Transfer396S0:ℚ):ℝ)| + ((d2Transfer396C1:ℚ):ℝ)*Real.log |x-((d2Transfer396S1:ℚ):ℝ)| ≤ ((d2Transfer396Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer396S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer396S0,d2Transfer396Lo,d2Transfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer396C0 then |x-((d2Transfer396S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer396S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer396S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer396S0,d2Transfer396Lo,d2Transfer396Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer396C0,d2Log92Q,d2Transfer396S0,d2Transfer396Lo,d2Transfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer396C0 d2Transfer396S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have hn1 : x-((d2Transfer396S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer396S1,d2Transfer396Lo,d2Transfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer396C1 then |x-((d2Transfer396S1:ℚ):ℝ)| ≤ ((d2Log82Q:ℚ):ℝ) else ((d2Log82Q:ℚ):ℝ) ≤ |x-((d2Transfer396S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer396S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer396S1,d2Transfer396Lo,d2Transfer396Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer396C1,d2Log82Q,d2Transfer396S1,d2Transfer396Lo,d2Transfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer396C1 d2Transfer396S1 d2Log82Q d2Log82Lo d2Log82Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log82Bounds
  have har : (((weightedUpper d2Transfer396C0 d2Log92Lo d2Log92Hi:ℚ):ℝ) + ((weightedUpper d2Transfer396C1 d2Log82Lo d2Log82Hi:ℚ):ℝ)) ≤ ((d2Transfer396Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer396Arithmetic
  linarith
#print axioms d2Transfer396Arithmetic
#print axioms d2Transfer396Bound
def d2Transfer397Lo : ℚ := (d2LitsNearTransfers049.q2 (14931593) 1 (-27))
def d2Transfer397Hi : ℚ := (d2LitsNearTransfers049.q2 (61404093) 1 (-29))
def d2Transfer397Cap : ℚ := (d2LitsNearTransfers049.q2 (1169469059) 1 (-40))
def d2Transfer397C0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 55 (-3))
def d2Transfer397S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
def d2Transfer397C1 : ℚ := (d2LitsNearTransfers049.q2 (-1) 55 (-3))
def d2Transfer397S1 : ℚ := (d2LitsNearTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer397Arithmetic : weightedUpper d2Transfer397C0 d2Log92Lo d2Log92Hi + weightedUpper d2Transfer397C1 d2Log81Lo d2Log81Hi ≤ d2Transfer397Cap := by decide +kernel
theorem d2Transfer397Bound : ∀ x ∈ Set.Icc ((d2Transfer397Lo:ℚ):ℝ) ((d2Transfer397Hi:ℚ):ℝ), ((d2Transfer397C0:ℚ):ℝ)*Real.log |x-((d2Transfer397S0:ℚ):ℝ)| + ((d2Transfer397C1:ℚ):ℝ)*Real.log |x-((d2Transfer397S1:ℚ):ℝ)| ≤ ((d2Transfer397Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer397S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer397S0,d2Transfer397Lo,d2Transfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer397C0 then |x-((d2Transfer397S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer397S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer397S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer397S0,d2Transfer397Lo,d2Transfer397Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer397C0,d2Log92Q,d2Transfer397S0,d2Transfer397Lo,d2Transfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer397C0 d2Transfer397S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have hn1 : x-((d2Transfer397S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer397S1,d2Transfer397Lo,d2Transfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer397C1 then |x-((d2Transfer397S1:ℚ):ℝ)| ≤ ((d2Log81Q:ℚ):ℝ) else ((d2Log81Q:ℚ):ℝ) ≤ |x-((d2Transfer397S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer397S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer397S1,d2Transfer397Lo,d2Transfer397Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer397C1,d2Log81Q,d2Transfer397S1,d2Transfer397Lo,d2Transfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer397C1 d2Transfer397S1 d2Log81Q d2Log81Lo d2Log81Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log81Bounds
  have har : (((weightedUpper d2Transfer397C0 d2Log92Lo d2Log92Hi:ℚ):ℝ) + ((weightedUpper d2Transfer397C1 d2Log81Lo d2Log81Hi:ℚ):ℝ)) ≤ ((d2Transfer397Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer397Arithmetic
  linarith
#print axioms d2Transfer397Arithmetic
#print axioms d2Transfer397Bound
def d2Transfer398Lo : ℚ := (d2LitsNearTransfers049.q2 (14931593) 1 (-27))
def d2Transfer398Hi : ℚ := (d2LitsNearTransfers049.q2 (61404093) 1 (-29))
def d2Transfer398Cap : ℚ := (d2LitsNearTransfers049.q2 (15113656175) 1 (-40))
def d2Transfer398C0 : ℚ := (d2LitsNearTransfers049.q2 (23) 25 (-5))
def d2Transfer398S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer398Arithmetic : weightedUpper d2Transfer398C0 d2Log93Lo d2Log93Hi ≤ d2Transfer398Cap := by decide +kernel
theorem d2Transfer398Bound : ∀ x ∈ Set.Icc ((d2Transfer398Lo:ℚ):ℝ) ((d2Transfer398Hi:ℚ):ℝ), ((d2Transfer398C0:ℚ):ℝ)*Real.log |x-((d2Transfer398S0:ℚ):ℝ)| ≤ ((d2Transfer398Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer398S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer398S0,d2Transfer398Lo,d2Transfer398Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer398C0 then |x-((d2Transfer398S0:ℚ):ℝ)| ≤ ((d2Log93Q:ℚ):ℝ) else ((d2Log93Q:ℚ):ℝ) ≤ |x-((d2Transfer398S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer398S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer398S0,d2Transfer398Lo,d2Transfer398Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer398C0,d2Log93Q,d2Transfer398S0,d2Transfer398Lo,d2Transfer398Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer398C0 d2Transfer398S0 d2Log93Q d2Log93Lo d2Log93Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log93Bounds
  have har : (((weightedUpper d2Transfer398C0 d2Log93Lo d2Log93Hi:ℚ):ℝ)) ≤ ((d2Transfer398Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer398Arithmetic
  linarith
#print axioms d2Transfer398Arithmetic
#print axioms d2Transfer398Bound
def d2Transfer399Lo : ℚ := (d2LitsNearTransfers049.q2 (14931593) 1 (-27))
def d2Transfer399Hi : ℚ := (d2LitsNearTransfers049.q2 (61404093) 1 (-29))
def d2Transfer399Cap : ℚ := (d2LitsNearTransfers049.q2 (30439539927) 1 (-40))
def d2Transfer399C0 : ℚ := (d2LitsNearTransfers049.q2 (3) 275 (-5))
def d2Transfer399S0 : ℚ := (d2LitsNearTransfers049.q2 (-1) 1 (0))
def d2Transfer399C1 : ℚ := (d2LitsNearTransfers049.q2 (-5) 11 (-4))
def d2Transfer399S1 : ℚ := (d2LitsNearTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer399Arithmetic : weightedUpper d2Transfer399C0 d2Log93Lo d2Log93Hi + weightedUpper d2Transfer399C1 d2Log81Lo d2Log81Hi ≤ d2Transfer399Cap := by decide +kernel
theorem d2Transfer399Bound : ∀ x ∈ Set.Icc ((d2Transfer399Lo:ℚ):ℝ) ((d2Transfer399Hi:ℚ):ℝ), ((d2Transfer399C0:ℚ):ℝ)*Real.log |x-((d2Transfer399S0:ℚ):ℝ)| + ((d2Transfer399C1:ℚ):ℝ)*Real.log |x-((d2Transfer399S1:ℚ):ℝ)| ≤ ((d2Transfer399Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer399S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer399S0,d2Transfer399Lo,d2Transfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer399C0 then |x-((d2Transfer399S0:ℚ):ℝ)| ≤ ((d2Log93Q:ℚ):ℝ) else ((d2Log93Q:ℚ):ℝ) ≤ |x-((d2Transfer399S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer399S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer399S0,d2Transfer399Lo,d2Transfer399Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer399C0,d2Log93Q,d2Transfer399S0,d2Transfer399Lo,d2Transfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer399C0 d2Transfer399S0 d2Log93Q d2Log93Lo d2Log93Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log93Bounds
  have hn1 : x-((d2Transfer399S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer399S1,d2Transfer399Lo,d2Transfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer399C1 then |x-((d2Transfer399S1:ℚ):ℝ)| ≤ ((d2Log81Q:ℚ):ℝ) else ((d2Log81Q:ℚ):ℝ) ≤ |x-((d2Transfer399S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer399S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer399S1,d2Transfer399Lo,d2Transfer399Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers049.q2, d2LitsNearLogCache005.q2, d2Transfer399C1,d2Log81Q,d2Transfer399S1,d2Transfer399Lo,d2Transfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer399C1 d2Transfer399S1 d2Log81Q d2Log81Lo d2Log81Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log81Bounds
  have har : (((weightedUpper d2Transfer399C0 d2Log93Lo d2Log93Hi:ℚ):ℝ) + ((weightedUpper d2Transfer399C1 d2Log81Lo d2Log81Hi:ℚ):ℝ)) ≤ ((d2Transfer399Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer399Arithmetic
  linarith
#print axioms d2Transfer399Arithmetic
#print axioms d2Transfer399Bound
end CatalanMeasure.GenD.Signed.Data.Cells
