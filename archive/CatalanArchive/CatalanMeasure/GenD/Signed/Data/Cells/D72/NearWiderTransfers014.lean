module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers014
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers014
open D72.LogTransfer
def d2WiderTransfer112Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (329839453) 1 (-29))
def d2WiderTransfer112Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (661356627) 1 (-30))
def d2WiderTransfer112Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (4537313759313862163287) 1 (-78))
def d2WiderTransfer112C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 1 (-5))
def d2WiderTransfer112S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer112Arithmetic : weightedUpper d2WiderTransfer112C0 d2Log130Lo d2Log130Hi ≤ d2WiderTransfer112Cap := by decide +kernel
theorem d2WiderTransfer112Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer112Lo:ℚ):ℝ) ((d2WiderTransfer112Hi:ℚ):ℝ), ((d2WiderTransfer112C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer112S0:ℚ):ℝ)| ≤ ((d2WiderTransfer112Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer112S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer112S0,d2WiderTransfer112Lo,d2WiderTransfer112Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer112C0 then |x-((d2WiderTransfer112S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer112S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer112S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer112S0,d2WiderTransfer112Lo,d2WiderTransfer112Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer112C0,d2Log130Q,d2WiderTransfer112S0,d2WiderTransfer112Lo,d2WiderTransfer112Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer112C0 d2WiderTransfer112S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have har : (((weightedUpper d2WiderTransfer112C0 d2Log130Lo d2Log130Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer112Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer112Arithmetic
  linarith
#print axioms d2WiderTransfer112Arithmetic
#print axioms d2WiderTransfer112Bound
def d2WiderTransfer113Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (329839453) 1 (-29))
def d2WiderTransfer113Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (661356627) 1 (-30))
def d2WiderTransfer113Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (8628523089886739004247) 1 (-78))
def d2WiderTransfer113C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 11 (-5))
def d2WiderTransfer113S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
def d2WiderTransfer113C1 : ℚ := (d2LitsNearWiderTransfers014.q2 (-5) 11 (-4))
def d2WiderTransfer113S1 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer113Arithmetic : weightedUpper d2WiderTransfer113C0 d2Log130Lo d2Log130Hi + weightedUpper d2WiderTransfer113C1 d2Log44Lo d2Log44Hi ≤ d2WiderTransfer113Cap := by decide +kernel
theorem d2WiderTransfer113Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer113Lo:ℚ):ℝ) ((d2WiderTransfer113Hi:ℚ):ℝ), ((d2WiderTransfer113C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer113S0:ℚ):ℝ)| + ((d2WiderTransfer113C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer113S1:ℚ):ℝ)| ≤ ((d2WiderTransfer113Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer113S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer113S0,d2WiderTransfer113Lo,d2WiderTransfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer113C0 then |x-((d2WiderTransfer113S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer113S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer113S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer113S0,d2WiderTransfer113Lo,d2WiderTransfer113Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer113C0,d2Log130Q,d2WiderTransfer113S0,d2WiderTransfer113Lo,d2WiderTransfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer113C0 d2WiderTransfer113S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have hn1 : x-((d2WiderTransfer113S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer113S1,d2WiderTransfer113Lo,d2WiderTransfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer113C1 then |x-((d2WiderTransfer113S1:ℚ):ℝ)| ≤ ((d2Log44Q:ℚ):ℝ) else ((d2Log44Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer113S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer113S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer113S1,d2WiderTransfer113Lo,d2WiderTransfer113Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer113C1,d2Log44Q,d2WiderTransfer113S1,d2WiderTransfer113Lo,d2WiderTransfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer113C1 d2WiderTransfer113S1 d2Log44Q d2Log44Lo d2Log44Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log44Bounds
  have har : (((weightedUpper d2WiderTransfer113C0 d2Log130Lo d2Log130Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer113C1 d2Log44Lo d2Log44Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer113Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer113Arithmetic
  linarith
#print axioms d2WiderTransfer113Arithmetic
#print axioms d2WiderTransfer113Bound
def d2WiderTransfer114Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (661356627) 1 (-30))
def d2WiderTransfer114Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (165758587) 1 (-28))
def d2WiderTransfer114Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (1819221899745516347231) 1 (-80))
def d2WiderTransfer114C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 25 (-4))
def d2WiderTransfer114S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer114Arithmetic : weightedUpper d2WiderTransfer114C0 d2Log131Lo d2Log131Hi ≤ d2WiderTransfer114Cap := by decide +kernel
theorem d2WiderTransfer114Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer114Lo:ℚ):ℝ) ((d2WiderTransfer114Hi:ℚ):ℝ), ((d2WiderTransfer114C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer114S0:ℚ):ℝ)| ≤ ((d2WiderTransfer114Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer114S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer114S0,d2WiderTransfer114Lo,d2WiderTransfer114Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer114C0 then |x-((d2WiderTransfer114S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer114S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer114S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer114S0,d2WiderTransfer114Lo,d2WiderTransfer114Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer114C0,d2Log131Q,d2WiderTransfer114S0,d2WiderTransfer114Lo,d2WiderTransfer114Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer114C0 d2WiderTransfer114S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2WiderTransfer114C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer114Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer114Arithmetic
  linarith
#print axioms d2WiderTransfer114Arithmetic
#print axioms d2WiderTransfer114Bound
def d2WiderTransfer115Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (661356627) 1 (-30))
def d2WiderTransfer115Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (165758587) 1 (-28))
def d2WiderTransfer115Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (3069522068381251690335) 1 (-80))
def d2WiderTransfer115C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 275 (-4))
def d2WiderTransfer115S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
def d2WiderTransfer115C1 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 55 (-3))
def d2WiderTransfer115S1 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer115Arithmetic : weightedUpper d2WiderTransfer115C0 d2Log131Lo d2Log131Hi + weightedUpper d2WiderTransfer115C1 d2Log43Lo d2Log43Hi ≤ d2WiderTransfer115Cap := by decide +kernel
theorem d2WiderTransfer115Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer115Lo:ℚ):ℝ) ((d2WiderTransfer115Hi:ℚ):ℝ), ((d2WiderTransfer115C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer115S0:ℚ):ℝ)| + ((d2WiderTransfer115C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer115S1:ℚ):ℝ)| ≤ ((d2WiderTransfer115Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer115S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer115S0,d2WiderTransfer115Lo,d2WiderTransfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer115C0 then |x-((d2WiderTransfer115S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer115S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer115S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer115S0,d2WiderTransfer115Lo,d2WiderTransfer115Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer115C0,d2Log131Q,d2WiderTransfer115S0,d2WiderTransfer115Lo,d2WiderTransfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer115C0 d2WiderTransfer115S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2WiderTransfer115S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer115S1,d2WiderTransfer115Lo,d2WiderTransfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer115C1 then |x-((d2WiderTransfer115S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer115S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer115S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer115S1,d2WiderTransfer115Lo,d2WiderTransfer115Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer115C1,d2Log43Q,d2WiderTransfer115S1,d2WiderTransfer115Lo,d2WiderTransfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer115C1 d2WiderTransfer115S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2WiderTransfer115C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer115C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer115Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer115Arithmetic
  linarith
#print axioms d2WiderTransfer115Arithmetic
#print axioms d2WiderTransfer115Bound
def d2WiderTransfer116Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (661356627) 1 (-30))
def d2WiderTransfer116Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (165758587) 1 (-28))
def d2WiderTransfer116Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (18292584158804212211551) 1 (-80))
def d2WiderTransfer116C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 1 (-5))
def d2WiderTransfer116S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer116Arithmetic : weightedUpper d2WiderTransfer116C0 d2Log131Lo d2Log131Hi ≤ d2WiderTransfer116Cap := by decide +kernel
theorem d2WiderTransfer116Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer116Lo:ℚ):ℝ) ((d2WiderTransfer116Hi:ℚ):ℝ), ((d2WiderTransfer116C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer116S0:ℚ):ℝ)| ≤ ((d2WiderTransfer116Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer116S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer116S0,d2WiderTransfer116Lo,d2WiderTransfer116Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer116C0 then |x-((d2WiderTransfer116S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer116S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer116S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer116S0,d2WiderTransfer116Lo,d2WiderTransfer116Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer116C0,d2Log131Q,d2WiderTransfer116S0,d2WiderTransfer116Lo,d2WiderTransfer116Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer116C0 d2WiderTransfer116S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2WiderTransfer116C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer116Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer116Arithmetic
  linarith
#print axioms d2WiderTransfer116Arithmetic
#print axioms d2WiderTransfer116Bound
def d2WiderTransfer117Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (661356627) 1 (-30))
def d2WiderTransfer117Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (165758587) 1 (-28))
def d2WiderTransfer117Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (34657421481095719575391) 1 (-80))
def d2WiderTransfer117C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 11 (-5))
def d2WiderTransfer117S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
def d2WiderTransfer117C1 : ℚ := (d2LitsNearWiderTransfers014.q2 (-5) 11 (-4))
def d2WiderTransfer117S1 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer117Arithmetic : weightedUpper d2WiderTransfer117C0 d2Log131Lo d2Log131Hi + weightedUpper d2WiderTransfer117C1 d2Log43Lo d2Log43Hi ≤ d2WiderTransfer117Cap := by decide +kernel
theorem d2WiderTransfer117Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer117Lo:ℚ):ℝ) ((d2WiderTransfer117Hi:ℚ):ℝ), ((d2WiderTransfer117C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer117S0:ℚ):ℝ)| + ((d2WiderTransfer117C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer117S1:ℚ):ℝ)| ≤ ((d2WiderTransfer117Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer117S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer117S0,d2WiderTransfer117Lo,d2WiderTransfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer117C0 then |x-((d2WiderTransfer117S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer117S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer117S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer117S0,d2WiderTransfer117Lo,d2WiderTransfer117Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer117C0,d2Log131Q,d2WiderTransfer117S0,d2WiderTransfer117Lo,d2WiderTransfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer117C0 d2WiderTransfer117S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2WiderTransfer117S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer117S1,d2WiderTransfer117Lo,d2WiderTransfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer117C1 then |x-((d2WiderTransfer117S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer117S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer117S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer117S1,d2WiderTransfer117Lo,d2WiderTransfer117Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer117C1,d2Log43Q,d2WiderTransfer117S1,d2WiderTransfer117Lo,d2WiderTransfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer117C1 d2WiderTransfer117S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2WiderTransfer117C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer117C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer117Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer117Arithmetic
  linarith
#print axioms d2WiderTransfer117Arithmetic
#print axioms d2WiderTransfer117Bound
def d2WiderTransfer118Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (165758587) 1 (-28))
def d2WiderTransfer118Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (1327746417) 1 (-31))
def d2WiderTransfer118Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (472774969983535760355) 1 (-78))
def d2WiderTransfer118C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 25 (-4))
def d2WiderTransfer118S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer118Arithmetic : weightedUpper d2WiderTransfer118C0 d2Log132Lo d2Log132Hi ≤ d2WiderTransfer118Cap := by decide +kernel
theorem d2WiderTransfer118Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer118Lo:ℚ):ℝ) ((d2WiderTransfer118Hi:ℚ):ℝ), ((d2WiderTransfer118C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer118S0:ℚ):ℝ)| ≤ ((d2WiderTransfer118Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer118S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer118S0,d2WiderTransfer118Lo,d2WiderTransfer118Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer118C0 then |x-((d2WiderTransfer118S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer118S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer118S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer118S0,d2WiderTransfer118Lo,d2WiderTransfer118Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer118C0,d2Log132Q,d2WiderTransfer118S0,d2WiderTransfer118Lo,d2WiderTransfer118Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer118C0 d2WiderTransfer118S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have har : (((weightedUpper d2WiderTransfer118C0 d2Log132Lo d2Log132Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer118Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer118Arithmetic
  linarith
#print axioms d2WiderTransfer118Arithmetic
#print axioms d2WiderTransfer118Bound
def d2WiderTransfer119Lo : ℚ := (d2LitsNearWiderTransfers014.q2 (165758587) 1 (-28))
def d2WiderTransfer119Hi : ℚ := (d2LitsNearWiderTransfers014.q2 (1327746417) 1 (-31))
def d2WiderTransfer119Cap : ℚ := (d2LitsNearWiderTransfers014.q2 (785350012142469596131) 1 (-78))
def d2WiderTransfer119C0 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 275 (-4))
def d2WiderTransfer119S0 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 1 (0))
def d2WiderTransfer119C1 : ℚ := (d2LitsNearWiderTransfers014.q2 (-1) 55 (-3))
def d2WiderTransfer119S1 : ℚ := (d2LitsNearWiderTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer119Arithmetic : weightedUpper d2WiderTransfer119C0 d2Log132Lo d2Log132Hi + weightedUpper d2WiderTransfer119C1 d2Log42Lo d2Log42Hi ≤ d2WiderTransfer119Cap := by decide +kernel
theorem d2WiderTransfer119Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer119Lo:ℚ):ℝ) ((d2WiderTransfer119Hi:ℚ):ℝ), ((d2WiderTransfer119C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer119S0:ℚ):ℝ)| + ((d2WiderTransfer119C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer119S1:ℚ):ℝ)| ≤ ((d2WiderTransfer119Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer119S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer119S0,d2WiderTransfer119Lo,d2WiderTransfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer119C0 then |x-((d2WiderTransfer119S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer119S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer119S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer119S0,d2WiderTransfer119Lo,d2WiderTransfer119Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer119C0,d2Log132Q,d2WiderTransfer119S0,d2WiderTransfer119Lo,d2WiderTransfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer119C0 d2WiderTransfer119S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have hn1 : x-((d2WiderTransfer119S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer119S1,d2WiderTransfer119Lo,d2WiderTransfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer119C1 then |x-((d2WiderTransfer119S1:ℚ):ℝ)| ≤ ((d2Log42Q:ℚ):ℝ) else ((d2Log42Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer119S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer119S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer119S1,d2WiderTransfer119Lo,d2WiderTransfer119Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers014.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer119C1,d2Log42Q,d2WiderTransfer119S1,d2WiderTransfer119Lo,d2WiderTransfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer119C1 d2WiderTransfer119S1 d2Log42Q d2Log42Lo d2Log42Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log42Bounds
  have har : (((weightedUpper d2WiderTransfer119C0 d2Log132Lo d2Log132Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer119C1 d2Log42Lo d2Log42Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer119Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer119Arithmetic
  linarith
#print axioms d2WiderTransfer119Arithmetic
#print axioms d2WiderTransfer119Bound
end CatalanMeasure.GenD.Signed.Data.Cells
