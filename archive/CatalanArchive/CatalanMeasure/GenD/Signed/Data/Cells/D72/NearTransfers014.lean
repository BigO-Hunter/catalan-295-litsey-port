module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers014
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers014
open D72.LogTransfer
def d2Transfer112Lo : ℚ := (d2LitsNearTransfers014.q2 (31540907) 1 (-28))
def d2Transfer112Hi : ℚ := (d2LitsNearTransfers014.q2 (8304657) 1 (-26))
def d2Transfer112Cap : ℚ := (d2LitsNearTransfers014.q2 (16281318465) 1 (-40))
def d2Transfer112C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 1 (-5))
def d2Transfer112S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer112Arithmetic : weightedUpper d2Transfer112C0 d2Log95Lo d2Log95Hi ≤ d2Transfer112Cap := by decide +kernel
theorem d2Transfer112Bound : ∀ x ∈ Set.Icc ((d2Transfer112Lo:ℚ):ℝ) ((d2Transfer112Hi:ℚ):ℝ), ((d2Transfer112C0:ℚ):ℝ)*Real.log |x-((d2Transfer112S0:ℚ):ℝ)| ≤ ((d2Transfer112Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer112S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer112S0,d2Transfer112Lo,d2Transfer112Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer112C0 then |x-((d2Transfer112S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer112S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer112S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer112S0,d2Transfer112Lo,d2Transfer112Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer112C0,d2Log95Q,d2Transfer112S0,d2Transfer112Lo,d2Transfer112Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer112C0 d2Transfer112S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2Transfer112C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2Transfer112Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer112Arithmetic
  linarith
#print axioms d2Transfer112Arithmetic
#print axioms d2Transfer112Bound
def d2Transfer113Lo : ℚ := (d2LitsNearTransfers014.q2 (31540907) 1 (-28))
def d2Transfer113Hi : ℚ := (d2LitsNearTransfers014.q2 (8304657) 1 (-26))
def d2Transfer113Cap : ℚ := (d2LitsNearTransfers014.q2 (31165051305) 1 (-40))
def d2Transfer113C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 11 (-5))
def d2Transfer113S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
def d2Transfer113C1 : ℚ := (d2LitsNearTransfers014.q2 (-5) 11 (-4))
def d2Transfer113S1 : ℚ := (d2LitsNearTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer113Arithmetic : weightedUpper d2Transfer113C0 d2Log95Lo d2Log95Hi + weightedUpper d2Transfer113C1 d2Log79Lo d2Log79Hi ≤ d2Transfer113Cap := by decide +kernel
theorem d2Transfer113Bound : ∀ x ∈ Set.Icc ((d2Transfer113Lo:ℚ):ℝ) ((d2Transfer113Hi:ℚ):ℝ), ((d2Transfer113C0:ℚ):ℝ)*Real.log |x-((d2Transfer113S0:ℚ):ℝ)| + ((d2Transfer113C1:ℚ):ℝ)*Real.log |x-((d2Transfer113S1:ℚ):ℝ)| ≤ ((d2Transfer113Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer113S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer113S0,d2Transfer113Lo,d2Transfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer113C0 then |x-((d2Transfer113S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer113S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer113S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer113S0,d2Transfer113Lo,d2Transfer113Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer113C0,d2Log95Q,d2Transfer113S0,d2Transfer113Lo,d2Transfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer113C0 d2Transfer113S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2Transfer113S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer113S1,d2Transfer113Lo,d2Transfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer113C1 then |x-((d2Transfer113S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2Transfer113S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer113S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer113S1,d2Transfer113Lo,d2Transfer113Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer113C1,d2Log79Q,d2Transfer113S1,d2Transfer113Lo,d2Transfer113Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer113C1 d2Transfer113S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2Transfer113C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2Transfer113C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2Transfer113Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer113Arithmetic
  linarith
#print axioms d2Transfer113Arithmetic
#print axioms d2Transfer113Bound
def d2Transfer114Lo : ℚ := (d2LitsNearTransfers014.q2 (8304657) 1 (-26))
def d2Transfer114Hi : ℚ := (d2LitsNearTransfers014.q2 (34896349) 1 (-28))
def d2Transfer114Cap : ℚ := (d2LitsNearTransfers014.q2 (649441385) 1 (-39))
def d2Transfer114C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 25 (-4))
def d2Transfer114S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer114Arithmetic : weightedUpper d2Transfer114C0 d2Log96Lo d2Log96Hi ≤ d2Transfer114Cap := by decide +kernel
theorem d2Transfer114Bound : ∀ x ∈ Set.Icc ((d2Transfer114Lo:ℚ):ℝ) ((d2Transfer114Hi:ℚ):ℝ), ((d2Transfer114C0:ℚ):ℝ)*Real.log |x-((d2Transfer114S0:ℚ):ℝ)| ≤ ((d2Transfer114Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer114S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer114S0,d2Transfer114Lo,d2Transfer114Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer114C0 then |x-((d2Transfer114S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer114S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer114S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer114S0,d2Transfer114Lo,d2Transfer114Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer114C0,d2Log96Q,d2Transfer114S0,d2Transfer114Lo,d2Transfer114Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer114C0 d2Transfer114S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have har : (((weightedUpper d2Transfer114C0 d2Log96Lo d2Log96Hi:ℚ):ℝ)) ≤ ((d2Transfer114Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer114Arithmetic
  linarith
#print axioms d2Transfer114Arithmetic
#print axioms d2Transfer114Bound
def d2Transfer115Lo : ℚ := (d2LitsNearTransfers014.q2 (8304657) 1 (-26))
def d2Transfer115Hi : ℚ := (d2LitsNearTransfers014.q2 (34896349) 1 (-28))
def d2Transfer115Cap : ℚ := (d2LitsNearTransfers014.q2 (2436024149) 1 (-40))
def d2Transfer115C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 275 (-4))
def d2Transfer115S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
def d2Transfer115C1 : ℚ := (d2LitsNearTransfers014.q2 (-1) 55 (-3))
def d2Transfer115S1 : ℚ := (d2LitsNearTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer115Arithmetic : weightedUpper d2Transfer115C0 d2Log96Lo d2Log96Hi + weightedUpper d2Transfer115C1 d2Log78Lo d2Log78Hi ≤ d2Transfer115Cap := by decide +kernel
theorem d2Transfer115Bound : ∀ x ∈ Set.Icc ((d2Transfer115Lo:ℚ):ℝ) ((d2Transfer115Hi:ℚ):ℝ), ((d2Transfer115C0:ℚ):ℝ)*Real.log |x-((d2Transfer115S0:ℚ):ℝ)| + ((d2Transfer115C1:ℚ):ℝ)*Real.log |x-((d2Transfer115S1:ℚ):ℝ)| ≤ ((d2Transfer115Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer115S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer115S0,d2Transfer115Lo,d2Transfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer115C0 then |x-((d2Transfer115S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer115S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer115S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer115S0,d2Transfer115Lo,d2Transfer115Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer115C0,d2Log96Q,d2Transfer115S0,d2Transfer115Lo,d2Transfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer115C0 d2Transfer115S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have hn1 : x-((d2Transfer115S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer115S1,d2Transfer115Lo,d2Transfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer115C1 then |x-((d2Transfer115S1:ℚ):ℝ)| ≤ ((d2Log78Q:ℚ):ℝ) else ((d2Log78Q:ℚ):ℝ) ≤ |x-((d2Transfer115S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer115S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer115S1,d2Transfer115Lo,d2Transfer115Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer115C1,d2Log78Q,d2Transfer115S1,d2Transfer115Lo,d2Transfer115Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer115C1 d2Transfer115S1 d2Log78Q d2Log78Lo d2Log78Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log78Bounds
  have har : (((weightedUpper d2Transfer115C0 d2Log96Lo d2Log96Hi:ℚ):ℝ) + ((weightedUpper d2Transfer115C1 d2Log78Lo d2Log78Hi:ℚ):ℝ)) ≤ ((d2Transfer115Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer115Arithmetic
  linarith
#print axioms d2Transfer115Arithmetic
#print axioms d2Transfer115Bound
def d2Transfer116Lo : ℚ := (d2LitsNearTransfers014.q2 (8304657) 1 (-26))
def d2Transfer116Hi : ℚ := (d2LitsNearTransfers014.q2 (34896349) 1 (-28))
def d2Transfer116Cap : ℚ := (d2LitsNearTransfers014.q2 (16281318465) 1 (-40))
def d2Transfer116C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 1 (-5))
def d2Transfer116S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer116Arithmetic : weightedUpper d2Transfer116C0 d2Log96Lo d2Log96Hi ≤ d2Transfer116Cap := by decide +kernel
theorem d2Transfer116Bound : ∀ x ∈ Set.Icc ((d2Transfer116Lo:ℚ):ℝ) ((d2Transfer116Hi:ℚ):ℝ), ((d2Transfer116C0:ℚ):ℝ)*Real.log |x-((d2Transfer116S0:ℚ):ℝ)| ≤ ((d2Transfer116Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer116S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer116S0,d2Transfer116Lo,d2Transfer116Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer116C0 then |x-((d2Transfer116S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer116S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer116S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer116S0,d2Transfer116Lo,d2Transfer116Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer116C0,d2Log96Q,d2Transfer116S0,d2Transfer116Lo,d2Transfer116Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer116C0 d2Transfer116S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have har : (((weightedUpper d2Transfer116C0 d2Log96Lo d2Log96Hi:ℚ):ℝ)) ≤ ((d2Transfer116Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer116Arithmetic
  linarith
#print axioms d2Transfer116Arithmetic
#print axioms d2Transfer116Bound
def d2Transfer117Lo : ℚ := (d2LitsNearTransfers014.q2 (8304657) 1 (-26))
def d2Transfer117Hi : ℚ := (d2LitsNearTransfers014.q2 (34896349) 1 (-28))
def d2Transfer117Cap : ℚ := (d2LitsNearTransfers014.q2 (31165051305) 1 (-40))
def d2Transfer117C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 11 (-5))
def d2Transfer117S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
def d2Transfer117C1 : ℚ := (d2LitsNearTransfers014.q2 (-5) 11 (-4))
def d2Transfer117S1 : ℚ := (d2LitsNearTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer117Arithmetic : weightedUpper d2Transfer117C0 d2Log96Lo d2Log96Hi + weightedUpper d2Transfer117C1 d2Log78Lo d2Log78Hi ≤ d2Transfer117Cap := by decide +kernel
theorem d2Transfer117Bound : ∀ x ∈ Set.Icc ((d2Transfer117Lo:ℚ):ℝ) ((d2Transfer117Hi:ℚ):ℝ), ((d2Transfer117C0:ℚ):ℝ)*Real.log |x-((d2Transfer117S0:ℚ):ℝ)| + ((d2Transfer117C1:ℚ):ℝ)*Real.log |x-((d2Transfer117S1:ℚ):ℝ)| ≤ ((d2Transfer117Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer117S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer117S0,d2Transfer117Lo,d2Transfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer117C0 then |x-((d2Transfer117S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer117S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer117S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer117S0,d2Transfer117Lo,d2Transfer117Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer117C0,d2Log96Q,d2Transfer117S0,d2Transfer117Lo,d2Transfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer117C0 d2Transfer117S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have hn1 : x-((d2Transfer117S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer117S1,d2Transfer117Lo,d2Transfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer117C1 then |x-((d2Transfer117S1:ℚ):ℝ)| ≤ ((d2Log78Q:ℚ):ℝ) else ((d2Log78Q:ℚ):ℝ) ≤ |x-((d2Transfer117S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer117S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer117S1,d2Transfer117Lo,d2Transfer117Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer117C1,d2Log78Q,d2Transfer117S1,d2Transfer117Lo,d2Transfer117Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer117C1 d2Transfer117S1 d2Log78Q d2Log78Lo d2Log78Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log78Bounds
  have har : (((weightedUpper d2Transfer117C0 d2Log96Lo d2Log96Hi:ℚ):ℝ) + ((weightedUpper d2Transfer117C1 d2Log78Lo d2Log78Hi:ℚ):ℝ)) ≤ ((d2Transfer117Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer117Arithmetic
  linarith
#print axioms d2Transfer117Arithmetic
#print axioms d2Transfer117Bound
def d2Transfer118Lo : ℚ := (d2LitsNearTransfers014.q2 (34896349) 1 (-28))
def d2Transfer118Hi : ℚ := (d2LitsNearTransfers014.q2 (18287035) 1 (-27))
def d2Transfer118Cap : ℚ := (d2LitsNearTransfers014.q2 (649441385) 1 (-39))
def d2Transfer118C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 25 (-4))
def d2Transfer118S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer118Arithmetic : weightedUpper d2Transfer118C0 d2Log97Lo d2Log97Hi ≤ d2Transfer118Cap := by decide +kernel
theorem d2Transfer118Bound : ∀ x ∈ Set.Icc ((d2Transfer118Lo:ℚ):ℝ) ((d2Transfer118Hi:ℚ):ℝ), ((d2Transfer118C0:ℚ):ℝ)*Real.log |x-((d2Transfer118S0:ℚ):ℝ)| ≤ ((d2Transfer118Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer118S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer118S0,d2Transfer118Lo,d2Transfer118Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer118C0 then |x-((d2Transfer118S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer118S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer118S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer118S0,d2Transfer118Lo,d2Transfer118Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer118C0,d2Log97Q,d2Transfer118S0,d2Transfer118Lo,d2Transfer118Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer118C0 d2Transfer118S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have har : (((weightedUpper d2Transfer118C0 d2Log97Lo d2Log97Hi:ℚ):ℝ)) ≤ ((d2Transfer118Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer118Arithmetic
  linarith
#print axioms d2Transfer118Arithmetic
#print axioms d2Transfer118Bound
def d2Transfer119Lo : ℚ := (d2LitsNearTransfers014.q2 (34896349) 1 (-28))
def d2Transfer119Hi : ℚ := (d2LitsNearTransfers014.q2 (18287035) 1 (-27))
def d2Transfer119Cap : ℚ := (d2LitsNearTransfers014.q2 (2436024149) 1 (-40))
def d2Transfer119C0 : ℚ := (d2LitsNearTransfers014.q2 (1) 275 (-4))
def d2Transfer119S0 : ℚ := (d2LitsNearTransfers014.q2 (-1) 1 (0))
def d2Transfer119C1 : ℚ := (d2LitsNearTransfers014.q2 (-1) 55 (-3))
def d2Transfer119S1 : ℚ := (d2LitsNearTransfers014.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer119Arithmetic : weightedUpper d2Transfer119C0 d2Log97Lo d2Log97Hi + weightedUpper d2Transfer119C1 d2Log77Lo d2Log77Hi ≤ d2Transfer119Cap := by decide +kernel
theorem d2Transfer119Bound : ∀ x ∈ Set.Icc ((d2Transfer119Lo:ℚ):ℝ) ((d2Transfer119Hi:ℚ):ℝ), ((d2Transfer119C0:ℚ):ℝ)*Real.log |x-((d2Transfer119S0:ℚ):ℝ)| + ((d2Transfer119C1:ℚ):ℝ)*Real.log |x-((d2Transfer119S1:ℚ):ℝ)| ≤ ((d2Transfer119Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer119S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer119S0,d2Transfer119Lo,d2Transfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer119C0 then |x-((d2Transfer119S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer119S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer119S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer119S0,d2Transfer119Lo,d2Transfer119Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer119C0,d2Log97Q,d2Transfer119S0,d2Transfer119Lo,d2Transfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer119C0 d2Transfer119S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have hn1 : x-((d2Transfer119S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer119S1,d2Transfer119Lo,d2Transfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer119C1 then |x-((d2Transfer119S1:ℚ):ℝ)| ≤ ((d2Log77Q:ℚ):ℝ) else ((d2Log77Q:ℚ):ℝ) ≤ |x-((d2Transfer119S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer119S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer119S1,d2Transfer119Lo,d2Transfer119Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers014.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer119C1,d2Log77Q,d2Transfer119S1,d2Transfer119Lo,d2Transfer119Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer119C1 d2Transfer119S1 d2Log77Q d2Log77Lo d2Log77Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log77Bounds
  have har : (((weightedUpper d2Transfer119C0 d2Log97Lo d2Log97Hi:ℚ):ℝ) + ((weightedUpper d2Transfer119C1 d2Log77Lo d2Log77Hi:ℚ):ℝ)) ≤ ((d2Transfer119Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer119Arithmetic
  linarith
#print axioms d2Transfer119Arithmetic
#print axioms d2Transfer119Bound
end CatalanMeasure.GenD.Signed.Data.Cells
