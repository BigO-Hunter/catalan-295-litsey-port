module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers052
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers052
open D72.LogTransfer
def d2WiderTransfer416Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (16383) 1 (-14))
def d2WiderTransfer416Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (32767) 1 (-15))
def d2WiderTransfer416Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (2094862691217971529353) 1 (-80))
def d2WiderTransfer416C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer416S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer416Arithmetic : weightedUpper d2WiderTransfer416C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer416Cap := by decide +kernel
theorem d2WiderTransfer416Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer416Lo:ℚ):ℝ) ((d2WiderTransfer416Hi:ℚ):ℝ), ((d2WiderTransfer416C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer416S0:ℚ):ℝ)| ≤ ((d2WiderTransfer416Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer416S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer416S0,d2WiderTransfer416Lo,d2WiderTransfer416Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer416C0 then |x-((d2WiderTransfer416S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer416S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer416S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer416S0,d2WiderTransfer416Lo,d2WiderTransfer416Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer416C0,d2Log181Q,d2WiderTransfer416S0,d2WiderTransfer416Lo,d2WiderTransfer416Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer416C0 d2WiderTransfer416S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer416C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer416Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer416Arithmetic
  linarith
#print axioms d2WiderTransfer416Arithmetic
#print axioms d2WiderTransfer416Bound
def d2WiderTransfer417Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (32767) 1 (-15))
def d2WiderTransfer417Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (65535) 1 (-16))
def d2WiderTransfer417Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (261860771103234971425) 1 (-77))
def d2WiderTransfer417C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer417S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer417Arithmetic : weightedUpper d2WiderTransfer417C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer417Cap := by decide +kernel
theorem d2WiderTransfer417Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer417Lo:ℚ):ℝ) ((d2WiderTransfer417Hi:ℚ):ℝ), ((d2WiderTransfer417C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer417S0:ℚ):ℝ)| ≤ ((d2WiderTransfer417Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer417S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer417S0,d2WiderTransfer417Lo,d2WiderTransfer417Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer417C0 then |x-((d2WiderTransfer417S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer417S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer417S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer417S0,d2WiderTransfer417Lo,d2WiderTransfer417Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer417C0,d2Log182Q,d2WiderTransfer417S0,d2WiderTransfer417Lo,d2WiderTransfer417Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer417C0 d2WiderTransfer417S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer417C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer417Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer417Arithmetic
  linarith
#print axioms d2WiderTransfer417Arithmetic
#print axioms d2WiderTransfer417Bound
def d2WiderTransfer418Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (32767) 1 (-15))
def d2WiderTransfer418Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (65535) 1 (-16))
def d2WiderTransfer418Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (261860718738993698593) 1 (-77))
def d2WiderTransfer418C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer418S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer418Arithmetic : weightedUpper d2WiderTransfer418C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer418Cap := by decide +kernel
theorem d2WiderTransfer418Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer418Lo:ℚ):ℝ) ((d2WiderTransfer418Hi:ℚ):ℝ), ((d2WiderTransfer418C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer418S0:ℚ):ℝ)| ≤ ((d2WiderTransfer418Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer418S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer418S0,d2WiderTransfer418Lo,d2WiderTransfer418Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer418C0 then |x-((d2WiderTransfer418S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer418S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer418S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer418S0,d2WiderTransfer418Lo,d2WiderTransfer418Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer418C0,d2Log182Q,d2WiderTransfer418S0,d2WiderTransfer418Lo,d2WiderTransfer418Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer418C0 d2WiderTransfer418S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer418C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer418Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer418Arithmetic
  linarith
#print axioms d2WiderTransfer418Arithmetic
#print axioms d2WiderTransfer418Bound
def d2WiderTransfer419Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (65535) 1 (-16))
def d2WiderTransfer419Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (131071) 1 (-17))
def d2WiderTransfer419Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (2094897698106896929007) 1 (-80))
def d2WiderTransfer419C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer419S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer419Arithmetic : weightedUpper d2WiderTransfer419C0 d2Log183Lo d2Log183Hi ≤ d2WiderTransfer419Cap := by decide +kernel
theorem d2WiderTransfer419Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer419Lo:ℚ):ℝ) ((d2WiderTransfer419Hi:ℚ):ℝ), ((d2WiderTransfer419C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer419S0:ℚ):ℝ)| ≤ ((d2WiderTransfer419Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer419S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer419S0,d2WiderTransfer419Lo,d2WiderTransfer419Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer419C0 then |x-((d2WiderTransfer419S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer419S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer419S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer419S0,d2WiderTransfer419Lo,d2WiderTransfer419Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer419C0,d2Log183Q,d2WiderTransfer419S0,d2WiderTransfer419Lo,d2WiderTransfer419Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer419C0 d2WiderTransfer419S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2WiderTransfer419C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer419Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer419Arithmetic
  linarith
#print axioms d2WiderTransfer419Arithmetic
#print axioms d2WiderTransfer419Bound
def d2WiderTransfer420Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (65535) 1 (-16))
def d2WiderTransfer420Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (131071) 1 (-17))
def d2WiderTransfer420Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (2094897279192966746351) 1 (-80))
def d2WiderTransfer420C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer420S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer420Arithmetic : weightedUpper d2WiderTransfer420C0 d2Log183Lo d2Log183Hi ≤ d2WiderTransfer420Cap := by decide +kernel
theorem d2WiderTransfer420Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer420Lo:ℚ):ℝ) ((d2WiderTransfer420Hi:ℚ):ℝ), ((d2WiderTransfer420C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer420S0:ℚ):ℝ)| ≤ ((d2WiderTransfer420Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer420S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer420S0,d2WiderTransfer420Lo,d2WiderTransfer420Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer420C0 then |x-((d2WiderTransfer420S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer420S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer420S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer420S0,d2WiderTransfer420Lo,d2WiderTransfer420Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer420C0,d2Log183Q,d2WiderTransfer420S0,d2WiderTransfer420Lo,d2WiderTransfer420Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer420C0 d2WiderTransfer420S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2WiderTransfer420C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer420Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer420Arithmetic
  linarith
#print axioms d2WiderTransfer420Arithmetic
#print axioms d2WiderTransfer420Bound
def d2WiderTransfer421Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (131071) 1 (-17))
def d2WiderTransfer421Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (262143) 1 (-18))
def d2WiderTransfer421Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (4091608325646313841) 1 (-71))
def d2WiderTransfer421C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer421S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer421Arithmetic : weightedUpper d2WiderTransfer421C0 d2Log184Lo d2Log184Hi ≤ d2WiderTransfer421Cap := by decide +kernel
theorem d2WiderTransfer421Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer421Lo:ℚ):ℝ) ((d2WiderTransfer421Hi:ℚ):ℝ), ((d2WiderTransfer421C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer421S0:ℚ):ℝ)| ≤ ((d2WiderTransfer421Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer421S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer421S0,d2WiderTransfer421Lo,d2WiderTransfer421Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer421C0 then |x-((d2WiderTransfer421S0:ℚ):ℝ)| ≤ ((d2Log184Q:ℚ):ℝ) else ((d2Log184Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer421S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer421S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer421S0,d2WiderTransfer421Lo,d2WiderTransfer421Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer421C0,d2Log184Q,d2WiderTransfer421S0,d2WiderTransfer421Lo,d2WiderTransfer421Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer421C0 d2WiderTransfer421S0 d2Log184Q d2Log184Lo d2Log184Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log184Bounds
  have har : (((weightedUpper d2WiderTransfer421C0 d2Log184Lo d2Log184Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer421Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer421Arithmetic
  linarith
#print axioms d2WiderTransfer421Arithmetic
#print axioms d2WiderTransfer421Bound
def d2WiderTransfer422Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (131071) 1 (-17))
def d2WiderTransfer422Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (262143) 1 (-18))
def d2WiderTransfer422Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (4091607507455043953) 1 (-71))
def d2WiderTransfer422C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer422S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer422Arithmetic : weightedUpper d2WiderTransfer422C0 d2Log184Lo d2Log184Hi ≤ d2WiderTransfer422Cap := by decide +kernel
theorem d2WiderTransfer422Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer422Lo:ℚ):ℝ) ((d2WiderTransfer422Hi:ℚ):ℝ), ((d2WiderTransfer422C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer422S0:ℚ):ℝ)| ≤ ((d2WiderTransfer422Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer422S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer422S0,d2WiderTransfer422Lo,d2WiderTransfer422Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer422C0 then |x-((d2WiderTransfer422S0:ℚ):ℝ)| ≤ ((d2Log184Q:ℚ):ℝ) else ((d2Log184Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer422S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer422S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer422S0,d2WiderTransfer422Lo,d2WiderTransfer422Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer422C0,d2Log184Q,d2WiderTransfer422S0,d2WiderTransfer422Lo,d2WiderTransfer422Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer422C0 d2WiderTransfer422S0 d2Log184Q d2Log184Lo d2Log184Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log184Bounds
  have har : (((weightedUpper d2WiderTransfer422C0 d2Log184Lo d2Log184Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer422Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer422Arithmetic
  linarith
#print axioms d2WiderTransfer422Arithmetic
#print axioms d2WiderTransfer422Bound
def d2WiderTransfer423Lo : ℚ := (d2LitsNearWiderTransfers052.q2 (262143) 1 (-18))
def d2WiderTransfer423Hi : ℚ := (d2LitsNearWiderTransfers052.q2 (524287) 1 (-19))
def d2WiderTransfer423Cap : ℚ := (d2LitsNearWiderTransfers052.q2 (1047453172519398689215) 1 (-79))
def d2WiderTransfer423C0 : ℚ := (d2LitsNearWiderTransfers052.q2 (1) 25 (-4))
def d2WiderTransfer423S0 : ℚ := (d2LitsNearWiderTransfers052.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer423Arithmetic : weightedUpper d2WiderTransfer423C0 d2Log185Lo d2Log185Hi ≤ d2WiderTransfer423Cap := by decide +kernel
theorem d2WiderTransfer423Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer423Lo:ℚ):ℝ) ((d2WiderTransfer423Hi:ℚ):ℝ), ((d2WiderTransfer423C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer423S0:ℚ):ℝ)| ≤ ((d2WiderTransfer423Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer423S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer423S0,d2WiderTransfer423Lo,d2WiderTransfer423Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer423C0 then |x-((d2WiderTransfer423S0:ℚ):ℝ)| ≤ ((d2Log185Q:ℚ):ℝ) else ((d2Log185Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer423S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer423S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer423S0,d2WiderTransfer423Lo,d2WiderTransfer423Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers052.q2, d2LitsNearLogCache011.q2, d2WiderTransfer423C0,d2Log185Q,d2WiderTransfer423S0,d2WiderTransfer423Lo,d2WiderTransfer423Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer423C0 d2WiderTransfer423S0 d2Log185Q d2Log185Lo d2Log185Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log185Bounds
  have har : (((weightedUpper d2WiderTransfer423C0 d2Log185Lo d2Log185Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer423Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer423Arithmetic
  linarith
#print axioms d2WiderTransfer423Arithmetic
#print axioms d2WiderTransfer423Bound
end CatalanMeasure.GenD.Signed.Data.Cells
