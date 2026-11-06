module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers058
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers058
open D72.LogTransfer
def d2WiderTransfer464Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (999) 125 (-3))
def d2WiderTransfer464Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (16760439) 1 (-24))
def d2WiderTransfer464Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (6018517399047162615887) 1 (-78))
def d2WiderTransfer464C0 : ℚ := (d2LitsNearWiderTransfers058.q2 (23) 25 (-5))
def d2WiderTransfer464S0 : ℚ := (d2LitsNearWiderTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer464Arithmetic : weightedUpper d2WiderTransfer464C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer464Cap := by decide +kernel
theorem d2WiderTransfer464Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer464Lo:ℚ):ℝ) ((d2WiderTransfer464Hi:ℚ):ℝ), ((d2WiderTransfer464C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer464S0:ℚ):ℝ)| ≤ ((d2WiderTransfer464Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer464S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer464S0,d2WiderTransfer464Lo,d2WiderTransfer464Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer464C0 then |x-((d2WiderTransfer464S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer464S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer464S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer464S0,d2WiderTransfer464Lo,d2WiderTransfer464Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer464C0,d2Log175Q,d2WiderTransfer464S0,d2WiderTransfer464Lo,d2WiderTransfer464Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer464C0 d2WiderTransfer464S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer464C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer464Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer464Arithmetic
  linarith
#print axioms d2WiderTransfer464Arithmetic
#print axioms d2WiderTransfer464Bound
def d2WiderTransfer465Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (999) 125 (-3))
def d2WiderTransfer465Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (16760439) 1 (-24))
def d2WiderTransfer465Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (6018517216528232405071) 1 (-78))
def d2WiderTransfer465C0 : ℚ := (d2LitsNearWiderTransfers058.q2 (23) 25 (-5))
def d2WiderTransfer465S0 : ℚ := (d2LitsNearWiderTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer465Arithmetic : weightedUpper d2WiderTransfer465C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer465Cap := by decide +kernel
theorem d2WiderTransfer465Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer465Lo:ℚ):ℝ) ((d2WiderTransfer465Hi:ℚ):ℝ), ((d2WiderTransfer465C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer465S0:ℚ):ℝ)| ≤ ((d2WiderTransfer465Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer465S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer465S0,d2WiderTransfer465Lo,d2WiderTransfer465Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer465C0 then |x-((d2WiderTransfer465S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer465S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer465S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer465S0,d2WiderTransfer465Lo,d2WiderTransfer465Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer465C0,d2Log175Q,d2WiderTransfer465S0,d2WiderTransfer465Lo,d2WiderTransfer465Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer465C0 d2WiderTransfer465S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer465C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer465Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer465Arithmetic
  linarith
#print axioms d2WiderTransfer465Arithmetic
#print axioms d2WiderTransfer465Bound
def d2WiderTransfer466Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (16760439) 1 (-24))
def d2WiderTransfer466Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (1023) 1 (-10))
def d2WiderTransfer466Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (51031128082795455) 1 (-77))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer466Arithmetic : (0 : ℚ) ≤ d2WiderTransfer466Cap := by decide +kernel
theorem d2WiderTransfer466Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer466Lo:ℚ):ℝ) ((d2WiderTransfer466Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer466Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer466Arithmetic
#print axioms d2WiderTransfer466Arithmetic
#print axioms d2WiderTransfer466Bound
def d2WiderTransfer467Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (16760439) 1 (-24))
def d2WiderTransfer467Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (1023) 1 (-10))
def d2WiderTransfer467Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (3009309609726507273151) 1 (-77))
def d2WiderTransfer467C0 : ℚ := (d2LitsNearWiderTransfers058.q2 (23) 25 (-5))
def d2WiderTransfer467S0 : ℚ := (d2LitsNearWiderTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer467Arithmetic : weightedUpper d2WiderTransfer467C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer467Cap := by decide +kernel
theorem d2WiderTransfer467Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer467Lo:ℚ):ℝ) ((d2WiderTransfer467Hi:ℚ):ℝ), ((d2WiderTransfer467C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer467S0:ℚ):ℝ)| ≤ ((d2WiderTransfer467Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer467S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer467S0,d2WiderTransfer467Lo,d2WiderTransfer467Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer467C0 then |x-((d2WiderTransfer467S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer467S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer467S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer467S0,d2WiderTransfer467Lo,d2WiderTransfer467Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer467C0,d2Log176Q,d2WiderTransfer467S0,d2WiderTransfer467Lo,d2WiderTransfer467Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer467C0 d2WiderTransfer467S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer467C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer467Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer467Arithmetic
  linarith
#print axioms d2WiderTransfer467Arithmetic
#print axioms d2WiderTransfer467Bound
def d2WiderTransfer468Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (16760439) 1 (-24))
def d2WiderTransfer468Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (1023) 1 (-10))
def d2WiderTransfer468Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (3009309518467042167743) 1 (-77))
def d2WiderTransfer468C0 : ℚ := (d2LitsNearWiderTransfers058.q2 (23) 25 (-5))
def d2WiderTransfer468S0 : ℚ := (d2LitsNearWiderTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer468Arithmetic : weightedUpper d2WiderTransfer468C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer468Cap := by decide +kernel
theorem d2WiderTransfer468Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer468Lo:ℚ):ℝ) ((d2WiderTransfer468Hi:ℚ):ℝ), ((d2WiderTransfer468C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer468S0:ℚ):ℝ)| ≤ ((d2WiderTransfer468Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer468S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer468S0,d2WiderTransfer468Lo,d2WiderTransfer468Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer468C0 then |x-((d2WiderTransfer468S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer468S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer468S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer468S0,d2WiderTransfer468Lo,d2WiderTransfer468Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer468C0,d2Log176Q,d2WiderTransfer468S0,d2WiderTransfer468Lo,d2WiderTransfer468Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer468C0 d2WiderTransfer468S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer468C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer468Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer468Arithmetic
  linarith
#print axioms d2WiderTransfer468Arithmetic
#print axioms d2WiderTransfer468Bound
def d2WiderTransfer469Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (1023) 1 (-10))
def d2WiderTransfer469Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (2047) 1 (-11))
def d2WiderTransfer469Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (8896859962917361653) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer469Arithmetic : (0 : ℚ) ≤ d2WiderTransfer469Cap := by decide +kernel
theorem d2WiderTransfer469Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer469Lo:ℚ):ℝ) ((d2WiderTransfer469Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer469Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer469Arithmetic
#print axioms d2WiderTransfer469Arithmetic
#print axioms d2WiderTransfer469Bound
def d2WiderTransfer470Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (1023) 1 (-10))
def d2WiderTransfer470Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (2047) 1 (-11))
def d2WiderTransfer470Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (24082965488750313183221) 1 (-80))
def d2WiderTransfer470C0 : ℚ := (d2LitsNearWiderTransfers058.q2 (23) 25 (-5))
def d2WiderTransfer470S0 : ℚ := (d2LitsNearWiderTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer470Arithmetic : weightedUpper d2WiderTransfer470C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer470Cap := by decide +kernel
theorem d2WiderTransfer470Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer470Lo:ℚ):ℝ) ((d2WiderTransfer470Hi:ℚ):ℝ), ((d2WiderTransfer470C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer470S0:ℚ):ℝ)| ≤ ((d2WiderTransfer470Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer470S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer470S0,d2WiderTransfer470Lo,d2WiderTransfer470Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer470C0 then |x-((d2WiderTransfer470S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer470S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer470S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer470S0,d2WiderTransfer470Lo,d2WiderTransfer470Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer470C0,d2Log177Q,d2WiderTransfer470S0,d2WiderTransfer470Lo,d2WiderTransfer470Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer470C0 d2WiderTransfer470S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer470C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer470Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer470Arithmetic
  linarith
#print axioms d2WiderTransfer470Arithmetic
#print axioms d2WiderTransfer470Bound
def d2WiderTransfer471Lo : ℚ := (d2LitsNearWiderTransfers058.q2 (1023) 1 (-10))
def d2WiderTransfer471Hi : ℚ := (d2LitsNearWiderTransfers058.q2 (2047) 1 (-11))
def d2WiderTransfer471Cap : ℚ := (d2LitsNearWiderTransfers058.q2 (24082964758674592339957) 1 (-80))
def d2WiderTransfer471C0 : ℚ := (d2LitsNearWiderTransfers058.q2 (23) 25 (-5))
def d2WiderTransfer471S0 : ℚ := (d2LitsNearWiderTransfers058.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer471Arithmetic : weightedUpper d2WiderTransfer471C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer471Cap := by decide +kernel
theorem d2WiderTransfer471Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer471Lo:ℚ):ℝ) ((d2WiderTransfer471Hi:ℚ):ℝ), ((d2WiderTransfer471C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer471S0:ℚ):ℝ)| ≤ ((d2WiderTransfer471Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer471S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer471S0,d2WiderTransfer471Lo,d2WiderTransfer471Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer471C0 then |x-((d2WiderTransfer471S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer471S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer471S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer471S0,d2WiderTransfer471Lo,d2WiderTransfer471Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers058.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer471C0,d2Log177Q,d2WiderTransfer471S0,d2WiderTransfer471Lo,d2WiderTransfer471Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer471C0 d2WiderTransfer471S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer471C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer471Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer471Arithmetic
  linarith
#print axioms d2WiderTransfer471Arithmetic
#print axioms d2WiderTransfer471Bound
end CatalanMeasure.GenD.Signed.Data.Cells
