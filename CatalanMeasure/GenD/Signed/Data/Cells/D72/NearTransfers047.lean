module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers047
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers047
open D72.LogTransfer
def d2Transfer376Lo : ℚ := (d2LitsNearTransfers047.q2 (16756223) 1 (-24))
def d2Transfer376Hi : ℚ := (d2LitsNearTransfers047.q2 (8380219) 1 (-23))
def d2Transfer376Cap : ℚ := (d2LitsNearTransfers047.q2 (223255705535961194743809) 1 (-80))
def d2Transfer376C0 : ℚ := (d2LitsNearTransfers047.q2 (1) 1 (-5))
def d2Transfer376S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer376Arithmetic : weightedUpper d2Transfer376C0 d2Log173Lo d2Log173Hi ≤ d2Transfer376Cap := by decide +kernel
theorem d2Transfer376Bound : ∀ x ∈ Set.Icc ((d2Transfer376Lo:ℚ):ℝ) ((d2Transfer376Hi:ℚ):ℝ), ((d2Transfer376C0:ℚ):ℝ)*Real.log |x-((d2Transfer376S0:ℚ):ℝ)| ≤ ((d2Transfer376Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer376S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer376S0,d2Transfer376Lo,d2Transfer376Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer376C0 then |x-((d2Transfer376S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer376S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer376S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer376S0,d2Transfer376Lo,d2Transfer376Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer376C0,d2Log173Q,d2Transfer376S0,d2Transfer376Lo,d2Transfer376Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer376C0 d2Transfer376S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2Transfer376C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2Transfer376Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer376Arithmetic
  linarith
#print axioms d2Transfer376Arithmetic
#print axioms d2Transfer376Bound
def d2Transfer377Lo : ℚ := (d2LitsNearTransfers047.q2 (16756223) 1 (-24))
def d2Transfer377Hi : ℚ := (d2LitsNearTransfers047.q2 (8380219) 1 (-23))
def d2Transfer377Cap : ℚ := (d2LitsNearTransfers047.q2 (239620542858252702107649) 1 (-80))
def d2Transfer377C0 : ℚ := (d2LitsNearTransfers047.q2 (1) 11 (-5))
def d2Transfer377S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
def d2Transfer377C1 : ℚ := (d2LitsNearTransfers047.q2 (-5) 11 (-4))
def d2Transfer377S1 : ℚ := (d2LitsNearTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer377Arithmetic : weightedUpper d2Transfer377C0 d2Log173Lo d2Log173Hi + weightedUpper d2Transfer377C1 d2Log1Lo d2Log1Hi ≤ d2Transfer377Cap := by decide +kernel
theorem d2Transfer377Bound : ∀ x ∈ Set.Icc ((d2Transfer377Lo:ℚ):ℝ) ((d2Transfer377Hi:ℚ):ℝ), ((d2Transfer377C0:ℚ):ℝ)*Real.log |x-((d2Transfer377S0:ℚ):ℝ)| + ((d2Transfer377C1:ℚ):ℝ)*Real.log |x-((d2Transfer377S1:ℚ):ℝ)| ≤ ((d2Transfer377Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer377S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer377S0,d2Transfer377Lo,d2Transfer377Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer377C0 then |x-((d2Transfer377S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer377S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer377S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer377S0,d2Transfer377Lo,d2Transfer377Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer377C0,d2Log173Q,d2Transfer377S0,d2Transfer377Lo,d2Transfer377Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer377C0 d2Transfer377S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2Transfer377S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer377S1,d2Transfer377Lo,d2Transfer377Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer377C1 then |x-((d2Transfer377S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2Transfer377S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer377S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer377S1,d2Transfer377Lo,d2Transfer377Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer377C1,d2Log1Q,d2Transfer377S1,d2Transfer377Lo,d2Transfer377Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer377C1 d2Transfer377S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2Transfer377C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2Transfer377C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2Transfer377Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer377Arithmetic
  linarith
#print axioms d2Transfer377Arithmetic
#print axioms d2Transfer377Bound
def d2Transfer378Lo : ℚ := (d2LitsNearTransfers047.q2 (8380219) 1 (-23))
def d2Transfer378Hi : ℚ := (d2LitsNearTransfers047.q2 (999) 125 (-3))
def d2Transfer378Cap : ℚ := (d2LitsNearTransfers047.q2 (206783948238830734700547) 1 (-80))
def d2Transfer378C0 : ℚ := (d2LitsNearTransfers047.q2 (1) 25 (-4))
def d2Transfer378S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer378Arithmetic : weightedUpper d2Transfer378C0 d2Log174Lo d2Log174Hi ≤ d2Transfer378Cap := by decide +kernel
theorem d2Transfer378Bound : ∀ x ∈ Set.Icc ((d2Transfer378Lo:ℚ):ℝ) ((d2Transfer378Hi:ℚ):ℝ), ((d2Transfer378C0:ℚ):ℝ)*Real.log |x-((d2Transfer378S0:ℚ):ℝ)| ≤ ((d2Transfer378Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer378S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer378S0,d2Transfer378Lo,d2Transfer378Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer378C0 then |x-((d2Transfer378S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer378S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer378S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer378S0,d2Transfer378Lo,d2Transfer378Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer378C0,d2Log174Q,d2Transfer378S0,d2Transfer378Lo,d2Transfer378Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer378C0 d2Transfer378S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2Transfer378C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2Transfer378Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer378Arithmetic
  linarith
#print axioms d2Transfer378Arithmetic
#print axioms d2Transfer378Bound
def d2Transfer379Lo : ℚ := (d2LitsNearTransfers047.q2 (8380219) 1 (-23))
def d2Transfer379Hi : ℚ := (d2LitsNearTransfers047.q2 (999) 125 (-3))
def d2Transfer379Cap : ℚ := (d2LitsNearTransfers047.q2 (208034248407466470043651) 1 (-80))
def d2Transfer379C0 : ℚ := (d2LitsNearTransfers047.q2 (1) 275 (-4))
def d2Transfer379S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
def d2Transfer379C1 : ℚ := (d2LitsNearTransfers047.q2 (-1) 55 (-3))
def d2Transfer379S1 : ℚ := (d2LitsNearTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer379Arithmetic : weightedUpper d2Transfer379C0 d2Log174Lo d2Log174Hi + weightedUpper d2Transfer379C1 d2Log0Lo d2Log0Hi ≤ d2Transfer379Cap := by decide +kernel
theorem d2Transfer379Bound : ∀ x ∈ Set.Icc ((d2Transfer379Lo:ℚ):ℝ) ((d2Transfer379Hi:ℚ):ℝ), ((d2Transfer379C0:ℚ):ℝ)*Real.log |x-((d2Transfer379S0:ℚ):ℝ)| + ((d2Transfer379C1:ℚ):ℝ)*Real.log |x-((d2Transfer379S1:ℚ):ℝ)| ≤ ((d2Transfer379Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer379S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer379S0,d2Transfer379Lo,d2Transfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer379C0 then |x-((d2Transfer379S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer379S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer379S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer379S0,d2Transfer379Lo,d2Transfer379Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer379C0,d2Log174Q,d2Transfer379S0,d2Transfer379Lo,d2Transfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer379C0 d2Transfer379S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2Transfer379S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer379S1,d2Transfer379Lo,d2Transfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer379C1 then |x-((d2Transfer379S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2Transfer379S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer379S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer379S1,d2Transfer379Lo,d2Transfer379Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer379C1,d2Log0Q,d2Transfer379S1,d2Transfer379Lo,d2Transfer379Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer379C1 d2Transfer379S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2Transfer379C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2Transfer379C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2Transfer379Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer379Arithmetic
  linarith
#print axioms d2Transfer379Arithmetic
#print axioms d2Transfer379Bound
def d2Transfer380Lo : ℚ := (d2LitsNearTransfers047.q2 (8380219) 1 (-23))
def d2Transfer380Hi : ℚ := (d2LitsNearTransfers047.q2 (999) 125 (-3))
def d2Transfer380Cap : ℚ := (d2LitsNearTransfers047.q2 (223257310497889430564867) 1 (-80))
def d2Transfer380C0 : ℚ := (d2LitsNearTransfers047.q2 (1) 1 (-5))
def d2Transfer380S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer380Arithmetic : weightedUpper d2Transfer380C0 d2Log174Lo d2Log174Hi ≤ d2Transfer380Cap := by decide +kernel
theorem d2Transfer380Bound : ∀ x ∈ Set.Icc ((d2Transfer380Lo:ℚ):ℝ) ((d2Transfer380Hi:ℚ):ℝ), ((d2Transfer380C0:ℚ):ℝ)*Real.log |x-((d2Transfer380S0:ℚ):ℝ)| ≤ ((d2Transfer380Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer380S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer380S0,d2Transfer380Lo,d2Transfer380Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer380C0 then |x-((d2Transfer380S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer380S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer380S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer380S0,d2Transfer380Lo,d2Transfer380Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer380C0,d2Log174Q,d2Transfer380S0,d2Transfer380Lo,d2Transfer380Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer380C0 d2Transfer380S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2Transfer380C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2Transfer380Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer380Arithmetic
  linarith
#print axioms d2Transfer380Arithmetic
#print axioms d2Transfer380Bound
def d2Transfer381Lo : ℚ := (d2LitsNearTransfers047.q2 (8380219) 1 (-23))
def d2Transfer381Hi : ℚ := (d2LitsNearTransfers047.q2 (999) 125 (-3))
def d2Transfer381Cap : ℚ := (d2LitsNearTransfers047.q2 (239622147820180937928707) 1 (-80))
def d2Transfer381C0 : ℚ := (d2LitsNearTransfers047.q2 (1) 11 (-5))
def d2Transfer381S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
def d2Transfer381C1 : ℚ := (d2LitsNearTransfers047.q2 (-5) 11 (-4))
def d2Transfer381S1 : ℚ := (d2LitsNearTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer381Arithmetic : weightedUpper d2Transfer381C0 d2Log174Lo d2Log174Hi + weightedUpper d2Transfer381C1 d2Log0Lo d2Log0Hi ≤ d2Transfer381Cap := by decide +kernel
theorem d2Transfer381Bound : ∀ x ∈ Set.Icc ((d2Transfer381Lo:ℚ):ℝ) ((d2Transfer381Hi:ℚ):ℝ), ((d2Transfer381C0:ℚ):ℝ)*Real.log |x-((d2Transfer381S0:ℚ):ℝ)| + ((d2Transfer381C1:ℚ):ℝ)*Real.log |x-((d2Transfer381S1:ℚ):ℝ)| ≤ ((d2Transfer381Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer381S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer381S0,d2Transfer381Lo,d2Transfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer381C0 then |x-((d2Transfer381S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer381S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer381S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer381S0,d2Transfer381Lo,d2Transfer381Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer381C0,d2Log174Q,d2Transfer381S0,d2Transfer381Lo,d2Transfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer381C0 d2Transfer381S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2Transfer381S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer381S1,d2Transfer381Lo,d2Transfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer381C1 then |x-((d2Transfer381S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2Transfer381S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer381S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer381S1,d2Transfer381Lo,d2Transfer381Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer381C1,d2Log0Q,d2Transfer381S1,d2Transfer381Lo,d2Transfer381Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer381C1 d2Transfer381S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2Transfer381C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2Transfer381C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2Transfer381Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer381Arithmetic
  linarith
#print axioms d2Transfer381Arithmetic
#print axioms d2Transfer381Bound
def d2Transfer382Lo : ℚ := (d2LitsNearTransfers047.q2 (98749) 15625 (-6))
def d2Transfer382Hi : ℚ := (d2LitsNearTransfers047.q2 (828367) 1 (-23))
def d2Transfer382Cap : ℚ := (d2LitsNearTransfers047.q2 (1169469059) 1 (-40))
def d2Transfer382C0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 55 (-3))
def d2Transfer382S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
def d2Transfer382C1 : ℚ := (d2LitsNearTransfers047.q2 (-1) 55 (-3))
def d2Transfer382S1 : ℚ := (d2LitsNearTransfers047.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer382Arithmetic : weightedUpper d2Transfer382C0 d2Log87Lo d2Log87Hi + weightedUpper d2Transfer382C1 d2Log86Lo d2Log86Hi ≤ d2Transfer382Cap := by decide +kernel
theorem d2Transfer382Bound : ∀ x ∈ Set.Icc ((d2Transfer382Lo:ℚ):ℝ) ((d2Transfer382Hi:ℚ):ℝ), ((d2Transfer382C0:ℚ):ℝ)*Real.log |x-((d2Transfer382S0:ℚ):ℝ)| + ((d2Transfer382C1:ℚ):ℝ)*Real.log |x-((d2Transfer382S1:ℚ):ℝ)| ≤ ((d2Transfer382Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer382S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer382S0,d2Transfer382Lo,d2Transfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer382C0 then |x-((d2Transfer382S0:ℚ):ℝ)| ≤ ((d2Log87Q:ℚ):ℝ) else ((d2Log87Q:ℚ):ℝ) ≤ |x-((d2Transfer382S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer382S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer382S0,d2Transfer382Lo,d2Transfer382Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer382C0,d2Log87Q,d2Transfer382S0,d2Transfer382Lo,d2Transfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer382C0 d2Transfer382S0 d2Log87Q d2Log87Lo d2Log87Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log87Bounds
  have hn1 : x-((d2Transfer382S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer382S1,d2Transfer382Lo,d2Transfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer382C1 then |x-((d2Transfer382S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2Transfer382S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer382S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer382S1,d2Transfer382Lo,d2Transfer382Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer382C1,d2Log86Q,d2Transfer382S1,d2Transfer382Lo,d2Transfer382Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer382C1 d2Transfer382S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2Transfer382C0 d2Log87Lo d2Log87Hi:ℚ):ℝ) + ((weightedUpper d2Transfer382C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2Transfer382Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer382Arithmetic
  linarith
#print axioms d2Transfer382Arithmetic
#print axioms d2Transfer382Bound
def d2Transfer383Lo : ℚ := (d2LitsNearTransfers047.q2 (98749) 15625 (-6))
def d2Transfer383Hi : ℚ := (d2LitsNearTransfers047.q2 (828367) 1 (-23))
def d2Transfer383Cap : ℚ := (d2LitsNearTransfers047.q2 (15113656175) 1 (-40))
def d2Transfer383C0 : ℚ := (d2LitsNearTransfers047.q2 (23) 25 (-5))
def d2Transfer383S0 : ℚ := (d2LitsNearTransfers047.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer383Arithmetic : weightedUpper d2Transfer383C0 d2Log88Lo d2Log88Hi ≤ d2Transfer383Cap := by decide +kernel
theorem d2Transfer383Bound : ∀ x ∈ Set.Icc ((d2Transfer383Lo:ℚ):ℝ) ((d2Transfer383Hi:ℚ):ℝ), ((d2Transfer383C0:ℚ):ℝ)*Real.log |x-((d2Transfer383S0:ℚ):ℝ)| ≤ ((d2Transfer383Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer383S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer383S0,d2Transfer383Lo,d2Transfer383Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer383C0 then |x-((d2Transfer383S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer383S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer383S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer383S0,d2Transfer383Lo,d2Transfer383Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers047.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer383C0,d2Log88Q,d2Transfer383S0,d2Transfer383Lo,d2Transfer383Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer383C0 d2Transfer383S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2Transfer383C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2Transfer383Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer383Arithmetic
  linarith
#print axioms d2Transfer383Arithmetic
#print axioms d2Transfer383Bound
end CatalanMeasure.GenD.Signed.Data.Cells
