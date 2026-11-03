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
namespace d2LitsNearTransfers010
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers010
open D72.LogTransfer
def d2Transfer80Lo : ℚ := (d2LitsNearTransfers010.q2 (31834725) 1 (-25))
def d2Transfer80Hi : ℚ := (d2LitsNearTransfers010.q2 (16756223) 1 (-24))
def d2Transfer80Cap : ℚ := (d2LitsNearTransfers010.q2 (17306181503079751321725) 1 (-80))
def d2Transfer80C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 25 (-4))
def d2Transfer80S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer80Arithmetic : weightedUpper d2Transfer80C0 d2Log172Lo d2Log172Hi ≤ d2Transfer80Cap := by decide +kernel
theorem d2Transfer80Bound : ∀ x ∈ Set.Icc ((d2Transfer80Lo:ℚ):ℝ) ((d2Transfer80Hi:ℚ):ℝ), ((d2Transfer80C0:ℚ):ℝ)*Real.log |x-((d2Transfer80S0:ℚ):ℝ)| ≤ ((d2Transfer80Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer80S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer80S0,d2Transfer80Lo,d2Transfer80Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer80C0 then |x-((d2Transfer80S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer80S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer80S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer80S0,d2Transfer80Lo,d2Transfer80Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer80C0,d2Log172Q,d2Transfer80S0,d2Transfer80Lo,d2Transfer80Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer80C0 d2Transfer80S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2Transfer80C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2Transfer80Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer80Arithmetic
  linarith
#print axioms d2Transfer80Arithmetic
#print axioms d2Transfer80Bound
def d2Transfer81Lo : ℚ := (d2LitsNearTransfers010.q2 (31834725) 1 (-25))
def d2Transfer81Hi : ℚ := (d2LitsNearTransfers010.q2 (16756223) 1 (-24))
def d2Transfer81Cap : ℚ := (d2LitsNearTransfers010.q2 (18553824547935338072189) 1 (-80))
def d2Transfer81C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 275 (-4))
def d2Transfer81S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
def d2Transfer81C1 : ℚ := (d2LitsNearTransfers010.q2 (-1) 55 (-3))
def d2Transfer81S1 : ℚ := (d2LitsNearTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer81Arithmetic : weightedUpper d2Transfer81C0 d2Log172Lo d2Log172Hi + weightedUpper d2Transfer81C1 d2Log2Lo d2Log2Hi ≤ d2Transfer81Cap := by decide +kernel
theorem d2Transfer81Bound : ∀ x ∈ Set.Icc ((d2Transfer81Lo:ℚ):ℝ) ((d2Transfer81Hi:ℚ):ℝ), ((d2Transfer81C0:ℚ):ℝ)*Real.log |x-((d2Transfer81S0:ℚ):ℝ)| + ((d2Transfer81C1:ℚ):ℝ)*Real.log |x-((d2Transfer81S1:ℚ):ℝ)| ≤ ((d2Transfer81Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer81S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer81S0,d2Transfer81Lo,d2Transfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer81C0 then |x-((d2Transfer81S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer81S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer81S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer81S0,d2Transfer81Lo,d2Transfer81Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer81C0,d2Log172Q,d2Transfer81S0,d2Transfer81Lo,d2Transfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer81C0 d2Transfer81S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2Transfer81S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer81S1,d2Transfer81Lo,d2Transfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer81C1 then |x-((d2Transfer81S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2Transfer81S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer81S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer81S1,d2Transfer81Lo,d2Transfer81Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer81C1,d2Log2Q,d2Transfer81S1,d2Transfer81Lo,d2Transfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer81C1 d2Transfer81S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2Transfer81C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2Transfer81C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2Transfer81Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer81Arithmetic
  linarith
#print axioms d2Transfer81Arithmetic
#print axioms d2Transfer81Bound
def d2Transfer82Lo : ℚ := (d2LitsNearTransfers010.q2 (16756223) 1 (-24))
def d2Transfer82Hi : ℚ := (d2LitsNearTransfers010.q2 (8380219) 1 (-23))
def d2Transfer82Cap : ℚ := (d2LitsNearTransfers010.q2 (4480500095951157354537) 1 (-78))
def d2Transfer82C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 25 (-4))
def d2Transfer82S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer82Arithmetic : weightedUpper d2Transfer82C0 d2Log173Lo d2Log173Hi ≤ d2Transfer82Cap := by decide +kernel
theorem d2Transfer82Bound : ∀ x ∈ Set.Icc ((d2Transfer82Lo:ℚ):ℝ) ((d2Transfer82Hi:ℚ):ℝ), ((d2Transfer82C0:ℚ):ℝ)*Real.log |x-((d2Transfer82S0:ℚ):ℝ)| ≤ ((d2Transfer82Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer82S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer82S0,d2Transfer82Lo,d2Transfer82Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer82C0 then |x-((d2Transfer82S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer82S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer82S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer82S0,d2Transfer82Lo,d2Transfer82Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer82C0,d2Log173Q,d2Transfer82S0,d2Transfer82Lo,d2Transfer82Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer82C0 d2Transfer82S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2Transfer82C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2Transfer82Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer82Arithmetic
  linarith
#print axioms d2Transfer82Arithmetic
#print axioms d2Transfer82Bound
def d2Transfer83Lo : ℚ := (d2LitsNearTransfers010.q2 (16756223) 1 (-24))
def d2Transfer83Hi : ℚ := (d2LitsNearTransfers010.q2 (8380219) 1 (-23))
def d2Transfer83Cap : ℚ := (d2LitsNearTransfers010.q2 (4792410857165054042153) 1 (-78))
def d2Transfer83C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 275 (-4))
def d2Transfer83S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
def d2Transfer83C1 : ℚ := (d2LitsNearTransfers010.q2 (-1) 55 (-3))
def d2Transfer83S1 : ℚ := (d2LitsNearTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer83Arithmetic : weightedUpper d2Transfer83C0 d2Log173Lo d2Log173Hi + weightedUpper d2Transfer83C1 d2Log1Lo d2Log1Hi ≤ d2Transfer83Cap := by decide +kernel
theorem d2Transfer83Bound : ∀ x ∈ Set.Icc ((d2Transfer83Lo:ℚ):ℝ) ((d2Transfer83Hi:ℚ):ℝ), ((d2Transfer83C0:ℚ):ℝ)*Real.log |x-((d2Transfer83S0:ℚ):ℝ)| + ((d2Transfer83C1:ℚ):ℝ)*Real.log |x-((d2Transfer83S1:ℚ):ℝ)| ≤ ((d2Transfer83Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer83S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer83S0,d2Transfer83Lo,d2Transfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer83C0 then |x-((d2Transfer83S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer83S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer83S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer83S0,d2Transfer83Lo,d2Transfer83Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer83C0,d2Log173Q,d2Transfer83S0,d2Transfer83Lo,d2Transfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer83C0 d2Transfer83S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2Transfer83S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer83S1,d2Transfer83Lo,d2Transfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer83C1 then |x-((d2Transfer83S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2Transfer83S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer83S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer83S1,d2Transfer83Lo,d2Transfer83Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer83C1,d2Log1Q,d2Transfer83S1,d2Transfer83Lo,d2Transfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer83C1 d2Transfer83S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2Transfer83C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2Transfer83C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2Transfer83Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer83Arithmetic
  linarith
#print axioms d2Transfer83Arithmetic
#print axioms d2Transfer83Bound
def d2Transfer84Lo : ℚ := (d2LitsNearTransfers010.q2 (8380219) 1 (-23))
def d2Transfer84Hi : ℚ := (d2LitsNearTransfers010.q2 (999) 125 (-3))
def d2Transfer84Cap : ℚ := (d2LitsNearTransfers010.q2 (17922128780758888283833) 1 (-80))
def d2Transfer84C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 25 (-4))
def d2Transfer84S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer84Arithmetic : weightedUpper d2Transfer84C0 d2Log174Lo d2Log174Hi ≤ d2Transfer84Cap := by decide +kernel
theorem d2Transfer84Bound : ∀ x ∈ Set.Icc ((d2Transfer84Lo:ℚ):ℝ) ((d2Transfer84Hi:ℚ):ℝ), ((d2Transfer84C0:ℚ):ℝ)*Real.log |x-((d2Transfer84S0:ℚ):ℝ)| ≤ ((d2Transfer84Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer84S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer84S0,d2Transfer84Lo,d2Transfer84Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer84C0 then |x-((d2Transfer84S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer84S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer84S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer84S0,d2Transfer84Lo,d2Transfer84Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer84C0,d2Log174Q,d2Transfer84S0,d2Transfer84Lo,d2Transfer84Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer84C0 d2Transfer84S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2Transfer84C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2Transfer84Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer84Arithmetic
  linarith
#print axioms d2Transfer84Arithmetic
#print axioms d2Transfer84Bound
def d2Transfer85Lo : ℚ := (d2LitsNearTransfers010.q2 (8380219) 1 (-23))
def d2Transfer85Hi : ℚ := (d2LitsNearTransfers010.q2 (999) 125 (-3))
def d2Transfer85Cap : ℚ := (d2LitsNearTransfers010.q2 (19169771825614475034297) 1 (-80))
def d2Transfer85C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 275 (-4))
def d2Transfer85S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
def d2Transfer85C1 : ℚ := (d2LitsNearTransfers010.q2 (-1) 55 (-3))
def d2Transfer85S1 : ℚ := (d2LitsNearTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer85Arithmetic : weightedUpper d2Transfer85C0 d2Log174Lo d2Log174Hi + weightedUpper d2Transfer85C1 d2Log0Lo d2Log0Hi ≤ d2Transfer85Cap := by decide +kernel
theorem d2Transfer85Bound : ∀ x ∈ Set.Icc ((d2Transfer85Lo:ℚ):ℝ) ((d2Transfer85Hi:ℚ):ℝ), ((d2Transfer85C0:ℚ):ℝ)*Real.log |x-((d2Transfer85S0:ℚ):ℝ)| + ((d2Transfer85C1:ℚ):ℝ)*Real.log |x-((d2Transfer85S1:ℚ):ℝ)| ≤ ((d2Transfer85Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer85S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer85S0,d2Transfer85Lo,d2Transfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer85C0 then |x-((d2Transfer85S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2Transfer85S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer85S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer85S0,d2Transfer85Lo,d2Transfer85Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer85C0,d2Log174Q,d2Transfer85S0,d2Transfer85Lo,d2Transfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer85C0 d2Transfer85S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2Transfer85S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer85S1,d2Transfer85Lo,d2Transfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer85C1 then |x-((d2Transfer85S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2Transfer85S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer85S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer85S1,d2Transfer85Lo,d2Transfer85Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer85C1,d2Log0Q,d2Transfer85S1,d2Transfer85Lo,d2Transfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer85C1 d2Transfer85S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2Transfer85C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2Transfer85C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2Transfer85Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer85Arithmetic
  linarith
#print axioms d2Transfer85Arithmetic
#print axioms d2Transfer85Bound
def d2Transfer86Lo : ℚ := (d2LitsNearTransfers010.q2 (98749) 15625 (-6))
def d2Transfer86Hi : ℚ := (d2LitsNearTransfers010.q2 (828367) 1 (-23))
def d2Transfer86Cap : ℚ := (d2LitsNearTransfers010.q2 (649441385) 1 (-39))
def d2Transfer86C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 25 (-4))
def d2Transfer86S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer86Arithmetic : weightedUpper d2Transfer86C0 d2Log88Lo d2Log88Hi ≤ d2Transfer86Cap := by decide +kernel
theorem d2Transfer86Bound : ∀ x ∈ Set.Icc ((d2Transfer86Lo:ℚ):ℝ) ((d2Transfer86Hi:ℚ):ℝ), ((d2Transfer86C0:ℚ):ℝ)*Real.log |x-((d2Transfer86S0:ℚ):ℝ)| ≤ ((d2Transfer86Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer86S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer86S0,d2Transfer86Lo,d2Transfer86Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer86C0 then |x-((d2Transfer86S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer86S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer86S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer86S0,d2Transfer86Lo,d2Transfer86Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer86C0,d2Log88Q,d2Transfer86S0,d2Transfer86Lo,d2Transfer86Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer86C0 d2Transfer86S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2Transfer86C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2Transfer86Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer86Arithmetic
  linarith
#print axioms d2Transfer86Arithmetic
#print axioms d2Transfer86Bound
def d2Transfer87Lo : ℚ := (d2LitsNearTransfers010.q2 (98749) 15625 (-6))
def d2Transfer87Hi : ℚ := (d2LitsNearTransfers010.q2 (828367) 1 (-23))
def d2Transfer87Cap : ℚ := (d2LitsNearTransfers010.q2 (2436024149) 1 (-40))
def d2Transfer87C0 : ℚ := (d2LitsNearTransfers010.q2 (1) 275 (-4))
def d2Transfer87S0 : ℚ := (d2LitsNearTransfers010.q2 (-1) 1 (0))
def d2Transfer87C1 : ℚ := (d2LitsNearTransfers010.q2 (-1) 55 (-3))
def d2Transfer87S1 : ℚ := (d2LitsNearTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer87Arithmetic : weightedUpper d2Transfer87C0 d2Log88Lo d2Log88Hi + weightedUpper d2Transfer87C1 d2Log86Lo d2Log86Hi ≤ d2Transfer87Cap := by decide +kernel
theorem d2Transfer87Bound : ∀ x ∈ Set.Icc ((d2Transfer87Lo:ℚ):ℝ) ((d2Transfer87Hi:ℚ):ℝ), ((d2Transfer87C0:ℚ):ℝ)*Real.log |x-((d2Transfer87S0:ℚ):ℝ)| + ((d2Transfer87C1:ℚ):ℝ)*Real.log |x-((d2Transfer87S1:ℚ):ℝ)| ≤ ((d2Transfer87Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer87S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer87S0,d2Transfer87Lo,d2Transfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer87C0 then |x-((d2Transfer87S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer87S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer87S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer87S0,d2Transfer87Lo,d2Transfer87Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer87C0,d2Log88Q,d2Transfer87S0,d2Transfer87Lo,d2Transfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer87C0 d2Transfer87S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2Transfer87S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer87S1,d2Transfer87Lo,d2Transfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer87C1 then |x-((d2Transfer87S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2Transfer87S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer87S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer87S1,d2Transfer87Lo,d2Transfer87Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers010.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2Transfer87C1,d2Log86Q,d2Transfer87S1,d2Transfer87Lo,d2Transfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer87C1 d2Transfer87S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2Transfer87C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2Transfer87C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2Transfer87Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer87Arithmetic
  linarith
#print axioms d2Transfer87Arithmetic
#print axioms d2Transfer87Bound
end CatalanMeasure.GenD.Signed.Data.Cells
