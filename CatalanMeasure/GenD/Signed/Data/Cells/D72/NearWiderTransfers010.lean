module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers010
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers010
open D72.LogTransfer
def d2WiderTransfer80Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (18412957) 1 (-25))
def d2WiderTransfer80Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (38503635) 1 (-26))
def d2WiderTransfer80Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (16281318465) 1 (-40))
def d2WiderTransfer80C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 1 (-5))
def d2WiderTransfer80S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer80Arithmetic : weightedUpper d2WiderTransfer80C0 d2Log122Lo d2Log122Hi ≤ d2WiderTransfer80Cap := by decide +kernel
theorem d2WiderTransfer80Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer80Lo:ℚ):ℝ) ((d2WiderTransfer80Hi:ℚ):ℝ), ((d2WiderTransfer80C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer80S0:ℚ):ℝ)| ≤ ((d2WiderTransfer80Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer80S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer80S0,d2WiderTransfer80Lo,d2WiderTransfer80Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer80C0 then |x-((d2WiderTransfer80S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer80S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer80S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer80S0,d2WiderTransfer80Lo,d2WiderTransfer80Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer80C0,d2Log122Q,d2WiderTransfer80S0,d2WiderTransfer80Lo,d2WiderTransfer80Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer80C0 d2WiderTransfer80S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2WiderTransfer80C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer80Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer80Arithmetic
  linarith
#print axioms d2WiderTransfer80Arithmetic
#print axioms d2WiderTransfer80Bound
def d2WiderTransfer81Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (18412957) 1 (-25))
def d2WiderTransfer81Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (38503635) 1 (-26))
def d2WiderTransfer81Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (31165051305) 1 (-40))
def d2WiderTransfer81C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 11 (-5))
def d2WiderTransfer81S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
def d2WiderTransfer81C1 : ℚ := (d2LitsNearWiderTransfers010.q2 (-5) 11 (-4))
def d2WiderTransfer81S1 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer81Arithmetic : weightedUpper d2WiderTransfer81C0 d2Log122Lo d2Log122Hi + weightedUpper d2WiderTransfer81C1 d2Log52Lo d2Log52Hi ≤ d2WiderTransfer81Cap := by decide +kernel
theorem d2WiderTransfer81Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer81Lo:ℚ):ℝ) ((d2WiderTransfer81Hi:ℚ):ℝ), ((d2WiderTransfer81C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer81S0:ℚ):ℝ)| + ((d2WiderTransfer81C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer81S1:ℚ):ℝ)| ≤ ((d2WiderTransfer81Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer81S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer81S0,d2WiderTransfer81Lo,d2WiderTransfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer81C0 then |x-((d2WiderTransfer81S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer81S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer81S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer81S0,d2WiderTransfer81Lo,d2WiderTransfer81Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer81C0,d2Log122Q,d2WiderTransfer81S0,d2WiderTransfer81Lo,d2WiderTransfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer81C0 d2WiderTransfer81S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2WiderTransfer81S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer81S1,d2WiderTransfer81Lo,d2WiderTransfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer81C1 then |x-((d2WiderTransfer81S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer81S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer81S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer81S1,d2WiderTransfer81Lo,d2WiderTransfer81Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer81C1,d2Log52Q,d2WiderTransfer81S1,d2WiderTransfer81Lo,d2WiderTransfer81Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer81C1 d2WiderTransfer81S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2WiderTransfer81C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer81C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer81Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer81Arithmetic
  linarith
#print axioms d2WiderTransfer81Arithmetic
#print axioms d2WiderTransfer81Bound
def d2WiderTransfer82Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (38503635) 1 (-26))
def d2WiderTransfer82Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (78684991) 1 (-27))
def d2WiderTransfer82Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (649441385) 1 (-39))
def d2WiderTransfer82C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 25 (-4))
def d2WiderTransfer82S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer82Arithmetic : weightedUpper d2WiderTransfer82C0 d2Log123Lo d2Log123Hi ≤ d2WiderTransfer82Cap := by decide +kernel
theorem d2WiderTransfer82Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer82Lo:ℚ):ℝ) ((d2WiderTransfer82Hi:ℚ):ℝ), ((d2WiderTransfer82C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer82S0:ℚ):ℝ)| ≤ ((d2WiderTransfer82Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer82S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer82S0,d2WiderTransfer82Lo,d2WiderTransfer82Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer82C0 then |x-((d2WiderTransfer82S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer82S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer82S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer82S0,d2WiderTransfer82Lo,d2WiderTransfer82Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer82C0,d2Log123Q,d2WiderTransfer82S0,d2WiderTransfer82Lo,d2WiderTransfer82Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer82C0 d2WiderTransfer82S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have har : (((weightedUpper d2WiderTransfer82C0 d2Log123Lo d2Log123Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer82Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer82Arithmetic
  linarith
#print axioms d2WiderTransfer82Arithmetic
#print axioms d2WiderTransfer82Bound
def d2WiderTransfer83Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (38503635) 1 (-26))
def d2WiderTransfer83Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (78684991) 1 (-27))
def d2WiderTransfer83Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (2436024149) 1 (-40))
def d2WiderTransfer83C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 275 (-4))
def d2WiderTransfer83S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
def d2WiderTransfer83C1 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 55 (-3))
def d2WiderTransfer83S1 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer83Arithmetic : weightedUpper d2WiderTransfer83C0 d2Log123Lo d2Log123Hi + weightedUpper d2WiderTransfer83C1 d2Log51Lo d2Log51Hi ≤ d2WiderTransfer83Cap := by decide +kernel
theorem d2WiderTransfer83Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer83Lo:ℚ):ℝ) ((d2WiderTransfer83Hi:ℚ):ℝ), ((d2WiderTransfer83C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer83S0:ℚ):ℝ)| + ((d2WiderTransfer83C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer83S1:ℚ):ℝ)| ≤ ((d2WiderTransfer83Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer83S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer83S0,d2WiderTransfer83Lo,d2WiderTransfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer83C0 then |x-((d2WiderTransfer83S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer83S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer83S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer83S0,d2WiderTransfer83Lo,d2WiderTransfer83Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer83C0,d2Log123Q,d2WiderTransfer83S0,d2WiderTransfer83Lo,d2WiderTransfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer83C0 d2WiderTransfer83S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have hn1 : x-((d2WiderTransfer83S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer83S1,d2WiderTransfer83Lo,d2WiderTransfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer83C1 then |x-((d2WiderTransfer83S1:ℚ):ℝ)| ≤ ((d2Log51Q:ℚ):ℝ) else ((d2Log51Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer83S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer83S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer83S1,d2WiderTransfer83Lo,d2WiderTransfer83Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer83C1,d2Log51Q,d2WiderTransfer83S1,d2WiderTransfer83Lo,d2WiderTransfer83Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer83C1 d2WiderTransfer83S1 d2Log51Q d2Log51Lo d2Log51Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log51Bounds
  have har : (((weightedUpper d2WiderTransfer83C0 d2Log123Lo d2Log123Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer83C1 d2Log51Lo d2Log51Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer83Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer83Arithmetic
  linarith
#print axioms d2WiderTransfer83Arithmetic
#print axioms d2WiderTransfer83Bound
def d2WiderTransfer84Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (38503635) 1 (-26))
def d2WiderTransfer84Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (78684991) 1 (-27))
def d2WiderTransfer84Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (16281318465) 1 (-40))
def d2WiderTransfer84C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 1 (-5))
def d2WiderTransfer84S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer84Arithmetic : weightedUpper d2WiderTransfer84C0 d2Log123Lo d2Log123Hi ≤ d2WiderTransfer84Cap := by decide +kernel
theorem d2WiderTransfer84Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer84Lo:ℚ):ℝ) ((d2WiderTransfer84Hi:ℚ):ℝ), ((d2WiderTransfer84C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer84S0:ℚ):ℝ)| ≤ ((d2WiderTransfer84Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer84S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer84S0,d2WiderTransfer84Lo,d2WiderTransfer84Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer84C0 then |x-((d2WiderTransfer84S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer84S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer84S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer84S0,d2WiderTransfer84Lo,d2WiderTransfer84Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer84C0,d2Log123Q,d2WiderTransfer84S0,d2WiderTransfer84Lo,d2WiderTransfer84Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer84C0 d2WiderTransfer84S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have har : (((weightedUpper d2WiderTransfer84C0 d2Log123Lo d2Log123Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer84Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer84Arithmetic
  linarith
#print axioms d2WiderTransfer84Arithmetic
#print axioms d2WiderTransfer84Bound
def d2WiderTransfer85Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (38503635) 1 (-26))
def d2WiderTransfer85Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (78684991) 1 (-27))
def d2WiderTransfer85Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (31165051305) 1 (-40))
def d2WiderTransfer85C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 11 (-5))
def d2WiderTransfer85S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
def d2WiderTransfer85C1 : ℚ := (d2LitsNearWiderTransfers010.q2 (-5) 11 (-4))
def d2WiderTransfer85S1 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer85Arithmetic : weightedUpper d2WiderTransfer85C0 d2Log123Lo d2Log123Hi + weightedUpper d2WiderTransfer85C1 d2Log51Lo d2Log51Hi ≤ d2WiderTransfer85Cap := by decide +kernel
theorem d2WiderTransfer85Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer85Lo:ℚ):ℝ) ((d2WiderTransfer85Hi:ℚ):ℝ), ((d2WiderTransfer85C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer85S0:ℚ):ℝ)| + ((d2WiderTransfer85C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer85S1:ℚ):ℝ)| ≤ ((d2WiderTransfer85Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer85S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer85S0,d2WiderTransfer85Lo,d2WiderTransfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer85C0 then |x-((d2WiderTransfer85S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer85S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer85S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer85S0,d2WiderTransfer85Lo,d2WiderTransfer85Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer85C0,d2Log123Q,d2WiderTransfer85S0,d2WiderTransfer85Lo,d2WiderTransfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer85C0 d2WiderTransfer85S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have hn1 : x-((d2WiderTransfer85S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer85S1,d2WiderTransfer85Lo,d2WiderTransfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer85C1 then |x-((d2WiderTransfer85S1:ℚ):ℝ)| ≤ ((d2Log51Q:ℚ):ℝ) else ((d2Log51Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer85S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer85S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer85S1,d2WiderTransfer85Lo,d2WiderTransfer85Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer85C1,d2Log51Q,d2WiderTransfer85S1,d2WiderTransfer85Lo,d2WiderTransfer85Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer85C1 d2WiderTransfer85S1 d2Log51Q d2Log51Lo d2Log51Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log51Bounds
  have har : (((weightedUpper d2WiderTransfer85C0 d2Log123Lo d2Log123Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer85C1 d2Log51Lo d2Log51Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer85Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer85Arithmetic
  linarith
#print axioms d2WiderTransfer85Arithmetic
#print axioms d2WiderTransfer85Bound
def d2WiderTransfer86Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (78684991) 1 (-27))
def d2WiderTransfer86Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (10045339) 1 (-24))
def d2WiderTransfer86Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (649441385) 1 (-39))
def d2WiderTransfer86C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 25 (-4))
def d2WiderTransfer86S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer86Arithmetic : weightedUpper d2WiderTransfer86C0 d2Log124Lo d2Log124Hi ≤ d2WiderTransfer86Cap := by decide +kernel
theorem d2WiderTransfer86Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer86Lo:ℚ):ℝ) ((d2WiderTransfer86Hi:ℚ):ℝ), ((d2WiderTransfer86C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer86S0:ℚ):ℝ)| ≤ ((d2WiderTransfer86Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer86S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer86S0,d2WiderTransfer86Lo,d2WiderTransfer86Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer86C0 then |x-((d2WiderTransfer86S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer86S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer86S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer86S0,d2WiderTransfer86Lo,d2WiderTransfer86Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer86C0,d2Log124Q,d2WiderTransfer86S0,d2WiderTransfer86Lo,d2WiderTransfer86Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer86C0 d2WiderTransfer86S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2WiderTransfer86C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer86Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer86Arithmetic
  linarith
#print axioms d2WiderTransfer86Arithmetic
#print axioms d2WiderTransfer86Bound
def d2WiderTransfer87Lo : ℚ := (d2LitsNearWiderTransfers010.q2 (78684991) 1 (-27))
def d2WiderTransfer87Hi : ℚ := (d2LitsNearWiderTransfers010.q2 (10045339) 1 (-24))
def d2WiderTransfer87Cap : ℚ := (d2LitsNearWiderTransfers010.q2 (2436024149) 1 (-40))
def d2WiderTransfer87C0 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 275 (-4))
def d2WiderTransfer87S0 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 1 (0))
def d2WiderTransfer87C1 : ℚ := (d2LitsNearWiderTransfers010.q2 (-1) 55 (-3))
def d2WiderTransfer87S1 : ℚ := (d2LitsNearWiderTransfers010.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer87Arithmetic : weightedUpper d2WiderTransfer87C0 d2Log124Lo d2Log124Hi + weightedUpper d2WiderTransfer87C1 d2Log50Lo d2Log50Hi ≤ d2WiderTransfer87Cap := by decide +kernel
theorem d2WiderTransfer87Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer87Lo:ℚ):ℝ) ((d2WiderTransfer87Hi:ℚ):ℝ), ((d2WiderTransfer87C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer87S0:ℚ):ℝ)| + ((d2WiderTransfer87C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer87S1:ℚ):ℝ)| ≤ ((d2WiderTransfer87Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer87S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer87S0,d2WiderTransfer87Lo,d2WiderTransfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer87C0 then |x-((d2WiderTransfer87S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer87S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer87S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer87S0,d2WiderTransfer87Lo,d2WiderTransfer87Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer87C0,d2Log124Q,d2WiderTransfer87S0,d2WiderTransfer87Lo,d2WiderTransfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer87C0 d2WiderTransfer87S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2WiderTransfer87S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer87S1,d2WiderTransfer87Lo,d2WiderTransfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer87C1 then |x-((d2WiderTransfer87S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer87S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer87S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer87S1,d2WiderTransfer87Lo,d2WiderTransfer87Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers010.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer87C1,d2Log50Q,d2WiderTransfer87S1,d2WiderTransfer87Lo,d2WiderTransfer87Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer87C1 d2WiderTransfer87S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2WiderTransfer87C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer87C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer87Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer87Arithmetic
  linarith
#print axioms d2WiderTransfer87Arithmetic
#print axioms d2WiderTransfer87Bound
end CatalanMeasure.GenD.Signed.Data.Cells
