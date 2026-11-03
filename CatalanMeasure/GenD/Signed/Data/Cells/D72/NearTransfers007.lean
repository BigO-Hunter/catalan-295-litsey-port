module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers007
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers007
open D72.LogTransfer
def d2Transfer56Lo : ℚ := (d2LitsNearTransfers007.q2 (18412957) 1 (-25))
def d2Transfer56Hi : ℚ := (d2LitsNearTransfers007.q2 (38503635) 1 (-26))
def d2Transfer56Cap : ℚ := (d2LitsNearTransfers007.q2 (648894057) 1 (-39))
def d2Transfer56C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 25 (-4))
def d2Transfer56S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer56Arithmetic : weightedUpper d2Transfer56C0 d2Log122Lo d2Log122Hi ≤ d2Transfer56Cap := by decide +kernel
theorem d2Transfer56Bound : ∀ x ∈ Set.Icc ((d2Transfer56Lo:ℚ):ℝ) ((d2Transfer56Hi:ℚ):ℝ), ((d2Transfer56C0:ℚ):ℝ)*Real.log |x-((d2Transfer56S0:ℚ):ℝ)| ≤ ((d2Transfer56Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer56S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer56S0,d2Transfer56Lo,d2Transfer56Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer56C0 then |x-((d2Transfer56S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer56S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer56S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer56S0,d2Transfer56Lo,d2Transfer56Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer56C0,d2Log122Q,d2Transfer56S0,d2Transfer56Lo,d2Transfer56Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer56C0 d2Transfer56S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2Transfer56C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2Transfer56Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer56Arithmetic
  linarith
#print axioms d2Transfer56Arithmetic
#print axioms d2Transfer56Bound
def d2Transfer57Lo : ℚ := (d2LitsNearTransfers007.q2 (18412957) 1 (-25))
def d2Transfer57Hi : ℚ := (d2LitsNearTransfers007.q2 (38503635) 1 (-26))
def d2Transfer57Cap : ℚ := (d2LitsNearTransfers007.q2 (2432512853) 1 (-40))
def d2Transfer57C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 275 (-4))
def d2Transfer57S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
def d2Transfer57C1 : ℚ := (d2LitsNearTransfers007.q2 (-1) 55 (-3))
def d2Transfer57S1 : ℚ := (d2LitsNearTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer57Arithmetic : weightedUpper d2Transfer57C0 d2Log122Lo d2Log122Hi + weightedUpper d2Transfer57C1 d2Log52Lo d2Log52Hi ≤ d2Transfer57Cap := by decide +kernel
theorem d2Transfer57Bound : ∀ x ∈ Set.Icc ((d2Transfer57Lo:ℚ):ℝ) ((d2Transfer57Hi:ℚ):ℝ), ((d2Transfer57C0:ℚ):ℝ)*Real.log |x-((d2Transfer57S0:ℚ):ℝ)| + ((d2Transfer57C1:ℚ):ℝ)*Real.log |x-((d2Transfer57S1:ℚ):ℝ)| ≤ ((d2Transfer57Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer57S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer57S0,d2Transfer57Lo,d2Transfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer57C0 then |x-((d2Transfer57S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer57S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer57S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer57S0,d2Transfer57Lo,d2Transfer57Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer57C0,d2Log122Q,d2Transfer57S0,d2Transfer57Lo,d2Transfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer57C0 d2Transfer57S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2Transfer57S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer57S1,d2Transfer57Lo,d2Transfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer57C1 then |x-((d2Transfer57S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2Transfer57S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer57S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer57S1,d2Transfer57Lo,d2Transfer57Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer57C1,d2Log52Q,d2Transfer57S1,d2Transfer57Lo,d2Transfer57Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer57C1 d2Transfer57S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2Transfer57C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2Transfer57C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2Transfer57Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer57Arithmetic
  linarith
#print axioms d2Transfer57Arithmetic
#print axioms d2Transfer57Bound
def d2Transfer58Lo : ℚ := (d2LitsNearTransfers007.q2 (38503635) 1 (-26))
def d2Transfer58Hi : ℚ := (d2LitsNearTransfers007.q2 (78684991) 1 (-27))
def d2Transfer58Cap : ℚ := (d2LitsNearTransfers007.q2 (648894057) 1 (-39))
def d2Transfer58C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 25 (-4))
def d2Transfer58S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer58Arithmetic : weightedUpper d2Transfer58C0 d2Log123Lo d2Log123Hi ≤ d2Transfer58Cap := by decide +kernel
theorem d2Transfer58Bound : ∀ x ∈ Set.Icc ((d2Transfer58Lo:ℚ):ℝ) ((d2Transfer58Hi:ℚ):ℝ), ((d2Transfer58C0:ℚ):ℝ)*Real.log |x-((d2Transfer58S0:ℚ):ℝ)| ≤ ((d2Transfer58Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer58S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer58S0,d2Transfer58Lo,d2Transfer58Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer58C0 then |x-((d2Transfer58S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2Transfer58S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer58S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer58S0,d2Transfer58Lo,d2Transfer58Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer58C0,d2Log123Q,d2Transfer58S0,d2Transfer58Lo,d2Transfer58Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer58C0 d2Transfer58S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have har : (((weightedUpper d2Transfer58C0 d2Log123Lo d2Log123Hi:ℚ):ℝ)) ≤ ((d2Transfer58Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer58Arithmetic
  linarith
#print axioms d2Transfer58Arithmetic
#print axioms d2Transfer58Bound
def d2Transfer59Lo : ℚ := (d2LitsNearTransfers007.q2 (38503635) 1 (-26))
def d2Transfer59Hi : ℚ := (d2LitsNearTransfers007.q2 (78684991) 1 (-27))
def d2Transfer59Cap : ℚ := (d2LitsNearTransfers007.q2 (2432512853) 1 (-40))
def d2Transfer59C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 275 (-4))
def d2Transfer59S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
def d2Transfer59C1 : ℚ := (d2LitsNearTransfers007.q2 (-1) 55 (-3))
def d2Transfer59S1 : ℚ := (d2LitsNearTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer59Arithmetic : weightedUpper d2Transfer59C0 d2Log123Lo d2Log123Hi + weightedUpper d2Transfer59C1 d2Log51Lo d2Log51Hi ≤ d2Transfer59Cap := by decide +kernel
theorem d2Transfer59Bound : ∀ x ∈ Set.Icc ((d2Transfer59Lo:ℚ):ℝ) ((d2Transfer59Hi:ℚ):ℝ), ((d2Transfer59C0:ℚ):ℝ)*Real.log |x-((d2Transfer59S0:ℚ):ℝ)| + ((d2Transfer59C1:ℚ):ℝ)*Real.log |x-((d2Transfer59S1:ℚ):ℝ)| ≤ ((d2Transfer59Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer59S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer59S0,d2Transfer59Lo,d2Transfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer59C0 then |x-((d2Transfer59S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2Transfer59S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer59S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer59S0,d2Transfer59Lo,d2Transfer59Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer59C0,d2Log123Q,d2Transfer59S0,d2Transfer59Lo,d2Transfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer59C0 d2Transfer59S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have hn1 : x-((d2Transfer59S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer59S1,d2Transfer59Lo,d2Transfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer59C1 then |x-((d2Transfer59S1:ℚ):ℝ)| ≤ ((d2Log51Q:ℚ):ℝ) else ((d2Log51Q:ℚ):ℝ) ≤ |x-((d2Transfer59S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer59S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer59S1,d2Transfer59Lo,d2Transfer59Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer59C1,d2Log51Q,d2Transfer59S1,d2Transfer59Lo,d2Transfer59Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer59C1 d2Transfer59S1 d2Log51Q d2Log51Lo d2Log51Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log51Bounds
  have har : (((weightedUpper d2Transfer59C0 d2Log123Lo d2Log123Hi:ℚ):ℝ) + ((weightedUpper d2Transfer59C1 d2Log51Lo d2Log51Hi:ℚ):ℝ)) ≤ ((d2Transfer59Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer59Arithmetic
  linarith
#print axioms d2Transfer59Arithmetic
#print axioms d2Transfer59Bound
def d2Transfer60Lo : ℚ := (d2LitsNearTransfers007.q2 (78684991) 1 (-27))
def d2Transfer60Hi : ℚ := (d2LitsNearTransfers007.q2 (10045339) 1 (-24))
def d2Transfer60Cap : ℚ := (d2LitsNearTransfers007.q2 (648894057) 1 (-39))
def d2Transfer60C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 25 (-4))
def d2Transfer60S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer60Arithmetic : weightedUpper d2Transfer60C0 d2Log124Lo d2Log124Hi ≤ d2Transfer60Cap := by decide +kernel
theorem d2Transfer60Bound : ∀ x ∈ Set.Icc ((d2Transfer60Lo:ℚ):ℝ) ((d2Transfer60Hi:ℚ):ℝ), ((d2Transfer60C0:ℚ):ℝ)*Real.log |x-((d2Transfer60S0:ℚ):ℝ)| ≤ ((d2Transfer60Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer60S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer60S0,d2Transfer60Lo,d2Transfer60Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer60C0 then |x-((d2Transfer60S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer60S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer60S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer60S0,d2Transfer60Lo,d2Transfer60Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer60C0,d2Log124Q,d2Transfer60S0,d2Transfer60Lo,d2Transfer60Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer60C0 d2Transfer60S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2Transfer60C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2Transfer60Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer60Arithmetic
  linarith
#print axioms d2Transfer60Arithmetic
#print axioms d2Transfer60Bound
def d2Transfer61Lo : ℚ := (d2LitsNearTransfers007.q2 (78684991) 1 (-27))
def d2Transfer61Hi : ℚ := (d2LitsNearTransfers007.q2 (10045339) 1 (-24))
def d2Transfer61Cap : ℚ := (d2LitsNearTransfers007.q2 (2432512853) 1 (-40))
def d2Transfer61C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 275 (-4))
def d2Transfer61S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
def d2Transfer61C1 : ℚ := (d2LitsNearTransfers007.q2 (-1) 55 (-3))
def d2Transfer61S1 : ℚ := (d2LitsNearTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer61Arithmetic : weightedUpper d2Transfer61C0 d2Log124Lo d2Log124Hi + weightedUpper d2Transfer61C1 d2Log50Lo d2Log50Hi ≤ d2Transfer61Cap := by decide +kernel
theorem d2Transfer61Bound : ∀ x ∈ Set.Icc ((d2Transfer61Lo:ℚ):ℝ) ((d2Transfer61Hi:ℚ):ℝ), ((d2Transfer61C0:ℚ):ℝ)*Real.log |x-((d2Transfer61S0:ℚ):ℝ)| + ((d2Transfer61C1:ℚ):ℝ)*Real.log |x-((d2Transfer61S1:ℚ):ℝ)| ≤ ((d2Transfer61Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer61S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer61S0,d2Transfer61Lo,d2Transfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer61C0 then |x-((d2Transfer61S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer61S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer61S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer61S0,d2Transfer61Lo,d2Transfer61Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer61C0,d2Log124Q,d2Transfer61S0,d2Transfer61Lo,d2Transfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer61C0 d2Transfer61S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2Transfer61S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer61S1,d2Transfer61Lo,d2Transfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer61C1 then |x-((d2Transfer61S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2Transfer61S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer61S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer61S1,d2Transfer61Lo,d2Transfer61Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer61C1,d2Log50Q,d2Transfer61S1,d2Transfer61Lo,d2Transfer61Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer61C1 d2Transfer61S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2Transfer61C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2Transfer61C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2Transfer61Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer61Arithmetic
  linarith
#print axioms d2Transfer61Arithmetic
#print axioms d2Transfer61Bound
def d2Transfer62Lo : ℚ := (d2LitsNearTransfers007.q2 (10045339) 1 (-24))
def d2Transfer62Hi : ℚ := (d2LitsNearTransfers007.q2 (162403145) 1 (-28))
def d2Transfer62Cap : ℚ := (d2LitsNearTransfers007.q2 (358616464823175574959) 1 (-78))
def d2Transfer62C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 25 (-4))
def d2Transfer62S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer62Arithmetic : weightedUpper d2Transfer62C0 d2Log125Lo d2Log125Hi ≤ d2Transfer62Cap := by decide +kernel
theorem d2Transfer62Bound : ∀ x ∈ Set.Icc ((d2Transfer62Lo:ℚ):ℝ) ((d2Transfer62Hi:ℚ):ℝ), ((d2Transfer62C0:ℚ):ℝ)*Real.log |x-((d2Transfer62S0:ℚ):ℝ)| ≤ ((d2Transfer62Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer62S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer62S0,d2Transfer62Lo,d2Transfer62Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer62C0 then |x-((d2Transfer62S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer62S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer62S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer62S0,d2Transfer62Lo,d2Transfer62Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer62C0,d2Log125Q,d2Transfer62S0,d2Transfer62Lo,d2Transfer62Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer62C0 d2Transfer62S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2Transfer62C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2Transfer62Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer62Arithmetic
  linarith
#print axioms d2Transfer62Arithmetic
#print axioms d2Transfer62Bound
def d2Transfer63Lo : ℚ := (d2LitsNearTransfers007.q2 (10045339) 1 (-24))
def d2Transfer63Hi : ℚ := (d2LitsNearTransfers007.q2 (162403145) 1 (-28))
def d2Transfer63Cap : ℚ := (d2LitsNearTransfers007.q2 (670527226037072262575) 1 (-78))
def d2Transfer63C0 : ℚ := (d2LitsNearTransfers007.q2 (1) 275 (-4))
def d2Transfer63S0 : ℚ := (d2LitsNearTransfers007.q2 (-1) 1 (0))
def d2Transfer63C1 : ℚ := (d2LitsNearTransfers007.q2 (-1) 55 (-3))
def d2Transfer63S1 : ℚ := (d2LitsNearTransfers007.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer63Arithmetic : weightedUpper d2Transfer63C0 d2Log125Lo d2Log125Hi + weightedUpper d2Transfer63C1 d2Log49Lo d2Log49Hi ≤ d2Transfer63Cap := by decide +kernel
theorem d2Transfer63Bound : ∀ x ∈ Set.Icc ((d2Transfer63Lo:ℚ):ℝ) ((d2Transfer63Hi:ℚ):ℝ), ((d2Transfer63C0:ℚ):ℝ)*Real.log |x-((d2Transfer63S0:ℚ):ℝ)| + ((d2Transfer63C1:ℚ):ℝ)*Real.log |x-((d2Transfer63S1:ℚ):ℝ)| ≤ ((d2Transfer63Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer63S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer63S0,d2Transfer63Lo,d2Transfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer63C0 then |x-((d2Transfer63S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer63S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer63S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer63S0,d2Transfer63Lo,d2Transfer63Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer63C0,d2Log125Q,d2Transfer63S0,d2Transfer63Lo,d2Transfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer63C0 d2Transfer63S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2Transfer63S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer63S1,d2Transfer63Lo,d2Transfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer63C1 then |x-((d2Transfer63S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2Transfer63S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer63S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer63S1,d2Transfer63Lo,d2Transfer63Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers007.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer63C1,d2Log49Q,d2Transfer63S1,d2Transfer63Lo,d2Transfer63Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer63C1 d2Transfer63S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2Transfer63C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2Transfer63C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2Transfer63Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer63Arithmetic
  linarith
#print axioms d2Transfer63Arithmetic
#print axioms d2Transfer63Bound
end CatalanMeasure.GenD.Signed.Data.Cells
