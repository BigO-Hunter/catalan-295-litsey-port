module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers087
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers087
open D72.LogTransfer
def d2Transfer696Lo : ℚ := (d2LitsNearTransfers087.q2 (32767) 1 (-15))
def d2Transfer696Hi : ℚ := (d2LitsNearTransfers087.q2 (65535) 1 (-16))
def d2Transfer696Cap : ℚ := (d2LitsNearTransfers087.q2 (24091186123987420270547) 1 (-80))
def d2Transfer696C0 : ℚ := (d2LitsNearTransfers087.q2 (23) 25 (-5))
def d2Transfer696S0 : ℚ := (d2LitsNearTransfers087.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer696Arithmetic : weightedUpper d2Transfer696C0 d2Log182Lo d2Log182Hi ≤ d2Transfer696Cap := by decide +kernel
theorem d2Transfer696Bound : ∀ x ∈ Set.Icc ((d2Transfer696Lo:ℚ):ℝ) ((d2Transfer696Hi:ℚ):ℝ), ((d2Transfer696C0:ℚ):ℝ)*Real.log |x-((d2Transfer696S0:ℚ):ℝ)| ≤ ((d2Transfer696Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer696S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer696S0,d2Transfer696Lo,d2Transfer696Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer696C0 then |x-((d2Transfer696S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer696S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer696S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer696S0,d2Transfer696Lo,d2Transfer696Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer696C0,d2Log182Q,d2Transfer696S0,d2Transfer696Lo,d2Transfer696Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer696C0 d2Transfer696S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer696C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer696Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer696Arithmetic
  linarith
#print axioms d2Transfer696Arithmetic
#print axioms d2Transfer696Bound
def d2Transfer697Lo : ℚ := (d2LitsNearTransfers087.q2 (65535) 1 (-16))
def d2Transfer697Hi : ℚ := (d2LitsNearTransfers087.q2 (131071) 1 (-17))
def d2Transfer697Cap : ℚ := (d2LitsNearTransfers087.q2 (17250812007442604725) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer697Arithmetic : (0 : ℚ) ≤ d2Transfer697Cap := by decide +kernel
theorem d2Transfer697Bound : ∀ x ∈ Set.Icc ((d2Transfer697Lo:ℚ):ℝ) ((d2Transfer697Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer697Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer697Arithmetic
#print axioms d2Transfer697Arithmetic
#print axioms d2Transfer697Bound
def d2Transfer698Lo : ℚ := (d2LitsNearTransfers087.q2 (65535) 1 (-16))
def d2Transfer698Hi : ℚ := (d2LitsNearTransfers087.q2 (131071) 1 (-17))
def d2Transfer698Cap : ℚ := (d2LitsNearTransfers087.q2 (24091319440794838426293) 1 (-80))
def d2Transfer698C0 : ℚ := (d2LitsNearTransfers087.q2 (23) 25 (-5))
def d2Transfer698S0 : ℚ := (d2LitsNearTransfers087.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer698Arithmetic : weightedUpper d2Transfer698C0 d2Log183Lo d2Log183Hi ≤ d2Transfer698Cap := by decide +kernel
theorem d2Transfer698Bound : ∀ x ∈ Set.Icc ((d2Transfer698Lo:ℚ):ℝ) ((d2Transfer698Hi:ℚ):ℝ), ((d2Transfer698C0:ℚ):ℝ)*Real.log |x-((d2Transfer698S0:ℚ):ℝ)| ≤ ((d2Transfer698Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer698S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer698S0,d2Transfer698Lo,d2Transfer698Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer698C0 then |x-((d2Transfer698S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2Transfer698S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer698S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer698S0,d2Transfer698Lo,d2Transfer698Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer698C0,d2Log183Q,d2Transfer698S0,d2Transfer698Lo,d2Transfer698Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer698C0 d2Transfer698S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2Transfer698C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2Transfer698Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer698Arithmetic
  linarith
#print axioms d2Transfer698Arithmetic
#print axioms d2Transfer698Bound
def d2Transfer699Lo : ℚ := (d2LitsNearTransfers087.q2 (65535) 1 (-16))
def d2Transfer699Hi : ℚ := (d2LitsNearTransfers087.q2 (131071) 1 (-17))
def d2Transfer699Cap : ℚ := (d2LitsNearTransfers087.q2 (24091318710719117583029) 1 (-80))
def d2Transfer699C0 : ℚ := (d2LitsNearTransfers087.q2 (23) 25 (-5))
def d2Transfer699S0 : ℚ := (d2LitsNearTransfers087.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer699Arithmetic : weightedUpper d2Transfer699C0 d2Log183Lo d2Log183Hi ≤ d2Transfer699Cap := by decide +kernel
theorem d2Transfer699Bound : ∀ x ∈ Set.Icc ((d2Transfer699Lo:ℚ):ℝ) ((d2Transfer699Hi:ℚ):ℝ), ((d2Transfer699C0:ℚ):ℝ)*Real.log |x-((d2Transfer699S0:ℚ):ℝ)| ≤ ((d2Transfer699Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer699S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer699S0,d2Transfer699Lo,d2Transfer699Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer699C0 then |x-((d2Transfer699S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2Transfer699S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer699S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer699S0,d2Transfer699Lo,d2Transfer699Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer699C0,d2Log183Q,d2Transfer699S0,d2Transfer699Lo,d2Transfer699Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer699C0 d2Transfer699S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2Transfer699C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2Transfer699Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer699Arithmetic
  linarith
#print axioms d2Transfer699Arithmetic
#print axioms d2Transfer699Bound
def d2Transfer700Lo : ℚ := (d2LitsNearTransfers087.q2 (131071) 1 (-17))
def d2Transfer700Hi : ℚ := (d2LitsNearTransfers087.q2 (1) 1 (0))
def d2Transfer700Cap : ℚ := (d2LitsNearTransfers087.q2 (4345849558340177411) 1 (-78))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer700Arithmetic : (0 : ℚ) ≤ d2Transfer700Cap := by decide +kernel
theorem d2Transfer700Bound : ∀ x ∈ Set.Icc ((d2Transfer700Lo:ℚ):ℝ) ((d2Transfer700Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer700Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer700Arithmetic
#print axioms d2Transfer700Arithmetic
#print axioms d2Transfer700Bound
def d2Transfer701Lo : ℚ := (d2LitsNearTransfers087.q2 (131071) 1 (-17))
def d2Transfer701Hi : ℚ := (d2LitsNearTransfers087.q2 (1) 1 (0))
def d2Transfer701Cap : ℚ := (d2LitsNearTransfers087.q2 (6022863006755189132803) 1 (-78))
def d2Transfer701C0 : ℚ := (d2LitsNearTransfers087.q2 (23) 25 (-5))
def d2Transfer701S0 : ℚ := (d2LitsNearTransfers087.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer701Arithmetic : weightedUpper d2Transfer701C0 d2Log186Lo d2Log186Hi ≤ d2Transfer701Cap := by decide +kernel
theorem d2Transfer701Bound : ∀ x ∈ Set.Icc ((d2Transfer701Lo:ℚ):ℝ) ((d2Transfer701Hi:ℚ):ℝ), ((d2Transfer701C0:ℚ):ℝ)*Real.log |x-((d2Transfer701S0:ℚ):ℝ)| ≤ ((d2Transfer701Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer701S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer701S0,d2Transfer701Lo,d2Transfer701Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer701C0 then |x-((d2Transfer701S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer701S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer701S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer701S0,d2Transfer701Lo,d2Transfer701Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer701C0,d2Log186Q,d2Transfer701S0,d2Transfer701Lo,d2Transfer701Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer701C0 d2Transfer701S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer701C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer701Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer701Arithmetic
  linarith
#print axioms d2Transfer701Arithmetic
#print axioms d2Transfer701Bound
def d2Transfer702Lo : ℚ := (d2LitsNearTransfers087.q2 (131071) 1 (-17))
def d2Transfer702Hi : ℚ := (d2LitsNearTransfers087.q2 (1) 1 (0))
def d2Transfer702Cap : ℚ := (d2LitsNearTransfers087.q2 (6022862824236258921987) 1 (-78))
def d2Transfer702C0 : ℚ := (d2LitsNearTransfers087.q2 (23) 25 (-5))
def d2Transfer702S0 : ℚ := (d2LitsNearTransfers087.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer702Arithmetic : weightedUpper d2Transfer702C0 d2Log186Lo d2Log186Hi ≤ d2Transfer702Cap := by decide +kernel
theorem d2Transfer702Bound : ∀ x ∈ Set.Icc ((d2Transfer702Lo:ℚ):ℝ) ((d2Transfer702Hi:ℚ):ℝ), ((d2Transfer702C0:ℚ):ℝ)*Real.log |x-((d2Transfer702S0:ℚ):ℝ)| ≤ ((d2Transfer702Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer702S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer702S0,d2Transfer702Lo,d2Transfer702Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer702C0 then |x-((d2Transfer702S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer702S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer702S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer702S0,d2Transfer702Lo,d2Transfer702Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers087.q2, d2LitsNearLogCache011.q2, d2Transfer702C0,d2Log186Q,d2Transfer702S0,d2Transfer702Lo,d2Transfer702Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer702C0 d2Transfer702S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer702C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer702Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer702Arithmetic
  linarith
#print axioms d2Transfer702Arithmetic
#print axioms d2Transfer702Bound
end CatalanMeasure.GenD.Signed.Data.Cells
