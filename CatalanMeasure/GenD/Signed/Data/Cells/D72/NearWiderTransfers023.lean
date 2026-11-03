module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers023
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers023
open D72.LogTransfer
def d2WiderTransfer184Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (169114029) 1 (-28))
def d2WiderTransfer184Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (678133837) 1 (-30))
def d2WiderTransfer184Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (9804385183990908497805) 1 (-79))
def d2WiderTransfer184C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 1 (-5))
def d2WiderTransfer184S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer184Arithmetic : weightedUpper d2WiderTransfer184C0 d2Log149Lo d2Log149Hi ≤ d2WiderTransfer184Cap := by decide +kernel
theorem d2WiderTransfer184Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer184Lo:ℚ):ℝ) ((d2WiderTransfer184Hi:ℚ):ℝ), ((d2WiderTransfer184C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer184S0:ℚ):ℝ)| ≤ ((d2WiderTransfer184Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer184S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer184S0,d2WiderTransfer184Lo,d2WiderTransfer184Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer184C0 then |x-((d2WiderTransfer184S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer184S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer184S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer184S0,d2WiderTransfer184Lo,d2WiderTransfer184Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer184C0,d2Log149Q,d2WiderTransfer184S0,d2WiderTransfer184Lo,d2WiderTransfer184Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer184C0 d2WiderTransfer184S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have har : (((weightedUpper d2WiderTransfer184C0 d2Log149Lo d2Log149Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer184Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer184Arithmetic
  linarith
#print axioms d2WiderTransfer184Arithmetic
#print axioms d2WiderTransfer184Bound
def d2WiderTransfer185Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (169114029) 1 (-28))
def d2WiderTransfer185Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (678133837) 1 (-30))
def d2WiderTransfer185Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (17986803845136662179725) 1 (-79))
def d2WiderTransfer185C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 11 (-5))
def d2WiderTransfer185S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
def d2WiderTransfer185C1 : ℚ := (d2LitsNearWiderTransfers023.q2 (-5) 11 (-4))
def d2WiderTransfer185S1 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer185Arithmetic : weightedUpper d2WiderTransfer185C0 d2Log149Lo d2Log149Hi + weightedUpper d2WiderTransfer185C1 d2Log25Lo d2Log25Hi ≤ d2WiderTransfer185Cap := by decide +kernel
theorem d2WiderTransfer185Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer185Lo:ℚ):ℝ) ((d2WiderTransfer185Hi:ℚ):ℝ), ((d2WiderTransfer185C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer185S0:ℚ):ℝ)| + ((d2WiderTransfer185C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer185S1:ℚ):ℝ)| ≤ ((d2WiderTransfer185Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer185S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer185S0,d2WiderTransfer185Lo,d2WiderTransfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer185C0 then |x-((d2WiderTransfer185S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer185S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer185S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer185S0,d2WiderTransfer185Lo,d2WiderTransfer185Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer185C0,d2Log149Q,d2WiderTransfer185S0,d2WiderTransfer185Lo,d2WiderTransfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer185C0 d2WiderTransfer185S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2WiderTransfer185S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer185S1,d2WiderTransfer185Lo,d2WiderTransfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer185C1 then |x-((d2WiderTransfer185S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer185S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer185S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer185S1,d2WiderTransfer185Lo,d2WiderTransfer185Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer185C1,d2Log25Q,d2WiderTransfer185S1,d2WiderTransfer185Lo,d2WiderTransfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer185C1 d2WiderTransfer185S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2WiderTransfer185C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer185C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer185Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer185Arithmetic
  linarith
#print axioms d2WiderTransfer185Arithmetic
#print axioms d2WiderTransfer185Bound
def d2WiderTransfer186Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (678133837) 1 (-30))
def d2WiderTransfer186Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (339905779) 1 (-29))
def d2WiderTransfer186Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (3284655724680182058789) 1 (-80))
def d2WiderTransfer186C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 25 (-4))
def d2WiderTransfer186S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer186Arithmetic : weightedUpper d2WiderTransfer186C0 d2Log151Lo d2Log151Hi ≤ d2WiderTransfer186Cap := by decide +kernel
theorem d2WiderTransfer186Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer186Lo:ℚ):ℝ) ((d2WiderTransfer186Hi:ℚ):ℝ), ((d2WiderTransfer186C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer186S0:ℚ):ℝ)| ≤ ((d2WiderTransfer186Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer186S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer186S0,d2WiderTransfer186Lo,d2WiderTransfer186Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer186C0 then |x-((d2WiderTransfer186S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer186S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer186S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer186S0,d2WiderTransfer186Lo,d2WiderTransfer186Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer186C0,d2Log151Q,d2WiderTransfer186S0,d2WiderTransfer186Lo,d2WiderTransfer186Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer186C0 d2WiderTransfer186S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have har : (((weightedUpper d2WiderTransfer186C0 d2Log151Lo d2Log151Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer186Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer186Arithmetic
  linarith
#print axioms d2WiderTransfer186Arithmetic
#print axioms d2WiderTransfer186Bound
def d2WiderTransfer187Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (678133837) 1 (-30))
def d2WiderTransfer187Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (339905779) 1 (-29))
def d2WiderTransfer187Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (4534955893315917401893) 1 (-80))
def d2WiderTransfer187C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 275 (-4))
def d2WiderTransfer187S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
def d2WiderTransfer187C1 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 55 (-3))
def d2WiderTransfer187S1 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer187Arithmetic : weightedUpper d2WiderTransfer187C0 d2Log151Lo d2Log151Hi + weightedUpper d2WiderTransfer187C1 d2Log23Lo d2Log23Hi ≤ d2WiderTransfer187Cap := by decide +kernel
theorem d2WiderTransfer187Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer187Lo:ℚ):ℝ) ((d2WiderTransfer187Hi:ℚ):ℝ), ((d2WiderTransfer187C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer187S0:ℚ):ℝ)| + ((d2WiderTransfer187C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer187S1:ℚ):ℝ)| ≤ ((d2WiderTransfer187Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer187S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer187S0,d2WiderTransfer187Lo,d2WiderTransfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer187C0 then |x-((d2WiderTransfer187S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer187S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer187S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer187S0,d2WiderTransfer187Lo,d2WiderTransfer187Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer187C0,d2Log151Q,d2WiderTransfer187S0,d2WiderTransfer187Lo,d2WiderTransfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer187C0 d2WiderTransfer187S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2WiderTransfer187S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer187S1,d2WiderTransfer187Lo,d2WiderTransfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer187C1 then |x-((d2WiderTransfer187S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer187S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer187S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer187S1,d2WiderTransfer187Lo,d2WiderTransfer187Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer187C1,d2Log23Q,d2WiderTransfer187S1,d2WiderTransfer187Lo,d2WiderTransfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer187C1 d2WiderTransfer187S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2WiderTransfer187C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer187C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer187Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer187Arithmetic
  linarith
#print axioms d2WiderTransfer187Arithmetic
#print axioms d2WiderTransfer187Bound
def d2WiderTransfer188Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (678133837) 1 (-30))
def d2WiderTransfer188Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (339905779) 1 (-29))
def d2WiderTransfer188Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (19758017983738877923109) 1 (-80))
def d2WiderTransfer188C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 1 (-5))
def d2WiderTransfer188S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer188Arithmetic : weightedUpper d2WiderTransfer188C0 d2Log151Lo d2Log151Hi ≤ d2WiderTransfer188Cap := by decide +kernel
theorem d2WiderTransfer188Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer188Lo:ℚ):ℝ) ((d2WiderTransfer188Hi:ℚ):ℝ), ((d2WiderTransfer188C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer188S0:ℚ):ℝ)| ≤ ((d2WiderTransfer188Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer188S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer188S0,d2WiderTransfer188Lo,d2WiderTransfer188Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer188C0 then |x-((d2WiderTransfer188S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer188S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer188S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer188S0,d2WiderTransfer188Lo,d2WiderTransfer188Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer188C0,d2Log151Q,d2WiderTransfer188S0,d2WiderTransfer188Lo,d2WiderTransfer188Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer188C0 d2WiderTransfer188S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have har : (((weightedUpper d2WiderTransfer188C0 d2Log151Lo d2Log151Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer188Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer188Arithmetic
  linarith
#print axioms d2WiderTransfer188Arithmetic
#print axioms d2WiderTransfer188Bound
def d2WiderTransfer189Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (678133837) 1 (-30))
def d2WiderTransfer189Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (339905779) 1 (-29))
def d2WiderTransfer189Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (36122855306030385286949) 1 (-80))
def d2WiderTransfer189C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 11 (-5))
def d2WiderTransfer189S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
def d2WiderTransfer189C1 : ℚ := (d2LitsNearWiderTransfers023.q2 (-5) 11 (-4))
def d2WiderTransfer189S1 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer189Arithmetic : weightedUpper d2WiderTransfer189C0 d2Log151Lo d2Log151Hi + weightedUpper d2WiderTransfer189C1 d2Log23Lo d2Log23Hi ≤ d2WiderTransfer189Cap := by decide +kernel
theorem d2WiderTransfer189Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer189Lo:ℚ):ℝ) ((d2WiderTransfer189Hi:ℚ):ℝ), ((d2WiderTransfer189C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer189S0:ℚ):ℝ)| + ((d2WiderTransfer189C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer189S1:ℚ):ℝ)| ≤ ((d2WiderTransfer189Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer189S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer189S0,d2WiderTransfer189Lo,d2WiderTransfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer189C0 then |x-((d2WiderTransfer189S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer189S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer189S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer189S0,d2WiderTransfer189Lo,d2WiderTransfer189Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer189C0,d2Log151Q,d2WiderTransfer189S0,d2WiderTransfer189Lo,d2WiderTransfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer189C0 d2WiderTransfer189S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2WiderTransfer189S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer189S1,d2WiderTransfer189Lo,d2WiderTransfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer189C1 then |x-((d2WiderTransfer189S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer189S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer189S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer189S1,d2WiderTransfer189Lo,d2WiderTransfer189Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer189C1,d2Log23Q,d2WiderTransfer189S1,d2WiderTransfer189Lo,d2WiderTransfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer189C1 d2WiderTransfer189S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2WiderTransfer189C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer189C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer189Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer189Arithmetic
  linarith
#print axioms d2WiderTransfer189Arithmetic
#print axioms d2WiderTransfer189Bound
def d2WiderTransfer190Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (339905779) 1 (-29))
def d2WiderTransfer190Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (85395875) 1 (-27))
def d2WiderTransfer190Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (3585015757831320625385) 1 (-80))
def d2WiderTransfer190C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 25 (-4))
def d2WiderTransfer190S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer190Arithmetic : weightedUpper d2WiderTransfer190C0 d2Log155Lo d2Log155Hi ≤ d2WiderTransfer190Cap := by decide +kernel
theorem d2WiderTransfer190Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer190Lo:ℚ):ℝ) ((d2WiderTransfer190Hi:ℚ):ℝ), ((d2WiderTransfer190C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer190S0:ℚ):ℝ)| ≤ ((d2WiderTransfer190Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer190S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer190S0,d2WiderTransfer190Lo,d2WiderTransfer190Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer190C0 then |x-((d2WiderTransfer190S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer190S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer190S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer190S0,d2WiderTransfer190Lo,d2WiderTransfer190Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer190C0,d2Log155Q,d2WiderTransfer190S0,d2WiderTransfer190Lo,d2WiderTransfer190Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer190C0 d2WiderTransfer190S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have har : (((weightedUpper d2WiderTransfer190C0 d2Log155Lo d2Log155Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer190Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer190Arithmetic
  linarith
#print axioms d2WiderTransfer190Arithmetic
#print axioms d2WiderTransfer190Bound
def d2WiderTransfer191Lo : ℚ := (d2LitsNearWiderTransfers023.q2 (339905779) 1 (-29))
def d2WiderTransfer191Hi : ℚ := (d2LitsNearWiderTransfers023.q2 (85395875) 1 (-27))
def d2WiderTransfer191Cap : ℚ := (d2LitsNearWiderTransfers023.q2 (4835315926467055968489) 1 (-80))
def d2WiderTransfer191C0 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 275 (-4))
def d2WiderTransfer191S0 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 1 (0))
def d2WiderTransfer191C1 : ℚ := (d2LitsNearWiderTransfers023.q2 (-1) 55 (-3))
def d2WiderTransfer191S1 : ℚ := (d2LitsNearWiderTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer191Arithmetic : weightedUpper d2WiderTransfer191C0 d2Log155Lo d2Log155Hi + weightedUpper d2WiderTransfer191C1 d2Log19Lo d2Log19Hi ≤ d2WiderTransfer191Cap := by decide +kernel
theorem d2WiderTransfer191Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer191Lo:ℚ):ℝ) ((d2WiderTransfer191Hi:ℚ):ℝ), ((d2WiderTransfer191C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer191S0:ℚ):ℝ)| + ((d2WiderTransfer191C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer191S1:ℚ):ℝ)| ≤ ((d2WiderTransfer191Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer191S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer191S0,d2WiderTransfer191Lo,d2WiderTransfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer191C0 then |x-((d2WiderTransfer191S0:ℚ):ℝ)| ≤ ((d2Log155Q:ℚ):ℝ) else ((d2Log155Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer191S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer191S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer191S0,d2WiderTransfer191Lo,d2WiderTransfer191Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer191C0,d2Log155Q,d2WiderTransfer191S0,d2WiderTransfer191Lo,d2WiderTransfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer191C0 d2WiderTransfer191S0 d2Log155Q d2Log155Lo d2Log155Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log155Bounds
  have hn1 : x-((d2WiderTransfer191S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer191S1,d2WiderTransfer191Lo,d2WiderTransfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer191C1 then |x-((d2WiderTransfer191S1:ℚ):ℝ)| ≤ ((d2Log19Q:ℚ):ℝ) else ((d2Log19Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer191S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer191S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer191S1,d2WiderTransfer191Lo,d2WiderTransfer191Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers023.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer191C1,d2Log19Q,d2WiderTransfer191S1,d2WiderTransfer191Lo,d2WiderTransfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer191C1 d2WiderTransfer191S1 d2Log19Q d2Log19Lo d2Log19Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log19Bounds
  have har : (((weightedUpper d2WiderTransfer191C0 d2Log155Lo d2Log155Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer191C1 d2Log19Lo d2Log19Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer191Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer191Arithmetic
  linarith
#print axioms d2WiderTransfer191Arithmetic
#print axioms d2WiderTransfer191Bound
end CatalanMeasure.GenD.Signed.Data.Cells
