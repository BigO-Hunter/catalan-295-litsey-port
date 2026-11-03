module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers023
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers023
open D72.LogTransfer
def d2Transfer184Lo : ℚ := (d2LitsNearTransfers023.q2 (313261) 1 (-20))
def d2Transfer184Hi : ℚ := (d2LitsNearTransfers023.q2 (21726425) 1 (-26))
def d2Transfer184Cap : ℚ := (d2LitsNearTransfers023.q2 (16281318465) 1 (-40))
def d2Transfer184C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 1 (-5))
def d2Transfer184S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer184Arithmetic : weightedUpper d2Transfer184C0 d2Log114Lo d2Log114Hi ≤ d2Transfer184Cap := by decide +kernel
theorem d2Transfer184Bound : ∀ x ∈ Set.Icc ((d2Transfer184Lo:ℚ):ℝ) ((d2Transfer184Hi:ℚ):ℝ), ((d2Transfer184C0:ℚ):ℝ)*Real.log |x-((d2Transfer184S0:ℚ):ℝ)| ≤ ((d2Transfer184Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer184S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer184S0,d2Transfer184Lo,d2Transfer184Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer184C0 then |x-((d2Transfer184S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer184S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer184S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer184S0,d2Transfer184Lo,d2Transfer184Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer184C0,d2Log114Q,d2Transfer184S0,d2Transfer184Lo,d2Transfer184Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer184C0 d2Transfer184S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have har : (((weightedUpper d2Transfer184C0 d2Log114Lo d2Log114Hi:ℚ):ℝ)) ≤ ((d2Transfer184Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer184Arithmetic
  linarith
#print axioms d2Transfer184Arithmetic
#print axioms d2Transfer184Bound
def d2Transfer185Lo : ℚ := (d2LitsNearTransfers023.q2 (313261) 1 (-20))
def d2Transfer185Hi : ℚ := (d2LitsNearTransfers023.q2 (21726425) 1 (-26))
def d2Transfer185Cap : ℚ := (d2LitsNearTransfers023.q2 (31165051305) 1 (-40))
def d2Transfer185C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 11 (-5))
def d2Transfer185S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
def d2Transfer185C1 : ℚ := (d2LitsNearTransfers023.q2 (-5) 11 (-4))
def d2Transfer185S1 : ℚ := (d2LitsNearTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer185Arithmetic : weightedUpper d2Transfer185C0 d2Log114Lo d2Log114Hi + weightedUpper d2Transfer185C1 d2Log60Lo d2Log60Hi ≤ d2Transfer185Cap := by decide +kernel
theorem d2Transfer185Bound : ∀ x ∈ Set.Icc ((d2Transfer185Lo:ℚ):ℝ) ((d2Transfer185Hi:ℚ):ℝ), ((d2Transfer185C0:ℚ):ℝ)*Real.log |x-((d2Transfer185S0:ℚ):ℝ)| + ((d2Transfer185C1:ℚ):ℝ)*Real.log |x-((d2Transfer185S1:ℚ):ℝ)| ≤ ((d2Transfer185Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer185S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer185S0,d2Transfer185Lo,d2Transfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer185C0 then |x-((d2Transfer185S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer185S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer185S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer185S0,d2Transfer185Lo,d2Transfer185Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer185C0,d2Log114Q,d2Transfer185S0,d2Transfer185Lo,d2Transfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer185C0 d2Transfer185S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have hn1 : x-((d2Transfer185S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer185S1,d2Transfer185Lo,d2Transfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer185C1 then |x-((d2Transfer185S1:ℚ):ℝ)| ≤ ((d2Log60Q:ℚ):ℝ) else ((d2Log60Q:ℚ):ℝ) ≤ |x-((d2Transfer185S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer185S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer185S1,d2Transfer185Lo,d2Transfer185Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer185C1,d2Log60Q,d2Transfer185S1,d2Transfer185Lo,d2Transfer185Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer185C1 d2Transfer185S1 d2Log60Q d2Log60Lo d2Log60Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log60Bounds
  have har : (((weightedUpper d2Transfer185C0 d2Log114Lo d2Log114Hi:ℚ):ℝ) + ((weightedUpper d2Transfer185C1 d2Log60Lo d2Log60Hi:ℚ):ℝ)) ≤ ((d2Transfer185Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer185Arithmetic
  linarith
#print axioms d2Transfer185Arithmetic
#print axioms d2Transfer185Bound
def d2Transfer186Lo : ℚ := (d2LitsNearTransfers023.q2 (21726425) 1 (-26))
def d2Transfer186Hi : ℚ := (d2LitsNearTransfers023.q2 (11702073) 1 (-25))
def d2Transfer186Cap : ℚ := (d2LitsNearTransfers023.q2 (649441385) 1 (-39))
def d2Transfer186C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 25 (-4))
def d2Transfer186S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer186Arithmetic : weightedUpper d2Transfer186C0 d2Log115Lo d2Log115Hi ≤ d2Transfer186Cap := by decide +kernel
theorem d2Transfer186Bound : ∀ x ∈ Set.Icc ((d2Transfer186Lo:ℚ):ℝ) ((d2Transfer186Hi:ℚ):ℝ), ((d2Transfer186C0:ℚ):ℝ)*Real.log |x-((d2Transfer186S0:ℚ):ℝ)| ≤ ((d2Transfer186Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer186S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer186S0,d2Transfer186Lo,d2Transfer186Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer186C0 then |x-((d2Transfer186S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer186S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer186S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer186S0,d2Transfer186Lo,d2Transfer186Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer186C0,d2Log115Q,d2Transfer186S0,d2Transfer186Lo,d2Transfer186Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer186C0 d2Transfer186S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have har : (((weightedUpper d2Transfer186C0 d2Log115Lo d2Log115Hi:ℚ):ℝ)) ≤ ((d2Transfer186Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer186Arithmetic
  linarith
#print axioms d2Transfer186Arithmetic
#print axioms d2Transfer186Bound
def d2Transfer187Lo : ℚ := (d2LitsNearTransfers023.q2 (21726425) 1 (-26))
def d2Transfer187Hi : ℚ := (d2LitsNearTransfers023.q2 (11702073) 1 (-25))
def d2Transfer187Cap : ℚ := (d2LitsNearTransfers023.q2 (2436024149) 1 (-40))
def d2Transfer187C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 275 (-4))
def d2Transfer187S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
def d2Transfer187C1 : ℚ := (d2LitsNearTransfers023.q2 (-1) 55 (-3))
def d2Transfer187S1 : ℚ := (d2LitsNearTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer187Arithmetic : weightedUpper d2Transfer187C0 d2Log115Lo d2Log115Hi + weightedUpper d2Transfer187C1 d2Log59Lo d2Log59Hi ≤ d2Transfer187Cap := by decide +kernel
theorem d2Transfer187Bound : ∀ x ∈ Set.Icc ((d2Transfer187Lo:ℚ):ℝ) ((d2Transfer187Hi:ℚ):ℝ), ((d2Transfer187C0:ℚ):ℝ)*Real.log |x-((d2Transfer187S0:ℚ):ℝ)| + ((d2Transfer187C1:ℚ):ℝ)*Real.log |x-((d2Transfer187S1:ℚ):ℝ)| ≤ ((d2Transfer187Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer187S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer187S0,d2Transfer187Lo,d2Transfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer187C0 then |x-((d2Transfer187S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer187S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer187S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer187S0,d2Transfer187Lo,d2Transfer187Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer187C0,d2Log115Q,d2Transfer187S0,d2Transfer187Lo,d2Transfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer187C0 d2Transfer187S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have hn1 : x-((d2Transfer187S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer187S1,d2Transfer187Lo,d2Transfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer187C1 then |x-((d2Transfer187S1:ℚ):ℝ)| ≤ ((d2Log59Q:ℚ):ℝ) else ((d2Log59Q:ℚ):ℝ) ≤ |x-((d2Transfer187S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer187S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer187S1,d2Transfer187Lo,d2Transfer187Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer187C1,d2Log59Q,d2Transfer187S1,d2Transfer187Lo,d2Transfer187Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer187C1 d2Transfer187S1 d2Log59Q d2Log59Lo d2Log59Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log59Bounds
  have har : (((weightedUpper d2Transfer187C0 d2Log115Lo d2Log115Hi:ℚ):ℝ) + ((weightedUpper d2Transfer187C1 d2Log59Lo d2Log59Hi:ℚ):ℝ)) ≤ ((d2Transfer187Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer187Arithmetic
  linarith
#print axioms d2Transfer187Arithmetic
#print axioms d2Transfer187Bound
def d2Transfer188Lo : ℚ := (d2LitsNearTransfers023.q2 (21726425) 1 (-26))
def d2Transfer188Hi : ℚ := (d2LitsNearTransfers023.q2 (11702073) 1 (-25))
def d2Transfer188Cap : ℚ := (d2LitsNearTransfers023.q2 (16281318465) 1 (-40))
def d2Transfer188C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 1 (-5))
def d2Transfer188S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer188Arithmetic : weightedUpper d2Transfer188C0 d2Log115Lo d2Log115Hi ≤ d2Transfer188Cap := by decide +kernel
theorem d2Transfer188Bound : ∀ x ∈ Set.Icc ((d2Transfer188Lo:ℚ):ℝ) ((d2Transfer188Hi:ℚ):ℝ), ((d2Transfer188C0:ℚ):ℝ)*Real.log |x-((d2Transfer188S0:ℚ):ℝ)| ≤ ((d2Transfer188Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer188S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer188S0,d2Transfer188Lo,d2Transfer188Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer188C0 then |x-((d2Transfer188S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer188S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer188S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer188S0,d2Transfer188Lo,d2Transfer188Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer188C0,d2Log115Q,d2Transfer188S0,d2Transfer188Lo,d2Transfer188Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer188C0 d2Transfer188S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have har : (((weightedUpper d2Transfer188C0 d2Log115Lo d2Log115Hi:ℚ):ℝ)) ≤ ((d2Transfer188Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer188Arithmetic
  linarith
#print axioms d2Transfer188Arithmetic
#print axioms d2Transfer188Bound
def d2Transfer189Lo : ℚ := (d2LitsNearTransfers023.q2 (21726425) 1 (-26))
def d2Transfer189Hi : ℚ := (d2LitsNearTransfers023.q2 (11702073) 1 (-25))
def d2Transfer189Cap : ℚ := (d2LitsNearTransfers023.q2 (31165051305) 1 (-40))
def d2Transfer189C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 11 (-5))
def d2Transfer189S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
def d2Transfer189C1 : ℚ := (d2LitsNearTransfers023.q2 (-5) 11 (-4))
def d2Transfer189S1 : ℚ := (d2LitsNearTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer189Arithmetic : weightedUpper d2Transfer189C0 d2Log115Lo d2Log115Hi + weightedUpper d2Transfer189C1 d2Log59Lo d2Log59Hi ≤ d2Transfer189Cap := by decide +kernel
theorem d2Transfer189Bound : ∀ x ∈ Set.Icc ((d2Transfer189Lo:ℚ):ℝ) ((d2Transfer189Hi:ℚ):ℝ), ((d2Transfer189C0:ℚ):ℝ)*Real.log |x-((d2Transfer189S0:ℚ):ℝ)| + ((d2Transfer189C1:ℚ):ℝ)*Real.log |x-((d2Transfer189S1:ℚ):ℝ)| ≤ ((d2Transfer189Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer189S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer189S0,d2Transfer189Lo,d2Transfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer189C0 then |x-((d2Transfer189S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer189S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer189S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer189S0,d2Transfer189Lo,d2Transfer189Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer189C0,d2Log115Q,d2Transfer189S0,d2Transfer189Lo,d2Transfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer189C0 d2Transfer189S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have hn1 : x-((d2Transfer189S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer189S1,d2Transfer189Lo,d2Transfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer189C1 then |x-((d2Transfer189S1:ℚ):ℝ)| ≤ ((d2Log59Q:ℚ):ℝ) else ((d2Log59Q:ℚ):ℝ) ≤ |x-((d2Transfer189S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer189S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer189S1,d2Transfer189Lo,d2Transfer189Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer189C1,d2Log59Q,d2Transfer189S1,d2Transfer189Lo,d2Transfer189Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer189C1 d2Transfer189S1 d2Log59Q d2Log59Lo d2Log59Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log59Bounds
  have har : (((weightedUpper d2Transfer189C0 d2Log115Lo d2Log115Hi:ℚ):ℝ) + ((weightedUpper d2Transfer189C1 d2Log59Lo d2Log59Hi:ℚ):ℝ)) ≤ ((d2Transfer189Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer189Arithmetic
  linarith
#print axioms d2Transfer189Arithmetic
#print axioms d2Transfer189Bound
def d2Transfer190Lo : ℚ := (d2LitsNearTransfers023.q2 (11702073) 1 (-25))
def d2Transfer190Hi : ℚ := (d2LitsNearTransfers023.q2 (25081867) 1 (-26))
def d2Transfer190Cap : ℚ := (d2LitsNearTransfers023.q2 (649441385) 1 (-39))
def d2Transfer190C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 25 (-4))
def d2Transfer190S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer190Arithmetic : weightedUpper d2Transfer190C0 d2Log116Lo d2Log116Hi ≤ d2Transfer190Cap := by decide +kernel
theorem d2Transfer190Bound : ∀ x ∈ Set.Icc ((d2Transfer190Lo:ℚ):ℝ) ((d2Transfer190Hi:ℚ):ℝ), ((d2Transfer190C0:ℚ):ℝ)*Real.log |x-((d2Transfer190S0:ℚ):ℝ)| ≤ ((d2Transfer190Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer190S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer190S0,d2Transfer190Lo,d2Transfer190Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer190C0 then |x-((d2Transfer190S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer190S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer190S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer190S0,d2Transfer190Lo,d2Transfer190Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer190C0,d2Log116Q,d2Transfer190S0,d2Transfer190Lo,d2Transfer190Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer190C0 d2Transfer190S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have har : (((weightedUpper d2Transfer190C0 d2Log116Lo d2Log116Hi:ℚ):ℝ)) ≤ ((d2Transfer190Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer190Arithmetic
  linarith
#print axioms d2Transfer190Arithmetic
#print axioms d2Transfer190Bound
def d2Transfer191Lo : ℚ := (d2LitsNearTransfers023.q2 (11702073) 1 (-25))
def d2Transfer191Hi : ℚ := (d2LitsNearTransfers023.q2 (25081867) 1 (-26))
def d2Transfer191Cap : ℚ := (d2LitsNearTransfers023.q2 (2436024149) 1 (-40))
def d2Transfer191C0 : ℚ := (d2LitsNearTransfers023.q2 (1) 275 (-4))
def d2Transfer191S0 : ℚ := (d2LitsNearTransfers023.q2 (-1) 1 (0))
def d2Transfer191C1 : ℚ := (d2LitsNearTransfers023.q2 (-1) 55 (-3))
def d2Transfer191S1 : ℚ := (d2LitsNearTransfers023.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer191Arithmetic : weightedUpper d2Transfer191C0 d2Log116Lo d2Log116Hi + weightedUpper d2Transfer191C1 d2Log58Lo d2Log58Hi ≤ d2Transfer191Cap := by decide +kernel
theorem d2Transfer191Bound : ∀ x ∈ Set.Icc ((d2Transfer191Lo:ℚ):ℝ) ((d2Transfer191Hi:ℚ):ℝ), ((d2Transfer191C0:ℚ):ℝ)*Real.log |x-((d2Transfer191S0:ℚ):ℝ)| + ((d2Transfer191C1:ℚ):ℝ)*Real.log |x-((d2Transfer191S1:ℚ):ℝ)| ≤ ((d2Transfer191Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer191S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer191S0,d2Transfer191Lo,d2Transfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer191C0 then |x-((d2Transfer191S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer191S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer191S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer191S0,d2Transfer191Lo,d2Transfer191Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer191C0,d2Log116Q,d2Transfer191S0,d2Transfer191Lo,d2Transfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer191C0 d2Transfer191S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have hn1 : x-((d2Transfer191S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer191S1,d2Transfer191Lo,d2Transfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer191C1 then |x-((d2Transfer191S1:ℚ):ℝ)| ≤ ((d2Log58Q:ℚ):ℝ) else ((d2Log58Q:ℚ):ℝ) ≤ |x-((d2Transfer191S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer191S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer191S1,d2Transfer191Lo,d2Transfer191Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers023.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer191C1,d2Log58Q,d2Transfer191S1,d2Transfer191Lo,d2Transfer191Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer191C1 d2Transfer191S1 d2Log58Q d2Log58Lo d2Log58Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log58Bounds
  have har : (((weightedUpper d2Transfer191C0 d2Log116Lo d2Log116Hi:ℚ):ℝ) + ((weightedUpper d2Transfer191C1 d2Log58Lo d2Log58Hi:ℚ):ℝ)) ≤ ((d2Transfer191Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer191Arithmetic
  linarith
#print axioms d2Transfer191Arithmetic
#print axioms d2Transfer191Bound
end CatalanMeasure.GenD.Signed.Data.Cells
