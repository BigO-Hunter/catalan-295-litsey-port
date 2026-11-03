module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers083
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers083
open D72.LogTransfer
def d2Transfer664Lo : ℚ := (d2LitsNearTransfers083.q2 (16383) 1 (-14))
def d2Transfer664Hi : ℚ := (d2LitsNearTransfers083.q2 (32767) 1 (-15))
def d2Transfer664Cap : ℚ := (d2LitsNearTransfers083.q2 (26185784036048830116261) 1 (-80))
def d2Transfer664C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 1 (-5))
def d2Transfer664S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer664Arithmetic : weightedUpper d2Transfer664C0 d2Log181Lo d2Log181Hi ≤ d2Transfer664Cap := by decide +kernel
theorem d2Transfer664Bound : ∀ x ∈ Set.Icc ((d2Transfer664Lo:ℚ):ℝ) ((d2Transfer664Hi:ℚ):ℝ), ((d2Transfer664C0:ℚ):ℝ)*Real.log |x-((d2Transfer664S0:ℚ):ℝ)| ≤ ((d2Transfer664Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer664S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer664S0,d2Transfer664Lo,d2Transfer664Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer664C0 then |x-((d2Transfer664S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer664S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer664S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer664S0,d2Transfer664Lo,d2Transfer664Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer664C0,d2Log181Q,d2Transfer664S0,d2Transfer664Lo,d2Transfer664Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer664C0 d2Transfer664S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer664C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer664Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer664Arithmetic
  linarith
#print axioms d2Transfer664Arithmetic
#print axioms d2Transfer664Bound
def d2Transfer665Lo : ℚ := (d2LitsNearTransfers083.q2 (32767) 1 (-15))
def d2Transfer665Hi : ℚ := (d2LitsNearTransfers083.q2 (65535) 1 (-16))
def d2Transfer665Cap : ℚ := (d2LitsNearTransfers083.q2 (1056001832012952110189) 1 (-79))
def d2Transfer665C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 25 (-4))
def d2Transfer665S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer665Arithmetic : weightedUpper d2Transfer665C0 d2Log182Lo d2Log182Hi ≤ d2Transfer665Cap := by decide +kernel
theorem d2Transfer665Bound : ∀ x ∈ Set.Icc ((d2Transfer665Lo:ℚ):ℝ) ((d2Transfer665Hi:ℚ):ℝ), ((d2Transfer665C0:ℚ):ℝ)*Real.log |x-((d2Transfer665S0:ℚ):ℝ)| ≤ ((d2Transfer665Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer665S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer665S0,d2Transfer665Lo,d2Transfer665Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer665C0 then |x-((d2Transfer665S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer665S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer665S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer665S0,d2Transfer665Lo,d2Transfer665Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer665C0,d2Log182Q,d2Transfer665S0,d2Transfer665Lo,d2Transfer665Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer665C0 d2Transfer665S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer665C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer665Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer665Arithmetic
  linarith
#print axioms d2Transfer665Arithmetic
#print axioms d2Transfer665Bound
def d2Transfer666Lo : ℚ := (d2LitsNearTransfers083.q2 (32767) 1 (-15))
def d2Transfer666Hi : ℚ := (d2LitsNearTransfers083.q2 (65535) 1 (-16))
def d2Transfer666Cap : ℚ := (d2LitsNearTransfers083.q2 (1056001622555987018861) 1 (-79))
def d2Transfer666C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 25 (-4))
def d2Transfer666S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer666Arithmetic : weightedUpper d2Transfer666C0 d2Log182Lo d2Log182Hi ≤ d2Transfer666Cap := by decide +kernel
theorem d2Transfer666Bound : ∀ x ∈ Set.Icc ((d2Transfer666Lo:ℚ):ℝ) ((d2Transfer666Hi:ℚ):ℝ), ((d2Transfer666C0:ℚ):ℝ)*Real.log |x-((d2Transfer666S0:ℚ):ℝ)| ≤ ((d2Transfer666Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer666S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer666S0,d2Transfer666Lo,d2Transfer666Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer666C0 then |x-((d2Transfer666S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer666S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer666S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer666S0,d2Transfer666Lo,d2Transfer666Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer666C0,d2Log182Q,d2Transfer666S0,d2Transfer666Lo,d2Transfer666Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer666C0 d2Transfer666S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer666C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer666Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer666Arithmetic
  linarith
#print axioms d2Transfer666Arithmetic
#print axioms d2Transfer666Bound
def d2Transfer667Lo : ℚ := (d2LitsNearTransfers083.q2 (32767) 1 (-15))
def d2Transfer667Hi : ℚ := (d2LitsNearTransfers083.q2 (65535) 1 (-16))
def d2Transfer667Cap : ℚ := (d2LitsNearTransfers083.q2 (13093035936949684929645) 1 (-79))
def d2Transfer667C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 1 (-5))
def d2Transfer667S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer667Arithmetic : weightedUpper d2Transfer667C0 d2Log182Lo d2Log182Hi ≤ d2Transfer667Cap := by decide +kernel
theorem d2Transfer667Bound : ∀ x ∈ Set.Icc ((d2Transfer667Lo:ℚ):ℝ) ((d2Transfer667Hi:ℚ):ℝ), ((d2Transfer667C0:ℚ):ℝ)*Real.log |x-((d2Transfer667S0:ℚ):ℝ)| ≤ ((d2Transfer667Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer667S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer667S0,d2Transfer667Lo,d2Transfer667Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer667C0 then |x-((d2Transfer667S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer667S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer667S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer667S0,d2Transfer667Lo,d2Transfer667Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer667C0,d2Log182Q,d2Transfer667S0,d2Transfer667Lo,d2Transfer667Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer667C0 d2Transfer667S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer667C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer667Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer667Arithmetic
  linarith
#print axioms d2Transfer667Arithmetic
#print axioms d2Transfer667Bound
def d2Transfer668Lo : ℚ := (d2LitsNearTransfers083.q2 (32767) 1 (-15))
def d2Transfer668Hi : ℚ := (d2LitsNearTransfers083.q2 (65535) 1 (-16))
def d2Transfer668Cap : ℚ := (d2LitsNearTransfers083.q2 (13093036134861777929325) 1 (-79))
def d2Transfer668C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 1 (-5))
def d2Transfer668S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer668Arithmetic : weightedUpper d2Transfer668C0 d2Log182Lo d2Log182Hi ≤ d2Transfer668Cap := by decide +kernel
theorem d2Transfer668Bound : ∀ x ∈ Set.Icc ((d2Transfer668Lo:ℚ):ℝ) ((d2Transfer668Hi:ℚ):ℝ), ((d2Transfer668C0:ℚ):ℝ)*Real.log |x-((d2Transfer668S0:ℚ):ℝ)| ≤ ((d2Transfer668Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer668S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer668S0,d2Transfer668Lo,d2Transfer668Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer668C0 then |x-((d2Transfer668S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer668S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer668S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer668S0,d2Transfer668Lo,d2Transfer668Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer668C0,d2Log182Q,d2Transfer668S0,d2Transfer668Lo,d2Transfer668Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer668C0 d2Transfer668S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer668C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer668Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer668Arithmetic
  linarith
#print axioms d2Transfer668Arithmetic
#print axioms d2Transfer668Bound
def d2Transfer669Lo : ℚ := (d2LitsNearTransfers083.q2 (65535) 1 (-16))
def d2Transfer669Hi : ℚ := (d2LitsNearTransfers083.q2 (1) 1 (0))
def d2Transfer669Cap : ℚ := (d2LitsNearTransfers083.q2 (132018243468848322021) 1 (-76))
def d2Transfer669C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 25 (-4))
def d2Transfer669S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer669Arithmetic : weightedUpper d2Transfer669C0 d2Log186Lo d2Log186Hi ≤ d2Transfer669Cap := by decide +kernel
theorem d2Transfer669Bound : ∀ x ∈ Set.Icc ((d2Transfer669Lo:ℚ):ℝ) ((d2Transfer669Hi:ℚ):ℝ), ((d2Transfer669C0:ℚ):ℝ)*Real.log |x-((d2Transfer669S0:ℚ):ℝ)| ≤ ((d2Transfer669Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer669S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer669S0,d2Transfer669Lo,d2Transfer669Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer669C0 then |x-((d2Transfer669S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer669S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer669S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer669S0,d2Transfer669Lo,d2Transfer669Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer669C0,d2Log186Q,d2Transfer669S0,d2Transfer669Lo,d2Transfer669Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer669C0 d2Transfer669S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer669C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer669Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer669Arithmetic
  linarith
#print axioms d2Transfer669Arithmetic
#print axioms d2Transfer669Bound
def d2Transfer670Lo : ℚ := (d2LitsNearTransfers083.q2 (65535) 1 (-16))
def d2Transfer670Hi : ℚ := (d2LitsNearTransfers083.q2 (1) 1 (0))
def d2Transfer670Cap : ℚ := (d2LitsNearTransfers083.q2 (132018217286727685605) 1 (-76))
def d2Transfer670C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 25 (-4))
def d2Transfer670S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer670Arithmetic : weightedUpper d2Transfer670C0 d2Log186Lo d2Log186Hi ≤ d2Transfer670Cap := by decide +kernel
theorem d2Transfer670Bound : ∀ x ∈ Set.Icc ((d2Transfer670Lo:ℚ):ℝ) ((d2Transfer670Hi:ℚ):ℝ), ((d2Transfer670C0:ℚ):ℝ)*Real.log |x-((d2Transfer670S0:ℚ):ℝ)| ≤ ((d2Transfer670Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer670S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer670S0,d2Transfer670Lo,d2Transfer670Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer670C0 then |x-((d2Transfer670S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer670S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer670S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer670S0,d2Transfer670Lo,d2Transfer670Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer670C0,d2Log186Q,d2Transfer670S0,d2Transfer670Lo,d2Transfer670Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer670C0 d2Transfer670S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer670C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer670Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer670Arithmetic
  linarith
#print axioms d2Transfer670Arithmetic
#print axioms d2Transfer670Bound
def d2Transfer671Lo : ℚ := (d2LitsNearTransfers083.q2 (65535) 1 (-16))
def d2Transfer671Hi : ℚ := (d2LitsNearTransfers083.q2 (1) 1 (0))
def d2Transfer671Cap : ℚ := (d2LitsNearTransfers083.q2 (1636647506585939924453) 1 (-76))
def d2Transfer671C0 : ℚ := (d2LitsNearTransfers083.q2 (1) 1 (-5))
def d2Transfer671S0 : ℚ := (d2LitsNearTransfers083.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer671Arithmetic : weightedUpper d2Transfer671C0 d2Log186Lo d2Log186Hi ≤ d2Transfer671Cap := by decide +kernel
theorem d2Transfer671Bound : ∀ x ∈ Set.Icc ((d2Transfer671Lo:ℚ):ℝ) ((d2Transfer671Hi:ℚ):ℝ), ((d2Transfer671C0:ℚ):ℝ)*Real.log |x-((d2Transfer671S0:ℚ):ℝ)| ≤ ((d2Transfer671Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer671S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer671S0,d2Transfer671Lo,d2Transfer671Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer671C0 then |x-((d2Transfer671S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer671S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer671S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer671S0,d2Transfer671Lo,d2Transfer671Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers083.q2, d2LitsNearLogCache011.q2, d2Transfer671C0,d2Log186Q,d2Transfer671S0,d2Transfer671Lo,d2Transfer671Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer671C0 d2Transfer671S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer671C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer671Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer671Arithmetic
  linarith
#print axioms d2Transfer671Arithmetic
#print axioms d2Transfer671Bound
end CatalanMeasure.GenD.Signed.Data.Cells
