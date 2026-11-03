module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers080
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers080
open D72.LogTransfer
def d2Transfer640Lo : ℚ := (d2LitsNearTransfers080.q2 (999) 125 (-3))
def d2Transfer640Hi : ℚ := (d2LitsNearTransfers080.q2 (16760439) 1 (-24))
def d2Transfer640Cap : ℚ := (d2LitsNearTransfers080.q2 (13083733277321293880269) 1 (-79))
def d2Transfer640C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 1 (-5))
def d2Transfer640S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer640Arithmetic : weightedUpper d2Transfer640C0 d2Log175Lo d2Log175Hi ≤ d2Transfer640Cap := by decide +kernel
theorem d2Transfer640Bound : ∀ x ∈ Set.Icc ((d2Transfer640Lo:ℚ):ℝ) ((d2Transfer640Hi:ℚ):ℝ), ((d2Transfer640C0:ℚ):ℝ)*Real.log |x-((d2Transfer640S0:ℚ):ℝ)| ≤ ((d2Transfer640Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer640S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer640S0,d2Transfer640Lo,d2Transfer640Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer640C0 then |x-((d2Transfer640S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer640S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer640S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer640S0,d2Transfer640Lo,d2Transfer640Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer640C0,d2Log175Q,d2Transfer640S0,d2Transfer640Lo,d2Transfer640Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer640C0 d2Transfer640S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer640C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer640Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer640Arithmetic
  linarith
#print axioms d2Transfer640Arithmetic
#print axioms d2Transfer640Bound
def d2Transfer641Lo : ℚ := (d2LitsNearTransfers080.q2 (16760439) 1 (-24))
def d2Transfer641Hi : ℚ := (d2LitsNearTransfers080.q2 (1023) 1 (-10))
def d2Transfer641Cap : ℚ := (d2LitsNearTransfers080.q2 (1046920323180841822905) 1 (-79))
def d2Transfer641C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 25 (-4))
def d2Transfer641S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer641Arithmetic : weightedUpper d2Transfer641C0 d2Log176Lo d2Log176Hi ≤ d2Transfer641Cap := by decide +kernel
theorem d2Transfer641Bound : ∀ x ∈ Set.Icc ((d2Transfer641Lo:ℚ):ℝ) ((d2Transfer641Hi:ℚ):ℝ), ((d2Transfer641C0:ℚ):ℝ)*Real.log |x-((d2Transfer641S0:ℚ):ℝ)| ≤ ((d2Transfer641Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer641S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer641S0,d2Transfer641Lo,d2Transfer641Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer641C0 then |x-((d2Transfer641S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer641S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer641S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer641S0,d2Transfer641Lo,d2Transfer641Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer641C0,d2Log176Q,d2Transfer641S0,d2Transfer641Lo,d2Transfer641Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer641C0 d2Transfer641S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer641C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer641Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer641Arithmetic
  linarith
#print axioms d2Transfer641Arithmetic
#print axioms d2Transfer641Bound
def d2Transfer642Lo : ℚ := (d2LitsNearTransfers080.q2 (16760439) 1 (-24))
def d2Transfer642Hi : ℚ := (d2LitsNearTransfers080.q2 (1023) 1 (-10))
def d2Transfer642Cap : ℚ := (d2LitsNearTransfers080.q2 (1046920113723876731577) 1 (-79))
def d2Transfer642C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 25 (-4))
def d2Transfer642S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer642Arithmetic : weightedUpper d2Transfer642C0 d2Log176Lo d2Log176Hi ≤ d2Transfer642Cap := by decide +kernel
theorem d2Transfer642Bound : ∀ x ∈ Set.Icc ((d2Transfer642Lo:ℚ):ℝ) ((d2Transfer642Hi:ℚ):ℝ), ((d2Transfer642C0:ℚ):ℝ)*Real.log |x-((d2Transfer642S0:ℚ):ℝ)| ≤ ((d2Transfer642Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer642S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer642S0,d2Transfer642Lo,d2Transfer642Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer642C0 then |x-((d2Transfer642S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer642S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer642S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer642S0,d2Transfer642Lo,d2Transfer642Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer642C0,d2Log176Q,d2Transfer642S0,d2Transfer642Lo,d2Transfer642Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer642C0 d2Transfer642S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer642C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer642Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer642Arithmetic
  linarith
#print axioms d2Transfer642Arithmetic
#print axioms d2Transfer642Bound
def d2Transfer643Lo : ℚ := (d2LitsNearTransfers080.q2 (16760439) 1 (-24))
def d2Transfer643Hi : ℚ := (d2LitsNearTransfers080.q2 (1023) 1 (-10))
def d2Transfer643Cap : ℚ := (d2LitsNearTransfers080.q2 (13083954428117574642361) 1 (-79))
def d2Transfer643C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 1 (-5))
def d2Transfer643S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer643Arithmetic : weightedUpper d2Transfer643C0 d2Log176Lo d2Log176Hi ≤ d2Transfer643Cap := by decide +kernel
theorem d2Transfer643Bound : ∀ x ∈ Set.Icc ((d2Transfer643Lo:ℚ):ℝ) ((d2Transfer643Hi:ℚ):ℝ), ((d2Transfer643C0:ℚ):ℝ)*Real.log |x-((d2Transfer643S0:ℚ):ℝ)| ≤ ((d2Transfer643Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer643S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer643S0,d2Transfer643Lo,d2Transfer643Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer643C0 then |x-((d2Transfer643S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer643S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer643S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer643S0,d2Transfer643Lo,d2Transfer643Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer643C0,d2Log176Q,d2Transfer643S0,d2Transfer643Lo,d2Transfer643Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer643C0 d2Transfer643S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer643C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer643Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer643Arithmetic
  linarith
#print axioms d2Transfer643Arithmetic
#print axioms d2Transfer643Bound
def d2Transfer644Lo : ℚ := (d2LitsNearTransfers080.q2 (16760439) 1 (-24))
def d2Transfer644Hi : ℚ := (d2LitsNearTransfers080.q2 (1023) 1 (-10))
def d2Transfer644Cap : ℚ := (d2LitsNearTransfers080.q2 (13083954626029667642041) 1 (-79))
def d2Transfer644C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 1 (-5))
def d2Transfer644S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer644Arithmetic : weightedUpper d2Transfer644C0 d2Log176Lo d2Log176Hi ≤ d2Transfer644Cap := by decide +kernel
theorem d2Transfer644Bound : ∀ x ∈ Set.Icc ((d2Transfer644Lo:ℚ):ℝ) ((d2Transfer644Hi:ℚ):ℝ), ((d2Transfer644C0:ℚ):ℝ)*Real.log |x-((d2Transfer644S0:ℚ):ℝ)| ≤ ((d2Transfer644Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer644S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer644S0,d2Transfer644Lo,d2Transfer644Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer644C0 then |x-((d2Transfer644S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer644S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer644S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer644S0,d2Transfer644Lo,d2Transfer644Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer644C0,d2Log176Q,d2Transfer644S0,d2Transfer644Lo,d2Transfer644Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer644C0 d2Transfer644S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer644C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer644Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer644Arithmetic
  linarith
#print axioms d2Transfer644Arithmetic
#print axioms d2Transfer644Bound
def d2Transfer645Lo : ℚ := (d2LitsNearTransfers080.q2 (1023) 1 (-10))
def d2Transfer645Hi : ℚ := (d2LitsNearTransfers080.q2 (2047) 1 (-11))
def d2Transfer645Cap : ℚ := (d2LitsNearTransfers080.q2 (1051533698690763017477) 1 (-79))
def d2Transfer645C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 25 (-4))
def d2Transfer645S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer645Arithmetic : weightedUpper d2Transfer645C0 d2Log177Lo d2Log177Hi ≤ d2Transfer645Cap := by decide +kernel
theorem d2Transfer645Bound : ∀ x ∈ Set.Icc ((d2Transfer645Lo:ℚ):ℝ) ((d2Transfer645Hi:ℚ):ℝ), ((d2Transfer645C0:ℚ):ℝ)*Real.log |x-((d2Transfer645S0:ℚ):ℝ)| ≤ ((d2Transfer645Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer645S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer645S0,d2Transfer645Lo,d2Transfer645Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer645C0 then |x-((d2Transfer645S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer645S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer645S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer645S0,d2Transfer645Lo,d2Transfer645Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer645C0,d2Log177Q,d2Transfer645S0,d2Transfer645Lo,d2Transfer645Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer645C0 d2Transfer645S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer645C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer645Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer645Arithmetic
  linarith
#print axioms d2Transfer645Arithmetic
#print axioms d2Transfer645Bound
def d2Transfer646Lo : ℚ := (d2LitsNearTransfers080.q2 (1023) 1 (-10))
def d2Transfer646Hi : ℚ := (d2LitsNearTransfers080.q2 (2047) 1 (-11))
def d2Transfer646Cap : ℚ := (d2LitsNearTransfers080.q2 (1051533489233797926149) 1 (-79))
def d2Transfer646C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 25 (-4))
def d2Transfer646S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer646Arithmetic : weightedUpper d2Transfer646C0 d2Log177Lo d2Log177Hi ≤ d2Transfer646Cap := by decide +kernel
theorem d2Transfer646Bound : ∀ x ∈ Set.Icc ((d2Transfer646Lo:ℚ):ℝ) ((d2Transfer646Hi:ℚ):ℝ), ((d2Transfer646C0:ℚ):ℝ)*Real.log |x-((d2Transfer646S0:ℚ):ℝ)| ≤ ((d2Transfer646Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer646S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer646S0,d2Transfer646Lo,d2Transfer646Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer646C0 then |x-((d2Transfer646S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer646S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer646S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer646S0,d2Transfer646Lo,d2Transfer646Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer646C0,d2Log177Q,d2Transfer646S0,d2Transfer646Lo,d2Transfer646Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer646C0 d2Transfer646S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer646C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer646Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer646Arithmetic
  linarith
#print axioms d2Transfer646Arithmetic
#print axioms d2Transfer646Bound
def d2Transfer647Lo : ℚ := (d2LitsNearTransfers080.q2 (1023) 1 (-10))
def d2Transfer647Hi : ℚ := (d2LitsNearTransfers080.q2 (2047) 1 (-11))
def d2Transfer647Cap : ℚ := (d2LitsNearTransfers080.q2 (13088567803627495836933) 1 (-79))
def d2Transfer647C0 : ℚ := (d2LitsNearTransfers080.q2 (1) 1 (-5))
def d2Transfer647S0 : ℚ := (d2LitsNearTransfers080.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer647Arithmetic : weightedUpper d2Transfer647C0 d2Log177Lo d2Log177Hi ≤ d2Transfer647Cap := by decide +kernel
theorem d2Transfer647Bound : ∀ x ∈ Set.Icc ((d2Transfer647Lo:ℚ):ℝ) ((d2Transfer647Hi:ℚ):ℝ), ((d2Transfer647C0:ℚ):ℝ)*Real.log |x-((d2Transfer647S0:ℚ):ℝ)| ≤ ((d2Transfer647Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer647S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer647S0,d2Transfer647Lo,d2Transfer647Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer647C0 then |x-((d2Transfer647S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer647S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer647S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer647S0,d2Transfer647Lo,d2Transfer647Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers080.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer647C0,d2Log177Q,d2Transfer647S0,d2Transfer647Lo,d2Transfer647Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer647C0 d2Transfer647S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer647C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer647Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer647Arithmetic
  linarith
#print axioms d2Transfer647Arithmetic
#print axioms d2Transfer647Bound
end CatalanMeasure.GenD.Signed.Data.Cells
