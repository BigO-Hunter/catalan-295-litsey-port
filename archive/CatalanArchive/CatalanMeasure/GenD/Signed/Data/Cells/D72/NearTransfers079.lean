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
namespace d2LitsNearTransfers079
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers079
open D72.LogTransfer
def d2Transfer632Lo : ℚ := (d2LitsNearTransfers079.q2 (131071) 1 (-17))
def d2Transfer632Hi : ℚ := (d2LitsNearTransfers079.q2 (262143) 1 (-18))
def d2Transfer632Cap : ℚ := (d2LitsNearTransfers079.q2 (4091607507455043953) 1 (-71))
def d2Transfer632C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 25 (-4))
def d2Transfer632S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer632Arithmetic : weightedUpper d2Transfer632C0 d2Log184Lo d2Log184Hi ≤ d2Transfer632Cap := by decide +kernel
theorem d2Transfer632Bound : ∀ x ∈ Set.Icc ((d2Transfer632Lo:ℚ):ℝ) ((d2Transfer632Hi:ℚ):ℝ), ((d2Transfer632C0:ℚ):ℝ)*Real.log |x-((d2Transfer632S0:ℚ):ℝ)| ≤ ((d2Transfer632Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer632S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer632S0,d2Transfer632Lo,d2Transfer632Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer632C0 then |x-((d2Transfer632S0:ℚ):ℝ)| ≤ ((d2Log184Q:ℚ):ℝ) else ((d2Log184Q:ℚ):ℝ) ≤ |x-((d2Transfer632S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer632S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer632S0,d2Transfer632Lo,d2Transfer632Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer632C0,d2Log184Q,d2Transfer632S0,d2Transfer632Lo,d2Transfer632Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer632C0 d2Transfer632S0 d2Log184Q d2Log184Lo d2Log184Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log184Bounds
  have har : (((weightedUpper d2Transfer632C0 d2Log184Lo d2Log184Hi:ℚ):ℝ)) ≤ ((d2Transfer632Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer632Arithmetic
  linarith
#print axioms d2Transfer632Arithmetic
#print axioms d2Transfer632Bound
def d2Transfer633Lo : ℚ := (d2LitsNearTransfers079.q2 (262143) 1 (-18))
def d2Transfer633Hi : ℚ := (d2LitsNearTransfers079.q2 (524287) 1 (-19))
def d2Transfer633Cap : ℚ := (d2LitsNearTransfers079.q2 (1047453172519398689215) 1 (-79))
def d2Transfer633C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 25 (-4))
def d2Transfer633S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer633Arithmetic : weightedUpper d2Transfer633C0 d2Log185Lo d2Log185Hi ≤ d2Transfer633Cap := by decide +kernel
theorem d2Transfer633Bound : ∀ x ∈ Set.Icc ((d2Transfer633Lo:ℚ):ℝ) ((d2Transfer633Hi:ℚ):ℝ), ((d2Transfer633C0:ℚ):ℝ)*Real.log |x-((d2Transfer633S0:ℚ):ℝ)| ≤ ((d2Transfer633Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer633S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer633S0,d2Transfer633Lo,d2Transfer633Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer633C0 then |x-((d2Transfer633S0:ℚ):ℝ)| ≤ ((d2Log185Q:ℚ):ℝ) else ((d2Log185Q:ℚ):ℝ) ≤ |x-((d2Transfer633S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer633S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer633S0,d2Transfer633Lo,d2Transfer633Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer633C0,d2Log185Q,d2Transfer633S0,d2Transfer633Lo,d2Transfer633Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer633C0 d2Transfer633S0 d2Log185Q d2Log185Lo d2Log185Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log185Bounds
  have har : (((weightedUpper d2Transfer633C0 d2Log185Lo d2Log185Hi:ℚ):ℝ)) ≤ ((d2Transfer633Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer633Arithmetic
  linarith
#print axioms d2Transfer633Arithmetic
#print axioms d2Transfer633Bound
def d2Transfer634Lo : ℚ := (d2LitsNearTransfers079.q2 (262143) 1 (-18))
def d2Transfer634Hi : ℚ := (d2LitsNearTransfers079.q2 (524287) 1 (-19))
def d2Transfer634Cap : ℚ := (d2LitsNearTransfers079.q2 (1047452963062433597887) 1 (-79))
def d2Transfer634C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 25 (-4))
def d2Transfer634S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer634Arithmetic : weightedUpper d2Transfer634C0 d2Log185Lo d2Log185Hi ≤ d2Transfer634Cap := by decide +kernel
theorem d2Transfer634Bound : ∀ x ∈ Set.Icc ((d2Transfer634Lo:ℚ):ℝ) ((d2Transfer634Hi:ℚ):ℝ), ((d2Transfer634C0:ℚ):ℝ)*Real.log |x-((d2Transfer634S0:ℚ):ℝ)| ≤ ((d2Transfer634Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer634S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer634S0,d2Transfer634Lo,d2Transfer634Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer634C0 then |x-((d2Transfer634S0:ℚ):ℝ)| ≤ ((d2Log185Q:ℚ):ℝ) else ((d2Log185Q:ℚ):ℝ) ≤ |x-((d2Transfer634S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer634S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer634S0,d2Transfer634Lo,d2Transfer634Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer634C0,d2Log185Q,d2Transfer634S0,d2Transfer634Lo,d2Transfer634Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer634C0 d2Transfer634S0 d2Log185Q d2Log185Lo d2Log185Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log185Bounds
  have har : (((weightedUpper d2Transfer634C0 d2Log185Lo d2Log185Hi:ℚ):ℝ)) ≤ ((d2Transfer634Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer634Arithmetic
  linarith
#print axioms d2Transfer634Arithmetic
#print axioms d2Transfer634Bound
def d2Transfer635Lo : ℚ := (d2LitsNearTransfers079.q2 (524287) 1 (-19))
def d2Transfer635Hi : ℚ := (d2LitsNearTransfers079.q2 (1) 1 (0))
def d2Transfer635Cap : ℚ := (d2LitsNearTransfers079.q2 (523727306835983321489) 1 (-78))
def d2Transfer635C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 25 (-4))
def d2Transfer635S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer635Arithmetic : weightedUpper d2Transfer635C0 d2Log186Lo d2Log186Hi ≤ d2Transfer635Cap := by decide +kernel
theorem d2Transfer635Bound : ∀ x ∈ Set.Icc ((d2Transfer635Lo:ℚ):ℝ) ((d2Transfer635Hi:ℚ):ℝ), ((d2Transfer635C0:ℚ):ℝ)*Real.log |x-((d2Transfer635S0:ℚ):ℝ)| ≤ ((d2Transfer635Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer635S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer635S0,d2Transfer635Lo,d2Transfer635Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer635C0 then |x-((d2Transfer635S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer635S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer635S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer635S0,d2Transfer635Lo,d2Transfer635Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer635C0,d2Log186Q,d2Transfer635S0,d2Transfer635Lo,d2Transfer635Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer635C0 d2Transfer635S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer635C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer635Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer635Arithmetic
  linarith
#print axioms d2Transfer635Arithmetic
#print axioms d2Transfer635Bound
def d2Transfer636Lo : ℚ := (d2LitsNearTransfers079.q2 (524287) 1 (-19))
def d2Transfer636Hi : ℚ := (d2LitsNearTransfers079.q2 (1) 1 (0))
def d2Transfer636Cap : ℚ := (d2LitsNearTransfers079.q2 (523727202107500775825) 1 (-78))
def d2Transfer636C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 25 (-4))
def d2Transfer636S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer636Arithmetic : weightedUpper d2Transfer636C0 d2Log186Lo d2Log186Hi ≤ d2Transfer636Cap := by decide +kernel
theorem d2Transfer636Bound : ∀ x ∈ Set.Icc ((d2Transfer636Lo:ℚ):ℝ) ((d2Transfer636Hi:ℚ):ℝ), ((d2Transfer636C0:ℚ):ℝ)*Real.log |x-((d2Transfer636S0:ℚ):ℝ)| ≤ ((d2Transfer636Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer636S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer636S0,d2Transfer636Lo,d2Transfer636Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer636C0 then |x-((d2Transfer636S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer636S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer636S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer636S0,d2Transfer636Lo,d2Transfer636Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer636C0,d2Log186Q,d2Transfer636S0,d2Transfer636Lo,d2Transfer636Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer636C0 d2Transfer636S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer636C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer636Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer636Arithmetic
  linarith
#print axioms d2Transfer636Arithmetic
#print axioms d2Transfer636Bound
def d2Transfer637Lo : ℚ := (d2LitsNearTransfers079.q2 (999) 125 (-3))
def d2Transfer637Hi : ℚ := (d2LitsNearTransfers079.q2 (16760439) 1 (-24))
def d2Transfer637Cap : ℚ := (d2LitsNearTransfers079.q2 (1046698974472468061133) 1 (-79))
def d2Transfer637C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 25 (-4))
def d2Transfer637S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer637Arithmetic : weightedUpper d2Transfer637C0 d2Log175Lo d2Log175Hi ≤ d2Transfer637Cap := by decide +kernel
theorem d2Transfer637Bound : ∀ x ∈ Set.Icc ((d2Transfer637Lo:ℚ):ℝ) ((d2Transfer637Hi:ℚ):ℝ), ((d2Transfer637C0:ℚ):ℝ)*Real.log |x-((d2Transfer637S0:ℚ):ℝ)| ≤ ((d2Transfer637Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer637S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer637S0,d2Transfer637Lo,d2Transfer637Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer637C0 then |x-((d2Transfer637S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer637S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer637S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer637S0,d2Transfer637Lo,d2Transfer637Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer637C0,d2Log175Q,d2Transfer637S0,d2Transfer637Lo,d2Transfer637Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer637C0 d2Transfer637S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer637C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer637Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer637Arithmetic
  linarith
#print axioms d2Transfer637Arithmetic
#print axioms d2Transfer637Bound
def d2Transfer638Lo : ℚ := (d2LitsNearTransfers079.q2 (999) 125 (-3))
def d2Transfer638Hi : ℚ := (d2LitsNearTransfers079.q2 (16760439) 1 (-24))
def d2Transfer638Cap : ℚ := (d2LitsNearTransfers079.q2 (1046698765015502969805) 1 (-79))
def d2Transfer638C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 25 (-4))
def d2Transfer638S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer638Arithmetic : weightedUpper d2Transfer638C0 d2Log175Lo d2Log175Hi ≤ d2Transfer638Cap := by decide +kernel
theorem d2Transfer638Bound : ∀ x ∈ Set.Icc ((d2Transfer638Lo:ℚ):ℝ) ((d2Transfer638Hi:ℚ):ℝ), ((d2Transfer638C0:ℚ):ℝ)*Real.log |x-((d2Transfer638S0:ℚ):ℝ)| ≤ ((d2Transfer638Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer638S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer638S0,d2Transfer638Lo,d2Transfer638Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer638C0 then |x-((d2Transfer638S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer638S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer638S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer638S0,d2Transfer638Lo,d2Transfer638Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer638C0,d2Log175Q,d2Transfer638S0,d2Transfer638Lo,d2Transfer638Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer638C0 d2Transfer638S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer638C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer638Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer638Arithmetic
  linarith
#print axioms d2Transfer638Arithmetic
#print axioms d2Transfer638Bound
def d2Transfer639Lo : ℚ := (d2LitsNearTransfers079.q2 (999) 125 (-3))
def d2Transfer639Hi : ℚ := (d2LitsNearTransfers079.q2 (16760439) 1 (-24))
def d2Transfer639Cap : ℚ := (d2LitsNearTransfers079.q2 (13083733079409200880589) 1 (-79))
def d2Transfer639C0 : ℚ := (d2LitsNearTransfers079.q2 (1) 1 (-5))
def d2Transfer639S0 : ℚ := (d2LitsNearTransfers079.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer639Arithmetic : weightedUpper d2Transfer639C0 d2Log175Lo d2Log175Hi ≤ d2Transfer639Cap := by decide +kernel
theorem d2Transfer639Bound : ∀ x ∈ Set.Icc ((d2Transfer639Lo:ℚ):ℝ) ((d2Transfer639Hi:ℚ):ℝ), ((d2Transfer639C0:ℚ):ℝ)*Real.log |x-((d2Transfer639S0:ℚ):ℝ)| ≤ ((d2Transfer639Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer639S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer639S0,d2Transfer639Lo,d2Transfer639Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer639C0 then |x-((d2Transfer639S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer639S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer639S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer639S0,d2Transfer639Lo,d2Transfer639Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers079.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer639C0,d2Log175Q,d2Transfer639S0,d2Transfer639Lo,d2Transfer639Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer639C0 d2Transfer639S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer639C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer639Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer639Arithmetic
  linarith
#print axioms d2Transfer639Arithmetic
#print axioms d2Transfer639Bound
end CatalanMeasure.GenD.Signed.Data.Cells
