module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers013
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers013
open D72.LogTransfer
def d2Transfer104Lo : ℚ := (d2LitsNearTransfers013.q2 (58048651) 1 (-29))
def d2Transfer104Hi : ℚ := (d2LitsNearTransfers013.q2 (14931593) 1 (-27))
def d2Transfer104Cap : ℚ := (d2LitsNearTransfers013.q2 (16281318465) 1 (-40))
def d2Transfer104C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 1 (-5))
def d2Transfer104S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer104Arithmetic : weightedUpper d2Transfer104C0 d2Log92Lo d2Log92Hi ≤ d2Transfer104Cap := by decide +kernel
theorem d2Transfer104Bound : ∀ x ∈ Set.Icc ((d2Transfer104Lo:ℚ):ℝ) ((d2Transfer104Hi:ℚ):ℝ), ((d2Transfer104C0:ℚ):ℝ)*Real.log |x-((d2Transfer104S0:ℚ):ℝ)| ≤ ((d2Transfer104Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer104S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer104S0,d2Transfer104Lo,d2Transfer104Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer104C0 then |x-((d2Transfer104S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer104S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer104S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer104S0,d2Transfer104Lo,d2Transfer104Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer104C0,d2Log92Q,d2Transfer104S0,d2Transfer104Lo,d2Transfer104Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer104C0 d2Transfer104S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have har : (((weightedUpper d2Transfer104C0 d2Log92Lo d2Log92Hi:ℚ):ℝ)) ≤ ((d2Transfer104Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer104Arithmetic
  linarith
#print axioms d2Transfer104Arithmetic
#print axioms d2Transfer104Bound
def d2Transfer105Lo : ℚ := (d2LitsNearTransfers013.q2 (58048651) 1 (-29))
def d2Transfer105Hi : ℚ := (d2LitsNearTransfers013.q2 (14931593) 1 (-27))
def d2Transfer105Cap : ℚ := (d2LitsNearTransfers013.q2 (31165051305) 1 (-40))
def d2Transfer105C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 11 (-5))
def d2Transfer105S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
def d2Transfer105C1 : ℚ := (d2LitsNearTransfers013.q2 (-5) 11 (-4))
def d2Transfer105S1 : ℚ := (d2LitsNearTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer105Arithmetic : weightedUpper d2Transfer105C0 d2Log92Lo d2Log92Hi + weightedUpper d2Transfer105C1 d2Log82Lo d2Log82Hi ≤ d2Transfer105Cap := by decide +kernel
theorem d2Transfer105Bound : ∀ x ∈ Set.Icc ((d2Transfer105Lo:ℚ):ℝ) ((d2Transfer105Hi:ℚ):ℝ), ((d2Transfer105C0:ℚ):ℝ)*Real.log |x-((d2Transfer105S0:ℚ):ℝ)| + ((d2Transfer105C1:ℚ):ℝ)*Real.log |x-((d2Transfer105S1:ℚ):ℝ)| ≤ ((d2Transfer105Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer105S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer105S0,d2Transfer105Lo,d2Transfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer105C0 then |x-((d2Transfer105S0:ℚ):ℝ)| ≤ ((d2Log92Q:ℚ):ℝ) else ((d2Log92Q:ℚ):ℝ) ≤ |x-((d2Transfer105S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer105S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer105S0,d2Transfer105Lo,d2Transfer105Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer105C0,d2Log92Q,d2Transfer105S0,d2Transfer105Lo,d2Transfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer105C0 d2Transfer105S0 d2Log92Q d2Log92Lo d2Log92Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log92Bounds
  have hn1 : x-((d2Transfer105S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer105S1,d2Transfer105Lo,d2Transfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer105C1 then |x-((d2Transfer105S1:ℚ):ℝ)| ≤ ((d2Log82Q:ℚ):ℝ) else ((d2Log82Q:ℚ):ℝ) ≤ |x-((d2Transfer105S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer105S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer105S1,d2Transfer105Lo,d2Transfer105Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer105C1,d2Log82Q,d2Transfer105S1,d2Transfer105Lo,d2Transfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer105C1 d2Transfer105S1 d2Log82Q d2Log82Lo d2Log82Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log82Bounds
  have har : (((weightedUpper d2Transfer105C0 d2Log92Lo d2Log92Hi:ℚ):ℝ) + ((weightedUpper d2Transfer105C1 d2Log82Lo d2Log82Hi:ℚ):ℝ)) ≤ ((d2Transfer105Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer105Arithmetic
  linarith
#print axioms d2Transfer105Arithmetic
#print axioms d2Transfer105Bound
def d2Transfer106Lo : ℚ := (d2LitsNearTransfers013.q2 (14931593) 1 (-27))
def d2Transfer106Hi : ℚ := (d2LitsNearTransfers013.q2 (31540907) 1 (-28))
def d2Transfer106Cap : ℚ := (d2LitsNearTransfers013.q2 (649441385) 1 (-39))
def d2Transfer106C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 25 (-4))
def d2Transfer106S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer106Arithmetic : weightedUpper d2Transfer106C0 d2Log94Lo d2Log94Hi ≤ d2Transfer106Cap := by decide +kernel
theorem d2Transfer106Bound : ∀ x ∈ Set.Icc ((d2Transfer106Lo:ℚ):ℝ) ((d2Transfer106Hi:ℚ):ℝ), ((d2Transfer106C0:ℚ):ℝ)*Real.log |x-((d2Transfer106S0:ℚ):ℝ)| ≤ ((d2Transfer106Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer106S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer106S0,d2Transfer106Lo,d2Transfer106Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer106C0 then |x-((d2Transfer106S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer106S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer106S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer106S0,d2Transfer106Lo,d2Transfer106Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer106C0,d2Log94Q,d2Transfer106S0,d2Transfer106Lo,d2Transfer106Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer106C0 d2Transfer106S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have har : (((weightedUpper d2Transfer106C0 d2Log94Lo d2Log94Hi:ℚ):ℝ)) ≤ ((d2Transfer106Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer106Arithmetic
  linarith
#print axioms d2Transfer106Arithmetic
#print axioms d2Transfer106Bound
def d2Transfer107Lo : ℚ := (d2LitsNearTransfers013.q2 (14931593) 1 (-27))
def d2Transfer107Hi : ℚ := (d2LitsNearTransfers013.q2 (31540907) 1 (-28))
def d2Transfer107Cap : ℚ := (d2LitsNearTransfers013.q2 (2436024149) 1 (-40))
def d2Transfer107C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 275 (-4))
def d2Transfer107S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
def d2Transfer107C1 : ℚ := (d2LitsNearTransfers013.q2 (-1) 55 (-3))
def d2Transfer107S1 : ℚ := (d2LitsNearTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer107Arithmetic : weightedUpper d2Transfer107C0 d2Log94Lo d2Log94Hi + weightedUpper d2Transfer107C1 d2Log80Lo d2Log80Hi ≤ d2Transfer107Cap := by decide +kernel
theorem d2Transfer107Bound : ∀ x ∈ Set.Icc ((d2Transfer107Lo:ℚ):ℝ) ((d2Transfer107Hi:ℚ):ℝ), ((d2Transfer107C0:ℚ):ℝ)*Real.log |x-((d2Transfer107S0:ℚ):ℝ)| + ((d2Transfer107C1:ℚ):ℝ)*Real.log |x-((d2Transfer107S1:ℚ):ℝ)| ≤ ((d2Transfer107Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer107S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer107S0,d2Transfer107Lo,d2Transfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer107C0 then |x-((d2Transfer107S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer107S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer107S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer107S0,d2Transfer107Lo,d2Transfer107Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer107C0,d2Log94Q,d2Transfer107S0,d2Transfer107Lo,d2Transfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer107C0 d2Transfer107S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have hn1 : x-((d2Transfer107S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer107S1,d2Transfer107Lo,d2Transfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer107C1 then |x-((d2Transfer107S1:ℚ):ℝ)| ≤ ((d2Log80Q:ℚ):ℝ) else ((d2Log80Q:ℚ):ℝ) ≤ |x-((d2Transfer107S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer107S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer107S1,d2Transfer107Lo,d2Transfer107Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer107C1,d2Log80Q,d2Transfer107S1,d2Transfer107Lo,d2Transfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer107C1 d2Transfer107S1 d2Log80Q d2Log80Lo d2Log80Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log80Bounds
  have har : (((weightedUpper d2Transfer107C0 d2Log94Lo d2Log94Hi:ℚ):ℝ) + ((weightedUpper d2Transfer107C1 d2Log80Lo d2Log80Hi:ℚ):ℝ)) ≤ ((d2Transfer107Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer107Arithmetic
  linarith
#print axioms d2Transfer107Arithmetic
#print axioms d2Transfer107Bound
def d2Transfer108Lo : ℚ := (d2LitsNearTransfers013.q2 (14931593) 1 (-27))
def d2Transfer108Hi : ℚ := (d2LitsNearTransfers013.q2 (31540907) 1 (-28))
def d2Transfer108Cap : ℚ := (d2LitsNearTransfers013.q2 (16281318465) 1 (-40))
def d2Transfer108C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 1 (-5))
def d2Transfer108S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer108Arithmetic : weightedUpper d2Transfer108C0 d2Log94Lo d2Log94Hi ≤ d2Transfer108Cap := by decide +kernel
theorem d2Transfer108Bound : ∀ x ∈ Set.Icc ((d2Transfer108Lo:ℚ):ℝ) ((d2Transfer108Hi:ℚ):ℝ), ((d2Transfer108C0:ℚ):ℝ)*Real.log |x-((d2Transfer108S0:ℚ):ℝ)| ≤ ((d2Transfer108Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer108S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer108S0,d2Transfer108Lo,d2Transfer108Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer108C0 then |x-((d2Transfer108S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer108S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer108S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer108S0,d2Transfer108Lo,d2Transfer108Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer108C0,d2Log94Q,d2Transfer108S0,d2Transfer108Lo,d2Transfer108Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer108C0 d2Transfer108S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have har : (((weightedUpper d2Transfer108C0 d2Log94Lo d2Log94Hi:ℚ):ℝ)) ≤ ((d2Transfer108Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer108Arithmetic
  linarith
#print axioms d2Transfer108Arithmetic
#print axioms d2Transfer108Bound
def d2Transfer109Lo : ℚ := (d2LitsNearTransfers013.q2 (14931593) 1 (-27))
def d2Transfer109Hi : ℚ := (d2LitsNearTransfers013.q2 (31540907) 1 (-28))
def d2Transfer109Cap : ℚ := (d2LitsNearTransfers013.q2 (31165051305) 1 (-40))
def d2Transfer109C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 11 (-5))
def d2Transfer109S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
def d2Transfer109C1 : ℚ := (d2LitsNearTransfers013.q2 (-5) 11 (-4))
def d2Transfer109S1 : ℚ := (d2LitsNearTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer109Arithmetic : weightedUpper d2Transfer109C0 d2Log94Lo d2Log94Hi + weightedUpper d2Transfer109C1 d2Log80Lo d2Log80Hi ≤ d2Transfer109Cap := by decide +kernel
theorem d2Transfer109Bound : ∀ x ∈ Set.Icc ((d2Transfer109Lo:ℚ):ℝ) ((d2Transfer109Hi:ℚ):ℝ), ((d2Transfer109C0:ℚ):ℝ)*Real.log |x-((d2Transfer109S0:ℚ):ℝ)| + ((d2Transfer109C1:ℚ):ℝ)*Real.log |x-((d2Transfer109S1:ℚ):ℝ)| ≤ ((d2Transfer109Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer109S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer109S0,d2Transfer109Lo,d2Transfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer109C0 then |x-((d2Transfer109S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer109S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer109S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer109S0,d2Transfer109Lo,d2Transfer109Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer109C0,d2Log94Q,d2Transfer109S0,d2Transfer109Lo,d2Transfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer109C0 d2Transfer109S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have hn1 : x-((d2Transfer109S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer109S1,d2Transfer109Lo,d2Transfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer109C1 then |x-((d2Transfer109S1:ℚ):ℝ)| ≤ ((d2Log80Q:ℚ):ℝ) else ((d2Log80Q:ℚ):ℝ) ≤ |x-((d2Transfer109S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer109S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer109S1,d2Transfer109Lo,d2Transfer109Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer109C1,d2Log80Q,d2Transfer109S1,d2Transfer109Lo,d2Transfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer109C1 d2Transfer109S1 d2Log80Q d2Log80Lo d2Log80Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log80Bounds
  have har : (((weightedUpper d2Transfer109C0 d2Log94Lo d2Log94Hi:ℚ):ℝ) + ((weightedUpper d2Transfer109C1 d2Log80Lo d2Log80Hi:ℚ):ℝ)) ≤ ((d2Transfer109Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer109Arithmetic
  linarith
#print axioms d2Transfer109Arithmetic
#print axioms d2Transfer109Bound
def d2Transfer110Lo : ℚ := (d2LitsNearTransfers013.q2 (31540907) 1 (-28))
def d2Transfer110Hi : ℚ := (d2LitsNearTransfers013.q2 (8304657) 1 (-26))
def d2Transfer110Cap : ℚ := (d2LitsNearTransfers013.q2 (649441385) 1 (-39))
def d2Transfer110C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 25 (-4))
def d2Transfer110S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer110Arithmetic : weightedUpper d2Transfer110C0 d2Log95Lo d2Log95Hi ≤ d2Transfer110Cap := by decide +kernel
theorem d2Transfer110Bound : ∀ x ∈ Set.Icc ((d2Transfer110Lo:ℚ):ℝ) ((d2Transfer110Hi:ℚ):ℝ), ((d2Transfer110C0:ℚ):ℝ)*Real.log |x-((d2Transfer110S0:ℚ):ℝ)| ≤ ((d2Transfer110Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer110S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer110S0,d2Transfer110Lo,d2Transfer110Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer110C0 then |x-((d2Transfer110S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer110S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer110S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer110S0,d2Transfer110Lo,d2Transfer110Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer110C0,d2Log95Q,d2Transfer110S0,d2Transfer110Lo,d2Transfer110Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer110C0 d2Transfer110S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2Transfer110C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2Transfer110Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer110Arithmetic
  linarith
#print axioms d2Transfer110Arithmetic
#print axioms d2Transfer110Bound
def d2Transfer111Lo : ℚ := (d2LitsNearTransfers013.q2 (31540907) 1 (-28))
def d2Transfer111Hi : ℚ := (d2LitsNearTransfers013.q2 (8304657) 1 (-26))
def d2Transfer111Cap : ℚ := (d2LitsNearTransfers013.q2 (2436024149) 1 (-40))
def d2Transfer111C0 : ℚ := (d2LitsNearTransfers013.q2 (1) 275 (-4))
def d2Transfer111S0 : ℚ := (d2LitsNearTransfers013.q2 (-1) 1 (0))
def d2Transfer111C1 : ℚ := (d2LitsNearTransfers013.q2 (-1) 55 (-3))
def d2Transfer111S1 : ℚ := (d2LitsNearTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer111Arithmetic : weightedUpper d2Transfer111C0 d2Log95Lo d2Log95Hi + weightedUpper d2Transfer111C1 d2Log79Lo d2Log79Hi ≤ d2Transfer111Cap := by decide +kernel
theorem d2Transfer111Bound : ∀ x ∈ Set.Icc ((d2Transfer111Lo:ℚ):ℝ) ((d2Transfer111Hi:ℚ):ℝ), ((d2Transfer111C0:ℚ):ℝ)*Real.log |x-((d2Transfer111S0:ℚ):ℝ)| + ((d2Transfer111C1:ℚ):ℝ)*Real.log |x-((d2Transfer111S1:ℚ):ℝ)| ≤ ((d2Transfer111Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer111S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer111S0,d2Transfer111Lo,d2Transfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer111C0 then |x-((d2Transfer111S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer111S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer111S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer111S0,d2Transfer111Lo,d2Transfer111Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer111C0,d2Log95Q,d2Transfer111S0,d2Transfer111Lo,d2Transfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer111C0 d2Transfer111S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2Transfer111S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer111S1,d2Transfer111Lo,d2Transfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer111C1 then |x-((d2Transfer111S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2Transfer111S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer111S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer111S1,d2Transfer111Lo,d2Transfer111Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers013.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2Transfer111C1,d2Log79Q,d2Transfer111S1,d2Transfer111Lo,d2Transfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer111C1 d2Transfer111S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2Transfer111C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2Transfer111C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2Transfer111Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer111Arithmetic
  linarith
#print axioms d2Transfer111Arithmetic
#print axioms d2Transfer111Bound
end CatalanMeasure.GenD.Signed.Data.Cells
