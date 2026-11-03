module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers057
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers057
open D72.LogTransfer
def d2WiderTransfer456Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (32767) 1 (-15))
def d2WiderTransfer456Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (65535) 1 (-16))
def d2WiderTransfer456Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (1056001622555987018861) 1 (-79))
def d2WiderTransfer456C0 : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 25 (-4))
def d2WiderTransfer456S0 : ℚ := (d2LitsNearWiderTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer456Arithmetic : weightedUpper d2WiderTransfer456C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer456Cap := by decide +kernel
theorem d2WiderTransfer456Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer456Lo:ℚ):ℝ) ((d2WiderTransfer456Hi:ℚ):ℝ), ((d2WiderTransfer456C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer456S0:ℚ):ℝ)| ≤ ((d2WiderTransfer456Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer456S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer456S0,d2WiderTransfer456Lo,d2WiderTransfer456Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer456C0 then |x-((d2WiderTransfer456S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer456S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer456S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer456S0,d2WiderTransfer456Lo,d2WiderTransfer456Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer456C0,d2Log182Q,d2WiderTransfer456S0,d2WiderTransfer456Lo,d2WiderTransfer456Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer456C0 d2WiderTransfer456S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer456C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer456Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer456Arithmetic
  linarith
#print axioms d2WiderTransfer456Arithmetic
#print axioms d2WiderTransfer456Bound
def d2WiderTransfer457Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (32767) 1 (-15))
def d2WiderTransfer457Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (65535) 1 (-16))
def d2WiderTransfer457Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (13093035936949684929645) 1 (-79))
def d2WiderTransfer457C0 : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (-5))
def d2WiderTransfer457S0 : ℚ := (d2LitsNearWiderTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer457Arithmetic : weightedUpper d2WiderTransfer457C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer457Cap := by decide +kernel
theorem d2WiderTransfer457Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer457Lo:ℚ):ℝ) ((d2WiderTransfer457Hi:ℚ):ℝ), ((d2WiderTransfer457C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer457S0:ℚ):ℝ)| ≤ ((d2WiderTransfer457Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer457S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer457S0,d2WiderTransfer457Lo,d2WiderTransfer457Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer457C0 then |x-((d2WiderTransfer457S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer457S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer457S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer457S0,d2WiderTransfer457Lo,d2WiderTransfer457Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer457C0,d2Log182Q,d2WiderTransfer457S0,d2WiderTransfer457Lo,d2WiderTransfer457Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer457C0 d2WiderTransfer457S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer457C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer457Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer457Arithmetic
  linarith
#print axioms d2WiderTransfer457Arithmetic
#print axioms d2WiderTransfer457Bound
def d2WiderTransfer458Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (32767) 1 (-15))
def d2WiderTransfer458Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (65535) 1 (-16))
def d2WiderTransfer458Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (13093036134861777929325) 1 (-79))
def d2WiderTransfer458C0 : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (-5))
def d2WiderTransfer458S0 : ℚ := (d2LitsNearWiderTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer458Arithmetic : weightedUpper d2WiderTransfer458C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer458Cap := by decide +kernel
theorem d2WiderTransfer458Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer458Lo:ℚ):ℝ) ((d2WiderTransfer458Hi:ℚ):ℝ), ((d2WiderTransfer458C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer458S0:ℚ):ℝ)| ≤ ((d2WiderTransfer458Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer458S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer458S0,d2WiderTransfer458Lo,d2WiderTransfer458Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer458C0 then |x-((d2WiderTransfer458S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer458S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer458S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer458S0,d2WiderTransfer458Lo,d2WiderTransfer458Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer458C0,d2Log182Q,d2WiderTransfer458S0,d2WiderTransfer458Lo,d2WiderTransfer458Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer458C0 d2WiderTransfer458S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer458C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer458Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer458Arithmetic
  linarith
#print axioms d2WiderTransfer458Arithmetic
#print axioms d2WiderTransfer458Bound
def d2WiderTransfer459Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (65535) 1 (-16))
def d2WiderTransfer459Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (0))
def d2WiderTransfer459Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (132018243468848322021) 1 (-76))
def d2WiderTransfer459C0 : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 25 (-4))
def d2WiderTransfer459S0 : ℚ := (d2LitsNearWiderTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer459Arithmetic : weightedUpper d2WiderTransfer459C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer459Cap := by decide +kernel
theorem d2WiderTransfer459Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer459Lo:ℚ):ℝ) ((d2WiderTransfer459Hi:ℚ):ℝ), ((d2WiderTransfer459C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer459S0:ℚ):ℝ)| ≤ ((d2WiderTransfer459Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer459S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer459S0,d2WiderTransfer459Lo,d2WiderTransfer459Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer459C0 then |x-((d2WiderTransfer459S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer459S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer459S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer459S0,d2WiderTransfer459Lo,d2WiderTransfer459Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer459C0,d2Log186Q,d2WiderTransfer459S0,d2WiderTransfer459Lo,d2WiderTransfer459Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer459C0 d2WiderTransfer459S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer459C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer459Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer459Arithmetic
  linarith
#print axioms d2WiderTransfer459Arithmetic
#print axioms d2WiderTransfer459Bound
def d2WiderTransfer460Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (65535) 1 (-16))
def d2WiderTransfer460Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (0))
def d2WiderTransfer460Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (132018217286727685605) 1 (-76))
def d2WiderTransfer460C0 : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 25 (-4))
def d2WiderTransfer460S0 : ℚ := (d2LitsNearWiderTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer460Arithmetic : weightedUpper d2WiderTransfer460C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer460Cap := by decide +kernel
theorem d2WiderTransfer460Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer460Lo:ℚ):ℝ) ((d2WiderTransfer460Hi:ℚ):ℝ), ((d2WiderTransfer460C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer460S0:ℚ):ℝ)| ≤ ((d2WiderTransfer460Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer460S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer460S0,d2WiderTransfer460Lo,d2WiderTransfer460Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer460C0 then |x-((d2WiderTransfer460S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer460S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer460S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer460S0,d2WiderTransfer460Lo,d2WiderTransfer460Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer460C0,d2Log186Q,d2WiderTransfer460S0,d2WiderTransfer460Lo,d2WiderTransfer460Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer460C0 d2WiderTransfer460S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer460C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer460Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer460Arithmetic
  linarith
#print axioms d2WiderTransfer460Arithmetic
#print axioms d2WiderTransfer460Bound
def d2WiderTransfer461Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (65535) 1 (-16))
def d2WiderTransfer461Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (0))
def d2WiderTransfer461Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (1636647506585939924453) 1 (-76))
def d2WiderTransfer461C0 : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (-5))
def d2WiderTransfer461S0 : ℚ := (d2LitsNearWiderTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer461Arithmetic : weightedUpper d2WiderTransfer461C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer461Cap := by decide +kernel
theorem d2WiderTransfer461Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer461Lo:ℚ):ℝ) ((d2WiderTransfer461Hi:ℚ):ℝ), ((d2WiderTransfer461C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer461S0:ℚ):ℝ)| ≤ ((d2WiderTransfer461Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer461S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer461S0,d2WiderTransfer461Lo,d2WiderTransfer461Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer461C0 then |x-((d2WiderTransfer461S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer461S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer461S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer461S0,d2WiderTransfer461Lo,d2WiderTransfer461Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer461C0,d2Log186Q,d2WiderTransfer461S0,d2WiderTransfer461Lo,d2WiderTransfer461Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer461C0 d2WiderTransfer461S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer461C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer461Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer461Arithmetic
  linarith
#print axioms d2WiderTransfer461Arithmetic
#print axioms d2WiderTransfer461Bound
def d2WiderTransfer462Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (65535) 1 (-16))
def d2WiderTransfer462Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (0))
def d2WiderTransfer462Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (1636647531324951549413) 1 (-76))
def d2WiderTransfer462C0 : ℚ := (d2LitsNearWiderTransfers057.q2 (1) 1 (-5))
def d2WiderTransfer462S0 : ℚ := (d2LitsNearWiderTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer462Arithmetic : weightedUpper d2WiderTransfer462C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer462Cap := by decide +kernel
theorem d2WiderTransfer462Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer462Lo:ℚ):ℝ) ((d2WiderTransfer462Hi:ℚ):ℝ), ((d2WiderTransfer462C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer462S0:ℚ):ℝ)| ≤ ((d2WiderTransfer462Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer462S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer462S0,d2WiderTransfer462Lo,d2WiderTransfer462Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer462C0 then |x-((d2WiderTransfer462S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer462S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer462S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer462S0,d2WiderTransfer462Lo,d2WiderTransfer462Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers057.q2, d2LitsNearLogCache011.q2, d2WiderTransfer462C0,d2Log186Q,d2WiderTransfer462S0,d2WiderTransfer462Lo,d2WiderTransfer462Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer462C0 d2WiderTransfer462S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer462C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer462Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer462Arithmetic
  linarith
#print axioms d2WiderTransfer462Arithmetic
#print axioms d2WiderTransfer462Bound
def d2WiderTransfer463Lo : ℚ := (d2LitsNearWiderTransfers057.q2 (999) 125 (-3))
def d2WiderTransfer463Hi : ℚ := (d2LitsNearWiderTransfers057.q2 (16760439) 1 (-24))
def d2WiderTransfer463Cap : ℚ := (d2LitsNearWiderTransfers057.q2 (241850313660495) 1 (-78))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer463Arithmetic : (0 : ℚ) ≤ d2WiderTransfer463Cap := by decide +kernel
theorem d2WiderTransfer463Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer463Lo:ℚ):ℝ) ((d2WiderTransfer463Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer463Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer463Arithmetic
#print axioms d2WiderTransfer463Arithmetic
#print axioms d2WiderTransfer463Bound
end CatalanMeasure.GenD.Signed.Data.Cells
