module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogCacheBench16
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0
namespace decay2LitsNearProfileTransfer8
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end decay2LitsNearProfileTransfer8
open D72.LogTransfer
def ceTransfer0Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (98749) 15625 (-6))
def ceTransfer0Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (828367) 1 (-23))
def ceTransfer0Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (2432512853) 1 (-40))
def ceTransfer0C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 275 (-4))
def ceTransfer0S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
def ceTransfer0C1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 55 (-3))
def ceTransfer0S1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 1 (0))
theorem ceTransfer0Arithmetic : weightedUpper ceTransfer0C0 ceLog8Lo ceLog8Hi + weightedUpper ceTransfer0C1 ceLog7Lo ceLog7Hi ≤ ceTransfer0Cap := by decide +kernel
theorem ceTransfer0Bound : ∀ x ∈ Set.Icc ((ceTransfer0Lo:ℚ):ℝ) ((ceTransfer0Hi:ℚ):ℝ), ((ceTransfer0C0:ℚ):ℝ)*Real.log |x-((ceTransfer0S0:ℚ):ℝ)| + ((ceTransfer0C1:ℚ):ℝ)*Real.log |x-((ceTransfer0S1:ℚ):ℝ)| ≤ ((ceTransfer0Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer0S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer0S0,ceTransfer0Lo,ceTransfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer0C0 then |x-((ceTransfer0S0:ℚ):ℝ)| ≤ ((ceLog8Q:ℚ):ℝ) else ((ceLog8Q:ℚ):ℝ) ≤ |x-((ceTransfer0S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer0S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer0S0,ceTransfer0Lo,ceTransfer0Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer0C0,ceLog8Q,ceTransfer0S0,ceTransfer0Lo,ceTransfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer0C0 ceTransfer0S0 ceLog8Q ceLog8Lo ceLog8Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog8Bounds
  have hn1 : x-((ceTransfer0S1:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer0S1,ceTransfer0Lo,ceTransfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ ceTransfer0C1 then |x-((ceTransfer0S1:ℚ):ℝ)| ≤ ((ceLog7Q:ℚ):ℝ) else ((ceLog7Q:ℚ):ℝ) ≤ |x-((ceTransfer0S1:ℚ):ℝ)|) := by
    have ha : x-((ceTransfer0S1:ℚ):ℝ) ≤ 0 := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer0S1,ceTransfer0Lo,ceTransfer0Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer0C1,ceLog7Q,ceTransfer0S1,ceTransfer0Lo,ceTransfer0Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper ceTransfer0C1 ceTransfer0S1 ceLog7Q ceLog7Lo ceLog7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 ceLog7Bounds
  have har : (((weightedUpper ceTransfer0C0 ceLog8Lo ceLog8Hi:ℚ):ℝ) + ((weightedUpper ceTransfer0C1 ceLog7Lo ceLog7Hi:ℚ):ℝ)) ≤ ((ceTransfer0Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer0Arithmetic
  linarith
#print axioms ceTransfer0Arithmetic
#print axioms ceTransfer0Bound
def ceTransfer1Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (828367) 1 (-23))
def ceTransfer1Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (54693209) 1 (-29))
def ceTransfer1Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (2432512853) 1 (-40))
def ceTransfer1C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 275 (-4))
def ceTransfer1S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
def ceTransfer1C1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 55 (-3))
def ceTransfer1S1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 1 (0))
theorem ceTransfer1Arithmetic : weightedUpper ceTransfer1C0 ceLog9Lo ceLog9Hi + weightedUpper ceTransfer1C1 ceLog6Lo ceLog6Hi ≤ ceTransfer1Cap := by decide +kernel
theorem ceTransfer1Bound : ∀ x ∈ Set.Icc ((ceTransfer1Lo:ℚ):ℝ) ((ceTransfer1Hi:ℚ):ℝ), ((ceTransfer1C0:ℚ):ℝ)*Real.log |x-((ceTransfer1S0:ℚ):ℝ)| + ((ceTransfer1C1:ℚ):ℝ)*Real.log |x-((ceTransfer1S1:ℚ):ℝ)| ≤ ((ceTransfer1Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer1S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer1S0,ceTransfer1Lo,ceTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer1C0 then |x-((ceTransfer1S0:ℚ):ℝ)| ≤ ((ceLog9Q:ℚ):ℝ) else ((ceLog9Q:ℚ):ℝ) ≤ |x-((ceTransfer1S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer1S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer1S0,ceTransfer1Lo,ceTransfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer1C0,ceLog9Q,ceTransfer1S0,ceTransfer1Lo,ceTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer1C0 ceTransfer1S0 ceLog9Q ceLog9Lo ceLog9Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog9Bounds
  have hn1 : x-((ceTransfer1S1:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer1S1,ceTransfer1Lo,ceTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ ceTransfer1C1 then |x-((ceTransfer1S1:ℚ):ℝ)| ≤ ((ceLog6Q:ℚ):ℝ) else ((ceLog6Q:ℚ):ℝ) ≤ |x-((ceTransfer1S1:ℚ):ℝ)|) := by
    have ha : x-((ceTransfer1S1:ℚ):ℝ) ≤ 0 := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer1S1,ceTransfer1Lo,ceTransfer1Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer1C1,ceLog6Q,ceTransfer1S1,ceTransfer1Lo,ceTransfer1Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper ceTransfer1C1 ceTransfer1S1 ceLog6Q ceLog6Lo ceLog6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 ceLog6Bounds
  have har : (((weightedUpper ceTransfer1C0 ceLog9Lo ceLog9Hi:ℚ):ℝ) + ((weightedUpper ceTransfer1C1 ceLog6Lo ceLog6Hi:ℚ):ℝ)) ≤ ((ceTransfer1Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer1Arithmetic
  linarith
#print axioms ceTransfer1Arithmetic
#print axioms ceTransfer1Bound
def ceTransfer2Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (54693209) 1 (-29))
def ceTransfer2Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (28185465) 1 (-28))
def ceTransfer2Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (2432512853) 1 (-40))
def ceTransfer2C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 275 (-4))
def ceTransfer2S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
def ceTransfer2C1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 55 (-3))
def ceTransfer2S1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 1 (0))
theorem ceTransfer2Arithmetic : weightedUpper ceTransfer2C0 ceLog10Lo ceLog10Hi + weightedUpper ceTransfer2C1 ceLog5Lo ceLog5Hi ≤ ceTransfer2Cap := by decide +kernel
theorem ceTransfer2Bound : ∀ x ∈ Set.Icc ((ceTransfer2Lo:ℚ):ℝ) ((ceTransfer2Hi:ℚ):ℝ), ((ceTransfer2C0:ℚ):ℝ)*Real.log |x-((ceTransfer2S0:ℚ):ℝ)| + ((ceTransfer2C1:ℚ):ℝ)*Real.log |x-((ceTransfer2S1:ℚ):ℝ)| ≤ ((ceTransfer2Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer2S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer2S0,ceTransfer2Lo,ceTransfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer2C0 then |x-((ceTransfer2S0:ℚ):ℝ)| ≤ ((ceLog10Q:ℚ):ℝ) else ((ceLog10Q:ℚ):ℝ) ≤ |x-((ceTransfer2S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer2S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer2S0,ceTransfer2Lo,ceTransfer2Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer2C0,ceLog10Q,ceTransfer2S0,ceTransfer2Lo,ceTransfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer2C0 ceTransfer2S0 ceLog10Q ceLog10Lo ceLog10Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog10Bounds
  have hn1 : x-((ceTransfer2S1:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer2S1,ceTransfer2Lo,ceTransfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ ceTransfer2C1 then |x-((ceTransfer2S1:ℚ):ℝ)| ≤ ((ceLog5Q:ℚ):ℝ) else ((ceLog5Q:ℚ):ℝ) ≤ |x-((ceTransfer2S1:ℚ):ℝ)|) := by
    have ha : x-((ceTransfer2S1:ℚ):ℝ) ≤ 0 := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer2S1,ceTransfer2Lo,ceTransfer2Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer2C1,ceLog5Q,ceTransfer2S1,ceTransfer2Lo,ceTransfer2Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper ceTransfer2C1 ceTransfer2S1 ceLog5Q ceLog5Lo ceLog5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 ceLog5Bounds
  have har : (((weightedUpper ceTransfer2C0 ceLog10Lo ceLog10Hi:ℚ):ℝ) + ((weightedUpper ceTransfer2C1 ceLog5Lo ceLog5Hi:ℚ):ℝ)) ≤ ((ceTransfer2Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer2Arithmetic
  linarith
#print axioms ceTransfer2Arithmetic
#print axioms ceTransfer2Bound
def ceTransfer3Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (28185465) 1 (-28))
def ceTransfer3Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (14931593) 1 (-27))
def ceTransfer3Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (2432512853) 1 (-40))
def ceTransfer3C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 275 (-4))
def ceTransfer3S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
def ceTransfer3C1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 55 (-3))
def ceTransfer3S1 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 1 (0))
theorem ceTransfer3Arithmetic : weightedUpper ceTransfer3C0 ceLog11Lo ceLog11Hi + weightedUpper ceTransfer3C1 ceLog4Lo ceLog4Hi ≤ ceTransfer3Cap := by decide +kernel
theorem ceTransfer3Bound : ∀ x ∈ Set.Icc ((ceTransfer3Lo:ℚ):ℝ) ((ceTransfer3Hi:ℚ):ℝ), ((ceTransfer3C0:ℚ):ℝ)*Real.log |x-((ceTransfer3S0:ℚ):ℝ)| + ((ceTransfer3C1:ℚ):ℝ)*Real.log |x-((ceTransfer3S1:ℚ):ℝ)| ≤ ((ceTransfer3Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer3S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer3S0,ceTransfer3Lo,ceTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer3C0 then |x-((ceTransfer3S0:ℚ):ℝ)| ≤ ((ceLog11Q:ℚ):ℝ) else ((ceLog11Q:ℚ):ℝ) ≤ |x-((ceTransfer3S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer3S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer3S0,ceTransfer3Lo,ceTransfer3Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer3C0,ceLog11Q,ceTransfer3S0,ceTransfer3Lo,ceTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer3C0 ceTransfer3S0 ceLog11Q ceLog11Lo ceLog11Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog11Bounds
  have hn1 : x-((ceTransfer3S1:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer3S1,ceTransfer3Lo,ceTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ ceTransfer3C1 then |x-((ceTransfer3S1:ℚ):ℝ)| ≤ ((ceLog4Q:ℚ):ℝ) else ((ceLog4Q:ℚ):ℝ) ≤ |x-((ceTransfer3S1:ℚ):ℝ)|) := by
    have ha : x-((ceTransfer3S1:ℚ):ℝ) ≤ 0 := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer3S1,ceTransfer3Lo,ceTransfer3Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer3C1,ceLog4Q,ceTransfer3S1,ceTransfer3Lo,ceTransfer3Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper ceTransfer3C1 ceTransfer3S1 ceLog4Q ceLog4Lo ceLog4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 ceLog4Bounds
  have har : (((weightedUpper ceTransfer3C0 ceLog11Lo ceLog11Hi:ℚ):ℝ) + ((weightedUpper ceTransfer3C1 ceLog4Lo ceLog4Hi:ℚ):ℝ)) ≤ ((ceTransfer3Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer3Arithmetic
  linarith
#print axioms ceTransfer3Arithmetic
#print axioms ceTransfer3Bound
def ceTransfer4Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (14931593) 1 (-27))
def ceTransfer4Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (31540907) 1 (-28))
def ceTransfer4Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (648894057) 1 (-39))
def ceTransfer4C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 25 (-4))
def ceTransfer4S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
theorem ceTransfer4Arithmetic : weightedUpper ceTransfer4C0 ceLog12Lo ceLog12Hi ≤ ceTransfer4Cap := by decide +kernel
theorem ceTransfer4Bound : ∀ x ∈ Set.Icc ((ceTransfer4Lo:ℚ):ℝ) ((ceTransfer4Hi:ℚ):ℝ), ((ceTransfer4C0:ℚ):ℝ)*Real.log |x-((ceTransfer4S0:ℚ):ℝ)| ≤ ((ceTransfer4Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer4S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer4S0,ceTransfer4Lo,ceTransfer4Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer4C0 then |x-((ceTransfer4S0:ℚ):ℝ)| ≤ ((ceLog12Q:ℚ):ℝ) else ((ceLog12Q:ℚ):ℝ) ≤ |x-((ceTransfer4S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer4S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer4S0,ceTransfer4Lo,ceTransfer4Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer4C0,ceLog12Q,ceTransfer4S0,ceTransfer4Lo,ceTransfer4Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer4C0 ceTransfer4S0 ceLog12Q ceLog12Lo ceLog12Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog12Bounds
  have har : (((weightedUpper ceTransfer4C0 ceLog12Lo ceLog12Hi:ℚ):ℝ)) ≤ ((ceTransfer4Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer4Arithmetic
  linarith
#print axioms ceTransfer4Arithmetic
#print axioms ceTransfer4Bound
def ceTransfer5Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (31540907) 1 (-28))
def ceTransfer5Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (8304657) 1 (-26))
def ceTransfer5Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (648894057) 1 (-39))
def ceTransfer5C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 25 (-4))
def ceTransfer5S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
theorem ceTransfer5Arithmetic : weightedUpper ceTransfer5C0 ceLog13Lo ceLog13Hi ≤ ceTransfer5Cap := by decide +kernel
theorem ceTransfer5Bound : ∀ x ∈ Set.Icc ((ceTransfer5Lo:ℚ):ℝ) ((ceTransfer5Hi:ℚ):ℝ), ((ceTransfer5C0:ℚ):ℝ)*Real.log |x-((ceTransfer5S0:ℚ):ℝ)| ≤ ((ceTransfer5Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer5S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer5S0,ceTransfer5Lo,ceTransfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer5C0 then |x-((ceTransfer5S0:ℚ):ℝ)| ≤ ((ceLog13Q:ℚ):ℝ) else ((ceLog13Q:ℚ):ℝ) ≤ |x-((ceTransfer5S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer5S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer5S0,ceTransfer5Lo,ceTransfer5Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer5C0,ceLog13Q,ceTransfer5S0,ceTransfer5Lo,ceTransfer5Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer5C0 ceTransfer5S0 ceLog13Q ceLog13Lo ceLog13Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog13Bounds
  have har : (((weightedUpper ceTransfer5C0 ceLog13Lo ceLog13Hi:ℚ):ℝ)) ≤ ((ceTransfer5Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer5Arithmetic
  linarith
#print axioms ceTransfer5Arithmetic
#print axioms ceTransfer5Bound
def ceTransfer6Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (8304657) 1 (-26))
def ceTransfer6Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (34896349) 1 (-28))
def ceTransfer6Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (648894057) 1 (-39))
def ceTransfer6C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 25 (-4))
def ceTransfer6S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
theorem ceTransfer6Arithmetic : weightedUpper ceTransfer6C0 ceLog14Lo ceLog14Hi ≤ ceTransfer6Cap := by decide +kernel
theorem ceTransfer6Bound : ∀ x ∈ Set.Icc ((ceTransfer6Lo:ℚ):ℝ) ((ceTransfer6Hi:ℚ):ℝ), ((ceTransfer6C0:ℚ):ℝ)*Real.log |x-((ceTransfer6S0:ℚ):ℝ)| ≤ ((ceTransfer6Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer6S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer6S0,ceTransfer6Lo,ceTransfer6Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer6C0 then |x-((ceTransfer6S0:ℚ):ℝ)| ≤ ((ceLog14Q:ℚ):ℝ) else ((ceLog14Q:ℚ):ℝ) ≤ |x-((ceTransfer6S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer6S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer6S0,ceTransfer6Lo,ceTransfer6Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer6C0,ceLog14Q,ceTransfer6S0,ceTransfer6Lo,ceTransfer6Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer6C0 ceTransfer6S0 ceLog14Q ceLog14Lo ceLog14Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog14Bounds
  have har : (((weightedUpper ceTransfer6C0 ceLog14Lo ceLog14Hi:ℚ):ℝ)) ≤ ((ceTransfer6Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer6Arithmetic
  linarith
#print axioms ceTransfer6Arithmetic
#print axioms ceTransfer6Bound
def ceTransfer7Lo : ℚ := (decay2LitsNearProfileTransfer8.q2 (34896349) 1 (-28))
def ceTransfer7Hi : ℚ := (decay2LitsNearProfileTransfer8.q2 (18287035) 1 (-27))
def ceTransfer7Cap : ℚ := (decay2LitsNearProfileTransfer8.q2 (648894057) 1 (-39))
def ceTransfer7C0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (1) 25 (-4))
def ceTransfer7S0 : ℚ := (decay2LitsNearProfileTransfer8.q2 (-1) 1 (0))
theorem ceTransfer7Arithmetic : weightedUpper ceTransfer7C0 ceLog15Lo ceLog15Hi ≤ ceTransfer7Cap := by decide +kernel
theorem ceTransfer7Bound : ∀ x ∈ Set.Icc ((ceTransfer7Lo:ℚ):ℝ) ((ceTransfer7Hi:ℚ):ℝ), ((ceTransfer7C0:ℚ):ℝ)*Real.log |x-((ceTransfer7S0:ℚ):ℝ)| ≤ ((ceTransfer7Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((ceTransfer7S0:ℚ):ℝ) ≠ 0 := by
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer7S0,ceTransfer7Lo,ceTransfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ ceTransfer7C0 then |x-((ceTransfer7S0:ℚ):ℝ)| ≤ ((ceLog15Q:ℚ):ℝ) else ((ceLog15Q:ℚ):ℝ) ≤ |x-((ceTransfer7S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((ceTransfer7S0:ℚ):ℝ) := by
      norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer7S0,ceTransfer7Lo,ceTransfer7Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [decay2LitsNearProfileTransfer8.q2, ceTransfer7C0,ceLog15Q,ceTransfer7S0,ceTransfer7Lo,ceTransfer7Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper ceTransfer7C0 ceTransfer7S0 ceLog15Q ceLog15Lo ceLog15Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 ceLog15Bounds
  have har : (((weightedUpper ceTransfer7C0 ceLog15Lo ceLog15Hi:ℚ):ℝ)) ≤ ((ceTransfer7Cap:ℚ):ℝ) := by exact_mod_cast ceTransfer7Arithmetic
  linarith
#print axioms ceTransfer7Arithmetic
#print axioms ceTransfer7Bound
end CatalanMeasure.GenD.Signed.Data.Cells
