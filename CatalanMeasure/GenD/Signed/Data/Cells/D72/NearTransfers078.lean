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
namespace d2LitsNearTransfers078
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers078
open D72.LogTransfer
def d2Transfer624Lo : ℚ := (d2LitsNearTransfers078.q2 (8191) 1 (-13))
def d2Transfer624Hi : ℚ := (d2LitsNearTransfers078.q2 (16383) 1 (-14))
def d2Transfer624Cap : ℚ := (d2LitsNearTransfers078.q2 (1047408286651115519109) 1 (-79))
def d2Transfer624C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer624S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer624Arithmetic : weightedUpper d2Transfer624C0 d2Log180Lo d2Log180Hi ≤ d2Transfer624Cap := by decide +kernel
theorem d2Transfer624Bound : ∀ x ∈ Set.Icc ((d2Transfer624Lo:ℚ):ℝ) ((d2Transfer624Hi:ℚ):ℝ), ((d2Transfer624C0:ℚ):ℝ)*Real.log |x-((d2Transfer624S0:ℚ):ℝ)| ≤ ((d2Transfer624Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer624S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer624S0,d2Transfer624Lo,d2Transfer624Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer624C0 then |x-((d2Transfer624S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer624S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer624S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer624S0,d2Transfer624Lo,d2Transfer624Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer624C0,d2Log180Q,d2Transfer624S0,d2Transfer624Lo,d2Transfer624Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer624C0 d2Transfer624S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer624C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer624Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer624Arithmetic
  linarith
#print axioms d2Transfer624Arithmetic
#print axioms d2Transfer624Bound
def d2Transfer625Lo : ℚ := (d2LitsNearTransfers078.q2 (16383) 1 (-14))
def d2Transfer625Hi : ℚ := (d2LitsNearTransfers078.q2 (32767) 1 (-15))
def d2Transfer625Cap : ℚ := (d2LitsNearTransfers078.q2 (2094863110131901712009) 1 (-80))
def d2Transfer625C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer625S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer625Arithmetic : weightedUpper d2Transfer625C0 d2Log181Lo d2Log181Hi ≤ d2Transfer625Cap := by decide +kernel
theorem d2Transfer625Bound : ∀ x ∈ Set.Icc ((d2Transfer625Lo:ℚ):ℝ) ((d2Transfer625Hi:ℚ):ℝ), ((d2Transfer625C0:ℚ):ℝ)*Real.log |x-((d2Transfer625S0:ℚ):ℝ)| ≤ ((d2Transfer625Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer625S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer625S0,d2Transfer625Lo,d2Transfer625Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer625C0 then |x-((d2Transfer625S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer625S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer625S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer625S0,d2Transfer625Lo,d2Transfer625Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer625C0,d2Log181Q,d2Transfer625S0,d2Transfer625Lo,d2Transfer625Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer625C0 d2Transfer625S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer625C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer625Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer625Arithmetic
  linarith
#print axioms d2Transfer625Arithmetic
#print axioms d2Transfer625Bound
def d2Transfer626Lo : ℚ := (d2LitsNearTransfers078.q2 (16383) 1 (-14))
def d2Transfer626Hi : ℚ := (d2LitsNearTransfers078.q2 (32767) 1 (-15))
def d2Transfer626Cap : ℚ := (d2LitsNearTransfers078.q2 (2094862691217971529353) 1 (-80))
def d2Transfer626C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer626S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer626Arithmetic : weightedUpper d2Transfer626C0 d2Log181Lo d2Log181Hi ≤ d2Transfer626Cap := by decide +kernel
theorem d2Transfer626Bound : ∀ x ∈ Set.Icc ((d2Transfer626Lo:ℚ):ℝ) ((d2Transfer626Hi:ℚ):ℝ), ((d2Transfer626C0:ℚ):ℝ)*Real.log |x-((d2Transfer626S0:ℚ):ℝ)| ≤ ((d2Transfer626Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer626S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer626S0,d2Transfer626Lo,d2Transfer626Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer626C0 then |x-((d2Transfer626S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2Transfer626S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer626S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer626S0,d2Transfer626Lo,d2Transfer626Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer626C0,d2Log181Q,d2Transfer626S0,d2Transfer626Lo,d2Transfer626Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer626C0 d2Transfer626S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2Transfer626C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2Transfer626Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer626Arithmetic
  linarith
#print axioms d2Transfer626Arithmetic
#print axioms d2Transfer626Bound
def d2Transfer627Lo : ℚ := (d2LitsNearTransfers078.q2 (32767) 1 (-15))
def d2Transfer627Hi : ℚ := (d2LitsNearTransfers078.q2 (65535) 1 (-16))
def d2Transfer627Cap : ℚ := (d2LitsNearTransfers078.q2 (261860771103234971425) 1 (-77))
def d2Transfer627C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer627S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer627Arithmetic : weightedUpper d2Transfer627C0 d2Log182Lo d2Log182Hi ≤ d2Transfer627Cap := by decide +kernel
theorem d2Transfer627Bound : ∀ x ∈ Set.Icc ((d2Transfer627Lo:ℚ):ℝ) ((d2Transfer627Hi:ℚ):ℝ), ((d2Transfer627C0:ℚ):ℝ)*Real.log |x-((d2Transfer627S0:ℚ):ℝ)| ≤ ((d2Transfer627Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer627S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer627S0,d2Transfer627Lo,d2Transfer627Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer627C0 then |x-((d2Transfer627S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer627S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer627S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer627S0,d2Transfer627Lo,d2Transfer627Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer627C0,d2Log182Q,d2Transfer627S0,d2Transfer627Lo,d2Transfer627Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer627C0 d2Transfer627S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer627C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer627Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer627Arithmetic
  linarith
#print axioms d2Transfer627Arithmetic
#print axioms d2Transfer627Bound
def d2Transfer628Lo : ℚ := (d2LitsNearTransfers078.q2 (32767) 1 (-15))
def d2Transfer628Hi : ℚ := (d2LitsNearTransfers078.q2 (65535) 1 (-16))
def d2Transfer628Cap : ℚ := (d2LitsNearTransfers078.q2 (261860718738993698593) 1 (-77))
def d2Transfer628C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer628S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer628Arithmetic : weightedUpper d2Transfer628C0 d2Log182Lo d2Log182Hi ≤ d2Transfer628Cap := by decide +kernel
theorem d2Transfer628Bound : ∀ x ∈ Set.Icc ((d2Transfer628Lo:ℚ):ℝ) ((d2Transfer628Hi:ℚ):ℝ), ((d2Transfer628C0:ℚ):ℝ)*Real.log |x-((d2Transfer628S0:ℚ):ℝ)| ≤ ((d2Transfer628Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer628S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer628S0,d2Transfer628Lo,d2Transfer628Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer628C0 then |x-((d2Transfer628S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2Transfer628S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer628S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer628S0,d2Transfer628Lo,d2Transfer628Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer628C0,d2Log182Q,d2Transfer628S0,d2Transfer628Lo,d2Transfer628Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer628C0 d2Transfer628S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2Transfer628C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2Transfer628Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer628Arithmetic
  linarith
#print axioms d2Transfer628Arithmetic
#print axioms d2Transfer628Bound
def d2Transfer629Lo : ℚ := (d2LitsNearTransfers078.q2 (65535) 1 (-16))
def d2Transfer629Hi : ℚ := (d2LitsNearTransfers078.q2 (131071) 1 (-17))
def d2Transfer629Cap : ℚ := (d2LitsNearTransfers078.q2 (2094897698106896929007) 1 (-80))
def d2Transfer629C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer629S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer629Arithmetic : weightedUpper d2Transfer629C0 d2Log183Lo d2Log183Hi ≤ d2Transfer629Cap := by decide +kernel
theorem d2Transfer629Bound : ∀ x ∈ Set.Icc ((d2Transfer629Lo:ℚ):ℝ) ((d2Transfer629Hi:ℚ):ℝ), ((d2Transfer629C0:ℚ):ℝ)*Real.log |x-((d2Transfer629S0:ℚ):ℝ)| ≤ ((d2Transfer629Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer629S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer629S0,d2Transfer629Lo,d2Transfer629Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer629C0 then |x-((d2Transfer629S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2Transfer629S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer629S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer629S0,d2Transfer629Lo,d2Transfer629Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer629C0,d2Log183Q,d2Transfer629S0,d2Transfer629Lo,d2Transfer629Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer629C0 d2Transfer629S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2Transfer629C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2Transfer629Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer629Arithmetic
  linarith
#print axioms d2Transfer629Arithmetic
#print axioms d2Transfer629Bound
def d2Transfer630Lo : ℚ := (d2LitsNearTransfers078.q2 (65535) 1 (-16))
def d2Transfer630Hi : ℚ := (d2LitsNearTransfers078.q2 (131071) 1 (-17))
def d2Transfer630Cap : ℚ := (d2LitsNearTransfers078.q2 (2094897279192966746351) 1 (-80))
def d2Transfer630C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer630S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer630Arithmetic : weightedUpper d2Transfer630C0 d2Log183Lo d2Log183Hi ≤ d2Transfer630Cap := by decide +kernel
theorem d2Transfer630Bound : ∀ x ∈ Set.Icc ((d2Transfer630Lo:ℚ):ℝ) ((d2Transfer630Hi:ℚ):ℝ), ((d2Transfer630C0:ℚ):ℝ)*Real.log |x-((d2Transfer630S0:ℚ):ℝ)| ≤ ((d2Transfer630Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer630S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer630S0,d2Transfer630Lo,d2Transfer630Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer630C0 then |x-((d2Transfer630S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2Transfer630S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer630S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer630S0,d2Transfer630Lo,d2Transfer630Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer630C0,d2Log183Q,d2Transfer630S0,d2Transfer630Lo,d2Transfer630Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer630C0 d2Transfer630S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2Transfer630C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2Transfer630Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer630Arithmetic
  linarith
#print axioms d2Transfer630Arithmetic
#print axioms d2Transfer630Bound
def d2Transfer631Lo : ℚ := (d2LitsNearTransfers078.q2 (131071) 1 (-17))
def d2Transfer631Hi : ℚ := (d2LitsNearTransfers078.q2 (262143) 1 (-18))
def d2Transfer631Cap : ℚ := (d2LitsNearTransfers078.q2 (4091608325646313841) 1 (-71))
def d2Transfer631C0 : ℚ := (d2LitsNearTransfers078.q2 (1) 25 (-4))
def d2Transfer631S0 : ℚ := (d2LitsNearTransfers078.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer631Arithmetic : weightedUpper d2Transfer631C0 d2Log184Lo d2Log184Hi ≤ d2Transfer631Cap := by decide +kernel
theorem d2Transfer631Bound : ∀ x ∈ Set.Icc ((d2Transfer631Lo:ℚ):ℝ) ((d2Transfer631Hi:ℚ):ℝ), ((d2Transfer631C0:ℚ):ℝ)*Real.log |x-((d2Transfer631S0:ℚ):ℝ)| ≤ ((d2Transfer631Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer631S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer631S0,d2Transfer631Lo,d2Transfer631Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer631C0 then |x-((d2Transfer631S0:ℚ):ℝ)| ≤ ((d2Log184Q:ℚ):ℝ) else ((d2Log184Q:ℚ):ℝ) ≤ |x-((d2Transfer631S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer631S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer631S0,d2Transfer631Lo,d2Transfer631Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers078.q2, d2LitsNearLogCache011.q2, d2Transfer631C0,d2Log184Q,d2Transfer631S0,d2Transfer631Lo,d2Transfer631Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer631C0 d2Transfer631S0 d2Log184Q d2Log184Lo d2Log184Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log184Bounds
  have har : (((weightedUpper d2Transfer631C0 d2Log184Lo d2Log184Hi:ℚ):ℝ)) ≤ ((d2Transfer631Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer631Arithmetic
  linarith
#print axioms d2Transfer631Arithmetic
#print axioms d2Transfer631Bound
end CatalanMeasure.GenD.Signed.Data.Cells
