module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.Slots.HPSLB
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
def hpsLB72 : NullityLB P72 := hpsLB P72 p72_admissible

theorem hps_at72 {N p s k1 ilo : Nat} (hp : 0 < p)
    (hs : s * p ≤ P72.H N) (hk : (k1 - 1) * p ≤ P72.n N - P72.g N)
    (hi : ilo ≤ hpEta P72 N p s) :
    hpVal P72 N p s (-1) k1 + perVal P72 N p s (-1) k1 ilo ≤ hpsLB72.kap N p := by
  change _ ≤ hpsKap P72 N p
  unfold hpsKap
  have hs' : s ∈ Finset.range (P72.H N / p + 1) := by
    rw [Finset.mem_range]
    have h := (Nat.le_div_iff_mul_le hp).mpr hs
    omega
  have h0 : (-1 : Int) ∈ Finset.Icc (hpKmin P72 N p) (hpKmax P72 N p) := by
    rw [Finset.mem_Icc]
    unfold hpKmin hpKmax
    have ha := Int.natCast_nonneg ((P72.g N + p - 1) / p)
    have hb := Int.natCast_nonneg ((P72.n N - P72.g N) / p)
    constructor <;> omega
  have h1 : (k1 : Int) ∈ Finset.Icc (-1) (hpKmax P72 N p) := by
    rw [Finset.mem_Icc]
    have h := (Nat.le_div_iff_mul_le hp).mpr hk
    unfold hpKmax
    constructor <;> omega
  have hi' : ilo ∈ Finset.range (hpEta P72 N p s + 1) := by rw [Finset.mem_range]; omega
  let F := fun s k0 k1 ilo => hpVal P72 N p s k0 k1 + perVal P72 N p s k0 k1 ilo
  let I := fun s k0 k1 => (Finset.range (hpEta P72 N p s + 1)).sup (F s k0 k1)
  let G := fun s k0 => (Finset.Icc k0 (hpKmax P72 N p)).sup (I s k0)
  let H := fun s => (Finset.Icc (hpKmin P72 N p) (hpKmax P72 N p)).sup (G s)
  exact (Finset.le_sup (f := F s (-1) k1) hi').trans
    ((Finset.le_sup (f := I s (-1)) h1).trans
    ((Finset.le_sup (f := G s) h0).trans (Finset.le_sup (f := H) hs')))

#time theorem w110_hcert72 {N p : Nat} (hN : 0 < N) (hodd : p % 2 = 1)
    (hlo : (76 / 9 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (17 / 2 : ℝ) * N) :
    (N : ℝ) * ((-76 / 1 : ℝ) + (9 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hpsLB72.kap N p : ℝ) := by
  have hl : 76 * N < 9 * p := by
    exact_mod_cast (show (76 : ℝ) * N < 9 * p by linarith)
  have hr : 2 * p ≤ 17 * N := by
    exact_mod_cast (show (2 : ℝ) * p ≤ 17 * N by linarith)
  have hp : 0 < p := by omega
  have hjrange : P72.L N / p + 2 ≤ 13 := by
    have h := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [p72_L]; omega : P72.L N < 11 * p)
    omega
  let ilo : Nat := 86 * N - 10 * p
  have hv := hps_at72 (N := N) (p := p) (s := 10) (k1 := 7) (ilo := ilo) hp
    (by rw [p72_H]; omega) (by change (7 - 1) * p ≤ 72 * N - 6 * N; omega)
    (by simp only [ilo, hpEta, p72_H]; omega)
  have hap : perOK P72 N p 10 (-1) 7 ilo := by
    simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo]
    repeat' apply And.intro
    all_goals omega
  have hcp : (perJJ P72 N p 10 (-1) 7 ilo).card ≤ 8 := by
    have hsub : perJJ P72 N p 10 (-1) 7 ilo ⊆ Finset.Icc 2 9 := by
      intro J hJ
      simp only [perJJ, Finset.mem_filter, Finset.mem_range] at hJ
      have hJ' : J < 13 := hJ.1.trans_le hjrange
      have hj := hJ.2
      interval_cases J <;> simp only [Finset.mem_Icc] <;>
        simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo] at hj <;> omega
    exact (Finset.card_le_card hsub).trans (by decide)
  have hwp : ((perPmax P72 N p 10 (-1) 7).toNat - ilo + 1) ≤ perVal P72 N p 10 (-1) 7 ilo := by
    unfold perVal
    rw [if_pos hap]
    have hfac : 1 ≤ hpK (-1) 7 - (perJJ P72 N p 10 (-1) 7 ilo).card := by
      unfold hpK
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right ((perPmax P72 N p 10 (-1) 7).toNat - ilo + 1) hfac
  have hbound : 18 * p ≤ 2 * hpsLB72.kap N p + 4 + 152 * N := by
    generalize perVal P72 N p 10 (-1) 7 ilo = vp at hwp hv
    simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo] at hwp
    omega
  have hboundR : 18 * p ≤ 2 * (hpsLB72.kap N p : ℝ) + 4 + 152 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-76 / 1 : ℝ) + (9 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-76 / 1 : ℝ) * N + (9 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w119_hcert72 {N p : Nat} (hN : 0 < N) (hodd : p % 2 = 1)
    (hlo : (202 / 21 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (29 / 3 : ℝ) * N) :
    (N : ℝ) * ((-81 / 1 : ℝ) + (17 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hpsLB72.kap N p : ℝ) := by
  have hl : 202 * N < 21 * p := by
    exact_mod_cast (show (202 : ℝ) * N < 21 * p by linarith)
  have hr : 3 * p ≤ 29 * N := by
    exact_mod_cast (show (3 : ℝ) * p ≤ 29 * N by linarith)
  have hp : 0 < p := by omega
  have hjrange : P72.L N / p + 2 ≤ 13 := by
    have h := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [p72_L]; omega : P72.L N < 11 * p)
    omega
  let ilo : Nat := 0
  have hv := hps_at72 (N := N) (p := p) (s := 9) (k1 := 6) (ilo := ilo) hp
    (by rw [p72_H]; omega) (by change (6 - 1) * p ≤ 72 * N - 6 * N; omega)
    (by simp only [ilo, hpEta, p72_H]; omega)
  have hah : hpOK P72 N p 9 (-1) 6 := by
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hch : (hpJJ P72 N p 9 (-1) 6).card ≤ 8 := by
    have hsub : hpJJ P72 N p 9 (-1) 6 ⊆ Finset.Icc 1 8 := by
      intro J hJ
      simp only [hpJJ, Finset.mem_filter, Finset.mem_range] at hJ
      have hJ' : J < 13 := hJ.1.trans_le hjrange
      have hj := hJ.2
      interval_cases J <;> simp only [Finset.mem_Icc] <;>
        simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hj <;> omega
    exact (Finset.card_le_card hsub).trans (by decide)
  have hwh : (hpD P72 N p 9 (-1) 6 - hpElo P72 N p 9) ≤ hpVal P72 N p 9 (-1) 6 := by
    unfold hpVal
    rw [if_pos hah]
    have hfac : 1 ≤ min (hpK (-1) 6) (hpK (-1) 6 + 1 - (hpJJ P72 N p 9 (-1) 6).card) := by
      unfold hpK
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right (hpD P72 N p 9 (-1) 6 - hpElo P72 N p 9) hfac
  have hap : perOK P72 N p 9 (-1) 6 ilo := by
    simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo]
    repeat' apply And.intro
    all_goals omega
  have hcp : (perJJ P72 N p 9 (-1) 6 ilo).card ≤ 7 := by
    have hsub : perJJ P72 N p 9 (-1) 6 ilo ⊆ Finset.Icc 2 8 := by
      intro J hJ
      simp only [perJJ, Finset.mem_filter, Finset.mem_range] at hJ
      have hJ' : J < 13 := hJ.1.trans_le hjrange
      have hj := hJ.2
      interval_cases J <;> simp only [Finset.mem_Icc] <;>
        simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo] at hj <;> omega
    exact (Finset.card_le_card hsub).trans (by decide)
  have hwp : ((perPmax P72 N p 9 (-1) 6).toNat - ilo + 1) ≤ perVal P72 N p 9 (-1) 6 ilo := by
    unfold perVal
    rw [if_pos hap]
    have hfac : 1 ≤ hpK (-1) 6 - (perJJ P72 N p 9 (-1) 6 ilo).card := by
      unfold hpK
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right ((perPmax P72 N p 9 (-1) 6).toNat - ilo + 1) hfac
  have hbound : 17 * p ≤ 2 * hpsLB72.kap N p + 4 + 162 * N := by
    generalize hpVal P72 N p 9 (-1) 6 = vh at hwh hv
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hwh
    generalize perVal P72 N p 9 (-1) 6 ilo = vp at hwp hv
    simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo] at hwp
    omega
  have hboundR : 17 * p ≤ 2 * (hpsLB72.kap N p : ℝ) + 4 + 162 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-81 / 1 : ℝ) + (17 / 2 : ℝ) * ((p : ℝ) / N)) =
      (-81 / 1 : ℝ) * N + (17 / 2 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w123_hcert72 {N p : Nat} (hN : 0 < N) (hodd : p % 2 = 1)
    (hlo : (99999997 / 10000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (10 / 1 : ℝ) * N) :
    (N : ℝ) * ((10 / 1 : ℝ) + (-1 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hpsLB72.kap N p : ℝ) := by
  have hl : 99999997 * N < 10000000 * p := by
    exact_mod_cast (show (99999997 : ℝ) * N < 10000000 * p by linarith)
  have hr : 1 * p ≤ 10 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 10 * N by linarith)
  have hp : 0 < p := by omega
  have hjrange : P72.L N / p + 2 ≤ 13 := by
    have h := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [p72_L]; omega : P72.L N < 11 * p)
    omega
  let ilo : Nat := 0
  have hv := hps_at72 (N := N) (p := p) (s := 8) (k1 := 6) (ilo := ilo) hp
    (by rw [p72_H]; omega) (by change (6 - 1) * p ≤ 72 * N - 6 * N; omega)
    (by simp only [ilo, hpEta, p72_H]; omega)
  have hap : perOK P72 N p 8 (-1) 6 ilo := by
    simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo]
    repeat' apply And.intro
    all_goals omega
  have hcp : (perJJ P72 N p 8 (-1) 6 ilo).card ≤ 7 := by
    have hsub : perJJ P72 N p 8 (-1) 6 ilo ⊆ Finset.Icc 1 7 := by
      intro J hJ
      simp only [perJJ, Finset.mem_filter, Finset.mem_range] at hJ
      have hJ' : J < 13 := hJ.1.trans_le hjrange
      have hj := hJ.2
      interval_cases J <;> simp only [Finset.mem_Icc] <;>
        simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo] at hj <;> omega
    exact (Finset.card_le_card hsub).trans (by decide)
  have hwp : ((perPmax P72 N p 8 (-1) 6).toNat - ilo + 1) ≤ perVal P72 N p 8 (-1) 6 ilo := by
    unfold perVal
    rw [if_pos hap]
    have hfac : 1 ≤ hpK (-1) 6 - (perJJ P72 N p 8 (-1) 6 ilo).card := by
      unfold hpK
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right ((perPmax P72 N p 8 (-1) 6).toNat - ilo + 1) hfac
  have hbound : 20 * N ≤ 2 * hpsLB72.kap N p + 4 + 2 * p := by
    generalize perVal P72 N p 8 (-1) 6 ilo = vp at hwp hv
    simp only [perOK, perPmax, perD0, hpJstar, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, ilo] at hwp
    omega
  have hboundR : 20 * N ≤ 2 * (hpsLB72.kap N p : ℝ) + 4 + 2 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((10 / 1 : ℝ) + (-1 / 1 : ℝ) * ((p : ℝ) / N)) =
      (10 / 1 : ℝ) * N + (-1 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w124_hcert72 {N p : Nat} (hN : 0 < N) (hodd : p % 2 = 1)
    (hlo : (182 / 17 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (97 / 9 : ℝ) * N) :
    (N : ℝ) * ((-91 / 1 : ℝ) + (17 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hpsLB72.kap N p : ℝ) := by
  have hl : 182 * N < 17 * p := by
    exact_mod_cast (show (182 : ℝ) * N < 17 * p by linarith)
  have hr : 9 * p ≤ 97 * N := by
    exact_mod_cast (show (9 : ℝ) * p ≤ 97 * N by linarith)
  have hp : 0 < p := by omega
  have hjrange : P72.L N / p + 2 ≤ 13 := by
    have h := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [p72_L]; omega : P72.L N < 11 * p)
    omega
  let ilo : Nat := 0
  have hv := hps_at72 (N := N) (p := p) (s := 8) (k1 := 5) (ilo := ilo) hp
    (by rw [p72_H]; omega) (by change (5 - 1) * p ≤ 72 * N - 6 * N; omega)
    (by simp only [ilo, hpEta, p72_H]; omega)
  have hah : hpOK P72 N p 8 (-1) 5 := by
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hch : (hpJJ P72 N p 8 (-1) 5).card ≤ 7 := by
    have hsub : hpJJ P72 N p 8 (-1) 5 ⊆ Finset.Icc 1 7 := by
      intro J hJ
      simp only [hpJJ, Finset.mem_filter, Finset.mem_range] at hJ
      have hJ' : J < 13 := hJ.1.trans_le hjrange
      have hj := hJ.2
      interval_cases J <;> simp only [Finset.mem_Icc] <;>
        simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hj <;> omega
    exact (Finset.card_le_card hsub).trans (by decide)
  have hwh : (hpD P72 N p 8 (-1) 5 - hpElo P72 N p 8) ≤ hpVal P72 N p 8 (-1) 5 := by
    unfold hpVal
    rw [if_pos hah]
    have hfac : 1 ≤ min (hpK (-1) 5) (hpK (-1) 5 + 1 - (hpJJ P72 N p 8 (-1) 5).card) := by
      unfold hpK
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right (hpD P72 N p 8 (-1) 5 - hpElo P72 N p 8) hfac
  have hbound : 17 * p ≤ 2 * hpsLB72.kap N p + 4 + 182 * N := by
    generalize hpVal P72 N p 8 (-1) 5 = vh at hwh hv
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hwh
    omega
  have hboundR : 17 * p ≤ 2 * (hpsLB72.kap N p : ℝ) + 4 + 182 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-91 / 1 : ℝ) + (17 / 2 : ℝ) * ((p : ℝ) / N)) =
      (-91 / 1 : ℝ) * N + (17 / 2 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w125_hcert72 {N p : Nat} (hN : 0 < N) (hodd : p % 2 = 1)
    (hlo : (97 / 9 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (87 / 8 : ℝ) * N) :
    (N : ℝ) * ((6 / 1 : ℝ) + (-1 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hpsLB72.kap N p : ℝ) := by
  have hl : 97 * N < 9 * p := by
    exact_mod_cast (show (97 : ℝ) * N < 9 * p by linarith)
  have hr : 8 * p ≤ 87 * N := by
    exact_mod_cast (show (8 : ℝ) * p ≤ 87 * N by linarith)
  have hp : 0 < p := by omega
  have hjrange : P72.L N / p + 2 ≤ 13 := by
    have h := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [p72_L]; omega : P72.L N < 11 * p)
    omega
  let ilo : Nat := 0
  have hv := hps_at72 (N := N) (p := p) (s := 8) (k1 := 5) (ilo := ilo) hp
    (by rw [p72_H]; omega) (by change (5 - 1) * p ≤ 72 * N - 6 * N; omega)
    (by simp only [ilo, hpEta, p72_H]; omega)
  have hah : hpOK P72 N p 8 (-1) 5 := by
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hch : (hpJJ P72 N p 8 (-1) 5).card ≤ 7 := by
    have hsub : hpJJ P72 N p 8 (-1) 5 ⊆ Finset.Icc 1 7 := by
      intro J hJ
      simp only [hpJJ, Finset.mem_filter, Finset.mem_range] at hJ
      have hJ' : J < 13 := hJ.1.trans_le hjrange
      have hj := hJ.2
      interval_cases J <;> simp only [Finset.mem_Icc] <;>
        simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hj <;> omega
    exact (Finset.card_le_card hsub).trans (by decide)
  have hwh : (hpD P72 N p 8 (-1) 5 - hpElo P72 N p 8) ≤ hpVal P72 N p 8 (-1) 5 := by
    unfold hpVal
    rw [if_pos hah]
    have hfac : 1 ≤ min (hpK (-1) 5) (hpK (-1) 5 + 1 - (hpJJ P72 N p 8 (-1) 5).card) := by
      unfold hpK
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right (hpD P72 N p 8 (-1) 5 - hpElo P72 N p 8) hfac
  have hbound : 12 * N ≤ 2 * hpsLB72.kap N p + 4 + 1 * p := by
    generalize hpVal P72 N p 8 (-1) 5 = vh at hwh hv
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hwh
    omega
  have hboundR : 12 * N ≤ 2 * (hpsLB72.kap N p : ℝ) + 4 + 1 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((6 / 1 : ℝ) + (-1 / 2 : ℝ) * ((p : ℝ) / N)) =
      (6 / 1 : ℝ) * N + (-1 / 2 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w126_hcert72 {N p : Nat} (hN : 0 < N) (hodd : p % 2 = 1)
    (hlo : (87 / 8 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (186 / 17 : ℝ) * N) :
    (N : ℝ) * ((93 / 1 : ℝ) + (-17 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hpsLB72.kap N p : ℝ) := by
  have hl : 87 * N < 8 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 8 * p by linarith)
  have hr : 17 * p ≤ 186 * N := by
    exact_mod_cast (show (17 : ℝ) * p ≤ 186 * N by linarith)
  have hp : 0 < p := by omega
  have hjrange : P72.L N / p + 2 ≤ 13 := by
    have h := (Nat.div_lt_iff_lt_mul hp).mpr (by rw [p72_L]; omega : P72.L N < 11 * p)
    omega
  let ilo : Nat := 0
  have hv := hps_at72 (N := N) (p := p) (s := 8) (k1 := 5) (ilo := ilo) hp
    (by rw [p72_H]; omega) (by change (5 - 1) * p ≤ 72 * N - 6 * N; omega)
    (by simp only [ilo, hpEta, p72_H]; omega)
  have hah : hpOK P72 N p 8 (-1) 5 := by
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hch : (hpJJ P72 N p 8 (-1) 5).card ≤ 7 := by
    have hsub : hpJJ P72 N p 8 (-1) 5 ⊆ Finset.Icc 1 7 := by
      intro J hJ
      simp only [hpJJ, Finset.mem_filter, Finset.mem_range] at hJ
      have hJ' : J < 13 := hJ.1.trans_le hjrange
      have hj := hJ.2
      interval_cases J <;> simp only [Finset.mem_Icc] <;>
        simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hj <;> omega
    exact (Finset.card_le_card hsub).trans (by decide)
  have hwh : (hpD P72 N p 8 (-1) 5 - hpElo P72 N p 8) ≤ hpVal P72 N p 8 (-1) 5 := by
    unfold hpVal
    rw [if_pos hah]
    have hfac : 1 ≤ min (hpK (-1) 5) (hpK (-1) 5 + 1 - (hpJJ P72 N p 8 (-1) 5).card) := by
      unfold hpK
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right (hpD P72 N p 8 (-1) 5 - hpElo P72 N p 8) hfac
  have hbound : 186 * N ≤ 2 * hpsLB72.kap N p + 4 + 17 * p := by
    generalize hpVal P72 N p 8 (-1) 5 = vh at hwh hv
    simp only [hpOK, hpD, hpDD, hpJstar, hpElo, hpEta, hh, p72_H, p72_L, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hwh
    omega
  have hboundR : 186 * N ≤ 2 * (hpsLB72.kap N p : ℝ) + 4 + 17 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((93 / 1 : ℝ) + (-17 / 2 : ℝ) * ((p : ℝ) / N)) =
      (93 / 1 : ℝ) * N + (-17 / 2 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
