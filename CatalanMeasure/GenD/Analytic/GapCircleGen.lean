module

public import CatalanMeasure.GenD.Analytic.GapWeights
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Analytic layer (CIRC): a piece cover proves `GapCircleBound`, any design

Generic form of `Parametric.GapCirclePieces`/`GapCircleCover` without logarithms.  Data: a radius
`r`, gap parameter `a` (rationals), exponents `d = n0 - g0`, `m = h0 + q0`, a rational `E` and a
list of pieces `(lo, hi, b1, b2, H, base)` of `|Re z|`.  A piece is `ok` when
`|z^2-1| <= b1`, `|z^2-a^2| <= b2`, `(b1+b2)/(1-a^2) <= H`, `H + sqrt(H^2-1) <= base`,
`base <= Csq`, and `base^d * (r^2+1+2 hi)^m <= E`.  The cover then gives
`|T_K(arg z)| |1-z|^(h+q) <= C exp(wc N)` for `K = (d N + 1)/2`, whenever `E <= exp(2 wc)` and
`Csq <= C^2`.  Squaring keeps the exponent `d N / 2` of the odd case exact (constant factor `base`).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Polynomial Polynomial.Chebyshev OAI.InternalCatalan CatalanMeasure.Parametric

noncomputable section

theorem gcg_norm_sq (z : ℂ) (c : ℝ) :
    ‖z ^ 2 - (c : ℂ) ^ 2‖ ^ 2 = (‖z‖ ^ 2 + c ^ 2) ^ 2 - 4 * c ^ 2 * z.re ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem gcg_arg_eval (a : ℝ) (z : ℂ) :
    ((gapArgument a).map (algebraMap ℝ ℂ)).eval z =
      (2 * z ^ 2 - (1 + (a : ℂ) ^ 2)) / (1 - (a : ℂ) ^ 2) := by
  simp only [gapArgument, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    Complex.coe_algebraMap, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem gcg_arg_dist {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (z : ℂ) :
    ‖((gapArgument a).map (algebraMap ℝ ℂ)).eval z - 1‖ = 2 * ‖z ^ 2 - 1‖ / (1 - a ^ 2) ∧
    ‖((gapArgument a).map (algebraMap ℝ ℂ)).eval z + 1‖ =
      2 * ‖z ^ 2 - (a : ℂ) ^ 2‖ / (1 - a ^ 2) := by
  have hd : 0 < 1 - a ^ 2 := by
    have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : 0 < 1 + a)
    nlinarith only [hh]
  have hdc : (1 : ℂ) - (a : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd.ne'
  have hnorm : ‖(1 : ℂ) - (a : ℂ) ^ 2‖ = 1 - a ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  rw [gcg_arg_eval]
  constructor
  · have he : (2 * z ^ 2 - (1 + (a : ℂ) ^ 2)) / (1 - (a : ℂ) ^ 2) - 1 =
        2 * (z ^ 2 - 1) / (1 - (a : ℂ) ^ 2) := by field_simp; ring
    rw [he, norm_div, norm_mul, Complex.norm_ofNat, hnorm]
  · have he : (2 * z ^ 2 - (1 + (a : ℂ) ^ 2)) / (1 - (a : ℂ) ^ 2) + 1 =
        2 * (z ^ 2 - (a : ℂ) ^ 2) / (1 - (a : ℂ) ^ 2) := by field_simp; ring
    rw [he, norm_div, norm_mul, Complex.norm_ofNat, hnorm]

theorem gcg_caps {a radius lo b1 b2 : ℝ}
    (hlo : 0 ≤ lo) (ha : 0 ≤ a) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hcap1 : (radius ^ 2 + 1) ^ 2 - 4 * lo ^ 2 ≤ b1 ^ 2)
    (hcap2 : (radius ^ 2 + a ^ 2) ^ 2 - 4 * a ^ 2 * lo ^ 2 ≤ b2 ^ 2)
    (z : ℂ) (hz : ‖z‖ = radius) (hs : lo ≤ |z.re|) :
    ‖z ^ 2 - 1‖ ≤ b1 ∧ ‖z ^ 2 - (a : ℂ) ^ 2‖ ≤ b2 := by
  have hsq : lo ^ 2 ≤ z.re ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ hlo hs 2
  have h1 := gcg_norm_sq z 1
  have h2 := gcg_norm_sq z a
  rw [hz] at h1 h2
  norm_num only [Complex.ofReal_one, one_pow, mul_one] at h1
  constructor
  · nlinarith only [h1, hcap1, hsq, norm_nonneg (z ^ 2 - 1), hb1]
  · have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * a ^ 2)
    nlinarith only [h2, hcap2, hh, norm_nonneg (z ^ 2 - (a : ℂ) ^ 2), hb2]

theorem gcg_filter {radius hi : ℝ} (z : ℂ) (hz : ‖z‖ = radius) (hs : |z.re| ≤ hi) :
    ‖(1 : ℂ) - z‖ ^ 2 ≤ radius ^ 2 + 1 + 2 * hi := by
  have hnorm := Complex.sq_norm_sub_sq_re z
  rw [hz] at hnorm
  have he : ‖(1 : ℂ) - z‖ ^ 2 = (1 - z.re) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [he]
  have hh := (abs_le.mp hs).1
  nlinarith only [hnorm, hh]

structure CircPiece where
  lo : ℚ
  hi : ℚ
  b1 : ℚ
  b2 : ℚ
  H : ℚ
  base : ℚ

def CircPiece.ok (a r E Csq : ℚ) (d m : ℕ) (p : CircPiece) : Bool :=
  decide (0 ≤ p.lo ∧ p.lo ≤ p.hi ∧ p.hi ≤ r ∧ 0 ≤ p.b1 ∧ 0 ≤ p.b2 ∧ 0 ≤ p.H ∧ p.H ≤ p.base ∧
    1 ≤ p.base ∧ p.base ≤ Csq ∧
    (r ^ 2 + 1) ^ 2 - 4 * p.lo ^ 2 ≤ p.b1 ^ 2 ∧
    (r ^ 2 + a ^ 2) ^ 2 - 4 * a ^ 2 * p.lo ^ 2 ≤ p.b2 ^ 2 ∧
    p.b1 + p.b2 ≤ p.H * (1 - a ^ 2) ∧ p.H ^ 2 - 1 ≤ (p.base - p.H) ^ 2 ∧
    p.base ^ d * (r ^ 2 + 1 + 2 * p.hi) ^ m ≤ E)

def circCover (a r E Csq : ℚ) (d m : ℕ) : ℚ → List CircPiece → Bool
  | c, [] => decide (c = r)
  | c, p :: l => decide (p.lo = c) && p.ok a r E Csq d m && circCover a r E Csq d m p.hi l

theorem circCover_exists {a r E Csq : ℚ} {d m : ℕ} {c : ℚ} {l : List CircPiece}
    (h : circCover a r E Csq d m c l = true) {s : ℝ} (hs : (c : ℝ) ≤ s) (hs2 : s ≤ (r : ℝ))
    (hne : (c : ℝ) < s ∨ l ≠ []) :
    ∃ p ∈ l, p.ok a r E Csq d m = true ∧ (p.lo : ℝ) ≤ s ∧ s ≤ (p.hi : ℝ) := by
  induction l generalizing c with
  | nil =>
    simp only [circCover, decide_eq_true_eq] at h
    subst h
    rcases hne with h1 | h1
    · exact absurd hs2 (not_le.mpr h1)
    · exact absurd rfl h1
  | cons p l ih =>
    simp only [circCover, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hp⟩, hrest⟩ := h
    by_cases hs1 : s ≤ (p.hi : ℝ)
    · exact ⟨p, by simp, hp, by rw [hc]; exact hs, hs1⟩
    · obtain ⟨q, hq, hq2⟩ := ih hrest (le_of_lt (not_le.mp hs1)) (Or.inl (not_le.mp hs1))
      exact ⟨q, List.mem_cons_of_mem _ hq, hq2⟩

theorem CircPiece.bound {a r E Csq : ℚ} {d m : ℕ} (ha0 : (0 : ℝ) < a) (ha1 : (a : ℝ) < 1)
    (p : CircPiece) (hp : p.ok a r E Csq d m = true) (N : ℕ) (z : ℂ) (hz : ‖z‖ = (r : ℝ))
    (hs : |z.re| ∈ Set.Icc (p.lo : ℝ) p.hi) :
    (‖((gapPolyK (a : ℝ) ((d * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 ≤ (Csq : ℝ) * (E : ℝ) ^ N := by
  obtain ⟨hlo, hlh, hhr, hb1, hb2, hH0, hHB, hB1, hBR, hc1, hc2, hHC, hBC, hE⟩ :=
    of_decide_eq_true hp
  have hd : (0 : ℝ) < 1 - (a : ℝ) ^ 2 := by
    have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : (0 : ℝ) < 1 + a)
    nlinarith only [hh]
  have hc1R : ((r : ℝ) ^ 2 + 1) ^ 2 - 4 * (p.lo : ℝ) ^ 2 ≤ (p.b1 : ℝ) ^ 2 := by
    exact_mod_cast hc1
  have hc2R : ((r : ℝ) ^ 2 + (a : ℝ) ^ 2) ^ 2 - 4 * (a : ℝ) ^ 2 * (p.lo : ℝ) ^ 2 ≤
      (p.b2 : ℝ) ^ 2 := by exact_mod_cast hc2
  have hc := gcg_caps (a := (a : ℝ)) (radius := (r : ℝ)) (lo := (p.lo : ℝ))
    (b1 := (p.b1 : ℝ)) (b2 := (p.b2 : ℝ)) (by exact_mod_cast hlo) ha0.le
    (by exact_mod_cast hb1) (by exact_mod_cast hb2) hc1R hc2R z hz hs.1
  have hdist := gcg_arg_dist ha0 ha1 z
  set w : ℂ := ((gapArgument (a : ℝ)).map (algebraMap ℝ ℂ)).eval z with hw
  set H : ℝ := (‖w - 1‖ + ‖w + 1‖) / 2 with hHdef
  have hH0' : 0 ≤ H := by positivity
  have hHR : (p.b1 : ℝ) + p.b2 ≤ (p.H : ℝ) * (1 - (a : ℝ) ^ 2) := by exact_mod_cast hHC
  have hHi : H ≤ (p.H : ℝ) := by
    rw [hHdef, hdist.1, hdist.2]
    have : (2 * ‖z ^ 2 - 1‖ / (1 - (a : ℝ) ^ 2) +
        2 * ‖z ^ 2 - ((a : ℝ) : ℂ) ^ 2‖ / (1 - (a : ℝ) ^ 2)) / 2 =
        (‖z ^ 2 - 1‖ + ‖z ^ 2 - ((a : ℝ) : ℂ) ^ 2‖) / (1 - (a : ℝ) ^ 2) := by ring
    rw [this, div_le_iff₀ hd]
    nlinarith only [hc.1, hc.2, hHR]
  have hbr : (0 : ℝ) ≤ (p.base : ℝ) - p.H := by exact_mod_cast sub_nonneg.mpr hHB
  have hroot : Real.sqrt (H ^ 2 - 1) ≤ (p.base : ℝ) - (p.H : ℝ) := by
    rw [Real.sqrt_le_left hbr]
    have hnum : (p.H : ℝ) ^ 2 - 1 ≤ ((p.base : ℝ) - (p.H : ℝ)) ^ 2 := by exact_mod_cast hBC
    have hHsq := pow_le_pow_left₀ hH0' hHi 2
    linarith only [hHsq, hnum]
  have hbase1 : (1 : ℝ) ≤ p.base := by exact_mod_cast hB1
  set K : ℕ := (d * N + 1) / 2 with hK
  have hT : ‖(T ℂ (K : ℤ)).eval w‖ ≤ (p.base : ℝ) ^ K := by
    apply (CatalanMeasure.norm_T_eval_le K w).trans
    apply pow_le_pow_left₀ (by positivity)
    change H + Real.sqrt (H ^ 2 - 1) ≤ (p.base : ℝ)
    linarith only [hHi, hroot]
  have he : ‖((gapPolyK (a : ℝ) K).map (algebraMap ℝ ℂ)).eval z‖ = ‖(T ℂ (K : ℤ)).eval w‖ := by
    rw [gapPolyK, Polynomial.map_comp, Chebyshev.map_T, eval_comp]
  have hT2 : ‖((gapPolyK (a : ℝ) K).map (algebraMap ℝ ℂ)).eval z‖ ^ 2 ≤
      (p.base : ℝ) ^ (d * N + 1) := by
    rw [he]
    calc _ ≤ ((p.base : ℝ) ^ K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hT 2
      _ = (p.base : ℝ) ^ (2 * K) := by rw [← pow_mul, mul_comm]
      _ ≤ (p.base : ℝ) ^ (d * N + 1) := pow_le_pow_right₀ hbase1 (by omega)
  have hf := gcg_filter (hi := (p.hi : ℝ)) z hz hs.2
  have hhi0 : (0 : ℝ) ≤ p.hi := by exact_mod_cast (le_trans hlo hlh)
  have hF0 : (0 : ℝ) ≤ (r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ) := by positivity
  have hf2 : (‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 ≤ (((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N := by
    calc (‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 = (‖(1 : ℂ) - z‖ ^ 2) ^ (m * N) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ (m * N) := pow_le_pow_left₀ (sq_nonneg _) hf _
      _ = (((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N := by rw [pow_mul]
  have hER : (p.base : ℝ) ^ d * ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m ≤ (E : ℝ) := by
    exact_mod_cast hE
  have hBR' : (p.base : ℝ) ≤ (Csq : ℝ) := by exact_mod_cast hBR
  have hbase0 : (0 : ℝ) ≤ p.base := by linarith only [hbase1]
  have hE0 : (0 : ℝ) ≤ (p.base : ℝ) ^ d * ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m := by
    positivity
  rw [mul_pow]
  calc _ ≤ (p.base : ℝ) ^ (d * N + 1) * (((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N :=
        mul_le_mul hT2 hf2 (by positivity) (by positivity)
    _ = (p.base : ℝ) * ((p.base : ℝ) ^ d * ((r : ℝ) ^ 2 + 1 + 2 * (p.hi : ℝ)) ^ m) ^ N := by
        rw [mul_pow, ← pow_mul, pow_succ]; ring
    _ ≤ (Csq : ℝ) * (E : ℝ) ^ N :=
        mul_le_mul hBR' (pow_le_pow_left₀ hE0 hER N) (by positivity)
          (by linarith only [hBR', hbase1])

/-- A piece cover certifies the circle estimate `GapCircleBound` (any design with
`n0 - g0 = d`, `h0 + q0 = m`). -/
theorem gapCircleBound_of_cover (P : Parameters) {d m : ℕ} (hd : P.n0 - P.g0 = d)
    (hm : P.h0 + P.q0 = m) {a r E Csq : ℚ} {pieces : List CircPiece}
    (ha0 : (0 : ℝ) < a) (ha1 : (a : ℝ) < 1)
    (hE0 : (0 : ℝ) ≤ E) (hne : pieces ≠ []) (hcov : circCover a r E Csq d m 0 pieces = true)
    {C wc : ℝ} (hC : 0 ≤ C) (hCsq : (Csq : ℝ) ≤ C ^ 2) (hEw : (E : ℝ) ≤ Real.exp (2 * wc)) :
    GapCircleBound P (a : ℝ) (r : ℝ) C wc := by
  intro N z hN hz
  have hs0 : |z.re| ≤ (r : ℝ) := by simpa only [hz] using Complex.abs_re_le_norm z
  obtain ⟨p, hpm, hpok, hlo, hhi⟩ :=
    circCover_exists hcov (by simp) hs0 (Or.inr hne)
  have hb := CircPiece.bound ha0 ha1 p hpok N z hz ⟨hlo, hhi⟩
  have hmN : P.h N + P.q N = m * N := by
    simp only [Parameters.h, Parameters.q]
    rw [← add_mul, hm]
  rw [hmN, hd]
  have hexp : (Real.exp (2 * wc)) ^ N = Real.exp (wc * N) ^ 2 := by
    rw [← Real.exp_nat_mul, sq, ← Real.exp_add]; congr 1; ring
  have hmain : (‖((gapPolyK (a : ℝ) ((d * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1 : ℂ) - z‖ ^ (m * N)) ^ 2 ≤ (C * Real.exp (wc * N)) ^ 2 := by
    calc _ ≤ (Csq : ℝ) * (E : ℝ) ^ N := hb
      _ ≤ C ^ 2 * (Real.exp (2 * wc)) ^ N := by
          exact mul_le_mul hCsq (pow_le_pow_left₀ hE0 hEw N) (pow_nonneg hE0 N) (sq_nonneg C)
      _ = _ := by rw [hexp, mul_pow]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hmain

open Finset

/-! ### Separated radii (any `r > 0`): keyhole weight bounds (S1)

The radius-`> 1` estimates of `GapWeights` carry the separation `r - 1` from the nodes.  For the
keyhole contour of PROOF-RHO Lemma KH the circle has radius `r ≤ 1`; the separation is then a
hypothesis `δ ≤ |p_i - r|` on the moduli `p_i` of the roots of `T_K(arg)`. -/

/-- `norm_cardinal_le_of_nodal` with the distance to the node as a hypothesis (any radius). -/
theorem norm_cardinal_le_of_nodal_sep {J : ℕ} {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (i : Fin J) {P : ℝ[X]} {c d δ : ℝ}
    (hP : P = C c * ∏ j : Fin J, (X - C (τ j)))
    (hd : 0 < d) (hder : d ≤ |(derivative P).eval (τ i)|)
    (hδ : 0 < δ) (z : ℂ) (hz : δ ≤ ‖z - (τ i : ℂ)‖) :
    ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      ‖(P.map (algebraMap ℝ ℂ)).eval z‖ / (d * δ) := by
  have he := congrArg (fun Q : ℝ[X] => (Q.map (algebraMap ℝ ℂ)).eval z)
    (quad_basis_mul_derivative_eq hτ i hP)
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub, Polynomial.map_X,
    eval_mul, eval_C, eval_sub, eval_X, Complex.coe_algebraMap] at he
  have hn := congrArg norm he
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hn
  apply (le_div_iff₀ (mul_pos hd hδ)).mpr
  calc
    _ ≤ ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ *
        |(derivative P).eval (τ i)| * ‖z - (τ i : ℂ)‖ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hder hz hδ.le (abs_nonneg _)) (norm_nonneg _)
    _ = _ := hn

/-- The modulus of every node is one of the positive roots `posNode`. -/
theorem gap_node_abs_eq_posNode (a : ℝ) (J : ℕ) (j : Fin J) :
    ∃ i : Fin ((J + 1) / 2), |gapNodesGen a J j| = posNode a ((J + 1) / 2) i := by
  unfold gapNodesGen
  generalize Fin.cast (show J = (J + 1) / 2 + J / 2 by omega) j = jj
  induction jj using Fin.addCases with
  | left i =>
    exact ⟨i, by rw [gapNodesKL_left]; exact abs_of_nonneg (Real.sqrt_nonneg _)⟩
  | right i =>
    exact ⟨Fin.castLE (show J / 2 ≤ (J + 1) / 2 by omega) i, by
      rw [gapNodesKL_right, abs_neg]; exact abs_of_nonneg (Real.sqrt_nonneg _)⟩

/-- Lower bound of the dropped factor on `|z| = r` from the separation of `r` from the moduli. -/
theorem gapExtra_norm_ge_of_sep {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) {r δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ i : Fin ((J + 1) / 2), δ ≤ |posNode a ((J + 1) / 2) i - r|)
    (z : ℂ) (hz : ‖z‖ = r) :
    δ ≤ ‖((gapExtra a J).map (algebraMap ℝ ℂ)).eval z‖ := by
  unfold gapExtra
  rw [Polynomial.map_prod, eval_prod, norm_prod]
  have hf : ∀ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val),
      δ ≤ ‖(((X + C (posNode a ((J + 1) / 2) i) : ℝ[X]).map (algebraMap ℝ ℂ)).eval z)‖ := by
    intro i _
    have hp := pos_node_bounds ha0 ha1 ((J + 1) / 2) i
    simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, eval_add, eval_X, eval_C,
      Complex.coe_algebraMap]
    have hh3 := abs_norm_sub_norm_le (-(posNode a ((J + 1) / 2) i : ℂ)) z
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, hz,
      abs_of_pos (show 0 < posNode a ((J + 1) / 2) i by linarith only [ha0, hp.1])] at hh3
    have hh4 : ‖-(posNode a ((J + 1) / 2) i : ℂ) - z‖ = ‖z + (posNode a ((J + 1) / 2) i : ℂ)‖ := by
      rw [← norm_neg]; congr 1; ring
    rw [hh4] at hh3
    exact (hsep i).trans hh3
  have hc : ∏ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val), δ ≤
      ∏ i ∈ univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val),
        ‖(((X + C (posNode a ((J + 1) / 2) i) : ℝ[X]).map (algebraMap ℝ ℂ)).eval z)‖ :=
    Finset.prod_le_prod₀ (fun _ _ => hδ0.le) hf
  rw [prod_const] at hc
  have hcard := gapExtra_card_le a J
  have hle : δ ^ 1 ≤ δ ^ (univ.filter (fun i : Fin ((J + 1) / 2) => J / 2 ≤ i.val)).card :=
    pow_le_pow_of_le_one hδ0.le hδ1 hcard
  simpa using hle.trans hc

/-- **Cardinal polynomial of the gap nodes on `|z| = r`, any `r > 0` separated from the moduli of
the roots by `δ`.**  Generalises `gap_cardinal_norm_le` (where `δ = r - 1`). -/
theorem gap_cardinal_norm_le_of_sep {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {J : ℕ} (hJ : 0 < J)
    (hD : 1 ≤ 4 * (((J + 1) / 2 : ℕ) : ℝ) * a / (1 - a ^ 2))
    {r δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ i : Fin ((J + 1) / 2), δ ≤ |posNode a ((J + 1) / 2) i - r|)
    (i : Fin J) (z : ℂ) (hz : ‖z‖ = r) :
    ‖((quadBasis (gapNodesGen a J) i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      2 * ‖((gapPolyK a ((J + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ / δ ^ 2 := by
  set lead := gapLead a ((J + 1) / 2) with hlead
  have hl : 0 < lead := gapLead_pos ha0 ha1 _
  have hQ : gapNodal a J = C 1 * ∏ j : Fin J, (X - C (gapNodesGen a J j)) := by
    simp [gapNodal]
  have hτ := gap_nodes_injective ha0 ha1 J
  have hmem : ∀ j, gapNodesGen a J j ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun j => (gap_nodes_bounds ha0 ha1 J j).1
  have hE2 := gapExtra_eval_abs_le ha0 ha1 J (t := gapNodesGen a J i)
    (abs_le.mpr ⟨by linarith only [(hmem i).1], by linarith only [(hmem i).2]⟩)
  have hPd := gapPolyK_derivative_ge ha0 ha1 J i
  have hPn := gapPolyK_derivative_node ha0 ha1 hJ i
  have hder : 1 / (2 * lead) ≤ |(derivative (gapNodal a J)).eval (gapNodesGen a J i)| := by
    rw [hPn, abs_mul, abs_mul, abs_of_pos hl] at hPd
    have h1 : 1 ≤ lead * (|(derivative (gapNodal a J)).eval (gapNodesGen a J i)| *
        |(gapExtra a J).eval (gapNodesGen a J i)|) := hD.trans hPd
    have h2 : lead * (|(derivative (gapNodal a J)).eval (gapNodesGen a J i)| *
        |(gapExtra a J).eval (gapNodesGen a J i)|) ≤
        lead * (|(derivative (gapNodal a J)).eval (gapNodesGen a J i)| * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE2 (abs_nonneg _)) hl.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [h1, h2]
  have hdist : δ ≤ ‖z - (gapNodesGen a J i : ℂ)‖ := by
    obtain ⟨i', hi'⟩ := gap_node_abs_eq_posNode a J i
    have hh := abs_norm_sub_norm_le z (gapNodesGen a J i : ℂ)
    rw [hz, Complex.norm_real, Real.norm_eq_abs, hi'] at hh
    have hs := hsep i'
    rw [abs_sub_comm] at hh
    exact hs.trans hh
  have hcard := norm_cardinal_le_of_nodal_sep hτ i hQ (by positivity) hder hδ0 z hdist
  have hP := congrArg (fun Q : ℝ[X] => ‖(Q.map (algebraMap ℝ ℂ)).eval z‖)
    (gapPolyK_eq_nodal ha0 ha1 hJ)
  simp only [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, norm_mul,
    Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl] at hP
  have hE := gapExtra_norm_ge_of_sep ha0 ha1 J hδ0 hδ1 hsep z hz
  set A := ‖((gapPolyK a ((J + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ with hA
  set q := ‖((gapNodal a J).map (algebraMap ℝ ℂ)).eval z‖ with hq
  set e := ‖((gapExtra a J).map (algebraMap ℝ ℂ)).eval z‖ with he
  have hq0 : 0 ≤ q := norm_nonneg _
  have hlq : lead * q * δ ≤ A := by
    have := mul_le_mul_of_nonneg_left hE (mul_nonneg hl.le hq0)
    have hP' : A = lead * (q * e) := by rw [hP, abs_of_pos hl]
    nlinarith only [this, hP']
  have hstep : q / (1 / (2 * lead) * δ) ≤ 2 * A / δ ^ 2 := by
    rw [show q / (1 / (2 * lead) * δ) = 2 * (lead * q) / δ by field_simp]
    rw [div_le_div_iff₀ hδ0 (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hlq (by positivity : (0 : ℝ) ≤ 2 * δ)]
  exact hcard.trans hstep

/-- **Keyhole form of the gap-node weight** (PROOF-RHO 2.2 with the node estimates): the circle
`|z| = r` (`0 < r ≤ 1`) is separated from the moduli of the roots by `δ`, the circle estimate
`GapCircleBound` holds, and the cardinal function is bounded by `B₀` against `|1-x|^(h+q)` on the
real segments `r ≤ |x| ≤ 1`.  Then every column weight satisfies
`|common(τ_j)| |weight_k(τ_j)| ≤ 4 (1 + (k - 2g)) max(1, r^A/r^(b+k+q)) max(2 C e^{wc N}/δ², B₀)`. -/
theorem gap_weight_joint_keyhole_le (P : Parameters) (hg : P.g0 ≤ P.n0) {a r C wc δ B₀ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (ha4 : 1 - a ^ 2 ≤ 4 * a)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcirc : GapCircleBound P a r C wc) (N k : ℕ) (j : Fin ((P.n0 - P.g0) * N))
    (hsep : ∀ i : Fin (((P.n0 - P.g0) * N + 1) / 2),
      δ ≤ |posNode a (((P.n0 - P.g0) * N + 1) / 2) i - r|)
    (hseg : ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 →
      |(quadBasis (gapNodesD P a N) j).eval x| * |1 - x| ^ (P.h N + P.q N) ≤ B₀) :
    |(rowCommonFactor P N).eval (gapNodesD P a N j)| *
      |restrictedWeight P N k (gapNodesD P a N) j| ≤
      4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) *
        (max 1 (r ^ P.A N / r ^ (P.b N + k + P.q N)) *
          max (2 * (C * Real.exp (wc * N)) / δ ^ 2) B₀) := by
  have hJ : 0 < (P.n0 - P.g0) * N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hJ)
  have hd := gapSq_pos ha0 ha1
  have hD : 1 ≤ 4 * ((((P.n0 - P.g0) * N + 1) / 2 : ℕ) : ℝ) * a / (1 - a ^ 2) := by
    rw [le_div_iff₀ hd]
    have : (1 : ℝ) ≤ ((((P.n0 - P.g0) * N + 1) / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ ((P.n0 - P.g0) * N + 1) / 2 by omega)
    nlinarith only [this, ha4, ha0]
  have hn := rowCommonFactor_eval_ne_zero_of P N (gap_nodes_ne_zero ha0 ha1 _ j)
    (gap_nodes_ne_one ha0 ha1 _ j)
  apply restrictedWeight_joint_le_of_keyhole P N k j hn
    (gap_common_basis_coeff_zero P hg N ha0 ha1 j) hr0 hr1 _ hseg
  intro z hz
  have hc := gap_cardinal_norm_le_of_sep ha0 ha1 hJ hD hδ0 hδ1 hsep j z hz
  have hb := hcirc N z hN hz
  calc _ ≤ (2 * ‖((gapPolyK a (((P.n0 - P.g0) * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval z‖ /
        δ ^ 2) * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 / δ ^ 2 * (‖((gapPolyK a (((P.n0 - P.g0) * N + 1) / 2)).map
          (algebraMap ℝ ℂ)).eval z‖ * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N)) := by ring
    _ ≤ 2 / δ ^ 2 * (C * Real.exp (wc * N)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end

end Analytic
end CatalanMeasure.GenD

#print axioms CatalanMeasure.GenD.Analytic.gap_cardinal_norm_le_of_sep

#print axioms CatalanMeasure.GenD.Analytic.gap_weight_joint_keyhole_le
