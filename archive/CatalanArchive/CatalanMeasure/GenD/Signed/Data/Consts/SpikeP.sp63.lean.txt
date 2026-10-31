module

public import CatalanMeasure.GenD.Signed.Data.Consts.ZPoly

/-!
# D2 constants: the (P') polynomial certificate of the spike classes (generic soundness)

For a trial with Chebyshev coefficients `bs` (dyadic, denominator `2^60`), `Pn` the integer
numerators of the monomial form of `chebPs (bSeq bs)` (checked once by `chebMono bs = Pn / 2^60`),
and one `q`-piece with `rho = r / 2^11`, `kappa = K / 2^14`, `c1 = 2^-j`:

* `floor_sound`: `1/4 <= chebPs (bSeq bs)` on `[-1, 1]` from a cell chain for `Pn - 2^58`;
* `spikePoly_sound`: the hypothesis `hpoly` of `SpikeTrialCert` from a cell chain for `spikeQ`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan

theorem lpEval_dyadic (ns : List ℤ) (sh : ℕ) (x : ℝ) :
    lpEval (ns.map (fun n : ℤ => (n : ℚ) / 2 ^ sh)) x = zv ns x / 2 ^ sh := by
  induction ns with
  | nil => simp [zv_nil]
  | cons c L ih =>
    simp only [List.map_cons, lpEval_cons, zv_cons]
    rw [ih]; push_cast; field_simp

theorem chebPs_of_int (bs : List ℚ) (Pn : List ℤ) (sh : ℕ)
    (h : chebMono bs = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ sh)) (u : ℝ) :
    chebPs (bSeq bs) u = zv Pn u / 2 ^ sh := by
  rw [chebPs_bSeq, h, lpEval_dyadic]

/-- Cut-chain from `-1` to `1` on the grid `2^-S`. -/
def covM1P1 (c : List ℤ) (S : ℕ) (cs : List ℤ) : Bool := zNonnegCov c S (-(2 : ℤ) ^ S) cs (2 ^ S)

theorem covM1P1_sound {c : List ℤ} {S : ℕ} {cs : List ℤ} (h : covM1P1 c S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1, 0 ≤ zv c u := by
  intro u hu
  have h2 : (0 : ℝ) < 2 ^ S := by positivity
  refine zNonnegCov_sound c S cs _ _ h u ?_ ?_
  · push_cast; rw [neg_div, div_self h2.ne']; exact hu.1
  · push_cast; rw [div_self h2.ne']; exact hu.2

theorem floor_sound {Pn : List ℤ} {S : ℕ} {cs : List ℤ}
    (h : covM1P1 (zAdd Pn [-(2 : ℤ) ^ 58]) S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1, 1 / 4 ≤ zv Pn u / 2 ^ 60 := by
  intro u hu
  have := covM1P1_sound h u hu
  rw [zv_add, zv_cons, zv_nil] at this
  push_cast at this
  have e : (2 : ℝ) ^ 60 = 4 * 2 ^ 58 := by norm_num
  rw [le_div_iff₀ (by positivity), e]
  nlinarith

/-- Integer polynomial of (P') (all scaled by `2^(60+22)`), `rho = r/2^11`, `kappa = K/2^14`,
`c1 = 2^-j`, `j <= 46`. -/
def spikeQ (Pn : List ℤ) (r K j : ℕ) : List ℤ :=
  zAdd (zMulAff (2 ^ 22 + (r : ℤ) ^ 2) (2 * r * 2 ^ 11)
      (zAdd Pn [-(((2 : ℤ) ^ 14 - K) * 2 ^ (46 - j))]))
    [-((K : ℤ) * (2 ^ 22 - (r : ℤ) ^ 2) * 2 ^ 46)]

theorem spikeQ_eval (Pn : List ℤ) (r K j : ℕ) (hj : j ≤ 46) (u : ℝ) :
    zv (spikeQ Pn r K j) u = 2 ^ 82 *
      (((zv Pn u / 2 ^ 60) - (1 - (K : ℝ) / 2 ^ 14) * (1 / 2 ^ j)) *
        (1 + 2 * ((r : ℝ) / 2 ^ 11) * u + ((r : ℝ) / 2 ^ 11) ^ 2) -
        ((K : ℝ) / 2 ^ 14) * (1 - ((r : ℝ) / 2 ^ 11) ^ 2)) := by
  have hpow : (2 : ℝ) ^ (46 - j) * 2 ^ j = 2 ^ 46 := by rw [← pow_add, Nat.sub_add_cancel hj]
  have hj0 : (2 : ℝ) ^ j ≠ 0 := by positivity
  have e46 : (2 : ℝ) ^ (46 - j) = 2 ^ 46 / 2 ^ j := by
    rw [eq_div_iff hj0]; exact hpow
  unfold spikeQ
  rw [zv_add, zv_mulAff, zv_add, zv_cons, zv_nil, zv_cons, zv_nil]
  push_cast
  rw [e46]
  field_simp
  ring

theorem spikePoly_sound {Pn : List ℤ} {S r K j : ℕ} (hj : j ≤ 46) {cs : List ℤ}
    (h : covM1P1 (spikeQ Pn r K j) S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1,
      ((K : ℝ) / 2 ^ 14) * (1 - ((r : ℝ) / 2 ^ 11) ^ 2) ≤
        ((zv Pn u / 2 ^ 60) - (1 - (K : ℝ) / 2 ^ 14) * (1 / 2 ^ j)) *
          (1 + 2 * ((r : ℝ) / 2 ^ 11) * u + ((r : ℝ) / 2 ^ 11) ^ 2) := by
  intro u hu
  have h1 := covM1P1_sound h u hu
  rw [spikeQ_eval Pn r K j hj] at h1
  have : (0 : ℝ) < 2 ^ 82 := by positivity
  have h2 := (mul_nonneg_iff_of_pos_left this).mp h1
  linarith

theorem floor_chebPs {bs : List ℚ} {Pn : List ℤ} {S : ℕ} {cs : List ℤ}
    (hc : chebMono bs = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))
    (h : covM1P1 (zAdd Pn [-(2 : ℤ) ^ 58]) S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1, 1 / 4 ≤ chebPs (bSeq bs) u := by
  intro u hu
  rw [chebPs_of_int bs Pn 60 hc]
  exact floor_sound h u hu

theorem spikePoly_chebPs {bs : List ℚ} {Pn : List ℤ} {S r K j : ℕ} {cs : List ℤ} (hj : j ≤ 46)
    (hc : chebMono bs = Pn.map (fun n : ℤ => (n : ℚ) / 2 ^ 60))
    (h : covM1P1 (spikeQ Pn r K j) S cs = true) :
    ∀ u ∈ Icc (-1 : ℝ) 1,
      ((K : ℝ) / 2 ^ 14) * (1 - ((r : ℝ) / 2 ^ 11) ^ 2) ≤
        (chebPs (bSeq bs) u - (1 - (K : ℝ) / 2 ^ 14) * (1 / 2 ^ j)) *
          (1 + 2 * ((r : ℝ) / 2 ^ 11) * u + ((r : ℝ) / 2 ^ 11) ^ 2) := by
  intro u hu
  rw [chebPs_of_int bs Pn 60 hc]
  exact spikePoly_sound hj h u hu

end CatalanMeasure.Signed.Consts
